// Lean compiler output
// Module: Lean.DocString.Formatter
// Imports: public import Lean.PrettyPrinter.Formatter import Lean.DocString.Parser
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLit(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_metadataContents_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NON-ATOM "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NON-IDENT "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_str"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value),LEAN_SCALAR_PTR_LITERAL(28, 110, 66, 227, 168, 59, 232, 226)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_num"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value),LEAN_SCALAR_PTR_LITERAL(14, 247, 226, 130, 46, 200, 13, 201)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "arg_ident"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 49, 249, 222, 84, 35, 6, 34)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "named"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value),LEAN_SCALAR_PTR_LITERAL(240, 209, 4, 173, 176, 102, 100, 110)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "named_no_paren"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value),LEAN_SCALAR_PTR_LITERAL(52, 78, 240, 214, 103, 62, 217, 25)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "flag_on"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(156, 222, 140, 123, 199, 224, 2, 54)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "flag_off"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__15 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__15_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__15_value),LEAN_SCALAR_PTR_LITERAL(29, 0, 37, 229, 12, 38, 20, 228)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "anon"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__17 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__17_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__17_value),LEAN_SCALAR_PTR_LITERAL(151, 30, 185, 65, 40, 8, 94, 56)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__19 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__19_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__19_value),LEAN_SCALAR_PTR_LITERAL(252, 149, 124, 218, 116, 154, 240, 105)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "emph"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__21 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__21_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(76, 183, 215, 94, 0, 242, 191, 239)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bold"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__23 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__23_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__23_value),LEAN_SCALAR_PTR_LITERAL(217, 240, 207, 144, 35, 3, 119, 11)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "link"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__25 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__25_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__25_value),LEAN_SCALAR_PTR_LITERAL(129, 184, 35, 28, 112, 167, 76, 80)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "image"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__27 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__27_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__27_value),LEAN_SCALAR_PTR_LITERAL(156, 113, 65, 80, 13, 110, 129, 61)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "role"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__29 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__29_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__29_value),LEAN_SCALAR_PTR_LITERAL(88, 39, 13, 65, 153, 69, 141, 111)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__31 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__31_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__31_value),LEAN_SCALAR_PTR_LITERAL(115, 95, 172, 118, 77, 213, 142, 126)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "footnote"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__33 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__33_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__33_value),LEAN_SCALAR_PTR_LITERAL(207, 87, 199, 0, 139, 133, 244, 123)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linebreak"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__35 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__35_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__35_value),LEAN_SCALAR_PTR_LITERAL(204, 183, 85, 224, 226, 177, 67, 207)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inline_math"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__37 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__37_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__37_value),LEAN_SCALAR_PTR_LITERAL(39, 58, 152, 4, 55, 96, 114, 182)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "display_math"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__39 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__39_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__39_value),LEAN_SCALAR_PTR_LITERAL(185, 134, 189, 58, 202, 192, 153, 244)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ref"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__41 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__41_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__41_value),LEAN_SCALAR_PTR_LITERAL(157, 197, 143, 220, 44, 158, 31, 133)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "url"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__43 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__43_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__43_value),LEAN_SCALAR_PTR_LITERAL(97, 109, 202, 165, 136, 148, 125, 206)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__45 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__45_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__45_value),LEAN_SCALAR_PTR_LITERAL(138, 131, 27, 234, 140, 72, 2, 168)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "para"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__47 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__47_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__47_value),LEAN_SCALAR_PTR_LITERAL(114, 72, 198, 245, 142, 145, 171, 144)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ul"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__49 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__49_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__49_value),LEAN_SCALAR_PTR_LITERAL(248, 90, 162, 51, 92, 30, 144, 89)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ol"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__51 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__51_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__51_value),LEAN_SCALAR_PTR_LITERAL(70, 73, 192, 118, 161, 88, 51, 173)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "blockquote"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__53 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__53_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__53_value),LEAN_SCALAR_PTR_LITERAL(154, 37, 74, 205, 107, 38, 107, 223)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "codeblock"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__55 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__55_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__55_value),LEAN_SCALAR_PTR_LITERAL(228, 242, 241, 127, 13, 6, 27, 177)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "directive"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__57 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__57_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__57_value),LEAN_SCALAR_PTR_LITERAL(59, 236, 126, 236, 245, 181, 4, 182)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__59 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__59_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__59_value),LEAN_SCALAR_PTR_LITERAL(163, 102, 246, 27, 44, 229, 232, 70)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "li"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(86, 229, 0, 156, 136, 247, 163, 99)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "}["};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__67 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__67_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__67_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__69 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__69_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__69_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__74 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__74_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__74_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString(lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "metadata_block"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 201, 5, 85, 129, 97, 253, 216)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_document_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_document_formatter___lam__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_document_formatter___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_document_formatter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(lean_object* v_x_2_){
_start:
{
lean_object* v_stx_4_; 
switch(lean_obj_tag(v_x_2_))
{
case 1:
{
lean_object* v_args_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v_args_13_ = lean_ctor_get(v_x_2_, 2);
v___x_14_ = lean_array_get_size(v_args_13_);
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_nat_dec_eq(v___x_14_, v___x_15_);
if (v___x_16_ == 0)
{
v_stx_4_ = v_x_2_;
goto v___jp_3_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_inc_ref(v_args_13_);
lean_dec_ref(v_x_2_);
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_array_fget(v_args_13_, v___x_17_);
lean_dec_ref(v_args_13_);
v_x_2_ = v___x_18_;
goto _start;
}
}
case 2:
{
lean_object* v_val_20_; 
v_val_20_ = lean_ctor_get(v_x_2_, 1);
lean_inc_ref(v_val_20_);
lean_dec_ref(v_x_2_);
return v_val_20_;
}
default: 
{
v_stx_4_ = v_x_2_;
goto v___jp_3_;
}
}
v___jp_3_:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_5_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0));
v___x_6_ = lean_box(0);
v___x_7_ = 0;
v___x_8_ = l_Lean_Syntax_formatStx(v_stx_4_, v___x_6_, v___x_7_);
v___x_9_ = l_Std_Format_defWidth;
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = l_Std_Format_pretty(v___x_8_, v___x_9_, v___x_10_, v___x_10_);
v___x_12_ = lean_string_append(v___x_5_, v___x_11_);
lean_dec_ref(v___x_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(lean_object* v___y_21_){
_start:
{
lean_object* v___x_23_; lean_object* v_stxTrav_24_; lean_object* v_cur_25_; lean_object* v___x_26_; 
v___x_23_ = lean_st_ref_get(v___y_21_);
v_stxTrav_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc_ref(v_stxTrav_24_);
lean_dec(v___x_23_);
v_cur_25_ = lean_ctor_get(v_stxTrav_24_, 0);
lean_inc(v_cur_25_);
lean_dec_ref(v_stxTrav_24_);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_cur_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg___boxed(lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0(lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_31_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___boxed(lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0(v___y_36_, v___y_37_, v___y_38_, v___y_39_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(lean_object* v___y_42_){
_start:
{
lean_object* v___x_44_; lean_object* v_stxTrav_45_; lean_object* v_leadWord_46_; uint8_t v_leadWordIdent_47_; uint8_t v_isUngrouped_48_; uint8_t v_mustBeGrouped_49_; lean_object* v_stack_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_61_; 
v___x_44_ = lean_st_ref_take(v___y_42_);
v_stxTrav_45_ = lean_ctor_get(v___x_44_, 0);
v_leadWord_46_ = lean_ctor_get(v___x_44_, 1);
v_leadWordIdent_47_ = lean_ctor_get_uint8(v___x_44_, sizeof(void*)*3);
v_isUngrouped_48_ = lean_ctor_get_uint8(v___x_44_, sizeof(void*)*3 + 1);
v_mustBeGrouped_49_ = lean_ctor_get_uint8(v___x_44_, sizeof(void*)*3 + 2);
v_stack_50_ = lean_ctor_get(v___x_44_, 2);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_61_ == 0)
{
v___x_52_ = v___x_44_;
v_isShared_53_ = v_isSharedCheck_61_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_stack_50_);
lean_inc(v_leadWord_46_);
lean_inc(v_stxTrav_45_);
lean_dec(v___x_44_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_61_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; lean_object* v___x_56_; 
v___x_54_ = l_Lean_Syntax_Traverser_left(v_stxTrav_45_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 0, v___x_54_);
v___x_56_ = v___x_52_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_leadWord_46_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v_stack_50_);
lean_ctor_set_uint8(v_reuseFailAlloc_60_, sizeof(void*)*3, v_leadWordIdent_47_);
lean_ctor_set_uint8(v_reuseFailAlloc_60_, sizeof(void*)*3 + 1, v_isUngrouped_48_);
lean_ctor_set_uint8(v_reuseFailAlloc_60_, sizeof(void*)*3 + 2, v_mustBeGrouped_49_);
v___x_56_ = v_reuseFailAlloc_60_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_st_ref_set(v___y_42_, v___x_56_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg___boxed(lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v___y_62_);
lean_dec(v___y_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1(lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v___y_66_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___boxed(lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1(v___y_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString(lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___x_82_; lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_93_; 
v___x_82_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v_a_78_);
v_a_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_93_ == 0)
{
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_93_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_93_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_a_83_);
if (v_isShared_86_ == 0)
{
lean_ctor_set_tag(v___x_85_, 3);
lean_ctor_set(v___x_85_, 0, v___x_87_);
v___x_89_ = v___x_85_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_92_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_89_, v_a_78_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v___x_91_; 
lean_dec_ref(v___x_90_);
v___x_91_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v_a_78_);
return v___x_91_;
}
else
{
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString___boxed(lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString(v_a_94_, v_a_95_, v_a_96_, v_a_97_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(lean_object* v_a_101_){
_start:
{
lean_object* v___x_103_; lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_119_; 
v___x_103_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v_a_101_);
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_119_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_119_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_119_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___y_109_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_a_104_);
v___x_116_ = l_Lean_Syntax_decodeStrLit(v___x_115_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v___x_117_; 
v___x_117_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_109_ = v___x_117_;
goto v___jp_108_;
}
else
{
lean_object* v_val_118_; 
v_val_118_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_val_118_);
lean_dec_ref(v___x_116_);
v___y_109_ = v_val_118_;
goto v___jp_108_;
}
v___jp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set_tag(v___x_106_, 3);
lean_ctor_set(v___x_106_, 0, v___y_109_);
v___x_111_ = v___x_106_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___y_109_);
v___x_111_ = v_reuseFailAlloc_114_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_111_, v_a_101_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v___x_113_; 
lean_dec_ref(v___x_112_);
v___x_113_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v_a_101_);
return v___x_113_;
}
else
{
return v___x_112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___boxed(lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(v_a_120_);
lean_dec(v_a_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit(lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(v_a_124_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___boxed(lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit(v_a_129_, v_a_130_, v_a_131_, v_a_132_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(lean_object* v_x_136_){
_start:
{
lean_object* v_stx_138_; 
switch(lean_obj_tag(v_x_136_))
{
case 1:
{
lean_object* v_args_147_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v_args_147_ = lean_ctor_get(v_x_136_, 2);
v___x_148_ = lean_array_get_size(v_args_147_);
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = lean_nat_dec_eq(v___x_148_, v___x_149_);
if (v___x_150_ == 0)
{
v_stx_138_ = v_x_136_;
goto v___jp_137_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_inc_ref(v_args_147_);
lean_dec_ref(v_x_136_);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_array_fget(v_args_147_, v___x_151_);
lean_dec_ref(v_args_147_);
v_x_136_ = v___x_152_;
goto _start;
}
}
case 3:
{
lean_object* v_val_154_; uint8_t v___x_155_; lean_object* v___x_156_; 
v_val_154_ = lean_ctor_get(v_x_136_, 2);
lean_inc(v_val_154_);
lean_dec_ref(v_x_136_);
v___x_155_ = 1;
v___x_156_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_154_, v___x_155_);
return v___x_156_;
}
default: 
{
v_stx_138_ = v_x_136_;
goto v___jp_137_;
}
}
v___jp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_139_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0));
v___x_140_ = lean_box(0);
v___x_141_ = 0;
v___x_142_ = l_Lean_Syntax_formatStx(v_stx_138_, v___x_140_, v___x_141_);
v___x_143_ = l_Std_Format_defWidth;
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = l_Std_Format_pretty(v___x_142_, v___x_143_, v___x_144_, v___x_144_);
v___x_146_ = lean_string_append(v___x_139_, v___x_145_);
lean_dec_ref(v___x_145_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(lean_object* v_a_157_){
_start:
{
lean_object* v___x_159_; lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_170_; 
v___x_159_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v_a_157_);
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_170_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_170_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_170_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_a_160_);
if (v_isShared_163_ == 0)
{
lean_ctor_set_tag(v___x_162_, 3);
lean_ctor_set(v___x_162_, 0, v___x_164_);
v___x_166_ = v___x_162_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_169_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_166_, v_a_157_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v___x_168_; 
lean_dec_ref(v___x_167_);
v___x_168_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v_a_157_);
return v___x_168_;
}
else
{
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg___boxed(lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(v_a_171_);
lean_dec(v_a_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent(lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(v_a_175_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___boxed(lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent(v_a_180_, v_a_181_, v_a_182_, v_a_183_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(lean_object* v_f_186_, lean_object* v_i_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_zero_193_; uint8_t v_isZero_194_; 
v_zero_193_ = lean_unsigned_to_nat(0u);
v_isZero_194_ = lean_nat_dec_eq(v_i_187_, v_zero_193_);
if (v_isZero_194_ == 1)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v_i_187_);
lean_dec_ref(v_f_186_);
v___x_195_ = lean_box(0);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; 
lean_inc_ref(v_f_186_);
lean_inc(v___y_191_);
lean_inc_ref(v___y_190_);
lean_inc(v___y_189_);
lean_inc_ref(v___y_188_);
v___x_197_ = lean_apply_5(v_f_186_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, lean_box(0));
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_one_198_; lean_object* v_n_199_; 
lean_dec_ref(v___x_197_);
v_one_198_ = lean_unsigned_to_nat(1u);
v_n_199_ = lean_nat_sub(v_i_187_, v_one_198_);
lean_dec(v_i_187_);
v_i_187_ = v_n_199_;
goto _start;
}
else
{
lean_dec(v_i_187_);
lean_dec_ref(v_f_186_);
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg___boxed(lean_object* v_f_201_, lean_object* v_i_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(v_f_201_, v_i_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0(lean_object* v_f_209_, lean_object* v_n_210_, lean_object* v_i_211_, lean_object* v_a_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(v_f_209_, v_i_211_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___boxed(lean_object* v_f_219_, lean_object* v_n_220_, lean_object* v_i_221_, lean_object* v_a_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0(v_f_219_, v_n_220_, v_i_221_, v_a_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v_n_220_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0(lean_object* v_f_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; lean_object* v_a_236_; lean_object* v___x_237_; lean_object* v_count_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_235_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_231_);
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref(v___x_235_);
v___x_237_ = l_Lean_Syntax_getArgs(v_a_236_);
lean_dec(v_a_236_);
v_count_238_ = lean_array_get_size(v___x_237_);
lean_dec_ref(v___x_237_);
v___x_239_ = lean_alloc_closure((void*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___boxed), 9, 4);
lean_closure_set(v___x_239_, 0, v_f_229_);
lean_closure_set(v___x_239_, 1, v_count_238_);
lean_closure_set(v___x_239_, 2, v_count_238_);
lean_closure_set(v___x_239_, 3, lean_box(0));
v___x_240_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___x_239_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0___boxed(lean_object* v_f_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0(v_f_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep(lean_object* v_f_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___f_254_; lean_object* v___x_255_; 
v___f_254_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0___boxed), 6, 1);
lean_closure_set(v___f_254_, 0, v_f_248_);
v___x_255_ = l_Lean_PrettyPrinter_Formatter_concat(v___f_254_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___boxed(lean_object* v_f_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep(v_f_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(lean_object* v_s_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_box(0);
v___x_266_ = lean_string_append(v_a_264_, v_s_263_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg___boxed(lean_object* v_s_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v_s_268_, v_a_269_);
lean_dec_ref(v_s_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out(lean_object* v_s_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v_s_271_, v_a_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___boxed(lean_object* v_s_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out(v_s_275_, v_a_276_, v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_s_275_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
lean_object* v_zero_281_; uint8_t v_isZero_282_; 
v_zero_281_ = lean_unsigned_to_nat(0u);
v_isZero_282_ = lean_nat_dec_eq(v_x_279_, v_zero_281_);
if (v_isZero_282_ == 1)
{
lean_dec(v_x_279_);
return v_x_280_;
}
else
{
uint32_t v___x_283_; lean_object* v_one_284_; lean_object* v_n_285_; lean_object* v___x_286_; 
v___x_283_ = 32;
v_one_284_ = lean_unsigned_to_nat(1u);
v_n_285_ = lean_nat_sub(v_x_279_, v_one_284_);
lean_dec(v_x_279_);
v___x_286_ = lean_string_push(v_x_280_, v___x_283_);
v_x_279_ = v_n_285_;
v_x_280_ = v___x_286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl(lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_291_ = lean_box(0);
v___x_292_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
lean_inc(v_a_289_);
v___x_293_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_289_, v___x_292_);
v___x_294_ = lean_string_append(v_a_290_, v___x_293_);
lean_dec_ref(v___x_293_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_291_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___boxed(lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl(v_a_296_, v_a_297_);
lean_dec(v_a_296_);
return v_res_298_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
v___x_300_ = lean_string_utf8_byte_size(v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_306_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
v___x_307_ = lean_string_utf8_byte_size(v_a_302_);
v___x_308_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0);
v___x_309_ = lean_nat_dec_le(v___x_308_, v___x_307_);
if (v___x_309_ == 0)
{
goto v___jp_303_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_nat_sub(v___x_307_, v___x_308_);
v___x_312_ = lean_string_memcmp(v_a_302_, v___x_306_, v___x_311_, v___x_310_, v___x_308_);
lean_dec(v___x_311_);
if (v___x_312_ == 0)
{
goto v___jp_303_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
lean_inc(v_a_301_);
v___x_314_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_301_, v___x_313_);
v___x_315_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_314_, v_a_302_);
lean_dec_ref(v___x_314_);
return v___x_315_;
}
}
v___jp_303_:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_box(0);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v_a_302_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___boxed(lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_316_, v_a_317_);
lean_dec(v_a_316_);
return v_res_318_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0));
v___x_321_ = lean_string_utf8_byte_size(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(lean_object* v_a_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_323_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0));
v___x_335_ = lean_string_utf8_byte_size(v_a_322_);
v___x_336_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1);
v___x_337_ = lean_nat_dec_le(v___x_336_, v___x_335_);
if (v___x_337_ == 0)
{
goto v___jp_324_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_nat_sub(v___x_335_, v___x_336_);
v___x_340_ = lean_string_memcmp(v_a_322_, v___x_323_, v___x_339_, v___x_338_, v___x_336_);
lean_dec(v___x_339_);
if (v___x_340_ == 0)
{
goto v___jp_324_;
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_box(0);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v_a_322_);
return v___x_342_;
}
}
v___jp_324_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_325_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
v___x_326_ = lean_string_utf8_byte_size(v_a_322_);
v___x_327_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0);
v___x_328_ = lean_nat_dec_le(v___x_327_, v___x_326_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_323_, v_a_322_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_nat_sub(v___x_326_, v___x_327_);
v___x_332_ = lean_string_memcmp(v_a_322_, v___x_325_, v___x_331_, v___x_330_, v___x_327_);
lean_dec(v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_323_, v_a_322_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_325_, v_a_322_);
return v___x_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock(lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_a_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___boxed(lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock(v_a_346_, v_a_347_);
lean_dec(v_a_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(lean_object* v_s_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0));
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object* v_s_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_s_353_);
lean_dec_ref(v_s_353_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
lean_object* v_zero_357_; uint8_t v_isZero_358_; 
v_zero_357_ = lean_unsigned_to_nat(0u);
v_isZero_358_ = lean_nat_dec_eq(v_x_355_, v_zero_357_);
if (v_isZero_358_ == 1)
{
lean_dec(v_x_355_);
return v_x_356_;
}
else
{
uint32_t v___x_359_; lean_object* v_one_360_; lean_object* v_n_361_; lean_object* v___x_362_; 
v___x_359_ = 35;
v_one_360_ = lean_unsigned_to_nat(1u);
v_n_361_ = lean_nat_sub(v_x_355_, v_one_360_);
lean_dec(v_x_355_);
v___x_362_ = lean_string_push(v_x_356_, v___x_359_);
v_x_355_ = v_n_361_;
v_x_356_ = v___x_362_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(lean_object* v_a_364_, lean_object* v___y_365_, lean_object* v___x_366_, lean_object* v___x_367_, lean_object* v_a_368_, lean_object* v_b_369_){
_start:
{
lean_object* v_it_371_; lean_object* v_startInclusive_372_; lean_object* v_endExclusive_373_; 
if (lean_obj_tag(v_a_368_) == 0)
{
lean_object* v_currPos_380_; lean_object* v_searcher_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_407_; 
v_currPos_380_ = lean_ctor_get(v_a_368_, 0);
v_searcher_381_ = lean_ctor_get(v_a_368_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_a_368_);
if (v_isSharedCheck_407_ == 0)
{
v___x_383_ = v_a_368_;
v_isShared_384_ = v_isSharedCheck_407_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_searcher_381_);
lean_inc(v_currPos_380_);
lean_dec(v_a_368_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_407_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v_startInclusive_385_; lean_object* v_endExclusive_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_startInclusive_385_ = lean_ctor_get(v___x_366_, 1);
v_endExclusive_386_ = lean_ctor_get(v___x_366_, 2);
v___x_387_ = lean_nat_sub(v_endExclusive_386_, v_startInclusive_385_);
v___x_388_ = lean_nat_dec_eq(v_searcher_381_, v___x_387_);
lean_dec(v___x_387_);
if (v___x_388_ == 0)
{
uint32_t v___x_389_; uint32_t v___x_390_; uint8_t v___x_391_; 
v___x_389_ = 10;
v___x_390_ = lean_string_utf8_get_fast(v___y_365_, v_searcher_381_);
v___x_391_ = lean_uint32_dec_eq(v___x_390_, v___x_389_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_string_utf8_next_fast(v___y_365_, v_searcher_381_);
lean_dec(v_searcher_381_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v___x_392_);
v___x_394_ = v___x_383_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_currPos_380_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_392_);
v___x_394_ = v_reuseFailAlloc_396_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
v_a_368_ = v___x_394_;
goto _start;
}
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_slice_400_; lean_object* v_nextIt_402_; 
v___x_397_ = lean_string_utf8_next_fast(v___y_365_, v_searcher_381_);
v___x_398_ = lean_nat_sub(v___x_397_, v_searcher_381_);
v___x_399_ = lean_nat_add(v_searcher_381_, v___x_398_);
lean_dec(v___x_398_);
v_slice_400_ = l_String_Slice_subslice_x21(v___x_366_, v_currPos_380_, v_searcher_381_);
lean_inc(v___x_399_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v___x_399_);
lean_ctor_set(v___x_383_, 0, v___x_399_);
v_nextIt_402_ = v___x_383_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v___x_399_);
v_nextIt_402_ = v_reuseFailAlloc_405_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v_startInclusive_403_; lean_object* v_endExclusive_404_; 
v_startInclusive_403_ = lean_ctor_get(v_slice_400_, 0);
lean_inc(v_startInclusive_403_);
v_endExclusive_404_ = lean_ctor_get(v_slice_400_, 1);
lean_inc(v_endExclusive_404_);
lean_dec_ref(v_slice_400_);
v_it_371_ = v_nextIt_402_;
v_startInclusive_372_ = v_startInclusive_403_;
v_endExclusive_373_ = v_endExclusive_404_;
goto v___jp_370_;
}
}
}
else
{
lean_object* v___x_406_; 
lean_del_object(v___x_383_);
lean_dec(v_searcher_381_);
v___x_406_ = lean_box(1);
lean_inc(v___x_367_);
v_it_371_ = v___x_406_;
v_startInclusive_372_ = v_currPos_380_;
v_endExclusive_373_ = v___x_367_;
goto v___jp_370_;
}
}
}
else
{
lean_dec(v___x_367_);
return v_b_369_;
}
v___jp_370_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_374_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
lean_inc(v_a_364_);
v___x_375_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_364_, v___x_374_);
v___x_376_ = lean_string_utf8_extract(v___y_365_, v_startInclusive_372_, v_endExclusive_373_);
lean_dec(v_endExclusive_373_);
lean_dec(v_startInclusive_372_);
v___x_377_ = lean_string_append(v___x_375_, v___x_376_);
lean_dec_ref(v___x_376_);
v___x_378_ = lean_array_push(v_b_369_, v___x_377_);
v_a_368_ = v_it_371_;
v_b_369_ = v___x_378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg___boxed(lean_object* v_a_408_, lean_object* v___y_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v_a_412_, lean_object* v_b_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(v_a_408_, v___y_409_, v___x_410_, v___x_411_, v_a_412_, v_b_413_);
lean_dec_ref(v___x_410_);
lean_dec_ref(v___y_409_);
lean_dec(v_a_408_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(lean_object* v_as_598_, size_t v_sz_599_, size_t v_i_600_, lean_object* v_b_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
uint8_t v___x_604_; 
v___x_604_ = lean_usize_dec_lt(v_i_600_, v_sz_599_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v_b_601_);
lean_ctor_set(v___x_605_, 1, v___y_603_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_snd_608_; lean_object* v_a_609_; lean_object* v___x_610_; lean_object* v_snd_611_; lean_object* v___x_612_; size_t v___x_613_; size_t v___x_614_; 
v___x_606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0));
v___x_607_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_606_, v___y_603_);
v_snd_608_ = lean_ctor_get(v___x_607_, 1);
lean_inc(v_snd_608_);
lean_dec_ref(v___x_607_);
v_a_609_ = lean_array_uget_borrowed(v_as_598_, v_i_600_);
lean_inc(v_a_609_);
v___x_610_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_609_, v___y_602_, v_snd_608_);
v_snd_611_ = lean_ctor_get(v___x_610_, 1);
lean_inc(v_snd_611_);
lean_dec_ref(v___x_610_);
v___x_612_ = lean_box(0);
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_add(v_i_600_, v___x_613_);
v_i_600_ = v___x_614_;
v_b_601_ = v___x_612_;
v___y_603_ = v_snd_611_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(lean_object* v_as_617_, size_t v_sz_618_, size_t v_i_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_lt(v_i_619_, v_sz_618_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v_b_620_);
lean_ctor_set(v___x_624_, 1, v___y_622_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_snd_627_; lean_object* v_a_628_; lean_object* v___x_629_; lean_object* v_snd_630_; lean_object* v___x_631_; size_t v___x_632_; size_t v___x_633_; 
v___x_625_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0));
v___x_626_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_625_, v___y_622_);
v_snd_627_ = lean_ctor_get(v___x_626_, 1);
lean_inc(v_snd_627_);
lean_dec_ref(v___x_626_);
v_a_628_ = lean_array_uget_borrowed(v_as_617_, v_i_619_);
lean_inc(v_a_628_);
v___x_629_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_628_, v___y_621_, v_snd_627_);
v_snd_630_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_snd_630_);
lean_dec_ref(v___x_629_);
v___x_631_ = lean_box(0);
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_add(v_i_619_, v___x_632_);
v_i_619_ = v___x_633_;
v_b_620_ = v___x_631_;
v___y_622_ = v_snd_630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(lean_object* v_as_645_, size_t v_sz_646_, size_t v_i_647_, lean_object* v_b_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_a_652_; lean_object* v_snd_653_; uint8_t v___x_657_; 
v___x_657_ = lean_usize_dec_lt(v_i_647_, v_sz_646_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v_b_648_);
lean_ctor_set(v___x_658_, 1, v___y_650_);
return v___x_658_;
}
else
{
lean_object* v_a_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v_a_659_ = lean_array_uget_borrowed(v_as_645_, v_i_647_);
v___x_660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4));
lean_inc(v_a_659_);
v___x_661_ = l_Lean_Syntax_isOfKind(v_a_659_, v___x_660_);
if (v___x_661_ == 0)
{
v_a_652_ = v_b_648_;
v_snd_653_ = v___y_650_;
goto v___jp_651_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_snd_666_; lean_object* v___x_667_; lean_object* v_snd_669_; lean_object* v___y_674_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
lean_inc(v_b_648_);
v___x_662_ = l_Nat_reprFast(v_b_648_);
v___x_663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0));
v___x_664_ = lean_string_append(v___x_662_, v___x_663_);
v___x_665_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_664_, v___y_650_);
lean_dec_ref(v___x_664_);
v_snd_666_ = lean_ctor_get(v___x_665_, 1);
lean_inc(v_snd_666_);
lean_dec_ref(v___x_665_);
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = l_Lean_Syntax_getArg(v_a_659_, v___x_667_);
v___x_678_ = l_Lean_Syntax_getArgs(v___x_677_);
lean_dec(v___x_677_);
v___x_679_ = lean_array_get_size(v___x_678_);
v___x_680_ = lean_nat_dec_lt(v___x_676_, v___x_679_);
if (v___x_680_ == 0)
{
lean_dec_ref(v___x_678_);
v_snd_669_ = v_snd_666_;
goto v___jp_668_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_681_ = lean_unsigned_to_nat(2u);
v___x_682_ = lean_nat_add(v___y_649_, v___x_681_);
v___x_683_ = lean_box(0);
v___x_684_ = lean_nat_dec_le(v___x_679_, v___x_679_);
if (v___x_684_ == 0)
{
if (v___x_680_ == 0)
{
lean_dec(v___x_682_);
lean_dec_ref(v___x_678_);
v_snd_669_ = v_snd_666_;
goto v___jp_668_;
}
else
{
size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_685_ = ((size_t)0ULL);
v___x_686_ = lean_usize_of_nat(v___x_679_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_678_, v___x_685_, v___x_686_, v___x_683_, v___x_682_, v_snd_666_);
lean_dec(v___x_682_);
lean_dec_ref(v___x_678_);
v___y_674_ = v___x_687_;
goto v___jp_673_;
}
}
else
{
size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; 
v___x_688_ = ((size_t)0ULL);
v___x_689_ = lean_usize_of_nat(v___x_679_);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_678_, v___x_688_, v___x_689_, v___x_683_, v___x_682_, v_snd_666_);
lean_dec(v___x_682_);
lean_dec_ref(v___x_678_);
v___y_674_ = v___x_690_;
goto v___jp_673_;
}
}
v___jp_668_:
{
lean_object* v___x_670_; lean_object* v_snd_671_; lean_object* v___x_672_; 
v___x_670_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_669_);
v_snd_671_ = lean_ctor_get(v___x_670_, 1);
lean_inc(v_snd_671_);
lean_dec_ref(v___x_670_);
v___x_672_ = lean_nat_add(v_b_648_, v___x_667_);
lean_dec(v_b_648_);
v_a_652_ = v___x_672_;
v_snd_653_ = v_snd_671_;
goto v___jp_651_;
}
v___jp_673_:
{
lean_object* v_snd_675_; 
v_snd_675_ = lean_ctor_get(v___y_674_, 1);
lean_inc(v_snd_675_);
lean_dec_ref(v___y_674_);
v_snd_669_ = v_snd_675_;
goto v___jp_668_;
}
}
}
v___jp_651_:
{
size_t v___x_654_; size_t v___x_655_; 
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_add(v_i_647_, v___x_654_);
v_i_647_ = v___x_655_;
v_b_648_ = v_a_652_;
v___y_650_ = v_snd_653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(lean_object* v_as_692_, size_t v_i_693_, size_t v_stop_694_, lean_object* v_b_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_fst_699_; lean_object* v_snd_700_; lean_object* v___y_705_; lean_object* v___y_709_; uint8_t v___x_712_; 
v___x_712_ = lean_usize_dec_eq(v_i_693_, v_stop_694_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_array_uget_borrowed(v_as_692_, v_i_693_);
v___x_714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4));
lean_inc(v___x_713_);
v___x_715_ = l_Lean_Syntax_isOfKind(v___x_713_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_box(0);
v_fst_699_ = v___x_716_;
v_snd_700_ = v___y_697_;
goto v___jp_698_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_snd_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5));
v___x_718_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_717_, v___y_697_);
v_snd_719_ = lean_ctor_get(v___x_718_, 1);
lean_inc(v_snd_719_);
lean_dec_ref(v___x_718_);
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = l_Lean_Syntax_getArg(v___x_713_, v___x_720_);
v___x_723_ = l_Lean_Syntax_getArgs(v___x_722_);
lean_dec(v___x_722_);
v___x_724_ = lean_array_get_size(v___x_723_);
v___x_725_ = lean_nat_dec_lt(v___x_721_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec_ref(v___x_723_);
v___x_726_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_719_);
v___y_705_ = v___x_726_;
goto v___jp_704_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_727_ = lean_unsigned_to_nat(2u);
v___x_728_ = lean_nat_add(v___y_696_, v___x_727_);
v___x_729_ = lean_box(0);
v___x_730_ = lean_nat_dec_le(v___x_724_, v___x_724_);
if (v___x_730_ == 0)
{
if (v___x_725_ == 0)
{
lean_object* v___x_731_; 
lean_dec(v___x_728_);
lean_dec_ref(v___x_723_);
v___x_731_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_719_);
v___y_705_ = v___x_731_;
goto v___jp_704_;
}
else
{
size_t v___x_732_; size_t v___x_733_; lean_object* v___x_734_; 
v___x_732_ = ((size_t)0ULL);
v___x_733_ = lean_usize_of_nat(v___x_724_);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_723_, v___x_732_, v___x_733_, v___x_729_, v___x_728_, v_snd_719_);
lean_dec(v___x_728_);
lean_dec_ref(v___x_723_);
v___y_709_ = v___x_734_;
goto v___jp_708_;
}
}
else
{
size_t v___x_735_; size_t v___x_736_; lean_object* v___x_737_; 
v___x_735_ = ((size_t)0ULL);
v___x_736_ = lean_usize_of_nat(v___x_724_);
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_723_, v___x_735_, v___x_736_, v___x_729_, v___x_728_, v_snd_719_);
lean_dec(v___x_728_);
lean_dec_ref(v___x_723_);
v___y_709_ = v___x_737_;
goto v___jp_708_;
}
}
}
}
else
{
lean_object* v___x_738_; 
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_b_695_);
lean_ctor_set(v___x_738_, 1, v___y_697_);
return v___x_738_;
}
v___jp_698_:
{
size_t v___x_701_; size_t v___x_702_; 
v___x_701_ = ((size_t)1ULL);
v___x_702_ = lean_usize_add(v_i_693_, v___x_701_);
v_i_693_ = v___x_702_;
v_b_695_ = v_fst_699_;
v___y_697_ = v_snd_700_;
goto _start;
}
v___jp_704_:
{
lean_object* v_fst_706_; lean_object* v_snd_707_; 
v_fst_706_ = lean_ctor_get(v___y_705_, 0);
lean_inc(v_fst_706_);
v_snd_707_ = lean_ctor_get(v___y_705_, 1);
lean_inc(v_snd_707_);
lean_dec_ref(v___y_705_);
v_fst_699_ = v_fst_706_;
v_snd_700_ = v_snd_707_;
goto v___jp_698_;
}
v___jp_708_:
{
lean_object* v_snd_710_; lean_object* v___x_711_; 
v_snd_710_ = lean_ctor_get(v___y_709_, 1);
lean_inc(v_snd_710_);
lean_dec_ref(v___y_709_);
v___x_711_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_710_);
v___y_705_ = v___x_711_;
goto v___jp_704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object* v_stx_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_snd_757_; lean_object* v___y_761_; lean_object* v___y_764_; lean_object* v___y_768_; lean_object* v___y_772_; lean_object* v___y_776_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
lean_inc(v_stx_753_);
v___x_779_ = l_Lean_Syntax_getKind(v_stx_753_);
v___x_780_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2));
v___x_781_ = lean_name_eq(v___x_779_, v___x_780_);
lean_dec(v___x_779_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4));
lean_inc(v_stx_753_);
v___x_783_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6));
lean_inc(v_stx_753_);
v___x_785_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
lean_inc(v_stx_753_);
v___x_787_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
lean_inc(v_stx_753_);
v___x_789_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12));
lean_inc(v_stx_753_);
v___x_791_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14));
lean_inc(v_stx_753_);
v___x_793_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16));
lean_inc(v_stx_753_);
v___x_795_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18));
lean_inc(v_stx_753_);
v___x_797_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20));
lean_inc(v_stx_753_);
v___x_799_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22));
lean_inc(v_stx_753_);
v___x_801_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24));
lean_inc(v_stx_753_);
v___x_803_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26));
lean_inc(v_stx_753_);
v___x_805_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28));
lean_inc(v_stx_753_);
v___x_807_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30));
lean_inc(v_stx_753_);
v___x_809_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32));
lean_inc(v_stx_753_);
v___x_811_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34));
lean_inc(v_stx_753_);
v___x_813_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36));
lean_inc(v_stx_753_);
v___x_815_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38));
lean_inc(v_stx_753_);
v___x_817_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40));
lean_inc(v_stx_753_);
v___x_819_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42));
lean_inc(v_stx_753_);
v___x_821_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44));
lean_inc(v_stx_753_);
v___x_823_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46));
lean_inc(v_stx_753_);
v___x_825_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48));
lean_inc(v_stx_753_);
v___x_827_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50));
lean_inc(v_stx_753_);
v___x_829_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52));
lean_inc(v_stx_753_);
v___x_831_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54));
lean_inc(v_stx_753_);
v___x_833_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56));
lean_inc(v_stx_753_);
v___x_835_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58));
lean_inc(v_stx_753_);
v___x_837_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60));
lean_inc(v_stx_753_);
v___x_839_ = l_Lean_Syntax_isOfKind(v_stx_753_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_840_ = lean_box(0);
v___x_841_ = l_Lean_Syntax_formatStx(v_stx_753_, v___x_840_, v___x_839_);
v___x_842_ = l_Std_Format_defWidth;
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = l_Std_Format_pretty(v___x_841_, v___x_842_, v___x_843_, v___x_843_);
v___x_845_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_844_, v_a_755_);
lean_dec_ref(v___x_844_);
return v___x_845_;
}
else
{
lean_object* v___x_846_; lean_object* v_snd_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_snd_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v_snd_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v_args_858_; lean_object* v___x_859_; size_t v_sz_860_; size_t v___x_861_; lean_object* v___x_862_; lean_object* v_snd_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_snd_866_; lean_object* v___x_867_; 
v___x_846_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_754_, v_a_755_);
v_snd_847_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_snd_847_);
lean_dec_ref(v___x_846_);
v___x_848_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61));
v___x_849_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_848_, v_snd_847_);
v_snd_850_ = lean_ctor_get(v___x_849_, 1);
lean_inc(v_snd_850_);
lean_dec_ref(v___x_849_);
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_851_);
v___x_853_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_852_);
v___x_854_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_853_, v_snd_850_);
lean_dec_ref(v___x_853_);
v_snd_855_ = lean_ctor_get(v___x_854_, 1);
lean_inc(v_snd_855_);
lean_dec_ref(v___x_854_);
v___x_856_ = lean_unsigned_to_nat(2u);
v___x_857_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_856_);
lean_dec(v_stx_753_);
v_args_858_ = l_Lean_Syntax_getArgs(v___x_857_);
lean_dec(v___x_857_);
v___x_859_ = lean_box(0);
v_sz_860_ = lean_array_size(v_args_858_);
v___x_861_ = ((size_t)0ULL);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_args_858_, v_sz_860_, v___x_861_, v___x_859_, v_a_754_, v_snd_855_);
lean_dec_ref(v_args_858_);
v_snd_863_ = lean_ctor_get(v___x_862_, 1);
lean_inc(v_snd_863_);
lean_dec_ref(v___x_862_);
v___x_864_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62));
v___x_865_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_864_, v_snd_863_);
v_snd_866_ = lean_ctor_get(v___x_865_, 1);
lean_inc(v_snd_866_);
lean_dec_ref(v___x_865_);
v___x_867_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_866_);
return v___x_867_;
}
}
else
{
lean_object* v___x_868_; lean_object* v_snd_869_; lean_object* v___x_870_; lean_object* v_tk1_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_snd_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v_snd_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_snd_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_args_885_; lean_object* v___x_886_; size_t v_sz_887_; size_t v___x_888_; lean_object* v___x_889_; lean_object* v_snd_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_snd_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_tk2_897_; lean_object* v_snd_899_; lean_object* v___y_909_; lean_object* v_blks_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_868_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_754_, v_a_755_);
v_snd_869_ = lean_ctor_get(v___x_868_, 1);
lean_inc(v_snd_869_);
lean_dec_ref(v___x_868_);
v___x_870_ = lean_unsigned_to_nat(0u);
v_tk1_871_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_870_);
v___x_872_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_871_);
v___x_873_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_872_, v_snd_869_);
lean_dec_ref(v___x_872_);
v_snd_874_ = lean_ctor_get(v___x_873_, 1);
lean_inc(v_snd_874_);
lean_dec_ref(v___x_873_);
v___x_875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0));
v___x_876_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_875_, v_snd_874_);
v_snd_877_ = lean_ctor_get(v___x_876_, 1);
lean_inc(v_snd_877_);
lean_dec_ref(v___x_876_);
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_878_);
v___x_880_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_879_);
v___x_881_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_880_, v_snd_877_);
lean_dec_ref(v___x_880_);
v_snd_882_ = lean_ctor_get(v___x_881_, 1);
lean_inc(v_snd_882_);
lean_dec_ref(v___x_881_);
v___x_883_ = lean_unsigned_to_nat(2u);
v___x_884_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_883_);
v_args_885_ = l_Lean_Syntax_getArgs(v___x_884_);
lean_dec(v___x_884_);
v___x_886_ = lean_box(0);
v_sz_887_ = lean_array_size(v_args_885_);
v___x_888_ = ((size_t)0ULL);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(v_args_885_, v_sz_887_, v___x_888_, v___x_886_, v_a_754_, v_snd_882_);
lean_dec_ref(v_args_885_);
v_snd_890_ = lean_ctor_get(v___x_889_, 1);
lean_inc(v_snd_890_);
lean_dec_ref(v___x_889_);
v___x_891_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
v___x_892_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_891_, v_snd_890_);
v_snd_893_ = lean_ctor_get(v___x_892_, 1);
lean_inc(v_snd_893_);
lean_dec_ref(v___x_892_);
v___x_894_ = lean_unsigned_to_nat(4u);
v___x_895_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_894_);
v___x_896_ = lean_unsigned_to_nat(5u);
v_tk2_897_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_896_);
lean_dec(v_stx_753_);
v_blks_911_ = l_Lean_Syntax_getArgs(v___x_895_);
lean_dec(v___x_895_);
v___x_912_ = lean_array_get_size(v_blks_911_);
v___x_913_ = lean_nat_dec_lt(v___x_870_, v___x_912_);
if (v___x_913_ == 0)
{
lean_dec_ref(v_blks_911_);
v_snd_899_ = v_snd_893_;
goto v___jp_898_;
}
else
{
uint8_t v___x_914_; 
v___x_914_ = lean_nat_dec_le(v___x_912_, v___x_912_);
if (v___x_914_ == 0)
{
if (v___x_913_ == 0)
{
lean_dec_ref(v_blks_911_);
v_snd_899_ = v_snd_893_;
goto v___jp_898_;
}
else
{
size_t v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_usize_of_nat(v___x_912_);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_911_, v___x_888_, v___x_915_, v___x_886_, v_a_754_, v_snd_893_);
lean_dec_ref(v_blks_911_);
v___y_909_ = v___x_916_;
goto v___jp_908_;
}
}
else
{
size_t v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_usize_of_nat(v___x_912_);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_911_, v___x_888_, v___x_917_, v___x_886_, v_a_754_, v_snd_893_);
lean_dec_ref(v_blks_911_);
v___y_909_ = v___x_918_;
goto v___jp_908_;
}
}
v___jp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v_snd_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v_snd_906_; lean_object* v___x_907_; 
v___x_900_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
lean_inc(v_a_754_);
v___x_901_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_754_, v___x_900_);
v___x_902_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_901_, v_snd_899_);
lean_dec_ref(v___x_901_);
v_snd_903_ = lean_ctor_get(v___x_902_, 1);
lean_inc(v_snd_903_);
lean_dec_ref(v___x_902_);
v___x_904_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_897_);
v___x_905_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_904_, v_snd_903_);
lean_dec_ref(v___x_904_);
v_snd_906_ = lean_ctor_get(v___x_905_, 1);
lean_inc(v_snd_906_);
lean_dec_ref(v___x_905_);
v___x_907_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_906_);
return v___x_907_;
}
v___jp_908_:
{
lean_object* v_snd_910_; 
v_snd_910_ = lean_ctor_get(v___y_909_, 1);
lean_inc(v_snd_910_);
lean_dec_ref(v___y_909_);
v_snd_899_ = v_snd_910_;
goto v___jp_898_;
}
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_919_);
v___x_921_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_920_);
v___x_922_ = l_Lean_Syntax_matchesNull(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v___x_924_ = l_Lean_Syntax_formatStx(v_stx_753_, v___x_923_, v___x_922_);
v___x_925_ = l_Std_Format_defWidth;
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = l_Std_Format_pretty(v___x_924_, v___x_925_, v___x_926_, v___x_926_);
v___x_928_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_927_, v_a_755_);
lean_dec_ref(v___x_927_);
return v___x_928_;
}
else
{
lean_object* v___x_929_; lean_object* v_snd_930_; lean_object* v___x_931_; lean_object* v_tk1_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v_snd_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v_snd_939_; lean_object* v___x_940_; lean_object* v_args_941_; lean_object* v___x_942_; size_t v_sz_943_; size_t v___x_944_; lean_object* v___x_945_; lean_object* v_snd_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v_snd_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v_tk2_953_; lean_object* v___y_955_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_929_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_754_, v_a_755_);
v_snd_930_ = lean_ctor_get(v___x_929_, 1);
lean_inc(v_snd_930_);
lean_dec_ref(v___x_929_);
v___x_931_ = lean_unsigned_to_nat(0u);
v_tk1_932_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_931_);
v___x_933_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_932_);
v___x_934_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_933_, v_snd_930_);
lean_dec_ref(v___x_933_);
v_snd_935_ = lean_ctor_get(v___x_934_, 1);
lean_inc(v_snd_935_);
lean_dec_ref(v___x_934_);
v___x_936_ = l_Lean_Syntax_getArg(v___x_920_, v___x_931_);
v___x_937_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_936_);
v___x_938_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_937_, v_snd_935_);
lean_dec_ref(v___x_937_);
v_snd_939_ = lean_ctor_get(v___x_938_, 1);
lean_inc(v_snd_939_);
lean_dec_ref(v___x_938_);
v___x_940_ = l_Lean_Syntax_getArg(v___x_920_, v___x_919_);
lean_dec(v___x_920_);
v_args_941_ = l_Lean_Syntax_getArgs(v___x_940_);
lean_dec(v___x_940_);
v___x_942_ = lean_box(0);
v_sz_943_ = lean_array_size(v_args_941_);
v___x_944_ = ((size_t)0ULL);
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_args_941_, v_sz_943_, v___x_944_, v___x_942_, v_a_754_, v_snd_939_);
lean_dec_ref(v_args_941_);
v_snd_946_ = lean_ctor_get(v___x_945_, 1);
lean_inc(v_snd_946_);
lean_dec_ref(v___x_945_);
v___x_947_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
v___x_948_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_947_, v_snd_946_);
v_snd_949_ = lean_ctor_get(v___x_948_, 1);
lean_inc(v_snd_949_);
lean_dec_ref(v___x_948_);
v___x_950_ = lean_unsigned_to_nat(3u);
v___x_951_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_950_);
v___x_952_ = lean_unsigned_to_nat(4u);
v_tk2_953_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_952_);
lean_dec(v_stx_753_);
v___x_973_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_951_);
v___x_974_ = l_Lean_Syntax_decodeStrLit(v___x_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v___x_975_; 
v___x_975_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_955_ = v___x_975_;
goto v___jp_954_;
}
else
{
lean_object* v_val_976_; 
v_val_976_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_val_976_);
lean_dec_ref(v___x_974_);
v___y_955_ = v_val_976_;
goto v___jp_954_;
}
v___jp_954_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_snd_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_snd_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v_snd_971_; lean_object* v___x_972_; 
v___x_956_ = lean_string_utf8_byte_size(v___y_955_);
lean_inc_ref(v___y_955_);
v___x_957_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_957_, 0, v___y_955_);
lean_ctor_set(v___x_957_, 1, v___x_931_);
lean_ctor_set(v___x_957_, 2, v___x_956_);
v___x_958_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v___x_957_);
v___x_959_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63));
v___x_960_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(v_a_754_, v___y_955_, v___x_957_, v___x_956_, v___x_958_, v___x_959_);
lean_dec_ref(v___x_957_);
lean_dec_ref(v___y_955_);
v___x_961_ = lean_array_to_list(v___x_960_);
v___x_962_ = l_String_intercalate(v___x_947_, v___x_961_);
v___x_963_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_962_, v_snd_949_);
lean_dec_ref(v___x_962_);
v_snd_964_ = lean_ctor_get(v___x_963_, 1);
lean_inc(v_snd_964_);
lean_dec_ref(v___x_963_);
v___x_965_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
lean_inc(v_a_754_);
v___x_966_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_754_, v___x_965_);
v___x_967_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_966_, v_snd_964_);
lean_dec_ref(v___x_966_);
v_snd_968_ = lean_ctor_get(v___x_967_, 1);
lean_inc(v_snd_968_);
lean_dec_ref(v___x_967_);
v___x_969_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_953_);
v___x_970_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_969_, v_snd_968_);
lean_dec_ref(v___x_969_);
v_snd_971_ = lean_ctor_get(v___x_970_, 1);
lean_inc(v_snd_971_);
lean_dec_ref(v___x_970_);
v___x_972_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_971_);
return v___x_972_;
}
}
}
}
else
{
lean_object* v___x_977_; lean_object* v_snd_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_snd_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v_blks_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_977_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_754_, v_a_755_);
v_snd_978_ = lean_ctor_get(v___x_977_, 1);
lean_inc(v_snd_978_);
lean_dec_ref(v___x_977_);
v___x_979_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64));
v___x_980_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_979_, v_snd_978_);
v_snd_981_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_snd_981_);
lean_dec_ref(v___x_980_);
v___x_982_ = lean_unsigned_to_nat(0u);
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_983_);
lean_dec(v_stx_753_);
v_blks_985_ = l_Lean_Syntax_getArgs(v___x_984_);
lean_dec(v___x_984_);
v___x_986_ = lean_array_get_size(v_blks_985_);
v___x_987_ = lean_nat_dec_lt(v___x_982_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
lean_dec_ref(v_blks_985_);
v___x_988_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_981_);
return v___x_988_;
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_989_ = lean_unsigned_to_nat(2u);
v___x_990_ = lean_nat_add(v_a_754_, v___x_989_);
v___x_991_ = lean_box(0);
v___x_992_ = lean_nat_dec_le(v___x_986_, v___x_986_);
if (v___x_992_ == 0)
{
if (v___x_987_ == 0)
{
lean_object* v___x_993_; 
lean_dec(v___x_990_);
lean_dec_ref(v_blks_985_);
v___x_993_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_981_);
return v___x_993_;
}
else
{
size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; 
v___x_994_ = ((size_t)0ULL);
v___x_995_ = lean_usize_of_nat(v___x_986_);
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_985_, v___x_994_, v___x_995_, v___x_991_, v___x_990_, v_snd_981_);
lean_dec(v___x_990_);
lean_dec_ref(v_blks_985_);
v___y_776_ = v___x_996_;
goto v___jp_775_;
}
}
else
{
size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v___x_997_ = ((size_t)0ULL);
v___x_998_ = lean_usize_of_nat(v___x_986_);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_985_, v___x_997_, v___x_998_, v___x_991_, v___x_990_, v_snd_981_);
lean_dec(v___x_990_);
lean_dec_ref(v_blks_985_);
v___y_776_ = v___x_999_;
goto v___jp_775_;
}
}
}
}
else
{
lean_object* v___x_1000_; lean_object* v_snd_1001_; lean_object* v___x_1002_; lean_object* v_n_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_items_1006_; lean_object* v___x_1007_; size_t v_sz_1008_; size_t v___x_1009_; lean_object* v___x_1010_; lean_object* v_snd_1011_; lean_object* v___x_1012_; 
v___x_1000_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_754_, v_a_755_);
v_snd_1001_ = lean_ctor_get(v___x_1000_, 1);
lean_inc(v_snd_1001_);
lean_dec_ref(v___x_1000_);
v___x_1002_ = lean_unsigned_to_nat(1u);
v_n_1003_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1002_);
v___x_1004_ = lean_unsigned_to_nat(4u);
v___x_1005_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1004_);
lean_dec(v_stx_753_);
v_items_1006_ = l_Lean_Syntax_getArgs(v___x_1005_);
lean_dec(v___x_1005_);
v___x_1007_ = l_Lean_TSyntax_getNat(v_n_1003_);
lean_dec(v_n_1003_);
v_sz_1008_ = lean_array_size(v_items_1006_);
v___x_1009_ = ((size_t)0ULL);
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v_items_1006_, v_sz_1008_, v___x_1009_, v___x_1007_, v_a_754_, v_snd_1001_);
lean_dec_ref(v_items_1006_);
v_snd_1011_ = lean_ctor_get(v___x_1010_, 1);
lean_inc(v_snd_1011_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1011_);
return v___x_1012_;
}
}
else
{
lean_object* v___x_1013_; lean_object* v_snd_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v_items_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1013_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_754_, v_a_755_);
v_snd_1014_ = lean_ctor_get(v___x_1013_, 1);
lean_inc(v_snd_1014_);
lean_dec_ref(v___x_1013_);
v___x_1015_ = lean_unsigned_to_nat(0u);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1016_);
lean_dec(v_stx_753_);
v_items_1018_ = l_Lean_Syntax_getArgs(v___x_1017_);
lean_dec(v___x_1017_);
v___x_1019_ = lean_array_get_size(v_items_1018_);
v___x_1020_ = lean_nat_dec_lt(v___x_1015_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_dec_ref(v_items_1018_);
v___x_1021_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1014_);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = lean_box(0);
v___x_1023_ = lean_nat_dec_le(v___x_1019_, v___x_1019_);
if (v___x_1023_ == 0)
{
if (v___x_1020_ == 0)
{
lean_object* v___x_1024_; 
lean_dec_ref(v_items_1018_);
v___x_1024_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1014_);
return v___x_1024_;
}
else
{
size_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = ((size_t)0ULL);
v___x_1026_ = lean_usize_of_nat(v___x_1019_);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v_items_1018_, v___x_1025_, v___x_1026_, v___x_1022_, v_a_754_, v_snd_1014_);
lean_dec_ref(v_items_1018_);
v___y_772_ = v___x_1027_;
goto v___jp_771_;
}
}
else
{
size_t v___x_1028_; size_t v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = ((size_t)0ULL);
v___x_1029_ = lean_usize_of_nat(v___x_1019_);
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v_items_1018_, v___x_1028_, v___x_1029_, v___x_1022_, v_a_754_, v_snd_1014_);
lean_dec_ref(v_items_1018_);
v___y_772_ = v___x_1030_;
goto v___jp_771_;
}
}
}
}
else
{
lean_object* v___x_1031_; lean_object* v_snd_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v_inl_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1031_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_754_, v_a_755_);
v_snd_1032_ = lean_ctor_get(v___x_1031_, 1);
lean_inc(v_snd_1032_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_unsigned_to_nat(1u);
v___x_1035_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1034_);
lean_dec(v_stx_753_);
v_inl_1036_ = l_Lean_Syntax_getArgs(v___x_1035_);
lean_dec(v___x_1035_);
v___x_1037_ = lean_array_get_size(v_inl_1036_);
v___x_1038_ = lean_nat_dec_lt(v___x_1033_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; 
lean_dec_ref(v_inl_1036_);
v___x_1039_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1032_);
return v___x_1039_;
}
else
{
lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_nat_dec_le(v___x_1037_, v___x_1037_);
if (v___x_1041_ == 0)
{
if (v___x_1038_ == 0)
{
lean_object* v___x_1042_; 
lean_dec_ref(v_inl_1036_);
v___x_1042_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1032_);
return v___x_1042_;
}
else
{
size_t v___x_1043_; size_t v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = ((size_t)0ULL);
v___x_1044_ = lean_usize_of_nat(v___x_1037_);
v___x_1045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1036_, v___x_1043_, v___x_1044_, v___x_1040_, v_a_754_, v_snd_1032_);
lean_dec_ref(v_inl_1036_);
v___y_768_ = v___x_1045_;
goto v___jp_767_;
}
}
else
{
size_t v___x_1046_; size_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = ((size_t)0ULL);
v___x_1047_ = lean_usize_of_nat(v___x_1037_);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1036_, v___x_1046_, v___x_1047_, v___x_1040_, v_a_754_, v_snd_1032_);
lean_dec_ref(v_inl_1036_);
v___y_768_ = v___x_1048_;
goto v___jp_767_;
}
}
}
}
else
{
lean_object* v___x_1049_; lean_object* v_n_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v_snd_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v_inl_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1049_ = lean_unsigned_to_nat(1u);
v_n_1050_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1049_);
v___x_1051_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65));
v___x_1052_ = l_Lean_TSyntax_getNat(v_n_1050_);
lean_dec(v_n_1050_);
v___x_1053_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___x_1052_, v___x_1051_);
v___x_1054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0));
v___x_1055_ = lean_string_append(v___x_1053_, v___x_1054_);
v___x_1056_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1055_, v_a_755_);
lean_dec_ref(v___x_1055_);
v_snd_1057_ = lean_ctor_get(v___x_1056_, 1);
lean_inc(v_snd_1057_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = lean_unsigned_to_nat(4u);
v___x_1060_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1059_);
lean_dec(v_stx_753_);
v_inl_1061_ = l_Lean_Syntax_getArgs(v___x_1060_);
lean_dec(v___x_1060_);
v___x_1062_ = lean_array_get_size(v_inl_1061_);
v___x_1063_ = lean_nat_dec_lt(v___x_1058_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
lean_dec_ref(v_inl_1061_);
v___x_1064_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1057_);
return v___x_1064_;
}
else
{
lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_nat_dec_le(v___x_1062_, v___x_1062_);
if (v___x_1066_ == 0)
{
if (v___x_1063_ == 0)
{
lean_object* v___x_1067_; 
lean_dec_ref(v_inl_1061_);
v___x_1067_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1057_);
return v___x_1067_;
}
else
{
size_t v___x_1068_; size_t v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = ((size_t)0ULL);
v___x_1069_ = lean_usize_of_nat(v___x_1062_);
v___x_1070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1061_, v___x_1068_, v___x_1069_, v___x_1065_, v_a_754_, v_snd_1057_);
lean_dec_ref(v_inl_1061_);
v___y_764_ = v___x_1070_;
goto v___jp_763_;
}
}
else
{
size_t v___x_1071_; size_t v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = ((size_t)0ULL);
v___x_1072_ = lean_usize_of_nat(v___x_1062_);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1061_, v___x_1071_, v___x_1072_, v___x_1065_, v_a_754_, v_snd_1057_);
lean_dec_ref(v_inl_1061_);
v___y_764_ = v___x_1073_;
goto v___jp_763_;
}
}
}
}
else
{
lean_object* v___x_1074_; lean_object* v_tk1_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v_snd_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v_tk2_1082_; lean_object* v___y_1084_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1074_ = lean_unsigned_to_nat(0u);
v_tk1_1075_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1074_);
v___x_1076_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1075_);
v___x_1077_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1076_, v_a_755_);
lean_dec_ref(v___x_1076_);
v_snd_1078_ = lean_ctor_get(v___x_1077_, 1);
lean_inc(v_snd_1078_);
lean_dec_ref(v___x_1077_);
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1079_);
v___x_1081_ = lean_unsigned_to_nat(2u);
v_tk2_1082_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1081_);
lean_dec(v_stx_753_);
v___x_1089_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1080_);
v___x_1090_ = l_Lean_Syntax_decodeStrLit(v___x_1089_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v___x_1091_; 
v___x_1091_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1084_ = v___x_1091_;
goto v___jp_1083_;
}
else
{
lean_object* v_val_1092_; 
v_val_1092_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_val_1092_);
lean_dec_ref(v___x_1090_);
v___y_1084_ = v_val_1092_;
goto v___jp_1083_;
}
v___jp_1083_:
{
lean_object* v___x_1085_; lean_object* v_snd_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1085_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1084_, v_snd_1078_);
lean_dec_ref(v___y_1084_);
v_snd_1086_ = lean_ctor_get(v___x_1085_, 1);
lean_inc(v_snd_1086_);
lean_dec_ref(v___x_1085_);
v___x_1087_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1082_);
v___x_1088_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1087_, v_snd_1086_);
lean_dec_ref(v___x_1087_);
return v___x_1088_;
}
}
}
else
{
lean_object* v___x_1093_; lean_object* v_tk1_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v_snd_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_tk2_1101_; lean_object* v___y_1103_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1093_ = lean_unsigned_to_nat(0u);
v_tk1_1094_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1093_);
v___x_1095_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1094_);
v___x_1096_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1095_, v_a_755_);
lean_dec_ref(v___x_1095_);
v_snd_1097_ = lean_ctor_get(v___x_1096_, 1);
lean_inc(v_snd_1097_);
lean_dec_ref(v___x_1096_);
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1098_);
v___x_1100_ = lean_unsigned_to_nat(2u);
v_tk2_1101_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1100_);
lean_dec(v_stx_753_);
v___x_1108_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1099_);
v___x_1109_ = l_Lean_Syntax_decodeStrLit(v___x_1108_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v___x_1110_; 
v___x_1110_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1103_ = v___x_1110_;
goto v___jp_1102_;
}
else
{
lean_object* v_val_1111_; 
v_val_1111_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_val_1111_);
lean_dec_ref(v___x_1109_);
v___y_1103_ = v_val_1111_;
goto v___jp_1102_;
}
v___jp_1102_:
{
lean_object* v___x_1104_; lean_object* v_snd_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1104_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1103_, v_snd_1097_);
lean_dec_ref(v___y_1103_);
v_snd_1105_ = lean_ctor_get(v___x_1104_, 1);
lean_inc(v_snd_1105_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1101_);
v___x_1107_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1106_, v_snd_1105_);
lean_dec_ref(v___x_1106_);
return v___x_1107_;
}
}
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1112_);
lean_inc(v___x_1113_);
v___x_1114_ = l_Lean_Syntax_isOfKind(v___x_1113_, v___x_810_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec(v___x_1113_);
v___x_1115_ = lean_box(0);
v___x_1116_ = l_Lean_Syntax_formatStx(v_stx_753_, v___x_1115_, v___x_1114_);
v___x_1117_ = l_Std_Format_defWidth;
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = l_Std_Format_pretty(v___x_1116_, v___x_1117_, v___x_1118_, v___x_1118_);
v___x_1120_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1119_, v_a_755_);
lean_dec_ref(v___x_1119_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; lean_object* v_tk1_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v_snd_1125_; lean_object* v_tk2_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_snd_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v_tk3_1132_; lean_object* v___y_1134_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1121_ = lean_unsigned_to_nat(0u);
v_tk1_1122_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1121_);
lean_dec(v_stx_753_);
v___x_1123_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1122_);
v___x_1124_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1123_, v_a_755_);
lean_dec_ref(v___x_1123_);
v_snd_1125_ = lean_ctor_get(v___x_1124_, 1);
lean_inc(v_snd_1125_);
lean_dec_ref(v___x_1124_);
v_tk2_1126_ = l_Lean_Syntax_getArg(v___x_1113_, v___x_1121_);
v___x_1127_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1126_);
v___x_1128_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1127_, v_snd_1125_);
lean_dec_ref(v___x_1127_);
v_snd_1129_ = lean_ctor_get(v___x_1128_, 1);
lean_inc(v_snd_1129_);
lean_dec_ref(v___x_1128_);
v___x_1130_ = l_Lean_Syntax_getArg(v___x_1113_, v___x_1112_);
v___x_1131_ = lean_unsigned_to_nat(2u);
v_tk3_1132_ = l_Lean_Syntax_getArg(v___x_1113_, v___x_1131_);
lean_dec(v___x_1113_);
v___x_1139_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1130_);
v___x_1140_ = l_Lean_Syntax_decodeStrLit(v___x_1139_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1134_ = v___x_1141_;
goto v___jp_1133_;
}
else
{
lean_object* v_val_1142_; 
v_val_1142_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_val_1142_);
lean_dec_ref(v___x_1140_);
v___y_1134_ = v_val_1142_;
goto v___jp_1133_;
}
v___jp_1133_:
{
lean_object* v___x_1135_; lean_object* v_snd_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1135_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1134_, v_snd_1129_);
lean_dec_ref(v___y_1134_);
v_snd_1136_ = lean_ctor_get(v___x_1135_, 1);
lean_inc(v_snd_1136_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk3_1132_);
v___x_1138_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1137_, v_snd_1136_);
lean_dec_ref(v___x_1137_);
return v___x_1138_;
}
}
}
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1143_ = lean_unsigned_to_nat(1u);
v___x_1144_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1143_);
lean_inc(v___x_1144_);
v___x_1145_ = l_Lean_Syntax_isOfKind(v___x_1144_, v___x_810_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec(v___x_1144_);
v___x_1146_ = lean_box(0);
v___x_1147_ = l_Lean_Syntax_formatStx(v_stx_753_, v___x_1146_, v___x_1145_);
v___x_1148_ = l_Std_Format_defWidth;
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = l_Std_Format_pretty(v___x_1147_, v___x_1148_, v___x_1149_, v___x_1149_);
v___x_1151_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1150_, v_a_755_);
lean_dec_ref(v___x_1150_);
return v___x_1151_;
}
else
{
lean_object* v___x_1152_; lean_object* v_tk1_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v_snd_1156_; lean_object* v_tk2_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_snd_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_tk3_1163_; lean_object* v___y_1165_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1152_ = lean_unsigned_to_nat(0u);
v_tk1_1153_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1152_);
lean_dec(v_stx_753_);
v___x_1154_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1153_);
v___x_1155_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1154_, v_a_755_);
lean_dec_ref(v___x_1154_);
v_snd_1156_ = lean_ctor_get(v___x_1155_, 1);
lean_inc(v_snd_1156_);
lean_dec_ref(v___x_1155_);
v_tk2_1157_ = l_Lean_Syntax_getArg(v___x_1144_, v___x_1152_);
v___x_1158_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1157_);
v___x_1159_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1158_, v_snd_1156_);
lean_dec_ref(v___x_1158_);
v_snd_1160_ = lean_ctor_get(v___x_1159_, 1);
lean_inc(v_snd_1160_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = l_Lean_Syntax_getArg(v___x_1144_, v___x_1143_);
v___x_1162_ = lean_unsigned_to_nat(2u);
v_tk3_1163_ = l_Lean_Syntax_getArg(v___x_1144_, v___x_1162_);
lean_dec(v___x_1144_);
v___x_1170_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1161_);
v___x_1171_ = l_Lean_Syntax_decodeStrLit(v___x_1170_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v___x_1172_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1165_ = v___x_1172_;
goto v___jp_1164_;
}
else
{
lean_object* v_val_1173_; 
v_val_1173_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_val_1173_);
lean_dec_ref(v___x_1171_);
v___y_1165_ = v_val_1173_;
goto v___jp_1164_;
}
v___jp_1164_:
{
lean_object* v___x_1166_; lean_object* v_snd_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1166_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1165_, v_snd_1160_);
lean_dec_ref(v___y_1165_);
v_snd_1167_ = lean_ctor_get(v___x_1166_, 1);
lean_inc(v_snd_1167_);
lean_dec_ref(v___x_1166_);
v___x_1168_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk3_1163_);
v___x_1169_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1168_, v_snd_1167_);
lean_dec_ref(v___x_1168_);
return v___x_1169_;
}
}
}
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
v___x_1175_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1174_);
lean_dec(v_stx_753_);
v___x_1176_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1175_);
v___x_1177_ = l_Lean_Syntax_decodeStrLit(v___x_1176_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___x_1179_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1178_, v_a_755_);
return v___x_1179_;
}
else
{
lean_object* v_val_1180_; lean_object* v___x_1181_; 
v_val_1180_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_val_1180_);
lean_dec_ref(v___x_1177_);
v___x_1181_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v_val_1180_, v_a_755_);
lean_dec(v_val_1180_);
return v___x_1181_;
}
}
}
else
{
lean_object* v___x_1182_; lean_object* v_tk1_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v_snd_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_tk2_1190_; lean_object* v___y_1192_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1182_ = lean_unsigned_to_nat(0u);
v_tk1_1183_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1182_);
v___x_1184_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1183_);
v___x_1185_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1184_, v_a_755_);
lean_dec_ref(v___x_1184_);
v_snd_1186_ = lean_ctor_get(v___x_1185_, 1);
lean_inc(v_snd_1186_);
lean_dec_ref(v___x_1185_);
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1187_);
v___x_1189_ = lean_unsigned_to_nat(2u);
v_tk2_1190_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1189_);
lean_dec(v_stx_753_);
v___x_1197_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1188_);
v___x_1198_ = l_Lean_Syntax_decodeStrLit(v___x_1197_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v___x_1199_; 
v___x_1199_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1192_ = v___x_1199_;
goto v___jp_1191_;
}
else
{
lean_object* v_val_1200_; 
v_val_1200_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_val_1200_);
lean_dec_ref(v___x_1198_);
v___y_1192_ = v_val_1200_;
goto v___jp_1191_;
}
v___jp_1191_:
{
lean_object* v___x_1193_; lean_object* v_snd_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1193_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1192_, v_snd_1186_);
lean_dec_ref(v___y_1192_);
v_snd_1194_ = lean_ctor_get(v___x_1193_, 1);
lean_inc(v_snd_1194_);
lean_dec_ref(v___x_1193_);
v___x_1195_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1190_);
v___x_1196_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1195_, v_snd_1194_);
lean_dec_ref(v___x_1195_);
return v___x_1196_;
}
}
}
else
{
lean_object* v___x_1201_; lean_object* v_tk1_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_snd_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v_tk2_1209_; lean_object* v___y_1211_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1201_ = lean_unsigned_to_nat(0u);
v_tk1_1202_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1201_);
v___x_1203_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1202_);
v___x_1204_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1203_, v_a_755_);
lean_dec_ref(v___x_1203_);
v_snd_1205_ = lean_ctor_get(v___x_1204_, 1);
lean_inc(v_snd_1205_);
lean_dec_ref(v___x_1204_);
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1206_);
v___x_1208_ = lean_unsigned_to_nat(2u);
v_tk2_1209_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1208_);
lean_dec(v_stx_753_);
v___x_1216_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1207_);
v___x_1217_ = l_Lean_Syntax_decodeStrLit(v___x_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1211_ = v___x_1218_;
goto v___jp_1210_;
}
else
{
lean_object* v_val_1219_; 
v_val_1219_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_val_1219_);
lean_dec_ref(v___x_1217_);
v___y_1211_ = v_val_1219_;
goto v___jp_1210_;
}
v___jp_1210_:
{
lean_object* v___x_1212_; lean_object* v_snd_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1212_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1211_, v_snd_1205_);
lean_dec_ref(v___y_1211_);
v_snd_1213_ = lean_ctor_get(v___x_1212_, 1);
lean_inc(v_snd_1213_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1209_);
v___x_1215_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1214_, v_snd_1213_);
lean_dec_ref(v___x_1214_);
return v___x_1215_;
}
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v_snd_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_snd_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v_args_1230_; lean_object* v___x_1231_; size_t v_sz_1232_; size_t v___x_1233_; lean_object* v___x_1234_; lean_object* v_snd_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v_snd_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v_inls_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1220_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61));
v___x_1221_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1220_, v_a_755_);
v_snd_1222_ = lean_ctor_get(v___x_1221_, 1);
lean_inc(v_snd_1222_);
lean_dec_ref(v___x_1221_);
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1223_);
v___x_1225_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_1224_);
v___x_1226_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1225_, v_snd_1222_);
lean_dec_ref(v___x_1225_);
v_snd_1227_ = lean_ctor_get(v___x_1226_, 1);
lean_inc(v_snd_1227_);
lean_dec_ref(v___x_1226_);
v___x_1228_ = lean_unsigned_to_nat(2u);
v___x_1229_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1228_);
v_args_1230_ = l_Lean_Syntax_getArgs(v___x_1229_);
lean_dec(v___x_1229_);
v___x_1231_ = lean_box(0);
v_sz_1232_ = lean_array_size(v_args_1230_);
v___x_1233_ = ((size_t)0ULL);
v___x_1234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_args_1230_, v_sz_1232_, v___x_1233_, v___x_1231_, v_a_754_, v_snd_1227_);
lean_dec_ref(v_args_1230_);
v_snd_1235_ = lean_ctor_get(v___x_1234_, 1);
lean_inc(v_snd_1235_);
lean_dec_ref(v___x_1234_);
v___x_1236_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66));
v___x_1237_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1236_, v_snd_1235_);
v_snd_1238_ = lean_ctor_get(v___x_1237_, 1);
lean_inc(v_snd_1238_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_unsigned_to_nat(5u);
v___x_1241_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1240_);
lean_dec(v_stx_753_);
v_inls_1242_ = l_Lean_Syntax_getArgs(v___x_1241_);
lean_dec(v___x_1241_);
v___x_1243_ = lean_array_get_size(v_inls_1242_);
v___x_1244_ = lean_nat_dec_lt(v___x_1239_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_dec_ref(v_inls_1242_);
v_snd_757_ = v_snd_1238_;
goto v___jp_756_;
}
else
{
uint8_t v___x_1245_; 
v___x_1245_ = lean_nat_dec_le(v___x_1243_, v___x_1243_);
if (v___x_1245_ == 0)
{
if (v___x_1244_ == 0)
{
lean_dec_ref(v_inls_1242_);
v_snd_757_ = v_snd_1238_;
goto v___jp_756_;
}
else
{
size_t v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_usize_of_nat(v___x_1243_);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inls_1242_, v___x_1233_, v___x_1246_, v___x_1231_, v_a_754_, v_snd_1238_);
lean_dec_ref(v_inls_1242_);
v___y_761_ = v___x_1247_;
goto v___jp_760_;
}
}
else
{
size_t v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_usize_of_nat(v___x_1243_);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inls_1242_, v___x_1233_, v___x_1248_, v___x_1231_, v_a_754_, v_snd_1238_);
lean_dec_ref(v_inls_1242_);
v___y_761_ = v___x_1249_;
goto v___jp_760_;
}
}
}
}
else
{
lean_object* v___x_1250_; lean_object* v_tk1_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_snd_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v_tk2_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___y_1262_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1250_ = lean_unsigned_to_nat(0u);
v_tk1_1251_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1250_);
v___x_1252_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1251_);
v___x_1253_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1252_, v_a_755_);
lean_dec_ref(v___x_1252_);
v_snd_1254_ = lean_ctor_get(v___x_1253_, 1);
lean_inc(v_snd_1254_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = lean_unsigned_to_nat(1u);
v___x_1256_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1255_);
v___x_1257_ = lean_unsigned_to_nat(2u);
v_tk2_1258_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1257_);
v___x_1259_ = lean_unsigned_to_nat(3u);
v___x_1260_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1259_);
lean_dec(v_stx_753_);
v___x_1269_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1256_);
v___x_1270_ = l_Lean_Syntax_decodeStrLit(v___x_1269_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1262_ = v___x_1271_;
goto v___jp_1261_;
}
else
{
lean_object* v_val_1272_; 
v_val_1272_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_val_1272_);
lean_dec_ref(v___x_1270_);
v___y_1262_ = v_val_1272_;
goto v___jp_1261_;
}
v___jp_1261_:
{
lean_object* v___x_1263_; lean_object* v_snd_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_snd_1267_; 
v___x_1263_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1262_, v_snd_1254_);
lean_dec_ref(v___y_1262_);
v_snd_1264_ = lean_ctor_get(v___x_1263_, 1);
lean_inc(v_snd_1264_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1258_);
v___x_1266_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1265_, v_snd_1264_);
lean_dec_ref(v___x_1265_);
v_snd_1267_ = lean_ctor_get(v___x_1266_, 1);
lean_inc(v_snd_1267_);
lean_dec_ref(v___x_1266_);
v_stx_753_ = v___x_1260_;
v_a_755_ = v_snd_1267_;
goto _start;
}
}
}
else
{
lean_object* v___x_1273_; lean_object* v_tk1_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v_snd_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v_tk2_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v_snd_1285_; lean_object* v___y_1291_; lean_object* v_inl_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1273_ = lean_unsigned_to_nat(0u);
v_tk1_1274_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1273_);
v___x_1275_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1274_);
v___x_1276_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1275_, v_a_755_);
lean_dec_ref(v___x_1275_);
v_snd_1277_ = lean_ctor_get(v___x_1276_, 1);
lean_inc(v_snd_1277_);
lean_dec_ref(v___x_1276_);
v___x_1278_ = lean_unsigned_to_nat(1u);
v___x_1279_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1278_);
v___x_1280_ = lean_unsigned_to_nat(2u);
v_tk2_1281_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1280_);
v___x_1282_ = lean_unsigned_to_nat(3u);
v___x_1283_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1282_);
lean_dec(v_stx_753_);
v_inl_1293_ = l_Lean_Syntax_getArgs(v___x_1279_);
lean_dec(v___x_1279_);
v___x_1294_ = lean_array_get_size(v_inl_1293_);
v___x_1295_ = lean_nat_dec_lt(v___x_1273_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_dec_ref(v_inl_1293_);
v_snd_1285_ = v_snd_1277_;
goto v___jp_1284_;
}
else
{
lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = lean_nat_dec_le(v___x_1294_, v___x_1294_);
if (v___x_1297_ == 0)
{
if (v___x_1295_ == 0)
{
lean_dec_ref(v_inl_1293_);
v_snd_1285_ = v_snd_1277_;
goto v___jp_1284_;
}
else
{
size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = ((size_t)0ULL);
v___x_1299_ = lean_usize_of_nat(v___x_1294_);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1293_, v___x_1298_, v___x_1299_, v___x_1296_, v_a_754_, v_snd_1277_);
lean_dec_ref(v_inl_1293_);
v___y_1291_ = v___x_1300_;
goto v___jp_1290_;
}
}
else
{
size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = ((size_t)0ULL);
v___x_1302_ = lean_usize_of_nat(v___x_1294_);
v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1293_, v___x_1301_, v___x_1302_, v___x_1296_, v_a_754_, v_snd_1277_);
lean_dec_ref(v_inl_1293_);
v___y_1291_ = v___x_1303_;
goto v___jp_1290_;
}
}
v___jp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v_snd_1288_; 
v___x_1286_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1281_);
v___x_1287_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1286_, v_snd_1285_);
lean_dec_ref(v___x_1286_);
v_snd_1288_ = lean_ctor_get(v___x_1287_, 1);
lean_inc(v_snd_1288_);
lean_dec_ref(v___x_1287_);
v_stx_753_ = v___x_1283_;
v_a_755_ = v_snd_1288_;
goto _start;
}
v___jp_1290_:
{
lean_object* v_snd_1292_; 
v_snd_1292_ = lean_ctor_get(v___y_1291_, 1);
lean_inc(v_snd_1292_);
lean_dec_ref(v___y_1291_);
v_snd_1285_ = v_snd_1292_;
goto v___jp_1284_;
}
}
}
else
{
lean_object* v___x_1304_; lean_object* v_tk1_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_snd_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v_tk2_1312_; lean_object* v_snd_1314_; lean_object* v___y_1318_; lean_object* v_inl_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1304_ = lean_unsigned_to_nat(0u);
v_tk1_1305_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1304_);
v___x_1306_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1305_);
v___x_1307_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1306_, v_a_755_);
lean_dec_ref(v___x_1306_);
v_snd_1308_ = lean_ctor_get(v___x_1307_, 1);
lean_inc(v_snd_1308_);
lean_dec_ref(v___x_1307_);
v___x_1309_ = lean_unsigned_to_nat(1u);
v___x_1310_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1309_);
v___x_1311_ = lean_unsigned_to_nat(2u);
v_tk2_1312_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1311_);
lean_dec(v_stx_753_);
v_inl_1320_ = l_Lean_Syntax_getArgs(v___x_1310_);
lean_dec(v___x_1310_);
v___x_1321_ = lean_array_get_size(v_inl_1320_);
v___x_1322_ = lean_nat_dec_lt(v___x_1304_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec_ref(v_inl_1320_);
v_snd_1314_ = v_snd_1308_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = lean_box(0);
v___x_1324_ = lean_nat_dec_le(v___x_1321_, v___x_1321_);
if (v___x_1324_ == 0)
{
if (v___x_1322_ == 0)
{
lean_dec_ref(v_inl_1320_);
v_snd_1314_ = v_snd_1308_;
goto v___jp_1313_;
}
else
{
size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = lean_usize_of_nat(v___x_1321_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1320_, v___x_1325_, v___x_1326_, v___x_1323_, v_a_754_, v_snd_1308_);
lean_dec_ref(v_inl_1320_);
v___y_1318_ = v___x_1327_;
goto v___jp_1317_;
}
}
else
{
size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = lean_usize_of_nat(v___x_1321_);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1320_, v___x_1328_, v___x_1329_, v___x_1323_, v_a_754_, v_snd_1308_);
lean_dec_ref(v_inl_1320_);
v___y_1318_ = v___x_1330_;
goto v___jp_1317_;
}
}
v___jp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1312_);
v___x_1316_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1315_, v_snd_1314_);
lean_dec_ref(v___x_1315_);
return v___x_1316_;
}
v___jp_1317_:
{
lean_object* v_snd_1319_; 
v_snd_1319_ = lean_ctor_get(v___y_1318_, 1);
lean_inc(v_snd_1319_);
lean_dec_ref(v___y_1318_);
v_snd_1314_ = v_snd_1319_;
goto v___jp_1313_;
}
}
}
else
{
lean_object* v___x_1331_; lean_object* v_tk1_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v_snd_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v_tk2_1339_; lean_object* v_snd_1341_; lean_object* v___y_1345_; lean_object* v_inl_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1331_ = lean_unsigned_to_nat(0u);
v_tk1_1332_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1331_);
v___x_1333_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1332_);
v___x_1334_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1333_, v_a_755_);
lean_dec_ref(v___x_1333_);
v_snd_1335_ = lean_ctor_get(v___x_1334_, 1);
lean_inc(v_snd_1335_);
lean_dec_ref(v___x_1334_);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1336_);
v___x_1338_ = lean_unsigned_to_nat(2u);
v_tk2_1339_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1338_);
lean_dec(v_stx_753_);
v_inl_1347_ = l_Lean_Syntax_getArgs(v___x_1337_);
lean_dec(v___x_1337_);
v___x_1348_ = lean_array_get_size(v_inl_1347_);
v___x_1349_ = lean_nat_dec_lt(v___x_1331_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_dec_ref(v_inl_1347_);
v_snd_1341_ = v_snd_1335_;
goto v___jp_1340_;
}
else
{
lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_nat_dec_le(v___x_1348_, v___x_1348_);
if (v___x_1351_ == 0)
{
if (v___x_1349_ == 0)
{
lean_dec_ref(v_inl_1347_);
v_snd_1341_ = v_snd_1335_;
goto v___jp_1340_;
}
else
{
size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = lean_usize_of_nat(v___x_1348_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1347_, v___x_1352_, v___x_1353_, v___x_1350_, v_a_754_, v_snd_1335_);
lean_dec_ref(v_inl_1347_);
v___y_1345_ = v___x_1354_;
goto v___jp_1344_;
}
}
else
{
size_t v___x_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = ((size_t)0ULL);
v___x_1356_ = lean_usize_of_nat(v___x_1348_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1347_, v___x_1355_, v___x_1356_, v___x_1350_, v_a_754_, v_snd_1335_);
lean_dec_ref(v_inl_1347_);
v___y_1345_ = v___x_1357_;
goto v___jp_1344_;
}
}
v___jp_1340_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1339_);
v___x_1343_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1342_, v_snd_1341_);
lean_dec_ref(v___x_1342_);
return v___x_1343_;
}
v___jp_1344_:
{
lean_object* v_snd_1346_; 
v_snd_1346_ = lean_ctor_get(v___y_1345_, 1);
lean_inc(v_snd_1346_);
lean_dec_ref(v___y_1345_);
v_snd_1341_ = v_snd_1346_;
goto v___jp_1340_;
}
}
}
else
{
lean_object* v___x_1358_; lean_object* v_s_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1358_ = lean_unsigned_to_nat(0u);
v_s_1359_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1358_);
v___x_1360_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68));
lean_inc(v_s_1359_);
v___x_1361_ = l_Lean_Syntax_isOfKind(v_s_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec(v_s_1359_);
v___x_1362_ = lean_box(0);
v___x_1363_ = l_Lean_Syntax_formatStx(v_stx_753_, v___x_1362_, v___x_1361_);
v___x_1364_ = l_Std_Format_defWidth;
v___x_1365_ = l_Std_Format_pretty(v___x_1363_, v___x_1364_, v___x_1358_, v___x_1358_);
v___x_1366_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1365_, v_a_755_);
lean_dec_ref(v___x_1365_);
return v___x_1366_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec(v_stx_753_);
v___x_1367_ = l_Lean_TSyntax_getString(v_s_1359_);
lean_dec(v_s_1359_);
v___x_1368_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1367_, v_a_755_);
lean_dec_ref(v___x_1367_);
return v___x_1368_;
}
}
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1369_);
lean_dec(v_stx_753_);
v_stx_753_ = v___x_1370_;
goto _start;
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1372_);
v___x_1374_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70));
lean_inc(v___x_1373_);
v___x_1375_ = l_Lean_Syntax_isOfKind(v___x_1373_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v___x_1377_ = l_Lean_Syntax_formatStx(v_stx_753_, v___x_1376_, v___x_1375_);
v___x_1378_ = l_Std_Format_defWidth;
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = l_Std_Format_pretty(v___x_1377_, v___x_1378_, v___x_1379_, v___x_1379_);
v___x_1381_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1380_, v_a_755_);
lean_dec_ref(v___x_1380_);
return v___x_1381_;
}
else
{
lean_object* v___x_1382_; lean_object* v_tk_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v_snd_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1382_ = lean_unsigned_to_nat(0u);
v_tk_1383_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1382_);
lean_dec(v_stx_753_);
v___x_1384_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk_1383_);
v___x_1385_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1384_, v_a_755_);
lean_dec_ref(v___x_1384_);
v_snd_1386_ = lean_ctor_get(v___x_1385_, 1);
lean_inc(v_snd_1386_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_1373_);
v___x_1388_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1387_, v_snd_1386_);
lean_dec_ref(v___x_1387_);
return v___x_1388_;
}
}
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1389_);
v___x_1391_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70));
lean_inc(v___x_1390_);
v___x_1392_ = l_Lean_Syntax_isOfKind(v___x_1390_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v___x_1394_ = l_Lean_Syntax_formatStx(v_stx_753_, v___x_1393_, v___x_1392_);
v___x_1395_ = l_Std_Format_defWidth;
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = l_Std_Format_pretty(v___x_1394_, v___x_1395_, v___x_1396_, v___x_1396_);
v___x_1398_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1397_, v_a_755_);
lean_dec_ref(v___x_1397_);
return v___x_1398_;
}
else
{
lean_object* v___x_1399_; lean_object* v_tk_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v_snd_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1399_ = lean_unsigned_to_nat(0u);
v_tk_1400_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1399_);
lean_dec(v_stx_753_);
v___x_1401_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk_1400_);
v___x_1402_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1401_, v_a_755_);
lean_dec_ref(v___x_1401_);
v_snd_1403_ = lean_ctor_get(v___x_1402_, 1);
lean_inc(v_snd_1403_);
lean_dec_ref(v___x_1402_);
v___x_1404_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_1390_);
v___x_1405_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1404_, v_snd_1403_);
lean_dec_ref(v___x_1404_);
return v___x_1405_;
}
}
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1406_);
v___x_1408_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70));
lean_inc(v___x_1407_);
v___x_1409_ = l_Lean_Syntax_isOfKind(v___x_1407_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v___x_1411_ = l_Lean_Syntax_formatStx(v_stx_753_, v___x_1410_, v___x_1409_);
v___x_1412_ = l_Std_Format_defWidth;
v___x_1413_ = l_Std_Format_pretty(v___x_1411_, v___x_1412_, v___x_1406_, v___x_1406_);
v___x_1414_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1413_, v_a_755_);
lean_dec_ref(v___x_1413_);
return v___x_1414_;
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_snd_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v_snd_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v_snd_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v_snd_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1415_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71));
v___x_1416_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1415_, v_a_755_);
v_snd_1417_ = lean_ctor_get(v___x_1416_, 1);
lean_inc(v_snd_1417_);
lean_dec_ref(v___x_1416_);
v___x_1418_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_1407_);
v___x_1419_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1418_, v_snd_1417_);
lean_dec_ref(v___x_1418_);
v_snd_1420_ = lean_ctor_get(v___x_1419_, 1);
lean_inc(v_snd_1420_);
lean_dec_ref(v___x_1419_);
v___x_1421_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72));
v___x_1422_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1421_, v_snd_1420_);
v_snd_1423_ = lean_ctor_get(v___x_1422_, 1);
lean_inc(v_snd_1423_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = lean_unsigned_to_nat(2u);
v___x_1425_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1424_);
lean_dec(v_stx_753_);
v___x_1426_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_1425_, v_a_754_, v_snd_1423_);
v_snd_1427_ = lean_ctor_get(v___x_1426_, 1);
lean_inc(v_snd_1427_);
lean_dec_ref(v___x_1426_);
v___x_1428_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73));
v___x_1429_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1428_, v_snd_1427_);
return v___x_1429_;
}
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v_snd_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_snd_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v_snd_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v_snd_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1430_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71));
v___x_1431_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1430_, v_a_755_);
v_snd_1432_ = lean_ctor_get(v___x_1431_, 1);
lean_inc(v_snd_1432_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = lean_unsigned_to_nat(1u);
v___x_1434_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1433_);
v___x_1435_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_1434_);
v___x_1436_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1435_, v_snd_1432_);
lean_dec_ref(v___x_1435_);
v_snd_1437_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_snd_1437_);
lean_dec_ref(v___x_1436_);
v___x_1438_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72));
v___x_1439_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1438_, v_snd_1437_);
v_snd_1440_ = lean_ctor_get(v___x_1439_, 1);
lean_inc(v_snd_1440_);
lean_dec_ref(v___x_1439_);
v___x_1441_ = lean_unsigned_to_nat(3u);
v___x_1442_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1441_);
lean_dec(v_stx_753_);
v___x_1443_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_1442_, v_a_754_, v_snd_1440_);
v_snd_1444_ = lean_ctor_get(v___x_1443_, 1);
lean_inc(v_snd_1444_);
lean_dec_ref(v___x_1443_);
v___x_1445_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73));
v___x_1446_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1445_, v_snd_1444_);
return v___x_1446_;
}
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1447_);
v___x_1449_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70));
lean_inc(v___x_1448_);
v___x_1450_ = l_Lean_Syntax_isOfKind(v___x_1448_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v___x_1452_ = l_Lean_Syntax_formatStx(v_stx_753_, v___x_1451_, v___x_1450_);
v___x_1453_ = l_Std_Format_defWidth;
v___x_1454_ = l_Std_Format_pretty(v___x_1452_, v___x_1453_, v___x_1447_, v___x_1447_);
v___x_1455_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1454_, v_a_755_);
lean_dec_ref(v___x_1454_);
return v___x_1455_;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_dec(v_stx_753_);
v___x_1456_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_1448_);
v___x_1457_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1456_, v_a_755_);
lean_dec_ref(v___x_1456_);
return v___x_1457_;
}
}
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1458_);
v___x_1460_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75));
lean_inc(v___x_1459_);
v___x_1461_ = l_Lean_Syntax_isOfKind(v___x_1459_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v___x_1463_ = l_Lean_Syntax_formatStx(v_stx_753_, v___x_1462_, v___x_1461_);
v___x_1464_ = l_Std_Format_defWidth;
v___x_1465_ = l_Std_Format_pretty(v___x_1463_, v___x_1464_, v___x_1458_, v___x_1458_);
v___x_1466_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1465_, v_a_755_);
lean_dec_ref(v___x_1465_);
return v___x_1466_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec(v_stx_753_);
v___x_1467_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1459_);
v___x_1468_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1467_, v_a_755_);
lean_dec_ref(v___x_1467_);
return v___x_1468_;
}
}
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = l_Lean_Syntax_getArg(v_stx_753_, v___x_1469_);
v___x_1471_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68));
lean_inc(v___x_1470_);
v___x_1472_ = l_Lean_Syntax_isOfKind(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v___x_1474_ = l_Lean_Syntax_formatStx(v_stx_753_, v___x_1473_, v___x_1472_);
v___x_1475_ = l_Std_Format_defWidth;
v___x_1476_ = l_Std_Format_pretty(v___x_1474_, v___x_1475_, v___x_1469_, v___x_1469_);
v___x_1477_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1476_, v_a_755_);
lean_dec_ref(v___x_1476_);
return v___x_1477_;
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec(v_stx_753_);
v___x_1478_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1470_);
v___x_1479_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1478_, v_a_755_);
lean_dec_ref(v___x_1478_);
return v___x_1479_;
}
}
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1480_ = l_Lean_Syntax_getArgs(v_stx_753_);
lean_dec(v_stx_753_);
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_array_get_size(v___x_1480_);
v___x_1483_ = lean_box(0);
v___x_1484_ = lean_nat_dec_lt(v___x_1481_, v___x_1482_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; 
lean_dec_ref(v___x_1480_);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1483_);
lean_ctor_set(v___x_1485_, 1, v_a_755_);
return v___x_1485_;
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_nat_dec_le(v___x_1482_, v___x_1482_);
if (v___x_1486_ == 0)
{
if (v___x_1484_ == 0)
{
lean_object* v___x_1487_; 
lean_dec_ref(v___x_1480_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1483_);
lean_ctor_set(v___x_1487_, 1, v_a_755_);
return v___x_1487_;
}
else
{
size_t v___x_1488_; size_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = ((size_t)0ULL);
v___x_1489_ = lean_usize_of_nat(v___x_1482_);
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_1480_, v___x_1488_, v___x_1489_, v___x_1483_, v_a_754_, v_a_755_);
lean_dec_ref(v___x_1480_);
return v___x_1490_;
}
}
else
{
size_t v___x_1491_; size_t v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = ((size_t)0ULL);
v___x_1492_ = lean_usize_of_nat(v___x_1482_);
v___x_1493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_1480_, v___x_1491_, v___x_1492_, v___x_1483_, v_a_754_, v_a_755_);
lean_dec_ref(v___x_1480_);
return v___x_1493_;
}
}
}
v___jp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0));
v___x_759_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_758_, v_snd_757_);
return v___x_759_;
}
v___jp_760_:
{
lean_object* v_snd_762_; 
v_snd_762_ = lean_ctor_get(v___y_761_, 1);
lean_inc(v_snd_762_);
lean_dec_ref(v___y_761_);
v_snd_757_ = v_snd_762_;
goto v___jp_756_;
}
v___jp_763_:
{
lean_object* v_snd_765_; lean_object* v___x_766_; 
v_snd_765_ = lean_ctor_get(v___y_764_, 1);
lean_inc(v_snd_765_);
lean_dec_ref(v___y_764_);
v___x_766_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_765_);
return v___x_766_;
}
v___jp_767_:
{
lean_object* v_snd_769_; lean_object* v___x_770_; 
v_snd_769_ = lean_ctor_get(v___y_768_, 1);
lean_inc(v_snd_769_);
lean_dec_ref(v___y_768_);
v___x_770_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_769_);
return v___x_770_;
}
v___jp_771_:
{
lean_object* v_snd_773_; lean_object* v___x_774_; 
v_snd_773_ = lean_ctor_get(v___y_772_, 1);
lean_inc(v_snd_773_);
lean_dec_ref(v___y_772_);
v___x_774_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_773_);
return v___x_774_;
}
v___jp_775_:
{
lean_object* v_snd_777_; lean_object* v___x_778_; 
v_snd_777_ = lean_ctor_get(v___y_776_, 1);
lean_inc(v_snd_777_);
lean_dec_ref(v___y_776_);
v___x_778_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_777_);
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(lean_object* v_as_1494_, size_t v_i_1495_, size_t v_stop_1496_, lean_object* v_b_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_usize_dec_eq(v_i_1495_, v_stop_1496_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v_fst_1503_; lean_object* v_snd_1504_; size_t v___x_1505_; size_t v___x_1506_; 
v___x_1501_ = lean_array_uget_borrowed(v_as_1494_, v_i_1495_);
lean_inc(v___x_1501_);
v___x_1502_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_1501_, v___y_1498_, v___y_1499_);
v_fst_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_fst_1503_);
v_snd_1504_ = lean_ctor_get(v___x_1502_, 1);
lean_inc(v_snd_1504_);
lean_dec_ref(v___x_1502_);
v___x_1505_ = ((size_t)1ULL);
v___x_1506_ = lean_usize_add(v_i_1495_, v___x_1505_);
v_i_1495_ = v___x_1506_;
v_b_1497_ = v_fst_1503_;
v___y_1499_ = v_snd_1504_;
goto _start;
}
else
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v_b_1497_);
lean_ctor_set(v___x_1508_, 1, v___y_1499_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2___boxed(lean_object* v_as_1509_, lean_object* v_i_1510_, lean_object* v_stop_1511_, lean_object* v_b_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
size_t v_i_boxed_1515_; size_t v_stop_boxed_1516_; lean_object* v_res_1517_; 
v_i_boxed_1515_ = lean_unbox_usize(v_i_1510_);
lean_dec(v_i_1510_);
v_stop_boxed_1516_ = lean_unbox_usize(v_stop_1511_);
lean_dec(v_stop_1511_);
v_res_1517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_as_1509_, v_i_boxed_1515_, v_stop_boxed_1516_, v_b_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v_as_1509_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___boxed(lean_object* v_as_1518_, lean_object* v_sz_1519_, lean_object* v_i_1520_, lean_object* v_b_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
size_t v_sz_boxed_1524_; size_t v_i_boxed_1525_; lean_object* v_res_1526_; 
v_sz_boxed_1524_ = lean_unbox_usize(v_sz_1519_);
lean_dec(v_sz_1519_);
v_i_boxed_1525_ = lean_unbox_usize(v_i_1520_);
lean_dec(v_i_1520_);
v_res_1526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_as_1518_, v_sz_boxed_1524_, v_i_boxed_1525_, v_b_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v_as_1518_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1___boxed(lean_object* v_as_1527_, lean_object* v_sz_1528_, lean_object* v_i_1529_, lean_object* v_b_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
size_t v_sz_boxed_1533_; size_t v_i_boxed_1534_; lean_object* v_res_1535_; 
v_sz_boxed_1533_ = lean_unbox_usize(v_sz_1528_);
lean_dec(v_sz_1528_);
v_i_boxed_1534_ = lean_unbox_usize(v_i_1529_);
lean_dec(v_i_1529_);
v_res_1535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(v_as_1527_, v_sz_boxed_1533_, v_i_boxed_1534_, v_b_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v_as_1527_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object* v_as_1536_, lean_object* v_i_1537_, lean_object* v_stop_1538_, lean_object* v_b_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
size_t v_i_boxed_1542_; size_t v_stop_boxed_1543_; lean_object* v_res_1544_; 
v_i_boxed_1542_ = lean_unbox_usize(v_i_1537_);
lean_dec(v_i_1537_);
v_stop_boxed_1543_ = lean_unbox_usize(v_stop_1538_);
lean_dec(v_stop_1538_);
v_res_1544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v_as_1536_, v_i_boxed_1542_, v_stop_boxed_1543_, v_b_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v_as_1536_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object* v_as_1545_, lean_object* v_sz_1546_, lean_object* v_i_1547_, lean_object* v_b_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
size_t v_sz_boxed_1551_; size_t v_i_boxed_1552_; lean_object* v_res_1553_; 
v_sz_boxed_1551_ = lean_unbox_usize(v_sz_1546_);
lean_dec(v_sz_1546_);
v_i_boxed_1552_ = lean_unbox_usize(v_i_1547_);
lean_dec(v_i_1547_);
v_res_1553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v_as_1545_, v_sz_boxed_1551_, v_i_boxed_1552_, v_b_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v_as_1545_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___boxed(lean_object* v_stx_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_1554_, v_a_1555_, v_a_1556_);
lean_dec(v_a_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(lean_object* v_a_1558_, lean_object* v___y_1559_, lean_object* v___x_1560_, lean_object* v___x_1561_, lean_object* v_inst_1562_, lean_object* v_R_1563_, lean_object* v_a_1564_, lean_object* v_b_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(v_a_1558_, v___y_1559_, v___x_1560_, v___x_1561_, v_a_1564_, v_b_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object* v_a_1567_, lean_object* v___y_1568_, lean_object* v___x_1569_, lean_object* v___x_1570_, lean_object* v_inst_1571_, lean_object* v_R_1572_, lean_object* v_a_1573_, lean_object* v_b_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v_a_1567_, v___y_1568_, v___x_1569_, v___x_1570_, v_inst_1571_, v_R_1572_, v_a_1573_, v_b_1574_);
lean_dec_ref(v___x_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v_a_1567_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0(lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_1577_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec_ref(v___x_1581_);
v___x_1582_ = lean_box(0);
v___x_1583_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1582_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v___x_1584_; 
lean_dec_ref(v___x_1583_);
v___x_1584_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_1577_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1585_; 
lean_dec_ref(v___x_1584_);
v___x_1585_ = l_Lean_Doc_Parser_metadataContents_formatter(v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v___x_1586_; 
lean_dec_ref(v___x_1585_);
v___x_1586_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_1577_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; 
lean_dec_ref(v___x_1586_);
v___x_1587_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1582_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
return v___x_1587_;
}
else
{
return v___x_1586_;
}
}
else
{
return v___x_1585_;
}
}
else
{
return v___x_1584_;
}
}
else
{
return v___x_1583_;
}
}
else
{
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0___boxed(lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0(v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v___f_1600_; lean_object* v___x_1601_; 
v___f_1600_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0));
v___x_1601_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___f_1600_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___boxed(lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString(lean_object* v_stx_1608_){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v_snd_1612_; 
v___x_1609_ = lean_unsigned_to_nat(0u);
v___x_1610_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___x_1611_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_1608_, v___x_1609_, v___x_1610_);
v_snd_1612_ = lean_ctor_get(v___x_1611_, 1);
lean_inc(v_snd_1612_);
lean_dec_ref(v___x_1611_);
return v_snd_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(lean_object* v_range_1619_, lean_object* v_b_1620_, lean_object* v_i_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_stop_1627_; lean_object* v_step_1628_; uint8_t v___x_1629_; 
v_stop_1627_ = lean_ctor_get(v_range_1619_, 1);
v_step_1628_ = lean_ctor_get(v_range_1619_, 2);
v___x_1629_ = lean_nat_dec_lt(v_i_1621_, v_stop_1627_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; 
lean_dec(v_i_1621_);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_b_1620_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1650_; 
v___x_1631_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_1623_);
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1650_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1650_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1636_ = lean_box(0);
lean_inc(v_a_1632_);
v___x_1640_ = l_Lean_Syntax_getKind(v_a_1632_);
v___x_1641_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1));
v___x_1642_ = lean_name_eq(v___x_1640_, v___x_1641_);
lean_dec(v___x_1640_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString(v_a_1632_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set_tag(v___x_1634_, 3);
lean_ctor_set(v___x_1634_, 0, v___x_1643_);
v___x_1645_ = v___x_1634_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_1645_, v___y_1623_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v___x_1647_; 
lean_dec_ref(v___x_1646_);
v___x_1647_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v___y_1623_);
lean_dec_ref(v___x_1647_);
goto v___jp_1637_;
}
else
{
lean_dec(v_i_1621_);
return v___x_1646_;
}
}
}
else
{
lean_object* v___x_1649_; 
lean_del_object(v___x_1634_);
lean_dec(v_a_1632_);
v___x_1649_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_dec_ref(v___x_1649_);
goto v___jp_1637_;
}
else
{
lean_dec(v_i_1621_);
return v___x_1649_;
}
}
v___jp_1637_:
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_nat_add(v_i_1621_, v_step_1628_);
lean_dec(v_i_1621_);
v_b_1620_ = v___x_1636_;
v_i_1621_ = v___x_1638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(lean_object* v_range_1651_, lean_object* v_b_1652_, lean_object* v_i_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v_range_1651_, v_b_1652_, v_i_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec_ref(v_range_1651_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0(lean_object* v___x_1660_, lean_object* v___x_1661_, lean_object* v___x_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___x_1660_, v___x_1661_, v___x_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; 
v_unused_1676_ = lean_ctor_get(v___x_1668_, 0);
lean_dec(v_unused_1676_);
v___x_1670_ = v___x_1668_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_dec(v___x_1668_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1661_);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1661_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
else
{
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0___boxed(lean_object* v___x_1677_, lean_object* v___x_1678_, lean_object* v___x_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_Doc_Parser_document_formatter___lam__0(v___x_1677_, v___x_1678_, v___x_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___x_1677_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1(lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; lean_object* v_a_1692_; lean_object* v___x_1693_; lean_object* v_i_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___f_1699_; lean_object* v___x_1700_; 
v___x_1691_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_1687_);
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref(v___x_1691_);
v___x_1693_ = l_Lean_Syntax_getArgs(v_a_1692_);
lean_dec(v_a_1692_);
v_i_1694_ = lean_array_get_size(v___x_1693_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v_i_1694_);
lean_ctor_set(v___x_1697_, 2, v___x_1696_);
v___x_1698_ = lean_box(0);
v___f_1699_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1699_, 0, v___x_1697_);
lean_closure_set(v___f_1699_, 1, v___x_1698_);
lean_closure_set(v___f_1699_, 2, v___x_1695_);
v___x_1700_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___f_1699_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1___boxed(lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Doc_Parser_document_formatter___lam__1(v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter(lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___f_1713_; lean_object* v___x_1714_; 
v___f_1713_ = ((lean_object*)(l_Lean_Doc_Parser_document_formatter___closed__0));
v___x_1714_ = l_Lean_PrettyPrinter_Formatter_concat(v___f_1713_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___boxed(lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Doc_Parser_document_formatter(v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0(lean_object* v_range_1721_, lean_object* v_b_1722_, lean_object* v_i_1723_, lean_object* v_hs_1724_, lean_object* v_hl_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v_range_1721_, v_b_1722_, v_i_1723_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(lean_object* v_range_1732_, lean_object* v_b_1733_, lean_object* v_i_1734_, lean_object* v_hs_1735_, lean_object* v_hl_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0(v_range_1732_, v_b_1733_, v_i_1734_, v_hs_1735_, v_hl_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v_range_1732_);
return v_res_1742_;
}
}
lean_object* runtime_initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Parser(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Formatter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Formatter(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* initialize_Lean_DocString_Parser(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Formatter(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Formatter(builtin);
}
#ifdef __cplusplus
}
#endif
