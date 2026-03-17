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
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(lean_object*, lean_object*);
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
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
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
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
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
v___x_293_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_289_, v___x_292_);
v___x_294_ = lean_string_append(v_a_290_, v___x_293_);
lean_dec_ref(v___x_293_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_291_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
v___x_297_ = lean_string_utf8_byte_size(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_303_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
v___x_304_ = lean_string_utf8_byte_size(v_a_299_);
v___x_305_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0);
v___x_306_ = lean_nat_dec_le(v___x_305_, v___x_304_);
if (v___x_306_ == 0)
{
lean_dec(v_a_298_);
goto v___jp_300_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_nat_sub(v___x_304_, v___x_305_);
v___x_309_ = lean_string_memcmp(v_a_299_, v___x_303_, v___x_308_, v___x_307_, v___x_305_);
lean_dec(v___x_308_);
if (v___x_309_ == 0)
{
lean_dec(v_a_298_);
goto v___jp_300_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___x_311_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_298_, v___x_310_);
v___x_312_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_311_, v_a_299_);
lean_dec_ref(v___x_311_);
return v___x_312_;
}
}
v___jp_300_:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_box(0);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v_a_299_);
return v___x_302_;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0));
v___x_315_ = lean_string_utf8_byte_size(v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(lean_object* v_a_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_317_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0));
v___x_329_ = lean_string_utf8_byte_size(v_a_316_);
v___x_330_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1);
v___x_331_ = lean_nat_dec_le(v___x_330_, v___x_329_);
if (v___x_331_ == 0)
{
goto v___jp_318_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_nat_sub(v___x_329_, v___x_330_);
v___x_334_ = lean_string_memcmp(v_a_316_, v___x_317_, v___x_333_, v___x_332_, v___x_330_);
lean_dec(v___x_333_);
if (v___x_334_ == 0)
{
goto v___jp_318_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_a_316_);
return v___x_336_;
}
}
v___jp_318_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_319_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
v___x_320_ = lean_string_utf8_byte_size(v_a_316_);
v___x_321_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0);
v___x_322_ = lean_nat_dec_le(v___x_321_, v___x_320_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
v___x_323_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_317_, v_a_316_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_nat_sub(v___x_320_, v___x_321_);
v___x_326_ = lean_string_memcmp(v_a_316_, v___x_319_, v___x_325_, v___x_324_, v___x_321_);
lean_dec(v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_317_, v_a_316_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_319_, v_a_316_);
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock(lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_a_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___boxed(lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock(v_a_340_, v_a_341_);
lean_dec(v_a_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(lean_object* v_s_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0));
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object* v_s_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_s_347_);
lean_dec_ref(v_s_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
lean_object* v_zero_351_; uint8_t v_isZero_352_; 
v_zero_351_ = lean_unsigned_to_nat(0u);
v_isZero_352_ = lean_nat_dec_eq(v_x_349_, v_zero_351_);
if (v_isZero_352_ == 1)
{
lean_dec(v_x_349_);
return v_x_350_;
}
else
{
uint32_t v___x_353_; lean_object* v_one_354_; lean_object* v_n_355_; lean_object* v___x_356_; 
v___x_353_ = 35;
v_one_354_ = lean_unsigned_to_nat(1u);
v_n_355_ = lean_nat_sub(v_x_349_, v_one_354_);
lean_dec(v_x_349_);
v___x_356_ = lean_string_push(v_x_350_, v___x_353_);
v_x_349_ = v_n_355_;
v_x_350_ = v___x_356_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(lean_object* v_a_358_, lean_object* v___y_359_, lean_object* v___x_360_, lean_object* v___x_361_, lean_object* v_a_362_, lean_object* v_b_363_){
_start:
{
lean_object* v_it_365_; lean_object* v_startInclusive_366_; lean_object* v_endExclusive_367_; 
if (lean_obj_tag(v_a_362_) == 0)
{
lean_object* v_currPos_374_; lean_object* v_searcher_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_401_; 
v_currPos_374_ = lean_ctor_get(v_a_362_, 0);
v_searcher_375_ = lean_ctor_get(v_a_362_, 1);
v_isSharedCheck_401_ = !lean_is_exclusive(v_a_362_);
if (v_isSharedCheck_401_ == 0)
{
v___x_377_ = v_a_362_;
v_isShared_378_ = v_isSharedCheck_401_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_searcher_375_);
lean_inc(v_currPos_374_);
lean_dec(v_a_362_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_401_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v_startInclusive_379_; lean_object* v_endExclusive_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_startInclusive_379_ = lean_ctor_get(v___x_360_, 1);
v_endExclusive_380_ = lean_ctor_get(v___x_360_, 2);
v___x_381_ = lean_nat_sub(v_endExclusive_380_, v_startInclusive_379_);
v___x_382_ = lean_nat_dec_eq(v_searcher_375_, v___x_381_);
lean_dec(v___x_381_);
if (v___x_382_ == 0)
{
uint32_t v___x_383_; uint32_t v___x_384_; uint8_t v___x_385_; 
v___x_383_ = 10;
v___x_384_ = lean_string_utf8_get_fast(v___y_359_, v_searcher_375_);
v___x_385_ = lean_uint32_dec_eq(v___x_384_, v___x_383_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_string_utf8_next_fast(v___y_359_, v_searcher_375_);
lean_dec(v_searcher_375_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v___x_386_);
v___x_388_ = v___x_377_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_currPos_374_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___x_386_);
v___x_388_ = v_reuseFailAlloc_390_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
v_a_362_ = v___x_388_;
goto _start;
}
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_slice_394_; lean_object* v_nextIt_396_; 
v___x_391_ = lean_string_utf8_next_fast(v___y_359_, v_searcher_375_);
v___x_392_ = lean_nat_sub(v___x_391_, v_searcher_375_);
v___x_393_ = lean_nat_add(v_searcher_375_, v___x_392_);
lean_dec(v___x_392_);
v_slice_394_ = l_String_Slice_subslice_x21(v___x_360_, v_currPos_374_, v_searcher_375_);
lean_inc(v___x_393_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v___x_393_);
lean_ctor_set(v___x_377_, 0, v___x_393_);
v_nextIt_396_ = v___x_377_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_393_);
v_nextIt_396_ = v_reuseFailAlloc_399_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v_startInclusive_397_; lean_object* v_endExclusive_398_; 
v_startInclusive_397_ = lean_ctor_get(v_slice_394_, 0);
lean_inc(v_startInclusive_397_);
v_endExclusive_398_ = lean_ctor_get(v_slice_394_, 1);
lean_inc(v_endExclusive_398_);
lean_dec_ref(v_slice_394_);
v_it_365_ = v_nextIt_396_;
v_startInclusive_366_ = v_startInclusive_397_;
v_endExclusive_367_ = v_endExclusive_398_;
goto v___jp_364_;
}
}
}
else
{
lean_object* v___x_400_; 
lean_del_object(v___x_377_);
lean_dec(v_searcher_375_);
v___x_400_ = lean_box(1);
lean_inc(v___x_361_);
v_it_365_ = v___x_400_;
v_startInclusive_366_ = v_currPos_374_;
v_endExclusive_367_ = v___x_361_;
goto v___jp_364_;
}
}
}
else
{
lean_dec(v___x_361_);
lean_dec(v_a_358_);
return v_b_363_;
}
v___jp_364_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_368_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
lean_inc(v_a_358_);
v___x_369_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_358_, v___x_368_);
v___x_370_ = lean_string_utf8_extract(v___y_359_, v_startInclusive_366_, v_endExclusive_367_);
lean_dec(v_endExclusive_367_);
lean_dec(v_startInclusive_366_);
v___x_371_ = lean_string_append(v___x_369_, v___x_370_);
lean_dec_ref(v___x_370_);
v___x_372_ = lean_array_push(v_b_363_, v___x_371_);
v_a_362_ = v_it_365_;
v_b_363_ = v___x_372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg___boxed(lean_object* v_a_402_, lean_object* v___y_403_, lean_object* v___x_404_, lean_object* v___x_405_, lean_object* v_a_406_, lean_object* v_b_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(v_a_402_, v___y_403_, v___x_404_, v___x_405_, v_a_406_, v_b_407_);
lean_dec_ref(v___x_404_);
lean_dec_ref(v___y_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(lean_object* v_as_592_, size_t v_sz_593_, size_t v_i_594_, lean_object* v_b_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
uint8_t v___x_598_; 
v___x_598_ = lean_usize_dec_lt(v_i_594_, v_sz_593_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
lean_dec(v___y_596_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_b_595_);
lean_ctor_set(v___x_599_, 1, v___y_597_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_snd_602_; lean_object* v_a_603_; lean_object* v___x_604_; lean_object* v_snd_605_; lean_object* v___x_606_; size_t v___x_607_; size_t v___x_608_; 
v___x_600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0));
v___x_601_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_600_, v___y_597_);
v_snd_602_ = lean_ctor_get(v___x_601_, 1);
lean_inc(v_snd_602_);
lean_dec_ref(v___x_601_);
v_a_603_ = lean_array_uget_borrowed(v_as_592_, v_i_594_);
lean_inc(v___y_596_);
lean_inc(v_a_603_);
v___x_604_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_603_, v___y_596_, v_snd_602_);
v_snd_605_ = lean_ctor_get(v___x_604_, 1);
lean_inc(v_snd_605_);
lean_dec_ref(v___x_604_);
v___x_606_ = lean_box(0);
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_add(v_i_594_, v___x_607_);
v_i_594_ = v___x_608_;
v_b_595_ = v___x_606_;
v___y_597_ = v_snd_605_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(lean_object* v_as_611_, size_t v_sz_612_, size_t v_i_613_, lean_object* v_b_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_lt(v_i_613_, v_sz_612_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_dec(v___y_615_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_b_614_);
lean_ctor_set(v___x_618_, 1, v___y_616_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_snd_621_; lean_object* v_a_622_; lean_object* v___x_623_; lean_object* v_snd_624_; lean_object* v___x_625_; size_t v___x_626_; size_t v___x_627_; 
v___x_619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0));
v___x_620_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_619_, v___y_616_);
v_snd_621_ = lean_ctor_get(v___x_620_, 1);
lean_inc(v_snd_621_);
lean_dec_ref(v___x_620_);
v_a_622_ = lean_array_uget_borrowed(v_as_611_, v_i_613_);
lean_inc(v___y_615_);
lean_inc(v_a_622_);
v___x_623_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_622_, v___y_615_, v_snd_621_);
v_snd_624_ = lean_ctor_get(v___x_623_, 1);
lean_inc(v_snd_624_);
lean_dec_ref(v___x_623_);
v___x_625_ = lean_box(0);
v___x_626_ = ((size_t)1ULL);
v___x_627_ = lean_usize_add(v_i_613_, v___x_626_);
v_i_613_ = v___x_627_;
v_b_614_ = v___x_625_;
v___y_616_ = v_snd_624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(lean_object* v_as_639_, size_t v_sz_640_, size_t v_i_641_, lean_object* v_b_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_a_646_; lean_object* v_snd_647_; uint8_t v___x_651_; 
v___x_651_ = lean_usize_dec_lt(v_i_641_, v_sz_640_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v_b_642_);
lean_ctor_set(v___x_652_, 1, v___y_644_);
return v___x_652_;
}
else
{
lean_object* v_a_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_a_653_ = lean_array_uget_borrowed(v_as_639_, v_i_641_);
v___x_654_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4));
lean_inc(v_a_653_);
v___x_655_ = l_Lean_Syntax_isOfKind(v_a_653_, v___x_654_);
if (v___x_655_ == 0)
{
v_a_646_ = v_b_642_;
v_snd_647_ = v___y_644_;
goto v___jp_645_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v_snd_660_; lean_object* v___x_661_; lean_object* v_snd_663_; lean_object* v___y_668_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
lean_inc(v_b_642_);
v___x_656_ = l_Nat_reprFast(v_b_642_);
v___x_657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0));
v___x_658_ = lean_string_append(v___x_656_, v___x_657_);
v___x_659_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_658_, v___y_644_);
lean_dec_ref(v___x_658_);
v_snd_660_ = lean_ctor_get(v___x_659_, 1);
lean_inc(v_snd_660_);
lean_dec_ref(v___x_659_);
v___x_661_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = l_Lean_Syntax_getArg(v_a_653_, v___x_661_);
v___x_672_ = l_Lean_Syntax_getArgs(v___x_671_);
lean_dec(v___x_671_);
v___x_673_ = lean_array_get_size(v___x_672_);
v___x_674_ = lean_nat_dec_lt(v___x_670_, v___x_673_);
if (v___x_674_ == 0)
{
lean_dec_ref(v___x_672_);
v_snd_663_ = v_snd_660_;
goto v___jp_662_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_675_ = lean_unsigned_to_nat(2u);
v___x_676_ = lean_nat_add(v___y_643_, v___x_675_);
v___x_677_ = lean_box(0);
v___x_678_ = lean_nat_dec_le(v___x_673_, v___x_673_);
if (v___x_678_ == 0)
{
if (v___x_674_ == 0)
{
lean_dec(v___x_676_);
lean_dec_ref(v___x_672_);
v_snd_663_ = v_snd_660_;
goto v___jp_662_;
}
else
{
size_t v___x_679_; size_t v___x_680_; lean_object* v___x_681_; 
v___x_679_ = ((size_t)0ULL);
v___x_680_ = lean_usize_of_nat(v___x_673_);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_672_, v___x_679_, v___x_680_, v___x_677_, v___x_676_, v_snd_660_);
lean_dec_ref(v___x_672_);
v___y_668_ = v___x_681_;
goto v___jp_667_;
}
}
else
{
size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_682_ = ((size_t)0ULL);
v___x_683_ = lean_usize_of_nat(v___x_673_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_672_, v___x_682_, v___x_683_, v___x_677_, v___x_676_, v_snd_660_);
lean_dec_ref(v___x_672_);
v___y_668_ = v___x_684_;
goto v___jp_667_;
}
}
v___jp_662_:
{
lean_object* v___x_664_; lean_object* v_snd_665_; lean_object* v___x_666_; 
v___x_664_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_663_);
v_snd_665_ = lean_ctor_get(v___x_664_, 1);
lean_inc(v_snd_665_);
lean_dec_ref(v___x_664_);
v___x_666_ = lean_nat_add(v_b_642_, v___x_661_);
lean_dec(v_b_642_);
v_a_646_ = v___x_666_;
v_snd_647_ = v_snd_665_;
goto v___jp_645_;
}
v___jp_667_:
{
lean_object* v_snd_669_; 
v_snd_669_ = lean_ctor_get(v___y_668_, 1);
lean_inc(v_snd_669_);
lean_dec_ref(v___y_668_);
v_snd_663_ = v_snd_669_;
goto v___jp_662_;
}
}
}
v___jp_645_:
{
size_t v___x_648_; size_t v___x_649_; 
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_641_, v___x_648_);
v_i_641_ = v___x_649_;
v_b_642_ = v_a_646_;
v___y_644_ = v_snd_647_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(lean_object* v_as_686_, size_t v_i_687_, size_t v_stop_688_, lean_object* v_b_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_fst_693_; lean_object* v_snd_694_; lean_object* v___y_699_; lean_object* v___y_703_; uint8_t v___x_706_; 
v___x_706_ = lean_usize_dec_eq(v_i_687_, v_stop_688_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_707_ = lean_array_uget_borrowed(v_as_686_, v_i_687_);
v___x_708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4));
lean_inc(v___x_707_);
v___x_709_ = l_Lean_Syntax_isOfKind(v___x_707_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
v___x_710_ = lean_box(0);
v_fst_693_ = v___x_710_;
v_snd_694_ = v___y_691_;
goto v___jp_692_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_snd_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5));
v___x_712_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_711_, v___y_691_);
v_snd_713_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_snd_713_);
lean_dec_ref(v___x_712_);
v___x_714_ = lean_unsigned_to_nat(1u);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = l_Lean_Syntax_getArg(v___x_707_, v___x_714_);
v___x_717_ = l_Lean_Syntax_getArgs(v___x_716_);
lean_dec(v___x_716_);
v___x_718_ = lean_array_get_size(v___x_717_);
v___x_719_ = lean_nat_dec_lt(v___x_715_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec_ref(v___x_717_);
v___x_720_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_713_);
v___y_699_ = v___x_720_;
goto v___jp_698_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_721_ = lean_unsigned_to_nat(2u);
v___x_722_ = lean_nat_add(v___y_690_, v___x_721_);
v___x_723_ = lean_box(0);
v___x_724_ = lean_nat_dec_le(v___x_718_, v___x_718_);
if (v___x_724_ == 0)
{
if (v___x_719_ == 0)
{
lean_object* v___x_725_; 
lean_dec(v___x_722_);
lean_dec_ref(v___x_717_);
v___x_725_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_713_);
v___y_699_ = v___x_725_;
goto v___jp_698_;
}
else
{
size_t v___x_726_; size_t v___x_727_; lean_object* v___x_728_; 
v___x_726_ = ((size_t)0ULL);
v___x_727_ = lean_usize_of_nat(v___x_718_);
v___x_728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_717_, v___x_726_, v___x_727_, v___x_723_, v___x_722_, v_snd_713_);
lean_dec_ref(v___x_717_);
v___y_703_ = v___x_728_;
goto v___jp_702_;
}
}
else
{
size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; 
v___x_729_ = ((size_t)0ULL);
v___x_730_ = lean_usize_of_nat(v___x_718_);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_717_, v___x_729_, v___x_730_, v___x_723_, v___x_722_, v_snd_713_);
lean_dec_ref(v___x_717_);
v___y_703_ = v___x_731_;
goto v___jp_702_;
}
}
}
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v_b_689_);
lean_ctor_set(v___x_732_, 1, v___y_691_);
return v___x_732_;
}
v___jp_692_:
{
size_t v___x_695_; size_t v___x_696_; 
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_add(v_i_687_, v___x_695_);
v_i_687_ = v___x_696_;
v_b_689_ = v_fst_693_;
v___y_691_ = v_snd_694_;
goto _start;
}
v___jp_698_:
{
lean_object* v_fst_700_; lean_object* v_snd_701_; 
v_fst_700_ = lean_ctor_get(v___y_699_, 0);
lean_inc(v_fst_700_);
v_snd_701_ = lean_ctor_get(v___y_699_, 1);
lean_inc(v_snd_701_);
lean_dec_ref(v___y_699_);
v_fst_693_ = v_fst_700_;
v_snd_694_ = v_snd_701_;
goto v___jp_692_;
}
v___jp_702_:
{
lean_object* v_snd_704_; lean_object* v___x_705_; 
v_snd_704_ = lean_ctor_get(v___y_703_, 1);
lean_inc(v_snd_704_);
lean_dec_ref(v___y_703_);
v___x_705_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_704_);
v___y_699_ = v___x_705_;
goto v___jp_698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object* v_stx_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_snd_751_; lean_object* v___y_755_; lean_object* v___y_758_; lean_object* v___y_762_; lean_object* v___y_766_; lean_object* v___y_770_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
lean_inc(v_stx_747_);
v___x_773_ = l_Lean_Syntax_getKind(v_stx_747_);
v___x_774_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2));
v___x_775_ = lean_name_eq(v___x_773_, v___x_774_);
lean_dec(v___x_773_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_776_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4));
lean_inc(v_stx_747_);
v___x_777_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6));
lean_inc(v_stx_747_);
v___x_779_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_780_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
lean_inc(v_stx_747_);
v___x_781_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
lean_inc(v_stx_747_);
v___x_783_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12));
lean_inc(v_stx_747_);
v___x_785_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14));
lean_inc(v_stx_747_);
v___x_787_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16));
lean_inc(v_stx_747_);
v___x_789_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18));
lean_inc(v_stx_747_);
v___x_791_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20));
lean_inc(v_stx_747_);
v___x_793_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22));
lean_inc(v_stx_747_);
v___x_795_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24));
lean_inc(v_stx_747_);
v___x_797_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26));
lean_inc(v_stx_747_);
v___x_799_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28));
lean_inc(v_stx_747_);
v___x_801_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30));
lean_inc(v_stx_747_);
v___x_803_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32));
lean_inc(v_stx_747_);
v___x_805_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34));
lean_inc(v_stx_747_);
v___x_807_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36));
lean_inc(v_stx_747_);
v___x_809_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38));
lean_inc(v_stx_747_);
v___x_811_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40));
lean_inc(v_stx_747_);
v___x_813_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42));
lean_inc(v_stx_747_);
v___x_815_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44));
lean_inc(v_stx_747_);
v___x_817_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46));
lean_inc(v_stx_747_);
v___x_819_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48));
lean_inc(v_stx_747_);
v___x_821_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50));
lean_inc(v_stx_747_);
v___x_823_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52));
lean_inc(v_stx_747_);
v___x_825_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54));
lean_inc(v_stx_747_);
v___x_827_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56));
lean_inc(v_stx_747_);
v___x_829_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58));
lean_inc(v_stx_747_);
v___x_831_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60));
lean_inc(v_stx_747_);
v___x_833_ = l_Lean_Syntax_isOfKind(v_stx_747_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v_a_748_);
v___x_834_ = lean_box(0);
v___x_835_ = l_Lean_Syntax_formatStx(v_stx_747_, v___x_834_, v___x_833_);
v___x_836_ = l_Std_Format_defWidth;
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = l_Std_Format_pretty(v___x_835_, v___x_836_, v___x_837_, v___x_837_);
v___x_839_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_838_, v_a_749_);
lean_dec_ref(v___x_838_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; lean_object* v_snd_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_snd_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_snd_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v_args_852_; lean_object* v___x_853_; size_t v_sz_854_; size_t v___x_855_; lean_object* v___x_856_; lean_object* v_snd_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_snd_860_; lean_object* v___x_861_; 
lean_inc(v_a_748_);
v___x_840_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_748_, v_a_749_);
v_snd_841_ = lean_ctor_get(v___x_840_, 1);
lean_inc(v_snd_841_);
lean_dec_ref(v___x_840_);
v___x_842_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61));
v___x_843_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_842_, v_snd_841_);
v_snd_844_ = lean_ctor_get(v___x_843_, 1);
lean_inc(v_snd_844_);
lean_dec_ref(v___x_843_);
v___x_845_ = lean_unsigned_to_nat(1u);
v___x_846_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_845_);
v___x_847_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_846_);
v___x_848_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_847_, v_snd_844_);
lean_dec_ref(v___x_847_);
v_snd_849_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_snd_849_);
lean_dec_ref(v___x_848_);
v___x_850_ = lean_unsigned_to_nat(2u);
v___x_851_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_850_);
lean_dec(v_stx_747_);
v_args_852_ = l_Lean_Syntax_getArgs(v___x_851_);
lean_dec(v___x_851_);
v___x_853_ = lean_box(0);
v_sz_854_ = lean_array_size(v_args_852_);
v___x_855_ = ((size_t)0ULL);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_args_852_, v_sz_854_, v___x_855_, v___x_853_, v_a_748_, v_snd_849_);
lean_dec_ref(v_args_852_);
v_snd_857_ = lean_ctor_get(v___x_856_, 1);
lean_inc(v_snd_857_);
lean_dec_ref(v___x_856_);
v___x_858_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62));
v___x_859_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_858_, v_snd_857_);
v_snd_860_ = lean_ctor_get(v___x_859_, 1);
lean_inc(v_snd_860_);
lean_dec_ref(v___x_859_);
v___x_861_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_860_);
return v___x_861_;
}
}
else
{
lean_object* v___x_862_; lean_object* v_snd_863_; lean_object* v___x_864_; lean_object* v_tk1_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v_snd_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v_snd_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_snd_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v_args_879_; lean_object* v___x_880_; size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; lean_object* v_snd_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v_snd_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v_tk2_891_; lean_object* v_snd_893_; lean_object* v___y_903_; lean_object* v_blks_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
lean_inc(v_a_748_);
v___x_862_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_748_, v_a_749_);
v_snd_863_ = lean_ctor_get(v___x_862_, 1);
lean_inc(v_snd_863_);
lean_dec_ref(v___x_862_);
v___x_864_ = lean_unsigned_to_nat(0u);
v_tk1_865_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_864_);
v___x_866_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_865_);
v___x_867_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_866_, v_snd_863_);
lean_dec_ref(v___x_866_);
v_snd_868_ = lean_ctor_get(v___x_867_, 1);
lean_inc(v_snd_868_);
lean_dec_ref(v___x_867_);
v___x_869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0));
v___x_870_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_869_, v_snd_868_);
v_snd_871_ = lean_ctor_get(v___x_870_, 1);
lean_inc(v_snd_871_);
lean_dec_ref(v___x_870_);
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_872_);
v___x_874_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_873_);
v___x_875_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_874_, v_snd_871_);
lean_dec_ref(v___x_874_);
v_snd_876_ = lean_ctor_get(v___x_875_, 1);
lean_inc(v_snd_876_);
lean_dec_ref(v___x_875_);
v___x_877_ = lean_unsigned_to_nat(2u);
v___x_878_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_877_);
v_args_879_ = l_Lean_Syntax_getArgs(v___x_878_);
lean_dec(v___x_878_);
v___x_880_ = lean_box(0);
v_sz_881_ = lean_array_size(v_args_879_);
v___x_882_ = ((size_t)0ULL);
lean_inc(v_a_748_);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(v_args_879_, v_sz_881_, v___x_882_, v___x_880_, v_a_748_, v_snd_876_);
lean_dec_ref(v_args_879_);
v_snd_884_ = lean_ctor_get(v___x_883_, 1);
lean_inc(v_snd_884_);
lean_dec_ref(v___x_883_);
v___x_885_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
v___x_886_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_885_, v_snd_884_);
v_snd_887_ = lean_ctor_get(v___x_886_, 1);
lean_inc(v_snd_887_);
lean_dec_ref(v___x_886_);
v___x_888_ = lean_unsigned_to_nat(4u);
v___x_889_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_888_);
v___x_890_ = lean_unsigned_to_nat(5u);
v_tk2_891_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_890_);
lean_dec(v_stx_747_);
v_blks_905_ = l_Lean_Syntax_getArgs(v___x_889_);
lean_dec(v___x_889_);
v___x_906_ = lean_array_get_size(v_blks_905_);
v___x_907_ = lean_nat_dec_lt(v___x_864_, v___x_906_);
if (v___x_907_ == 0)
{
lean_dec_ref(v_blks_905_);
v_snd_893_ = v_snd_887_;
goto v___jp_892_;
}
else
{
uint8_t v___x_908_; 
v___x_908_ = lean_nat_dec_le(v___x_906_, v___x_906_);
if (v___x_908_ == 0)
{
if (v___x_907_ == 0)
{
lean_dec_ref(v_blks_905_);
v_snd_893_ = v_snd_887_;
goto v___jp_892_;
}
else
{
size_t v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_usize_of_nat(v___x_906_);
lean_inc(v_a_748_);
v___x_910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_905_, v___x_882_, v___x_909_, v___x_880_, v_a_748_, v_snd_887_);
lean_dec_ref(v_blks_905_);
v___y_903_ = v___x_910_;
goto v___jp_902_;
}
}
else
{
size_t v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_usize_of_nat(v___x_906_);
lean_inc(v_a_748_);
v___x_912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_905_, v___x_882_, v___x_911_, v___x_880_, v_a_748_, v_snd_887_);
lean_dec_ref(v_blks_905_);
v___y_903_ = v___x_912_;
goto v___jp_902_;
}
}
v___jp_892_:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_snd_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_snd_900_; lean_object* v___x_901_; 
v___x_894_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___x_895_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_748_, v___x_894_);
v___x_896_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_895_, v_snd_893_);
lean_dec_ref(v___x_895_);
v_snd_897_ = lean_ctor_get(v___x_896_, 1);
lean_inc(v_snd_897_);
lean_dec_ref(v___x_896_);
v___x_898_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_891_);
v___x_899_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_898_, v_snd_897_);
lean_dec_ref(v___x_898_);
v_snd_900_ = lean_ctor_get(v___x_899_, 1);
lean_inc(v_snd_900_);
lean_dec_ref(v___x_899_);
v___x_901_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_900_);
return v___x_901_;
}
v___jp_902_:
{
lean_object* v_snd_904_; 
v_snd_904_ = lean_ctor_get(v___y_903_, 1);
lean_inc(v_snd_904_);
lean_dec_ref(v___y_903_);
v_snd_893_ = v_snd_904_;
goto v___jp_892_;
}
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_913_);
v___x_915_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_914_);
v___x_916_ = l_Lean_Syntax_matchesNull(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec(v___x_914_);
lean_dec(v_a_748_);
v___x_917_ = lean_box(0);
v___x_918_ = l_Lean_Syntax_formatStx(v_stx_747_, v___x_917_, v___x_916_);
v___x_919_ = l_Std_Format_defWidth;
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = l_Std_Format_pretty(v___x_918_, v___x_919_, v___x_920_, v___x_920_);
v___x_922_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_921_, v_a_749_);
lean_dec_ref(v___x_921_);
return v___x_922_;
}
else
{
lean_object* v___x_923_; lean_object* v_snd_924_; lean_object* v___x_925_; lean_object* v_tk1_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_snd_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v_snd_933_; lean_object* v___x_934_; lean_object* v_args_935_; lean_object* v___x_936_; size_t v_sz_937_; size_t v___x_938_; lean_object* v___x_939_; lean_object* v_snd_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v_snd_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_tk2_947_; lean_object* v___y_949_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_inc(v_a_748_);
v___x_923_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_748_, v_a_749_);
v_snd_924_ = lean_ctor_get(v___x_923_, 1);
lean_inc(v_snd_924_);
lean_dec_ref(v___x_923_);
v___x_925_ = lean_unsigned_to_nat(0u);
v_tk1_926_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_925_);
v___x_927_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_926_);
v___x_928_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_927_, v_snd_924_);
lean_dec_ref(v___x_927_);
v_snd_929_ = lean_ctor_get(v___x_928_, 1);
lean_inc(v_snd_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = l_Lean_Syntax_getArg(v___x_914_, v___x_925_);
v___x_931_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_930_);
v___x_932_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_931_, v_snd_929_);
lean_dec_ref(v___x_931_);
v_snd_933_ = lean_ctor_get(v___x_932_, 1);
lean_inc(v_snd_933_);
lean_dec_ref(v___x_932_);
v___x_934_ = l_Lean_Syntax_getArg(v___x_914_, v___x_913_);
lean_dec(v___x_914_);
v_args_935_ = l_Lean_Syntax_getArgs(v___x_934_);
lean_dec(v___x_934_);
v___x_936_ = lean_box(0);
v_sz_937_ = lean_array_size(v_args_935_);
v___x_938_ = ((size_t)0ULL);
lean_inc(v_a_748_);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_args_935_, v_sz_937_, v___x_938_, v___x_936_, v_a_748_, v_snd_933_);
lean_dec_ref(v_args_935_);
v_snd_940_ = lean_ctor_get(v___x_939_, 1);
lean_inc(v_snd_940_);
lean_dec_ref(v___x_939_);
v___x_941_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
v___x_942_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_941_, v_snd_940_);
v_snd_943_ = lean_ctor_get(v___x_942_, 1);
lean_inc(v_snd_943_);
lean_dec_ref(v___x_942_);
v___x_944_ = lean_unsigned_to_nat(3u);
v___x_945_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_944_);
v___x_946_ = lean_unsigned_to_nat(4u);
v_tk2_947_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_946_);
lean_dec(v_stx_747_);
v___x_967_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_945_);
v___x_968_ = l_Lean_Syntax_decodeStrLit(v___x_967_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v___x_969_; 
v___x_969_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_949_ = v___x_969_;
goto v___jp_948_;
}
else
{
lean_object* v_val_970_; 
v_val_970_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_val_970_);
lean_dec_ref(v___x_968_);
v___y_949_ = v_val_970_;
goto v___jp_948_;
}
v___jp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_snd_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v_snd_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v_snd_965_; lean_object* v___x_966_; 
v___x_950_ = lean_string_utf8_byte_size(v___y_949_);
lean_inc_ref(v___y_949_);
v___x_951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_951_, 0, v___y_949_);
lean_ctor_set(v___x_951_, 1, v___x_925_);
lean_ctor_set(v___x_951_, 2, v___x_950_);
v___x_952_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v___x_951_);
v___x_953_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63));
lean_inc(v_a_748_);
v___x_954_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(v_a_748_, v___y_949_, v___x_951_, v___x_950_, v___x_952_, v___x_953_);
lean_dec_ref(v___x_951_);
lean_dec_ref(v___y_949_);
v___x_955_ = lean_array_to_list(v___x_954_);
v___x_956_ = l_String_intercalate(v___x_941_, v___x_955_);
v___x_957_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_956_, v_snd_943_);
lean_dec_ref(v___x_956_);
v_snd_958_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_snd_958_);
lean_dec_ref(v___x_957_);
v___x_959_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___x_960_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_748_, v___x_959_);
v___x_961_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_960_, v_snd_958_);
lean_dec_ref(v___x_960_);
v_snd_962_ = lean_ctor_get(v___x_961_, 1);
lean_inc(v_snd_962_);
lean_dec_ref(v___x_961_);
v___x_963_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_947_);
v___x_964_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_963_, v_snd_962_);
lean_dec_ref(v___x_963_);
v_snd_965_ = lean_ctor_get(v___x_964_, 1);
lean_inc(v_snd_965_);
lean_dec_ref(v___x_964_);
v___x_966_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_965_);
return v___x_966_;
}
}
}
}
else
{
lean_object* v___x_971_; lean_object* v_snd_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v_snd_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v_blks_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
lean_inc(v_a_748_);
v___x_971_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_748_, v_a_749_);
v_snd_972_ = lean_ctor_get(v___x_971_, 1);
lean_inc(v_snd_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64));
v___x_974_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_973_, v_snd_972_);
v_snd_975_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_snd_975_);
lean_dec_ref(v___x_974_);
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_977_);
lean_dec(v_stx_747_);
v_blks_979_ = l_Lean_Syntax_getArgs(v___x_978_);
lean_dec(v___x_978_);
v___x_980_ = lean_array_get_size(v_blks_979_);
v___x_981_ = lean_nat_dec_lt(v___x_976_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
lean_dec_ref(v_blks_979_);
lean_dec(v_a_748_);
v___x_982_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_975_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_983_ = lean_unsigned_to_nat(2u);
v___x_984_ = lean_nat_add(v_a_748_, v___x_983_);
lean_dec(v_a_748_);
v___x_985_ = lean_box(0);
v___x_986_ = lean_nat_dec_le(v___x_980_, v___x_980_);
if (v___x_986_ == 0)
{
if (v___x_981_ == 0)
{
lean_object* v___x_987_; 
lean_dec(v___x_984_);
lean_dec_ref(v_blks_979_);
v___x_987_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_975_);
return v___x_987_;
}
else
{
size_t v___x_988_; size_t v___x_989_; lean_object* v___x_990_; 
v___x_988_ = ((size_t)0ULL);
v___x_989_ = lean_usize_of_nat(v___x_980_);
v___x_990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_979_, v___x_988_, v___x_989_, v___x_985_, v___x_984_, v_snd_975_);
lean_dec_ref(v_blks_979_);
v___y_770_ = v___x_990_;
goto v___jp_769_;
}
}
else
{
size_t v___x_991_; size_t v___x_992_; lean_object* v___x_993_; 
v___x_991_ = ((size_t)0ULL);
v___x_992_ = lean_usize_of_nat(v___x_980_);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_979_, v___x_991_, v___x_992_, v___x_985_, v___x_984_, v_snd_975_);
lean_dec_ref(v_blks_979_);
v___y_770_ = v___x_993_;
goto v___jp_769_;
}
}
}
}
else
{
lean_object* v___x_994_; lean_object* v_snd_995_; lean_object* v___x_996_; lean_object* v_n_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_items_1000_; lean_object* v___x_1001_; size_t v_sz_1002_; size_t v___x_1003_; lean_object* v___x_1004_; lean_object* v_snd_1005_; lean_object* v___x_1006_; 
lean_inc(v_a_748_);
v___x_994_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_748_, v_a_749_);
v_snd_995_ = lean_ctor_get(v___x_994_, 1);
lean_inc(v_snd_995_);
lean_dec_ref(v___x_994_);
v___x_996_ = lean_unsigned_to_nat(1u);
v_n_997_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_996_);
v___x_998_ = lean_unsigned_to_nat(4u);
v___x_999_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_998_);
lean_dec(v_stx_747_);
v_items_1000_ = l_Lean_Syntax_getArgs(v___x_999_);
lean_dec(v___x_999_);
v___x_1001_ = l_Lean_TSyntax_getNat(v_n_997_);
lean_dec(v_n_997_);
v_sz_1002_ = lean_array_size(v_items_1000_);
v___x_1003_ = ((size_t)0ULL);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v_items_1000_, v_sz_1002_, v___x_1003_, v___x_1001_, v_a_748_, v_snd_995_);
lean_dec(v_a_748_);
lean_dec_ref(v_items_1000_);
v_snd_1005_ = lean_ctor_get(v___x_1004_, 1);
lean_inc(v_snd_1005_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1005_);
return v___x_1006_;
}
}
else
{
lean_object* v___x_1007_; lean_object* v_snd_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v_items_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
lean_inc(v_a_748_);
v___x_1007_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_748_, v_a_749_);
v_snd_1008_ = lean_ctor_get(v___x_1007_, 1);
lean_inc(v_snd_1008_);
lean_dec_ref(v___x_1007_);
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = lean_unsigned_to_nat(1u);
v___x_1011_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1010_);
lean_dec(v_stx_747_);
v_items_1012_ = l_Lean_Syntax_getArgs(v___x_1011_);
lean_dec(v___x_1011_);
v___x_1013_ = lean_array_get_size(v_items_1012_);
v___x_1014_ = lean_nat_dec_lt(v___x_1009_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
lean_dec_ref(v_items_1012_);
lean_dec(v_a_748_);
v___x_1015_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1008_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_nat_dec_le(v___x_1013_, v___x_1013_);
if (v___x_1017_ == 0)
{
if (v___x_1014_ == 0)
{
lean_object* v___x_1018_; 
lean_dec_ref(v_items_1012_);
lean_dec(v_a_748_);
v___x_1018_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1008_);
return v___x_1018_;
}
else
{
size_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = ((size_t)0ULL);
v___x_1020_ = lean_usize_of_nat(v___x_1013_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v_items_1012_, v___x_1019_, v___x_1020_, v___x_1016_, v_a_748_, v_snd_1008_);
lean_dec(v_a_748_);
lean_dec_ref(v_items_1012_);
v___y_766_ = v___x_1021_;
goto v___jp_765_;
}
}
else
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = lean_usize_of_nat(v___x_1013_);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v_items_1012_, v___x_1022_, v___x_1023_, v___x_1016_, v_a_748_, v_snd_1008_);
lean_dec(v_a_748_);
lean_dec_ref(v_items_1012_);
v___y_766_ = v___x_1024_;
goto v___jp_765_;
}
}
}
}
else
{
lean_object* v___x_1025_; lean_object* v_snd_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v_inl_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
lean_inc(v_a_748_);
v___x_1025_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_748_, v_a_749_);
v_snd_1026_ = lean_ctor_get(v___x_1025_, 1);
lean_inc(v_snd_1026_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = lean_unsigned_to_nat(1u);
v___x_1029_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1028_);
lean_dec(v_stx_747_);
v_inl_1030_ = l_Lean_Syntax_getArgs(v___x_1029_);
lean_dec(v___x_1029_);
v___x_1031_ = lean_array_get_size(v_inl_1030_);
v___x_1032_ = lean_nat_dec_lt(v___x_1027_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
lean_dec_ref(v_inl_1030_);
lean_dec(v_a_748_);
v___x_1033_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1026_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_nat_dec_le(v___x_1031_, v___x_1031_);
if (v___x_1035_ == 0)
{
if (v___x_1032_ == 0)
{
lean_object* v___x_1036_; 
lean_dec_ref(v_inl_1030_);
lean_dec(v_a_748_);
v___x_1036_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1026_);
return v___x_1036_;
}
else
{
size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = ((size_t)0ULL);
v___x_1038_ = lean_usize_of_nat(v___x_1031_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1030_, v___x_1037_, v___x_1038_, v___x_1034_, v_a_748_, v_snd_1026_);
lean_dec_ref(v_inl_1030_);
v___y_762_ = v___x_1039_;
goto v___jp_761_;
}
}
else
{
size_t v___x_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = ((size_t)0ULL);
v___x_1041_ = lean_usize_of_nat(v___x_1031_);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1030_, v___x_1040_, v___x_1041_, v___x_1034_, v_a_748_, v_snd_1026_);
lean_dec_ref(v_inl_1030_);
v___y_762_ = v___x_1042_;
goto v___jp_761_;
}
}
}
}
else
{
lean_object* v___x_1043_; lean_object* v_n_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_snd_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v_inl_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1043_ = lean_unsigned_to_nat(1u);
v_n_1044_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1043_);
v___x_1045_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65));
v___x_1046_ = l_Lean_TSyntax_getNat(v_n_1044_);
lean_dec(v_n_1044_);
v___x_1047_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___x_1046_, v___x_1045_);
v___x_1048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0));
v___x_1049_ = lean_string_append(v___x_1047_, v___x_1048_);
v___x_1050_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1049_, v_a_749_);
lean_dec_ref(v___x_1049_);
v_snd_1051_ = lean_ctor_get(v___x_1050_, 1);
lean_inc(v_snd_1051_);
lean_dec_ref(v___x_1050_);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = lean_unsigned_to_nat(4u);
v___x_1054_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1053_);
lean_dec(v_stx_747_);
v_inl_1055_ = l_Lean_Syntax_getArgs(v___x_1054_);
lean_dec(v___x_1054_);
v___x_1056_ = lean_array_get_size(v_inl_1055_);
v___x_1057_ = lean_nat_dec_lt(v___x_1052_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; 
lean_dec_ref(v_inl_1055_);
lean_dec(v_a_748_);
v___x_1058_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1051_);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_nat_dec_le(v___x_1056_, v___x_1056_);
if (v___x_1060_ == 0)
{
if (v___x_1057_ == 0)
{
lean_object* v___x_1061_; 
lean_dec_ref(v_inl_1055_);
lean_dec(v_a_748_);
v___x_1061_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_1051_);
return v___x_1061_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = lean_usize_of_nat(v___x_1056_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1055_, v___x_1062_, v___x_1063_, v___x_1059_, v_a_748_, v_snd_1051_);
lean_dec_ref(v_inl_1055_);
v___y_758_ = v___x_1064_;
goto v___jp_757_;
}
}
else
{
size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_usize_of_nat(v___x_1056_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1055_, v___x_1065_, v___x_1066_, v___x_1059_, v_a_748_, v_snd_1051_);
lean_dec_ref(v_inl_1055_);
v___y_758_ = v___x_1067_;
goto v___jp_757_;
}
}
}
}
else
{
lean_object* v___x_1068_; lean_object* v_tk1_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_snd_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_tk2_1076_; lean_object* v___y_1078_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v_a_748_);
v___x_1068_ = lean_unsigned_to_nat(0u);
v_tk1_1069_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1068_);
v___x_1070_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1069_);
v___x_1071_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1070_, v_a_749_);
lean_dec_ref(v___x_1070_);
v_snd_1072_ = lean_ctor_get(v___x_1071_, 1);
lean_inc(v_snd_1072_);
lean_dec_ref(v___x_1071_);
v___x_1073_ = lean_unsigned_to_nat(1u);
v___x_1074_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1073_);
v___x_1075_ = lean_unsigned_to_nat(2u);
v_tk2_1076_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1075_);
lean_dec(v_stx_747_);
v___x_1083_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1074_);
v___x_1084_ = l_Lean_Syntax_decodeStrLit(v___x_1083_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v___x_1085_; 
v___x_1085_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1078_ = v___x_1085_;
goto v___jp_1077_;
}
else
{
lean_object* v_val_1086_; 
v_val_1086_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_val_1086_);
lean_dec_ref(v___x_1084_);
v___y_1078_ = v_val_1086_;
goto v___jp_1077_;
}
v___jp_1077_:
{
lean_object* v___x_1079_; lean_object* v_snd_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1079_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1078_, v_snd_1072_);
lean_dec_ref(v___y_1078_);
v_snd_1080_ = lean_ctor_get(v___x_1079_, 1);
lean_inc(v_snd_1080_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1076_);
v___x_1082_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1081_, v_snd_1080_);
lean_dec_ref(v___x_1081_);
return v___x_1082_;
}
}
}
else
{
lean_object* v___x_1087_; lean_object* v_tk1_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_snd_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_tk2_1095_; lean_object* v___y_1097_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec(v_a_748_);
v___x_1087_ = lean_unsigned_to_nat(0u);
v_tk1_1088_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1087_);
v___x_1089_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1088_);
v___x_1090_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1089_, v_a_749_);
lean_dec_ref(v___x_1089_);
v_snd_1091_ = lean_ctor_get(v___x_1090_, 1);
lean_inc(v_snd_1091_);
lean_dec_ref(v___x_1090_);
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1092_);
v___x_1094_ = lean_unsigned_to_nat(2u);
v_tk2_1095_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1094_);
lean_dec(v_stx_747_);
v___x_1102_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1093_);
v___x_1103_ = l_Lean_Syntax_decodeStrLit(v___x_1102_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1097_ = v___x_1104_;
goto v___jp_1096_;
}
else
{
lean_object* v_val_1105_; 
v_val_1105_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_val_1105_);
lean_dec_ref(v___x_1103_);
v___y_1097_ = v_val_1105_;
goto v___jp_1096_;
}
v___jp_1096_:
{
lean_object* v___x_1098_; lean_object* v_snd_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1098_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1097_, v_snd_1091_);
lean_dec_ref(v___y_1097_);
v_snd_1099_ = lean_ctor_get(v___x_1098_, 1);
lean_inc(v_snd_1099_);
lean_dec_ref(v___x_1098_);
v___x_1100_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1095_);
v___x_1101_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1100_, v_snd_1099_);
lean_dec_ref(v___x_1100_);
return v___x_1101_;
}
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
lean_dec(v_a_748_);
v___x_1106_ = lean_unsigned_to_nat(1u);
v___x_1107_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1106_);
lean_inc(v___x_1107_);
v___x_1108_ = l_Lean_Syntax_isOfKind(v___x_1107_, v___x_804_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec(v___x_1107_);
v___x_1109_ = lean_box(0);
v___x_1110_ = l_Lean_Syntax_formatStx(v_stx_747_, v___x_1109_, v___x_1108_);
v___x_1111_ = l_Std_Format_defWidth;
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = l_Std_Format_pretty(v___x_1110_, v___x_1111_, v___x_1112_, v___x_1112_);
v___x_1114_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1113_, v_a_749_);
lean_dec_ref(v___x_1113_);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; lean_object* v_tk1_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v_snd_1119_; lean_object* v_tk2_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_snd_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_tk3_1126_; lean_object* v___y_1128_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1115_ = lean_unsigned_to_nat(0u);
v_tk1_1116_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1115_);
lean_dec(v_stx_747_);
v___x_1117_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1116_);
v___x_1118_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1117_, v_a_749_);
lean_dec_ref(v___x_1117_);
v_snd_1119_ = lean_ctor_get(v___x_1118_, 1);
lean_inc(v_snd_1119_);
lean_dec_ref(v___x_1118_);
v_tk2_1120_ = l_Lean_Syntax_getArg(v___x_1107_, v___x_1115_);
v___x_1121_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1120_);
v___x_1122_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1121_, v_snd_1119_);
lean_dec_ref(v___x_1121_);
v_snd_1123_ = lean_ctor_get(v___x_1122_, 1);
lean_inc(v_snd_1123_);
lean_dec_ref(v___x_1122_);
v___x_1124_ = l_Lean_Syntax_getArg(v___x_1107_, v___x_1106_);
v___x_1125_ = lean_unsigned_to_nat(2u);
v_tk3_1126_ = l_Lean_Syntax_getArg(v___x_1107_, v___x_1125_);
lean_dec(v___x_1107_);
v___x_1133_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1124_);
v___x_1134_ = l_Lean_Syntax_decodeStrLit(v___x_1133_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v___x_1135_; 
v___x_1135_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1128_ = v___x_1135_;
goto v___jp_1127_;
}
else
{
lean_object* v_val_1136_; 
v_val_1136_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_val_1136_);
lean_dec_ref(v___x_1134_);
v___y_1128_ = v_val_1136_;
goto v___jp_1127_;
}
v___jp_1127_:
{
lean_object* v___x_1129_; lean_object* v_snd_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1129_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1128_, v_snd_1123_);
lean_dec_ref(v___y_1128_);
v_snd_1130_ = lean_ctor_get(v___x_1129_, 1);
lean_inc(v_snd_1130_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk3_1126_);
v___x_1132_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1131_, v_snd_1130_);
lean_dec_ref(v___x_1131_);
return v___x_1132_;
}
}
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
lean_dec(v_a_748_);
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1137_);
lean_inc(v___x_1138_);
v___x_1139_ = l_Lean_Syntax_isOfKind(v___x_1138_, v___x_804_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec(v___x_1138_);
v___x_1140_ = lean_box(0);
v___x_1141_ = l_Lean_Syntax_formatStx(v_stx_747_, v___x_1140_, v___x_1139_);
v___x_1142_ = l_Std_Format_defWidth;
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = l_Std_Format_pretty(v___x_1141_, v___x_1142_, v___x_1143_, v___x_1143_);
v___x_1145_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1144_, v_a_749_);
lean_dec_ref(v___x_1144_);
return v___x_1145_;
}
else
{
lean_object* v___x_1146_; lean_object* v_tk1_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_snd_1150_; lean_object* v_tk2_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_snd_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v_tk3_1157_; lean_object* v___y_1159_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
v_tk1_1147_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1146_);
lean_dec(v_stx_747_);
v___x_1148_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1147_);
v___x_1149_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1148_, v_a_749_);
lean_dec_ref(v___x_1148_);
v_snd_1150_ = lean_ctor_get(v___x_1149_, 1);
lean_inc(v_snd_1150_);
lean_dec_ref(v___x_1149_);
v_tk2_1151_ = l_Lean_Syntax_getArg(v___x_1138_, v___x_1146_);
v___x_1152_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1151_);
v___x_1153_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1152_, v_snd_1150_);
lean_dec_ref(v___x_1152_);
v_snd_1154_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_snd_1154_);
lean_dec_ref(v___x_1153_);
v___x_1155_ = l_Lean_Syntax_getArg(v___x_1138_, v___x_1137_);
v___x_1156_ = lean_unsigned_to_nat(2u);
v_tk3_1157_ = l_Lean_Syntax_getArg(v___x_1138_, v___x_1156_);
lean_dec(v___x_1138_);
v___x_1164_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1155_);
v___x_1165_ = l_Lean_Syntax_decodeStrLit(v___x_1164_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v___x_1166_; 
v___x_1166_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1159_ = v___x_1166_;
goto v___jp_1158_;
}
else
{
lean_object* v_val_1167_; 
v_val_1167_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_val_1167_);
lean_dec_ref(v___x_1165_);
v___y_1159_ = v_val_1167_;
goto v___jp_1158_;
}
v___jp_1158_:
{
lean_object* v___x_1160_; lean_object* v_snd_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1160_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1159_, v_snd_1154_);
lean_dec_ref(v___y_1159_);
v_snd_1161_ = lean_ctor_get(v___x_1160_, 1);
lean_inc(v_snd_1161_);
lean_dec_ref(v___x_1160_);
v___x_1162_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk3_1157_);
v___x_1163_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1162_, v_snd_1161_);
lean_dec_ref(v___x_1162_);
return v___x_1163_;
}
}
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec(v_a_748_);
v___x_1168_ = lean_unsigned_to_nat(1u);
v___x_1169_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1168_);
lean_dec(v_stx_747_);
v___x_1170_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1169_);
v___x_1171_ = l_Lean_Syntax_decodeStrLit(v___x_1170_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___x_1173_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1172_, v_a_749_);
return v___x_1173_;
}
else
{
lean_object* v_val_1174_; lean_object* v___x_1175_; 
v_val_1174_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_val_1174_);
lean_dec_ref(v___x_1171_);
v___x_1175_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v_val_1174_, v_a_749_);
lean_dec(v_val_1174_);
return v___x_1175_;
}
}
}
else
{
lean_object* v___x_1176_; lean_object* v_tk1_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_snd_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_tk2_1184_; lean_object* v___y_1186_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec(v_a_748_);
v___x_1176_ = lean_unsigned_to_nat(0u);
v_tk1_1177_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1176_);
v___x_1178_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1177_);
v___x_1179_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1178_, v_a_749_);
lean_dec_ref(v___x_1178_);
v_snd_1180_ = lean_ctor_get(v___x_1179_, 1);
lean_inc(v_snd_1180_);
lean_dec_ref(v___x_1179_);
v___x_1181_ = lean_unsigned_to_nat(1u);
v___x_1182_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1181_);
v___x_1183_ = lean_unsigned_to_nat(2u);
v_tk2_1184_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1183_);
lean_dec(v_stx_747_);
v___x_1191_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1182_);
v___x_1192_ = l_Lean_Syntax_decodeStrLit(v___x_1191_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v___x_1193_; 
v___x_1193_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1186_ = v___x_1193_;
goto v___jp_1185_;
}
else
{
lean_object* v_val_1194_; 
v_val_1194_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_val_1194_);
lean_dec_ref(v___x_1192_);
v___y_1186_ = v_val_1194_;
goto v___jp_1185_;
}
v___jp_1185_:
{
lean_object* v___x_1187_; lean_object* v_snd_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1187_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1186_, v_snd_1180_);
lean_dec_ref(v___y_1186_);
v_snd_1188_ = lean_ctor_get(v___x_1187_, 1);
lean_inc(v_snd_1188_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1184_);
v___x_1190_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1189_, v_snd_1188_);
lean_dec_ref(v___x_1189_);
return v___x_1190_;
}
}
}
else
{
lean_object* v___x_1195_; lean_object* v_tk1_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v_snd_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v_tk2_1203_; lean_object* v___y_1205_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec(v_a_748_);
v___x_1195_ = lean_unsigned_to_nat(0u);
v_tk1_1196_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1195_);
v___x_1197_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1196_);
v___x_1198_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1197_, v_a_749_);
lean_dec_ref(v___x_1197_);
v_snd_1199_ = lean_ctor_get(v___x_1198_, 1);
lean_inc(v_snd_1199_);
lean_dec_ref(v___x_1198_);
v___x_1200_ = lean_unsigned_to_nat(1u);
v___x_1201_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1200_);
v___x_1202_ = lean_unsigned_to_nat(2u);
v_tk2_1203_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1202_);
lean_dec(v_stx_747_);
v___x_1210_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1201_);
v___x_1211_ = l_Lean_Syntax_decodeStrLit(v___x_1210_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v___x_1212_; 
v___x_1212_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1205_ = v___x_1212_;
goto v___jp_1204_;
}
else
{
lean_object* v_val_1213_; 
v_val_1213_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_val_1213_);
lean_dec_ref(v___x_1211_);
v___y_1205_ = v_val_1213_;
goto v___jp_1204_;
}
v___jp_1204_:
{
lean_object* v___x_1206_; lean_object* v_snd_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1206_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1205_, v_snd_1199_);
lean_dec_ref(v___y_1205_);
v_snd_1207_ = lean_ctor_get(v___x_1206_, 1);
lean_inc(v_snd_1207_);
lean_dec_ref(v___x_1206_);
v___x_1208_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1203_);
v___x_1209_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1208_, v_snd_1207_);
lean_dec_ref(v___x_1208_);
return v___x_1209_;
}
}
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_snd_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_snd_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_args_1224_; lean_object* v___x_1225_; size_t v_sz_1226_; size_t v___x_1227_; lean_object* v___x_1228_; lean_object* v_snd_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v_snd_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_inls_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1214_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61));
v___x_1215_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1214_, v_a_749_);
v_snd_1216_ = lean_ctor_get(v___x_1215_, 1);
lean_inc(v_snd_1216_);
lean_dec_ref(v___x_1215_);
v___x_1217_ = lean_unsigned_to_nat(1u);
v___x_1218_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1217_);
v___x_1219_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_1218_);
v___x_1220_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1219_, v_snd_1216_);
lean_dec_ref(v___x_1219_);
v_snd_1221_ = lean_ctor_get(v___x_1220_, 1);
lean_inc(v_snd_1221_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = lean_unsigned_to_nat(2u);
v___x_1223_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1222_);
v_args_1224_ = l_Lean_Syntax_getArgs(v___x_1223_);
lean_dec(v___x_1223_);
v___x_1225_ = lean_box(0);
v_sz_1226_ = lean_array_size(v_args_1224_);
v___x_1227_ = ((size_t)0ULL);
lean_inc(v_a_748_);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_args_1224_, v_sz_1226_, v___x_1227_, v___x_1225_, v_a_748_, v_snd_1221_);
lean_dec_ref(v_args_1224_);
v_snd_1229_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_snd_1229_);
lean_dec_ref(v___x_1228_);
v___x_1230_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66));
v___x_1231_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1230_, v_snd_1229_);
v_snd_1232_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_snd_1232_);
lean_dec_ref(v___x_1231_);
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = lean_unsigned_to_nat(5u);
v___x_1235_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1234_);
lean_dec(v_stx_747_);
v_inls_1236_ = l_Lean_Syntax_getArgs(v___x_1235_);
lean_dec(v___x_1235_);
v___x_1237_ = lean_array_get_size(v_inls_1236_);
v___x_1238_ = lean_nat_dec_lt(v___x_1233_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_dec_ref(v_inls_1236_);
lean_dec(v_a_748_);
v_snd_751_ = v_snd_1232_;
goto v___jp_750_;
}
else
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_nat_dec_le(v___x_1237_, v___x_1237_);
if (v___x_1239_ == 0)
{
if (v___x_1238_ == 0)
{
lean_dec_ref(v_inls_1236_);
lean_dec(v_a_748_);
v_snd_751_ = v_snd_1232_;
goto v___jp_750_;
}
else
{
size_t v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_usize_of_nat(v___x_1237_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inls_1236_, v___x_1227_, v___x_1240_, v___x_1225_, v_a_748_, v_snd_1232_);
lean_dec_ref(v_inls_1236_);
v___y_755_ = v___x_1241_;
goto v___jp_754_;
}
}
else
{
size_t v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_usize_of_nat(v___x_1237_);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inls_1236_, v___x_1227_, v___x_1242_, v___x_1225_, v_a_748_, v_snd_1232_);
lean_dec_ref(v_inls_1236_);
v___y_755_ = v___x_1243_;
goto v___jp_754_;
}
}
}
}
else
{
lean_object* v___x_1244_; lean_object* v_tk1_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v_snd_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_tk2_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___y_1256_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1244_ = lean_unsigned_to_nat(0u);
v_tk1_1245_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1244_);
v___x_1246_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1245_);
v___x_1247_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1246_, v_a_749_);
lean_dec_ref(v___x_1246_);
v_snd_1248_ = lean_ctor_get(v___x_1247_, 1);
lean_inc(v_snd_1248_);
lean_dec_ref(v___x_1247_);
v___x_1249_ = lean_unsigned_to_nat(1u);
v___x_1250_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1249_);
v___x_1251_ = lean_unsigned_to_nat(2u);
v_tk2_1252_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1251_);
v___x_1253_ = lean_unsigned_to_nat(3u);
v___x_1254_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1253_);
lean_dec(v_stx_747_);
v___x_1263_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1250_);
v___x_1264_ = l_Lean_Syntax_decodeStrLit(v___x_1263_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v___x_1265_; 
v___x_1265_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___y_1256_ = v___x_1265_;
goto v___jp_1255_;
}
else
{
lean_object* v_val_1266_; 
v_val_1266_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_val_1266_);
lean_dec_ref(v___x_1264_);
v___y_1256_ = v_val_1266_;
goto v___jp_1255_;
}
v___jp_1255_:
{
lean_object* v___x_1257_; lean_object* v_snd_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v_snd_1261_; 
v___x_1257_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_1256_, v_snd_1248_);
lean_dec_ref(v___y_1256_);
v_snd_1258_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_snd_1258_);
lean_dec_ref(v___x_1257_);
v___x_1259_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1252_);
v___x_1260_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1259_, v_snd_1258_);
lean_dec_ref(v___x_1259_);
v_snd_1261_ = lean_ctor_get(v___x_1260_, 1);
lean_inc(v_snd_1261_);
lean_dec_ref(v___x_1260_);
v_stx_747_ = v___x_1254_;
v_a_749_ = v_snd_1261_;
goto _start;
}
}
}
else
{
lean_object* v___x_1267_; lean_object* v_tk1_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v_snd_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v_tk2_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v_snd_1279_; lean_object* v___y_1285_; lean_object* v_inl_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1267_ = lean_unsigned_to_nat(0u);
v_tk1_1268_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1267_);
v___x_1269_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1268_);
v___x_1270_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1269_, v_a_749_);
lean_dec_ref(v___x_1269_);
v_snd_1271_ = lean_ctor_get(v___x_1270_, 1);
lean_inc(v_snd_1271_);
lean_dec_ref(v___x_1270_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1272_);
v___x_1274_ = lean_unsigned_to_nat(2u);
v_tk2_1275_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1274_);
v___x_1276_ = lean_unsigned_to_nat(3u);
v___x_1277_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1276_);
lean_dec(v_stx_747_);
v_inl_1287_ = l_Lean_Syntax_getArgs(v___x_1273_);
lean_dec(v___x_1273_);
v___x_1288_ = lean_array_get_size(v_inl_1287_);
v___x_1289_ = lean_nat_dec_lt(v___x_1267_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_dec_ref(v_inl_1287_);
v_snd_1279_ = v_snd_1271_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = lean_box(0);
v___x_1291_ = lean_nat_dec_le(v___x_1288_, v___x_1288_);
if (v___x_1291_ == 0)
{
if (v___x_1289_ == 0)
{
lean_dec_ref(v_inl_1287_);
v_snd_1279_ = v_snd_1271_;
goto v___jp_1278_;
}
else
{
size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = ((size_t)0ULL);
v___x_1293_ = lean_usize_of_nat(v___x_1288_);
lean_inc(v_a_748_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1287_, v___x_1292_, v___x_1293_, v___x_1290_, v_a_748_, v_snd_1271_);
lean_dec_ref(v_inl_1287_);
v___y_1285_ = v___x_1294_;
goto v___jp_1284_;
}
}
else
{
size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
v___x_1295_ = ((size_t)0ULL);
v___x_1296_ = lean_usize_of_nat(v___x_1288_);
lean_inc(v_a_748_);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1287_, v___x_1295_, v___x_1296_, v___x_1290_, v_a_748_, v_snd_1271_);
lean_dec_ref(v_inl_1287_);
v___y_1285_ = v___x_1297_;
goto v___jp_1284_;
}
}
v___jp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v_snd_1282_; 
v___x_1280_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1275_);
v___x_1281_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1280_, v_snd_1279_);
lean_dec_ref(v___x_1280_);
v_snd_1282_ = lean_ctor_get(v___x_1281_, 1);
lean_inc(v_snd_1282_);
lean_dec_ref(v___x_1281_);
v_stx_747_ = v___x_1277_;
v_a_749_ = v_snd_1282_;
goto _start;
}
v___jp_1284_:
{
lean_object* v_snd_1286_; 
v_snd_1286_ = lean_ctor_get(v___y_1285_, 1);
lean_inc(v_snd_1286_);
lean_dec_ref(v___y_1285_);
v_snd_1279_ = v_snd_1286_;
goto v___jp_1278_;
}
}
}
else
{
lean_object* v___x_1298_; lean_object* v_tk1_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_snd_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v_tk2_1306_; lean_object* v_snd_1308_; lean_object* v___y_1312_; lean_object* v_inl_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v_tk1_1299_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1298_);
v___x_1300_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1299_);
v___x_1301_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1300_, v_a_749_);
lean_dec_ref(v___x_1300_);
v_snd_1302_ = lean_ctor_get(v___x_1301_, 1);
lean_inc(v_snd_1302_);
lean_dec_ref(v___x_1301_);
v___x_1303_ = lean_unsigned_to_nat(1u);
v___x_1304_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1303_);
v___x_1305_ = lean_unsigned_to_nat(2u);
v_tk2_1306_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1305_);
lean_dec(v_stx_747_);
v_inl_1314_ = l_Lean_Syntax_getArgs(v___x_1304_);
lean_dec(v___x_1304_);
v___x_1315_ = lean_array_get_size(v_inl_1314_);
v___x_1316_ = lean_nat_dec_lt(v___x_1298_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_dec_ref(v_inl_1314_);
lean_dec(v_a_748_);
v_snd_1308_ = v_snd_1302_;
goto v___jp_1307_;
}
else
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = lean_box(0);
v___x_1318_ = lean_nat_dec_le(v___x_1315_, v___x_1315_);
if (v___x_1318_ == 0)
{
if (v___x_1316_ == 0)
{
lean_dec_ref(v_inl_1314_);
lean_dec(v_a_748_);
v_snd_1308_ = v_snd_1302_;
goto v___jp_1307_;
}
else
{
size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = lean_usize_of_nat(v___x_1315_);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1314_, v___x_1319_, v___x_1320_, v___x_1317_, v_a_748_, v_snd_1302_);
lean_dec_ref(v_inl_1314_);
v___y_1312_ = v___x_1321_;
goto v___jp_1311_;
}
}
else
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = lean_usize_of_nat(v___x_1315_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1314_, v___x_1322_, v___x_1323_, v___x_1317_, v_a_748_, v_snd_1302_);
lean_dec_ref(v_inl_1314_);
v___y_1312_ = v___x_1324_;
goto v___jp_1311_;
}
}
v___jp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1306_);
v___x_1310_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1309_, v_snd_1308_);
lean_dec_ref(v___x_1309_);
return v___x_1310_;
}
v___jp_1311_:
{
lean_object* v_snd_1313_; 
v_snd_1313_ = lean_ctor_get(v___y_1312_, 1);
lean_inc(v_snd_1313_);
lean_dec_ref(v___y_1312_);
v_snd_1308_ = v_snd_1313_;
goto v___jp_1307_;
}
}
}
else
{
lean_object* v___x_1325_; lean_object* v_tk1_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v_snd_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_tk2_1333_; lean_object* v_snd_1335_; lean_object* v___y_1339_; lean_object* v_inl_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1325_ = lean_unsigned_to_nat(0u);
v_tk1_1326_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1325_);
v___x_1327_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_1326_);
v___x_1328_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1327_, v_a_749_);
lean_dec_ref(v___x_1327_);
v_snd_1329_ = lean_ctor_get(v___x_1328_, 1);
lean_inc(v_snd_1329_);
lean_dec_ref(v___x_1328_);
v___x_1330_ = lean_unsigned_to_nat(1u);
v___x_1331_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1330_);
v___x_1332_ = lean_unsigned_to_nat(2u);
v_tk2_1333_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1332_);
lean_dec(v_stx_747_);
v_inl_1341_ = l_Lean_Syntax_getArgs(v___x_1331_);
lean_dec(v___x_1331_);
v___x_1342_ = lean_array_get_size(v_inl_1341_);
v___x_1343_ = lean_nat_dec_lt(v___x_1325_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_dec_ref(v_inl_1341_);
lean_dec(v_a_748_);
v_snd_1335_ = v_snd_1329_;
goto v___jp_1334_;
}
else
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1344_ = lean_box(0);
v___x_1345_ = lean_nat_dec_le(v___x_1342_, v___x_1342_);
if (v___x_1345_ == 0)
{
if (v___x_1343_ == 0)
{
lean_dec_ref(v_inl_1341_);
lean_dec(v_a_748_);
v_snd_1335_ = v_snd_1329_;
goto v___jp_1334_;
}
else
{
size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = ((size_t)0ULL);
v___x_1347_ = lean_usize_of_nat(v___x_1342_);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1341_, v___x_1346_, v___x_1347_, v___x_1344_, v_a_748_, v_snd_1329_);
lean_dec_ref(v_inl_1341_);
v___y_1339_ = v___x_1348_;
goto v___jp_1338_;
}
}
else
{
size_t v___x_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = ((size_t)0ULL);
v___x_1350_ = lean_usize_of_nat(v___x_1342_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_1341_, v___x_1349_, v___x_1350_, v___x_1344_, v_a_748_, v_snd_1329_);
lean_dec_ref(v_inl_1341_);
v___y_1339_ = v___x_1351_;
goto v___jp_1338_;
}
}
v___jp_1334_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_1333_);
v___x_1337_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1336_, v_snd_1335_);
lean_dec_ref(v___x_1336_);
return v___x_1337_;
}
v___jp_1338_:
{
lean_object* v_snd_1340_; 
v_snd_1340_ = lean_ctor_get(v___y_1339_, 1);
lean_inc(v_snd_1340_);
lean_dec_ref(v___y_1339_);
v_snd_1335_ = v_snd_1340_;
goto v___jp_1334_;
}
}
}
else
{
lean_object* v___x_1352_; lean_object* v_s_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
lean_dec(v_a_748_);
v___x_1352_ = lean_unsigned_to_nat(0u);
v_s_1353_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1352_);
v___x_1354_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68));
lean_inc(v_s_1353_);
v___x_1355_ = l_Lean_Syntax_isOfKind(v_s_1353_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec(v_s_1353_);
v___x_1356_ = lean_box(0);
v___x_1357_ = l_Lean_Syntax_formatStx(v_stx_747_, v___x_1356_, v___x_1355_);
v___x_1358_ = l_Std_Format_defWidth;
v___x_1359_ = l_Std_Format_pretty(v___x_1357_, v___x_1358_, v___x_1352_, v___x_1352_);
v___x_1360_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1359_, v_a_749_);
lean_dec_ref(v___x_1359_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec(v_stx_747_);
v___x_1361_ = l_Lean_TSyntax_getString(v_s_1353_);
lean_dec(v_s_1353_);
v___x_1362_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1361_, v_a_749_);
lean_dec_ref(v___x_1361_);
return v___x_1362_;
}
}
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1363_);
lean_dec(v_stx_747_);
v_stx_747_ = v___x_1364_;
goto _start;
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
lean_dec(v_a_748_);
v___x_1366_ = lean_unsigned_to_nat(1u);
v___x_1367_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1366_);
v___x_1368_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70));
lean_inc(v___x_1367_);
v___x_1369_ = l_Lean_Syntax_isOfKind(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v___x_1371_ = l_Lean_Syntax_formatStx(v_stx_747_, v___x_1370_, v___x_1369_);
v___x_1372_ = l_Std_Format_defWidth;
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = l_Std_Format_pretty(v___x_1371_, v___x_1372_, v___x_1373_, v___x_1373_);
v___x_1375_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1374_, v_a_749_);
lean_dec_ref(v___x_1374_);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; lean_object* v_tk_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v_snd_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1376_ = lean_unsigned_to_nat(0u);
v_tk_1377_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1376_);
lean_dec(v_stx_747_);
v___x_1378_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk_1377_);
v___x_1379_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1378_, v_a_749_);
lean_dec_ref(v___x_1378_);
v_snd_1380_ = lean_ctor_get(v___x_1379_, 1);
lean_inc(v_snd_1380_);
lean_dec_ref(v___x_1379_);
v___x_1381_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_1367_);
v___x_1382_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1381_, v_snd_1380_);
lean_dec_ref(v___x_1381_);
return v___x_1382_;
}
}
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
lean_dec(v_a_748_);
v___x_1383_ = lean_unsigned_to_nat(1u);
v___x_1384_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1383_);
v___x_1385_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70));
lean_inc(v___x_1384_);
v___x_1386_ = l_Lean_Syntax_isOfKind(v___x_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v___x_1388_ = l_Lean_Syntax_formatStx(v_stx_747_, v___x_1387_, v___x_1386_);
v___x_1389_ = l_Std_Format_defWidth;
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = l_Std_Format_pretty(v___x_1388_, v___x_1389_, v___x_1390_, v___x_1390_);
v___x_1392_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1391_, v_a_749_);
lean_dec_ref(v___x_1391_);
return v___x_1392_;
}
else
{
lean_object* v___x_1393_; lean_object* v_tk_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_snd_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v_tk_1394_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1393_);
lean_dec(v_stx_747_);
v___x_1395_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk_1394_);
v___x_1396_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1395_, v_a_749_);
lean_dec_ref(v___x_1395_);
v_snd_1397_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_snd_1397_);
lean_dec_ref(v___x_1396_);
v___x_1398_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_1384_);
v___x_1399_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1398_, v_snd_1397_);
lean_dec_ref(v___x_1398_);
return v___x_1399_;
}
}
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1400_);
v___x_1402_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70));
lean_inc(v___x_1401_);
v___x_1403_ = l_Lean_Syntax_isOfKind(v___x_1401_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec(v___x_1401_);
lean_dec(v_a_748_);
v___x_1404_ = lean_box(0);
v___x_1405_ = l_Lean_Syntax_formatStx(v_stx_747_, v___x_1404_, v___x_1403_);
v___x_1406_ = l_Std_Format_defWidth;
v___x_1407_ = l_Std_Format_pretty(v___x_1405_, v___x_1406_, v___x_1400_, v___x_1400_);
v___x_1408_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1407_, v_a_749_);
lean_dec_ref(v___x_1407_);
return v___x_1408_;
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_snd_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v_snd_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_snd_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v_snd_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1409_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71));
v___x_1410_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1409_, v_a_749_);
v_snd_1411_ = lean_ctor_get(v___x_1410_, 1);
lean_inc(v_snd_1411_);
lean_dec_ref(v___x_1410_);
v___x_1412_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_1401_);
v___x_1413_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1412_, v_snd_1411_);
lean_dec_ref(v___x_1412_);
v_snd_1414_ = lean_ctor_get(v___x_1413_, 1);
lean_inc(v_snd_1414_);
lean_dec_ref(v___x_1413_);
v___x_1415_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72));
v___x_1416_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1415_, v_snd_1414_);
v_snd_1417_ = lean_ctor_get(v___x_1416_, 1);
lean_inc(v_snd_1417_);
lean_dec_ref(v___x_1416_);
v___x_1418_ = lean_unsigned_to_nat(2u);
v___x_1419_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1418_);
lean_dec(v_stx_747_);
v___x_1420_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_1419_, v_a_748_, v_snd_1417_);
v_snd_1421_ = lean_ctor_get(v___x_1420_, 1);
lean_inc(v_snd_1421_);
lean_dec_ref(v___x_1420_);
v___x_1422_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73));
v___x_1423_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1422_, v_snd_1421_);
return v___x_1423_;
}
}
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v_snd_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v_snd_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v_snd_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_snd_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1424_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71));
v___x_1425_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1424_, v_a_749_);
v_snd_1426_ = lean_ctor_get(v___x_1425_, 1);
lean_inc(v_snd_1426_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = lean_unsigned_to_nat(1u);
v___x_1428_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1427_);
v___x_1429_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_1428_);
v___x_1430_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1429_, v_snd_1426_);
lean_dec_ref(v___x_1429_);
v_snd_1431_ = lean_ctor_get(v___x_1430_, 1);
lean_inc(v_snd_1431_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72));
v___x_1433_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1432_, v_snd_1431_);
v_snd_1434_ = lean_ctor_get(v___x_1433_, 1);
lean_inc(v_snd_1434_);
lean_dec_ref(v___x_1433_);
v___x_1435_ = lean_unsigned_to_nat(3u);
v___x_1436_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1435_);
lean_dec(v_stx_747_);
v___x_1437_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_1436_, v_a_748_, v_snd_1434_);
v_snd_1438_ = lean_ctor_get(v___x_1437_, 1);
lean_inc(v_snd_1438_);
lean_dec_ref(v___x_1437_);
v___x_1439_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73));
v___x_1440_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1439_, v_snd_1438_);
return v___x_1440_;
}
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
lean_dec(v_a_748_);
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1441_);
v___x_1443_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70));
lean_inc(v___x_1442_);
v___x_1444_ = l_Lean_Syntax_isOfKind(v___x_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v___x_1446_ = l_Lean_Syntax_formatStx(v_stx_747_, v___x_1445_, v___x_1444_);
v___x_1447_ = l_Std_Format_defWidth;
v___x_1448_ = l_Std_Format_pretty(v___x_1446_, v___x_1447_, v___x_1441_, v___x_1441_);
v___x_1449_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1448_, v_a_749_);
lean_dec_ref(v___x_1448_);
return v___x_1449_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec(v_stx_747_);
v___x_1450_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_1442_);
v___x_1451_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1450_, v_a_749_);
lean_dec_ref(v___x_1450_);
return v___x_1451_;
}
}
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
lean_dec(v_a_748_);
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1452_);
v___x_1454_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75));
lean_inc(v___x_1453_);
v___x_1455_ = l_Lean_Syntax_isOfKind(v___x_1453_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v___x_1457_ = l_Lean_Syntax_formatStx(v_stx_747_, v___x_1456_, v___x_1455_);
v___x_1458_ = l_Std_Format_defWidth;
v___x_1459_ = l_Std_Format_pretty(v___x_1457_, v___x_1458_, v___x_1452_, v___x_1452_);
v___x_1460_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1459_, v_a_749_);
lean_dec_ref(v___x_1459_);
return v___x_1460_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec(v_stx_747_);
v___x_1461_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1453_);
v___x_1462_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1461_, v_a_749_);
lean_dec_ref(v___x_1461_);
return v___x_1462_;
}
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
lean_dec(v_a_748_);
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_1463_);
v___x_1465_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68));
lean_inc(v___x_1464_);
v___x_1466_ = l_Lean_Syntax_isOfKind(v___x_1464_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v___x_1468_ = l_Lean_Syntax_formatStx(v_stx_747_, v___x_1467_, v___x_1466_);
v___x_1469_ = l_Std_Format_defWidth;
v___x_1470_ = l_Std_Format_pretty(v___x_1468_, v___x_1469_, v___x_1463_, v___x_1463_);
v___x_1471_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1470_, v_a_749_);
lean_dec_ref(v___x_1470_);
return v___x_1471_;
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_stx_747_);
v___x_1472_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_1464_);
v___x_1473_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_1472_, v_a_749_);
lean_dec_ref(v___x_1472_);
return v___x_1473_;
}
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1474_ = l_Lean_Syntax_getArgs(v_stx_747_);
lean_dec(v_stx_747_);
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = lean_array_get_size(v___x_1474_);
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_nat_dec_lt(v___x_1475_, v___x_1476_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; 
lean_dec_ref(v___x_1474_);
lean_dec(v_a_748_);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v_a_749_);
return v___x_1479_;
}
else
{
uint8_t v___x_1480_; 
v___x_1480_ = lean_nat_dec_le(v___x_1476_, v___x_1476_);
if (v___x_1480_ == 0)
{
if (v___x_1478_ == 0)
{
lean_object* v___x_1481_; 
lean_dec_ref(v___x_1474_);
lean_dec(v_a_748_);
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1477_);
lean_ctor_set(v___x_1481_, 1, v_a_749_);
return v___x_1481_;
}
else
{
size_t v___x_1482_; size_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = ((size_t)0ULL);
v___x_1483_ = lean_usize_of_nat(v___x_1476_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_1474_, v___x_1482_, v___x_1483_, v___x_1477_, v_a_748_, v_a_749_);
lean_dec_ref(v___x_1474_);
return v___x_1484_;
}
}
else
{
size_t v___x_1485_; size_t v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = ((size_t)0ULL);
v___x_1486_ = lean_usize_of_nat(v___x_1476_);
v___x_1487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_1474_, v___x_1485_, v___x_1486_, v___x_1477_, v_a_748_, v_a_749_);
lean_dec_ref(v___x_1474_);
return v___x_1487_;
}
}
}
v___jp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0));
v___x_753_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_752_, v_snd_751_);
return v___x_753_;
}
v___jp_754_:
{
lean_object* v_snd_756_; 
v_snd_756_ = lean_ctor_get(v___y_755_, 1);
lean_inc(v_snd_756_);
lean_dec_ref(v___y_755_);
v_snd_751_ = v_snd_756_;
goto v___jp_750_;
}
v___jp_757_:
{
lean_object* v_snd_759_; lean_object* v___x_760_; 
v_snd_759_ = lean_ctor_get(v___y_758_, 1);
lean_inc(v_snd_759_);
lean_dec_ref(v___y_758_);
v___x_760_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_759_);
return v___x_760_;
}
v___jp_761_:
{
lean_object* v_snd_763_; lean_object* v___x_764_; 
v_snd_763_ = lean_ctor_get(v___y_762_, 1);
lean_inc(v_snd_763_);
lean_dec_ref(v___y_762_);
v___x_764_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_763_);
return v___x_764_;
}
v___jp_765_:
{
lean_object* v_snd_767_; lean_object* v___x_768_; 
v_snd_767_ = lean_ctor_get(v___y_766_, 1);
lean_inc(v_snd_767_);
lean_dec_ref(v___y_766_);
v___x_768_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_767_);
return v___x_768_;
}
v___jp_769_:
{
lean_object* v_snd_771_; lean_object* v___x_772_; 
v_snd_771_ = lean_ctor_get(v___y_770_, 1);
lean_inc(v_snd_771_);
lean_dec_ref(v___y_770_);
v___x_772_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_771_);
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(lean_object* v_as_1488_, size_t v_i_1489_, size_t v_stop_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_usize_dec_eq(v_i_1489_, v_stop_1490_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v_fst_1497_; lean_object* v_snd_1498_; size_t v___x_1499_; size_t v___x_1500_; 
v___x_1495_ = lean_array_uget_borrowed(v_as_1488_, v_i_1489_);
lean_inc(v___y_1492_);
lean_inc(v___x_1495_);
v___x_1496_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_1495_, v___y_1492_, v___y_1493_);
v_fst_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_fst_1497_);
v_snd_1498_ = lean_ctor_get(v___x_1496_, 1);
lean_inc(v_snd_1498_);
lean_dec_ref(v___x_1496_);
v___x_1499_ = ((size_t)1ULL);
v___x_1500_ = lean_usize_add(v_i_1489_, v___x_1499_);
v_i_1489_ = v___x_1500_;
v_b_1491_ = v_fst_1497_;
v___y_1493_ = v_snd_1498_;
goto _start;
}
else
{
lean_object* v___x_1502_; 
lean_dec(v___y_1492_);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v_b_1491_);
lean_ctor_set(v___x_1502_, 1, v___y_1493_);
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2___boxed(lean_object* v_as_1503_, lean_object* v_i_1504_, lean_object* v_stop_1505_, lean_object* v_b_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
size_t v_i_boxed_1509_; size_t v_stop_boxed_1510_; lean_object* v_res_1511_; 
v_i_boxed_1509_ = lean_unbox_usize(v_i_1504_);
lean_dec(v_i_1504_);
v_stop_boxed_1510_ = lean_unbox_usize(v_stop_1505_);
lean_dec(v_stop_1505_);
v_res_1511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_as_1503_, v_i_boxed_1509_, v_stop_boxed_1510_, v_b_1506_, v___y_1507_, v___y_1508_);
lean_dec_ref(v_as_1503_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___boxed(lean_object* v_as_1512_, lean_object* v_sz_1513_, lean_object* v_i_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
size_t v_sz_boxed_1518_; size_t v_i_boxed_1519_; lean_object* v_res_1520_; 
v_sz_boxed_1518_ = lean_unbox_usize(v_sz_1513_);
lean_dec(v_sz_1513_);
v_i_boxed_1519_ = lean_unbox_usize(v_i_1514_);
lean_dec(v_i_1514_);
v_res_1520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_as_1512_, v_sz_boxed_1518_, v_i_boxed_1519_, v_b_1515_, v___y_1516_, v___y_1517_);
lean_dec_ref(v_as_1512_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1___boxed(lean_object* v_as_1521_, lean_object* v_sz_1522_, lean_object* v_i_1523_, lean_object* v_b_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
size_t v_sz_boxed_1527_; size_t v_i_boxed_1528_; lean_object* v_res_1529_; 
v_sz_boxed_1527_ = lean_unbox_usize(v_sz_1522_);
lean_dec(v_sz_1522_);
v_i_boxed_1528_ = lean_unbox_usize(v_i_1523_);
lean_dec(v_i_1523_);
v_res_1529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(v_as_1521_, v_sz_boxed_1527_, v_i_boxed_1528_, v_b_1524_, v___y_1525_, v___y_1526_);
lean_dec_ref(v_as_1521_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object* v_as_1530_, lean_object* v_i_1531_, lean_object* v_stop_1532_, lean_object* v_b_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
size_t v_i_boxed_1536_; size_t v_stop_boxed_1537_; lean_object* v_res_1538_; 
v_i_boxed_1536_ = lean_unbox_usize(v_i_1531_);
lean_dec(v_i_1531_);
v_stop_boxed_1537_ = lean_unbox_usize(v_stop_1532_);
lean_dec(v_stop_1532_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v_as_1530_, v_i_boxed_1536_, v_stop_boxed_1537_, v_b_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v_as_1530_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object* v_as_1539_, lean_object* v_sz_1540_, lean_object* v_i_1541_, lean_object* v_b_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
size_t v_sz_boxed_1545_; size_t v_i_boxed_1546_; lean_object* v_res_1547_; 
v_sz_boxed_1545_ = lean_unbox_usize(v_sz_1540_);
lean_dec(v_sz_1540_);
v_i_boxed_1546_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_res_1547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v_as_1539_, v_sz_boxed_1545_, v_i_boxed_1546_, v_b_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v_as_1539_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(lean_object* v_a_1548_, lean_object* v___y_1549_, lean_object* v___x_1550_, lean_object* v___x_1551_, lean_object* v_inst_1552_, lean_object* v_R_1553_, lean_object* v_a_1554_, lean_object* v_b_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(v_a_1548_, v___y_1549_, v___x_1550_, v___x_1551_, v_a_1554_, v_b_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object* v_a_1557_, lean_object* v___y_1558_, lean_object* v___x_1559_, lean_object* v___x_1560_, lean_object* v_inst_1561_, lean_object* v_R_1562_, lean_object* v_a_1563_, lean_object* v_b_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v_a_1557_, v___y_1558_, v___x_1559_, v___x_1560_, v_inst_1561_, v_R_1562_, v_a_1563_, v_b_1564_);
lean_dec_ref(v___x_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0(lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_1567_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
lean_dec_ref(v___x_1571_);
v___x_1572_ = lean_box(0);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1568_);
lean_inc(v___y_1567_);
lean_inc_ref(v___y_1566_);
v___x_1573_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1572_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; 
lean_dec_ref(v___x_1573_);
v___x_1574_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_1567_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref(v___x_1574_);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1568_);
lean_inc(v___y_1567_);
lean_inc_ref(v___y_1566_);
v___x_1575_ = l_Lean_Doc_Parser_metadataContents_formatter(v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1576_; 
lean_dec_ref(v___x_1575_);
v___x_1576_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_1567_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref(v___x_1576_);
v___x_1577_ = l_Lean_PrettyPrinter_Formatter_visitAtom(v___x_1572_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
return v___x_1577_;
}
else
{
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
return v___x_1576_;
}
}
else
{
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
return v___x_1575_;
}
}
else
{
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
return v___x_1574_;
}
}
else
{
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
return v___x_1573_;
}
}
else
{
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
return v___x_1571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0___boxed(lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0(v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v___f_1590_; lean_object* v___x_1591_; 
v___f_1590_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0));
v___x_1591_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___f_1590_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___boxed(lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString(lean_object* v_stx_1598_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v_snd_1602_; 
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1600_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
v___x_1601_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_1598_, v___x_1599_, v___x_1600_);
v_snd_1602_ = lean_ctor_get(v___x_1601_, 1);
lean_inc(v_snd_1602_);
lean_dec_ref(v___x_1601_);
return v_snd_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(lean_object* v_range_1609_, lean_object* v_b_1610_, lean_object* v_i_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_stop_1617_; lean_object* v_step_1618_; uint8_t v___x_1619_; 
v_stop_1617_ = lean_ctor_get(v_range_1609_, 1);
v_step_1618_ = lean_ctor_get(v_range_1609_, 2);
v___x_1619_ = lean_nat_dec_lt(v_i_1611_, v_stop_1617_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v_i_1611_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v_b_1610_);
return v___x_1620_;
}
else
{
lean_object* v___x_1621_; lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1640_; 
v___x_1621_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_1613_);
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1640_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1640_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1626_ = lean_box(0);
lean_inc(v_a_1622_);
v___x_1630_ = l_Lean_Syntax_getKind(v_a_1622_);
v___x_1631_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1));
v___x_1632_ = lean_name_eq(v___x_1630_, v___x_1631_);
lean_dec(v___x_1630_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString(v_a_1622_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set_tag(v___x_1624_, 3);
lean_ctor_set(v___x_1624_, 0, v___x_1633_);
v___x_1635_ = v___x_1624_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_1635_, v___y_1613_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref(v___x_1636_);
v___x_1637_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v___y_1613_);
lean_dec_ref(v___x_1637_);
goto v___jp_1627_;
}
else
{
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v_i_1611_);
return v___x_1636_;
}
}
}
else
{
lean_object* v___x_1639_; 
lean_del_object(v___x_1624_);
lean_dec(v_a_1622_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1614_);
lean_inc(v___y_1613_);
lean_inc_ref(v___y_1612_);
v___x_1639_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_dec_ref(v___x_1639_);
goto v___jp_1627_;
}
else
{
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v_i_1611_);
return v___x_1639_;
}
}
v___jp_1627_:
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_nat_add(v_i_1611_, v_step_1618_);
lean_dec(v_i_1611_);
v_b_1610_ = v___x_1626_;
v_i_1611_ = v___x_1628_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(lean_object* v_range_1641_, lean_object* v_b_1642_, lean_object* v_i_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v_range_1641_, v_b_1642_, v_i_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec_ref(v_range_1641_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0(lean_object* v___x_1650_, lean_object* v___x_1651_, lean_object* v___x_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___x_1650_, v___x_1651_, v___x_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v___x_1658_, 0);
lean_dec(v_unused_1666_);
v___x_1660_ = v___x_1658_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_dec(v___x_1658_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1651_);
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1651_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
else
{
return v___x_1658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0___boxed(lean_object* v___x_1667_, lean_object* v___x_1668_, lean_object* v___x_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_Doc_Parser_document_formatter___lam__0(v___x_1667_, v___x_1668_, v___x_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec_ref(v___x_1667_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1(lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v_a_1682_; lean_object* v___x_1683_; lean_object* v_i_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___f_1689_; lean_object* v___x_1690_; 
v___x_1681_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_1677_);
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = l_Lean_Syntax_getArgs(v_a_1682_);
lean_dec(v_a_1682_);
v_i_1684_ = lean_array_get_size(v___x_1683_);
lean_dec_ref(v___x_1683_);
v___x_1685_ = lean_unsigned_to_nat(0u);
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set(v___x_1687_, 1, v_i_1684_);
lean_ctor_set(v___x_1687_, 2, v___x_1686_);
v___x_1688_ = lean_box(0);
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1689_, 0, v___x_1687_);
lean_closure_set(v___f_1689_, 1, v___x_1688_);
lean_closure_set(v___f_1689_, 2, v___x_1685_);
v___x_1690_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___f_1689_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1___boxed(lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Doc_Parser_document_formatter___lam__1(v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter(lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v___f_1703_; lean_object* v___x_1704_; 
v___f_1703_ = ((lean_object*)(l_Lean_Doc_Parser_document_formatter___closed__0));
v___x_1704_ = l_Lean_PrettyPrinter_Formatter_concat(v___f_1703_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___boxed(lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_Doc_Parser_document_formatter(v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0(lean_object* v_range_1711_, lean_object* v_b_1712_, lean_object* v_i_1713_, lean_object* v_hs_1714_, lean_object* v_hl_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v_range_1711_, v_b_1712_, v_i_1713_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(lean_object* v_range_1722_, lean_object* v_b_1723_, lean_object* v_i_1724_, lean_object* v_hs_1725_, lean_object* v_hl_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0(v_range_1722_, v_b_1723_, v_i_1724_, v_hs_1725_, v_hl_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec_ref(v_range_1722_);
return v_res_1732_;
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
