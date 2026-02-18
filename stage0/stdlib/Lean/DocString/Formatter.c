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
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NON-ATOM "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0_value;
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0_value;
lean_object* l_Lean_Syntax_decodeStrLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NON-IDENT "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0_value;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63;
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_metadataContents_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
x_2 = x_1;
goto block_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fget(x_12, x_16);
lean_dec_ref(x_12);
x_1 = x_17;
goto _start;
}
}
case 2:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_1);
return x_19;
}
default: 
{
x_2 = x_1;
goto block_11;
}
}
block_11:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0));
x_4 = lean_box(0);
x_5 = 0;
x_6 = l_Lean_Syntax_formatStx(x_2, x_4, x_5);
x_7 = l_Std_Format_defWidth;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_3, x_9);
lean_dec_ref(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_take(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Syntax_Traverser_left(x_5);
lean_ctor_set(x_3, 0, x_6);
x_7 = lean_st_ref_set(x_1, x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_16 = l_Lean_Syntax_Traverser_left(x_10);
x_17 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 1, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 2, x_14);
x_18 = lean_st_ref_set(x_1, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_8);
lean_ctor_set_tag(x_6, 3);
lean_ctor_set(x_6, 0, x_9);
x_10 = l_Lean_PrettyPrinter_Formatter_push___redArg(x_6, x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
x_11 = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(x_2);
return x_11;
}
else
{
return x_10;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_PrettyPrinter_Formatter_push___redArg(x_14, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_15);
x_16 = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(x_2);
return x_16;
}
else
{
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_11; lean_object* x_12; 
x_3 = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_5 = x_3;
} else {
 lean_dec_ref(x_3);
 x_5 = lean_box(0);
}
x_11 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_4);
x_12 = l_Lean_Syntax_decodeStrLit(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_6 = x_13;
goto block_10;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_6 = x_14;
goto block_10;
}
block_10:
{
lean_object* x_7; lean_object* x_8; 
if (lean_is_scalar(x_5)) {
 x_7 = lean_alloc_ctor(3, 1, 0);
} else {
 x_7 = x_5;
 lean_ctor_set_tag(x_7, 3);
}
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_push___redArg(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_8);
x_9 = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(x_1);
return x_9;
}
else
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
x_2 = x_1;
goto block_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fget(x_12, x_16);
lean_dec_ref(x_12);
x_1 = x_17;
goto _start;
}
}
case 3:
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_dec_ref(x_1);
x_20 = 1;
x_21 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_19, x_20);
return x_21;
}
default: 
{
x_2 = x_1;
goto block_11;
}
}
block_11:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0));
x_4 = lean_box(0);
x_5 = 0;
x_6 = l_Lean_Syntax_formatStx(x_2, x_4, x_5);
x_7 = l_Std_Format_defWidth;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_3, x_9);
lean_dec_ref(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(x_5);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_Lean_PrettyPrinter_Formatter_push___redArg(x_3, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec_ref(x_7);
x_8 = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(x_1);
return x_8;
}
else
{
return x_7;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_PrettyPrinter_Formatter_push___redArg(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_12);
x_13 = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(x_1);
return x_13;
}
else
{
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_12 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_12);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_2, x_13);
lean_dec(x_2);
x_2 = x_14;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(x_1, x_3, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_10 = lean_array_get_size(x_9);
lean_dec_ref(x_9);
x_11 = lean_alloc_closure((void*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___boxed), 9, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, lean_box(0));
x_12 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_11, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_concat(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_string_append(x_2, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 1)
{
lean_dec(x_1);
return x_2;
}
else
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 32;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_8 = lean_string_push(x_2, x_5);
x_1 = x_7;
x_2 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_box(0);
x_4 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
x_5 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(x_1, x_4);
x_6 = lean_string_append(x_2, x_5);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
x_7 = lean_string_utf8_byte_size(x_2);
x_8 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0;
x_9 = lean_nat_dec_le(x_8, x_7);
if (x_9 == 0)
{
lean_dec(x_1);
goto block_5;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_sub(x_7, x_8);
x_12 = lean_string_memcmp(x_2, x_6, x_11, x_10, x_8);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_1);
goto block_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_14 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(x_1, x_13);
x_15 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_14, x_2);
lean_dec_ref(x_14);
return x_15;
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_2 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0));
x_14 = lean_string_utf8_byte_size(x_1);
x_15 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1;
x_16 = lean_nat_dec_le(x_15, x_14);
if (x_16 == 0)
{
goto block_13;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_sub(x_14, x_15);
x_19 = lean_string_memcmp(x_1, x_2, x_18, x_17, x_15);
lean_dec(x_18);
if (x_19 == 0)
{
goto block_13;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
return x_21;
}
}
block_13:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0;
x_6 = lean_nat_dec_le(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_2, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_sub(x_4, x_5);
x_10 = lean_string_memcmp(x_1, x_3, x_9, x_8, x_5);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_2, x_1);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_3, x_1);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 1)
{
lean_dec(x_1);
return x_2;
}
else
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 35;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_8 = lean_string_push(x_2, x_5);
x_1 = x_7;
x_2 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_nat_sub(x_21, x_20);
x_23 = lean_nat_dec_eq(x_19, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint32_t x_24; uint32_t x_25; uint8_t x_26; 
x_24 = 10;
x_25 = lean_string_utf8_get_fast(x_2, x_19);
x_26 = lean_uint32_dec_eq(x_25, x_24);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_string_utf8_next_fast(x_2, x_19);
lean_dec(x_19);
lean_ctor_set(x_5, 1, x_27);
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_string_utf8_next_fast(x_2, x_19);
x_30 = lean_nat_sub(x_29, x_19);
x_31 = lean_nat_add(x_19, x_30);
lean_dec(x_30);
x_32 = l_String_Slice_subslice_x21(x_3, x_18, x_19);
lean_inc(x_31);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_7 = x_5;
x_8 = x_33;
x_9 = x_34;
goto block_16;
}
}
else
{
lean_object* x_35; 
lean_free_object(x_5);
lean_dec(x_19);
x_35 = lean_box(1);
lean_inc(x_4);
x_7 = x_35;
x_8 = x_18;
x_9 = x_4;
goto block_16;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_5);
x_38 = lean_ctor_get(x_3, 1);
x_39 = lean_ctor_get(x_3, 2);
x_40 = lean_nat_sub(x_39, x_38);
x_41 = lean_nat_dec_eq(x_37, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint32_t x_42; uint32_t x_43; uint8_t x_44; 
x_42 = 10;
x_43 = lean_string_utf8_get_fast(x_2, x_37);
x_44 = lean_uint32_dec_eq(x_43, x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_string_utf8_next_fast(x_2, x_37);
lean_dec(x_37);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
x_5 = x_46;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_string_utf8_next_fast(x_2, x_37);
x_49 = lean_nat_sub(x_48, x_37);
x_50 = lean_nat_add(x_37, x_49);
lean_dec(x_49);
x_51 = l_String_Slice_subslice_x21(x_3, x_36, x_37);
lean_inc(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec_ref(x_51);
x_7 = x_52;
x_8 = x_53;
x_9 = x_54;
goto block_16;
}
}
else
{
lean_object* x_55; 
lean_dec(x_37);
x_55 = lean_box(1);
lean_inc(x_4);
x_7 = x_55;
x_8 = x_36;
x_9 = x_4;
goto block_16;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
block_16:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
lean_inc(x_1);
x_11 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(x_1, x_10);
x_12 = lean_string_utf8_extract(x_2, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = lean_array_push(x_6, x_13);
x_5 = x_7;
x_6 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_9 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0));
x_10 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_9, x_6);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_5);
x_13 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(x_12, x_5, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_box(0);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_15;
x_6 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_9 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0));
x_10 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_9, x_6);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_5);
x_13 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(x_12, x_5, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_box(0);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_15;
x_6 = x_14;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_uget(x_1, x_3);
x_16 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4));
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_15);
x_7 = x_4;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_29; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_inc(x_4);
x_18 = l_Nat_reprFast(x_4);
x_19 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0));
x_20 = lean_string_append(x_18, x_19);
x_21 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_20, x_6);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_unsigned_to_nat(1u);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Syntax_getArg(x_15, x_23);
lean_dec(x_15);
x_34 = l_Lean_Syntax_getArgs(x_33);
lean_dec(x_33);
x_35 = lean_array_get_size(x_34);
x_36 = lean_nat_dec_lt(x_32, x_35);
if (x_36 == 0)
{
lean_dec_ref(x_34);
x_24 = x_22;
goto block_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_nat_add(x_5, x_37);
x_39 = lean_box(0);
x_40 = lean_nat_dec_le(x_35, x_35);
if (x_40 == 0)
{
if (x_36 == 0)
{
lean_dec(x_38);
lean_dec_ref(x_34);
x_24 = x_22;
goto block_28;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_35);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_34, x_41, x_42, x_39, x_38, x_22);
lean_dec_ref(x_34);
x_29 = x_43;
goto block_31;
}
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_35);
x_46 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_34, x_44, x_45, x_39, x_38, x_22);
lean_dec_ref(x_34);
x_29 = x_46;
goto block_31;
}
}
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_7 = x_27;
x_8 = x_26;
goto block_12;
}
block_31:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_24 = x_30;
goto block_28;
}
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_13; lean_object* x_17; uint8_t x_21; 
x_21 = lean_usize_dec_eq(x_2, x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_array_uget(x_1, x_2);
x_23 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4));
lean_inc(x_22);
x_24 = l_Lean_Syntax_isOfKind(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = lean_box(0);
x_7 = x_25;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5));
x_27 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_26, x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Syntax_getArg(x_22, x_29);
lean_dec(x_22);
x_32 = l_Lean_Syntax_getArgs(x_31);
lean_dec(x_31);
x_33 = lean_array_get_size(x_32);
x_34 = lean_nat_dec_lt(x_30, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_32);
x_35 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_28);
x_13 = x_35;
goto block_16;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_nat_add(x_5, x_36);
x_38 = lean_box(0);
x_39 = lean_nat_dec_le(x_33, x_33);
if (x_39 == 0)
{
if (x_34 == 0)
{
lean_object* x_40; 
lean_dec(x_37);
lean_dec_ref(x_32);
x_40 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_28);
x_13 = x_40;
goto block_16;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_33);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_32, x_41, x_42, x_38, x_37, x_28);
lean_dec_ref(x_32);
x_17 = x_43;
goto block_20;
}
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_33);
x_46 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_32, x_44, x_45, x_38, x_37, x_28);
lean_dec_ref(x_32);
x_17 = x_46;
goto block_20;
}
}
}
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_6);
return x_47;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_7 = x_14;
x_8 = x_15;
goto block_12;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_18);
x_13 = x_19;
goto block_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_11; lean_object* x_15; lean_object* x_19; lean_object* x_23; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_inc(x_1);
x_27 = l_Lean_Syntax_getKind(x_1);
x_28 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2));
x_29 = lean_name_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4));
lean_inc(x_1);
x_31 = l_Lean_Syntax_isOfKind(x_1, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6));
lean_inc(x_1);
x_33 = l_Lean_Syntax_isOfKind(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
lean_inc(x_1);
x_35 = l_Lean_Syntax_isOfKind(x_1, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
lean_inc(x_1);
x_37 = l_Lean_Syntax_isOfKind(x_1, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12));
lean_inc(x_1);
x_39 = l_Lean_Syntax_isOfKind(x_1, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14));
lean_inc(x_1);
x_41 = l_Lean_Syntax_isOfKind(x_1, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16));
lean_inc(x_1);
x_43 = l_Lean_Syntax_isOfKind(x_1, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18));
lean_inc(x_1);
x_45 = l_Lean_Syntax_isOfKind(x_1, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20));
lean_inc(x_1);
x_47 = l_Lean_Syntax_isOfKind(x_1, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22));
lean_inc(x_1);
x_49 = l_Lean_Syntax_isOfKind(x_1, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24));
lean_inc(x_1);
x_51 = l_Lean_Syntax_isOfKind(x_1, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26));
lean_inc(x_1);
x_53 = l_Lean_Syntax_isOfKind(x_1, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28));
lean_inc(x_1);
x_55 = l_Lean_Syntax_isOfKind(x_1, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30));
lean_inc(x_1);
x_57 = l_Lean_Syntax_isOfKind(x_1, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32));
lean_inc(x_1);
x_59 = l_Lean_Syntax_isOfKind(x_1, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34));
lean_inc(x_1);
x_61 = l_Lean_Syntax_isOfKind(x_1, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36));
lean_inc(x_1);
x_63 = l_Lean_Syntax_isOfKind(x_1, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38));
lean_inc(x_1);
x_65 = l_Lean_Syntax_isOfKind(x_1, x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40));
lean_inc(x_1);
x_67 = l_Lean_Syntax_isOfKind(x_1, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42));
lean_inc(x_1);
x_69 = l_Lean_Syntax_isOfKind(x_1, x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44));
lean_inc(x_1);
x_71 = l_Lean_Syntax_isOfKind(x_1, x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46));
lean_inc(x_1);
x_73 = l_Lean_Syntax_isOfKind(x_1, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48));
lean_inc(x_1);
x_75 = l_Lean_Syntax_isOfKind(x_1, x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50));
lean_inc(x_1);
x_77 = l_Lean_Syntax_isOfKind(x_1, x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52));
lean_inc(x_1);
x_79 = l_Lean_Syntax_isOfKind(x_1, x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54));
lean_inc(x_1);
x_81 = l_Lean_Syntax_isOfKind(x_1, x_80);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56));
lean_inc(x_1);
x_83 = l_Lean_Syntax_isOfKind(x_1, x_82);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58));
lean_inc(x_1);
x_85 = l_Lean_Syntax_isOfKind(x_1, x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60));
lean_inc(x_1);
x_87 = l_Lean_Syntax_isOfKind(x_1, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_2);
x_88 = lean_box(0);
x_89 = l_Lean_Syntax_formatStx(x_1, x_88, x_87);
x_90 = l_Std_Format_defWidth;
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Std_Format_pretty(x_89, x_90, x_91, x_91);
x_93 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_92, x_3);
lean_dec_ref(x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; size_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_inc(x_2);
x_94 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(x_2, x_3);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61));
x_97 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_96, x_95);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_unsigned_to_nat(1u);
x_100 = l_Lean_Syntax_getArg(x_1, x_99);
x_101 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(x_100);
x_102 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_101, x_98);
lean_dec_ref(x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec_ref(x_102);
x_104 = lean_unsigned_to_nat(2u);
x_105 = l_Lean_Syntax_getArg(x_1, x_104);
lean_dec(x_1);
x_106 = l_Lean_Syntax_getArgs(x_105);
lean_dec(x_105);
x_107 = lean_box(0);
x_108 = lean_array_size(x_106);
x_109 = 0;
x_110 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(x_106, x_108, x_109, x_107, x_2, x_103);
lean_dec_ref(x_106);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62));
x_113 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_112, x_111);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_114);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; size_t x_135; size_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_156; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_inc(x_2);
x_116 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(x_2, x_3);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = lean_unsigned_to_nat(0u);
x_119 = l_Lean_Syntax_getArg(x_1, x_118);
x_120 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_119);
x_121 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_120, x_117);
lean_dec_ref(x_120);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0));
x_124 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_123, x_122);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = lean_unsigned_to_nat(1u);
x_127 = l_Lean_Syntax_getArg(x_1, x_126);
x_128 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(x_127);
x_129 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_128, x_125);
lean_dec_ref(x_128);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = lean_unsigned_to_nat(2u);
x_132 = l_Lean_Syntax_getArg(x_1, x_131);
x_133 = l_Lean_Syntax_getArgs(x_132);
lean_dec(x_132);
x_134 = lean_box(0);
x_135 = lean_array_size(x_133);
x_136 = 0;
lean_inc(x_2);
x_137 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(x_133, x_135, x_136, x_134, x_2, x_130);
lean_dec_ref(x_133);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
x_140 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_139, x_138);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_unsigned_to_nat(4u);
x_143 = l_Lean_Syntax_getArg(x_1, x_142);
x_144 = lean_unsigned_to_nat(5u);
x_145 = l_Lean_Syntax_getArg(x_1, x_144);
lean_dec(x_1);
x_159 = l_Lean_Syntax_getArgs(x_143);
lean_dec(x_143);
x_160 = lean_array_get_size(x_159);
x_161 = lean_nat_dec_lt(x_118, x_160);
if (x_161 == 0)
{
lean_dec_ref(x_159);
x_146 = x_141;
goto block_155;
}
else
{
uint8_t x_162; 
x_162 = lean_nat_dec_le(x_160, x_160);
if (x_162 == 0)
{
if (x_161 == 0)
{
lean_dec_ref(x_159);
x_146 = x_141;
goto block_155;
}
else
{
size_t x_163; lean_object* x_164; 
x_163 = lean_usize_of_nat(x_160);
lean_inc(x_2);
x_164 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_159, x_136, x_163, x_134, x_2, x_141);
lean_dec_ref(x_159);
x_156 = x_164;
goto block_158;
}
}
else
{
size_t x_165; lean_object* x_166; 
x_165 = lean_usize_of_nat(x_160);
lean_inc(x_2);
x_166 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_159, x_136, x_165, x_134, x_2, x_141);
lean_dec_ref(x_159);
x_156 = x_166;
goto block_158;
}
}
block_155:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_147 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_148 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(x_2, x_147);
x_149 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_148, x_146);
lean_dec_ref(x_148);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec_ref(x_149);
x_151 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_145);
x_152 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_151, x_150);
lean_dec_ref(x_151);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec_ref(x_152);
x_154 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_153);
return x_154;
}
block_158:
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec_ref(x_156);
x_146 = x_157;
goto block_155;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = lean_unsigned_to_nat(1u);
x_168 = l_Lean_Syntax_getArg(x_1, x_167);
x_169 = lean_unsigned_to_nat(2u);
lean_inc(x_168);
x_170 = l_Lean_Syntax_matchesNull(x_168, x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_168);
lean_dec(x_2);
x_171 = lean_box(0);
x_172 = l_Lean_Syntax_formatStx(x_1, x_171, x_170);
x_173 = l_Std_Format_defWidth;
x_174 = lean_unsigned_to_nat(0u);
x_175 = l_Std_Format_pretty(x_172, x_173, x_174, x_174);
x_176 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_175, x_3);
lean_dec_ref(x_175);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; size_t x_191; size_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_221; lean_object* x_222; 
lean_inc(x_2);
x_177 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(x_2, x_3);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = lean_unsigned_to_nat(0u);
x_180 = l_Lean_Syntax_getArg(x_1, x_179);
x_181 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_180);
x_182 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_181, x_178);
lean_dec_ref(x_181);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec_ref(x_182);
x_184 = l_Lean_Syntax_getArg(x_168, x_179);
x_185 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(x_184);
x_186 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_185, x_183);
lean_dec_ref(x_185);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec_ref(x_186);
x_188 = l_Lean_Syntax_getArg(x_168, x_167);
lean_dec(x_168);
x_189 = l_Lean_Syntax_getArgs(x_188);
lean_dec(x_188);
x_190 = lean_box(0);
x_191 = lean_array_size(x_189);
x_192 = 0;
lean_inc(x_2);
x_193 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(x_189, x_191, x_192, x_190, x_2, x_187);
lean_dec_ref(x_189);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0));
x_196 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_195, x_194);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = lean_unsigned_to_nat(3u);
x_199 = l_Lean_Syntax_getArg(x_1, x_198);
x_200 = lean_unsigned_to_nat(4u);
x_201 = l_Lean_Syntax_getArg(x_1, x_200);
lean_dec(x_1);
x_221 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_199);
x_222 = l_Lean_Syntax_decodeStrLit(x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_202 = x_223;
goto block_220;
}
else
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
lean_dec_ref(x_222);
x_202 = x_224;
goto block_220;
}
block_220:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_203 = lean_string_utf8_byte_size(x_202);
lean_inc_ref(x_202);
x_204 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_179);
lean_ctor_set(x_204, 2, x_203);
x_205 = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(x_204);
x_206 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63;
lean_inc(x_2);
x_207 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(x_2, x_202, x_204, x_203, x_205, x_206);
lean_dec_ref(x_204);
lean_dec_ref(x_202);
x_208 = lean_array_to_list(x_207);
x_209 = l_String_intercalate(x_195, x_208);
x_210 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_209, x_197);
lean_dec_ref(x_209);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_213 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(x_2, x_212);
x_214 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_213, x_211);
lean_dec_ref(x_213);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec_ref(x_214);
x_216 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_201);
x_217 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_216, x_215);
lean_dec_ref(x_216);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec_ref(x_217);
x_219 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_218);
return x_219;
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
lean_inc(x_2);
x_225 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(x_2, x_3);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec_ref(x_225);
x_227 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64));
x_228 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_227, x_226);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec_ref(x_228);
x_230 = lean_unsigned_to_nat(0u);
x_231 = lean_unsigned_to_nat(1u);
x_232 = l_Lean_Syntax_getArg(x_1, x_231);
lean_dec(x_1);
x_233 = l_Lean_Syntax_getArgs(x_232);
lean_dec(x_232);
x_234 = lean_array_get_size(x_233);
x_235 = lean_nat_dec_lt(x_230, x_234);
if (x_235 == 0)
{
lean_object* x_236; 
lean_dec_ref(x_233);
lean_dec(x_2);
x_236 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_229);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_237 = lean_unsigned_to_nat(2u);
x_238 = lean_nat_add(x_2, x_237);
lean_dec(x_2);
x_239 = lean_box(0);
x_240 = lean_nat_dec_le(x_234, x_234);
if (x_240 == 0)
{
if (x_235 == 0)
{
lean_object* x_241; 
lean_dec(x_238);
lean_dec_ref(x_233);
x_241 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_229);
return x_241;
}
else
{
size_t x_242; size_t x_243; lean_object* x_244; 
x_242 = 0;
x_243 = lean_usize_of_nat(x_234);
x_244 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_233, x_242, x_243, x_239, x_238, x_229);
lean_dec_ref(x_233);
x_23 = x_244;
goto block_26;
}
}
else
{
size_t x_245; size_t x_246; lean_object* x_247; 
x_245 = 0;
x_246 = lean_usize_of_nat(x_234);
x_247 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_233, x_245, x_246, x_239, x_238, x_229);
lean_dec_ref(x_233);
x_23 = x_247;
goto block_26;
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; size_t x_256; size_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_inc(x_2);
x_248 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(x_2, x_3);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec_ref(x_248);
x_250 = lean_unsigned_to_nat(1u);
x_251 = l_Lean_Syntax_getArg(x_1, x_250);
x_252 = lean_unsigned_to_nat(4u);
x_253 = l_Lean_Syntax_getArg(x_1, x_252);
lean_dec(x_1);
x_254 = l_Lean_Syntax_getArgs(x_253);
lean_dec(x_253);
x_255 = l_Lean_TSyntax_getNat(x_251);
lean_dec(x_251);
x_256 = lean_array_size(x_254);
x_257 = 0;
x_258 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(x_254, x_256, x_257, x_255, x_2, x_249);
lean_dec(x_2);
lean_dec_ref(x_254);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec_ref(x_258);
x_260 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_259);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
lean_inc(x_2);
x_261 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(x_2, x_3);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
lean_dec_ref(x_261);
x_263 = lean_unsigned_to_nat(0u);
x_264 = lean_unsigned_to_nat(1u);
x_265 = l_Lean_Syntax_getArg(x_1, x_264);
lean_dec(x_1);
x_266 = l_Lean_Syntax_getArgs(x_265);
lean_dec(x_265);
x_267 = lean_array_get_size(x_266);
x_268 = lean_nat_dec_lt(x_263, x_267);
if (x_268 == 0)
{
lean_object* x_269; 
lean_dec_ref(x_266);
lean_dec(x_2);
x_269 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_262);
return x_269;
}
else
{
lean_object* x_270; uint8_t x_271; 
x_270 = lean_box(0);
x_271 = lean_nat_dec_le(x_267, x_267);
if (x_271 == 0)
{
if (x_268 == 0)
{
lean_object* x_272; 
lean_dec_ref(x_266);
lean_dec(x_2);
x_272 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_262);
return x_272;
}
else
{
size_t x_273; size_t x_274; lean_object* x_275; 
x_273 = 0;
x_274 = lean_usize_of_nat(x_267);
x_275 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(x_266, x_273, x_274, x_270, x_2, x_262);
lean_dec(x_2);
lean_dec_ref(x_266);
x_19 = x_275;
goto block_22;
}
}
else
{
size_t x_276; size_t x_277; lean_object* x_278; 
x_276 = 0;
x_277 = lean_usize_of_nat(x_267);
x_278 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(x_266, x_276, x_277, x_270, x_2, x_262);
lean_dec(x_2);
lean_dec_ref(x_266);
x_19 = x_278;
goto block_22;
}
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
lean_inc(x_2);
x_279 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(x_2, x_3);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec_ref(x_279);
x_281 = lean_unsigned_to_nat(0u);
x_282 = lean_unsigned_to_nat(1u);
x_283 = l_Lean_Syntax_getArg(x_1, x_282);
lean_dec(x_1);
x_284 = l_Lean_Syntax_getArgs(x_283);
lean_dec(x_283);
x_285 = lean_array_get_size(x_284);
x_286 = lean_nat_dec_lt(x_281, x_285);
if (x_286 == 0)
{
lean_object* x_287; 
lean_dec_ref(x_284);
lean_dec(x_2);
x_287 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_280);
return x_287;
}
else
{
lean_object* x_288; uint8_t x_289; 
x_288 = lean_box(0);
x_289 = lean_nat_dec_le(x_285, x_285);
if (x_289 == 0)
{
if (x_286 == 0)
{
lean_object* x_290; 
lean_dec_ref(x_284);
lean_dec(x_2);
x_290 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_280);
return x_290;
}
else
{
size_t x_291; size_t x_292; lean_object* x_293; 
x_291 = 0;
x_292 = lean_usize_of_nat(x_285);
x_293 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_284, x_291, x_292, x_288, x_2, x_280);
lean_dec_ref(x_284);
x_15 = x_293;
goto block_18;
}
}
else
{
size_t x_294; size_t x_295; lean_object* x_296; 
x_294 = 0;
x_295 = lean_usize_of_nat(x_285);
x_296 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_284, x_294, x_295, x_288, x_2, x_280);
lean_dec_ref(x_284);
x_15 = x_296;
goto block_18;
}
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_297 = lean_unsigned_to_nat(1u);
x_298 = l_Lean_Syntax_getArg(x_1, x_297);
x_299 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65));
x_300 = l_Lean_TSyntax_getNat(x_298);
lean_dec(x_298);
x_301 = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(x_300, x_299);
x_302 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0));
x_303 = lean_string_append(x_301, x_302);
x_304 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_303, x_3);
lean_dec_ref(x_303);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec_ref(x_304);
x_306 = lean_unsigned_to_nat(0u);
x_307 = lean_unsigned_to_nat(4u);
x_308 = l_Lean_Syntax_getArg(x_1, x_307);
lean_dec(x_1);
x_309 = l_Lean_Syntax_getArgs(x_308);
lean_dec(x_308);
x_310 = lean_array_get_size(x_309);
x_311 = lean_nat_dec_lt(x_306, x_310);
if (x_311 == 0)
{
lean_object* x_312; 
lean_dec_ref(x_309);
lean_dec(x_2);
x_312 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_305);
return x_312;
}
else
{
lean_object* x_313; uint8_t x_314; 
x_313 = lean_box(0);
x_314 = lean_nat_dec_le(x_310, x_310);
if (x_314 == 0)
{
if (x_311 == 0)
{
lean_object* x_315; 
lean_dec_ref(x_309);
lean_dec(x_2);
x_315 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_305);
return x_315;
}
else
{
size_t x_316; size_t x_317; lean_object* x_318; 
x_316 = 0;
x_317 = lean_usize_of_nat(x_310);
x_318 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_309, x_316, x_317, x_313, x_2, x_305);
lean_dec_ref(x_309);
x_11 = x_318;
goto block_14;
}
}
else
{
size_t x_319; size_t x_320; lean_object* x_321; 
x_319 = 0;
x_320 = lean_usize_of_nat(x_310);
x_321 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_309, x_319, x_320, x_313, x_2, x_305);
lean_dec_ref(x_309);
x_11 = x_321;
goto block_14;
}
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_337; lean_object* x_338; 
lean_dec(x_2);
x_322 = lean_unsigned_to_nat(0u);
x_323 = l_Lean_Syntax_getArg(x_1, x_322);
x_324 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_323);
x_325 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_324, x_3);
lean_dec_ref(x_324);
x_326 = lean_ctor_get(x_325, 1);
lean_inc(x_326);
lean_dec_ref(x_325);
x_327 = lean_unsigned_to_nat(1u);
x_328 = l_Lean_Syntax_getArg(x_1, x_327);
x_329 = lean_unsigned_to_nat(2u);
x_330 = l_Lean_Syntax_getArg(x_1, x_329);
lean_dec(x_1);
x_337 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_328);
x_338 = l_Lean_Syntax_decodeStrLit(x_337);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; 
x_339 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_331 = x_339;
goto block_336;
}
else
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_338, 0);
lean_inc(x_340);
lean_dec_ref(x_338);
x_331 = x_340;
goto block_336;
}
block_336:
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_331, x_326);
lean_dec_ref(x_331);
x_333 = lean_ctor_get(x_332, 1);
lean_inc(x_333);
lean_dec_ref(x_332);
x_334 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_330);
x_335 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_334, x_333);
lean_dec_ref(x_334);
return x_335;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_356; lean_object* x_357; 
lean_dec(x_2);
x_341 = lean_unsigned_to_nat(0u);
x_342 = l_Lean_Syntax_getArg(x_1, x_341);
x_343 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_342);
x_344 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_343, x_3);
lean_dec_ref(x_343);
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
lean_dec_ref(x_344);
x_346 = lean_unsigned_to_nat(1u);
x_347 = l_Lean_Syntax_getArg(x_1, x_346);
x_348 = lean_unsigned_to_nat(2u);
x_349 = l_Lean_Syntax_getArg(x_1, x_348);
lean_dec(x_1);
x_356 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_347);
x_357 = l_Lean_Syntax_decodeStrLit(x_356);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_350 = x_358;
goto block_355;
}
else
{
lean_object* x_359; 
x_359 = lean_ctor_get(x_357, 0);
lean_inc(x_359);
lean_dec_ref(x_357);
x_350 = x_359;
goto block_355;
}
block_355:
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_351 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_350, x_345);
lean_dec_ref(x_350);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec_ref(x_351);
x_353 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_349);
x_354 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_353, x_352);
lean_dec_ref(x_353);
return x_354;
}
}
}
else
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; 
lean_dec(x_2);
x_360 = lean_unsigned_to_nat(1u);
x_361 = l_Lean_Syntax_getArg(x_1, x_360);
lean_inc(x_361);
x_362 = l_Lean_Syntax_isOfKind(x_361, x_58);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_361);
x_363 = lean_box(0);
x_364 = l_Lean_Syntax_formatStx(x_1, x_363, x_362);
x_365 = l_Std_Format_defWidth;
x_366 = lean_unsigned_to_nat(0u);
x_367 = l_Std_Format_pretty(x_364, x_365, x_366, x_366);
x_368 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_367, x_3);
lean_dec_ref(x_367);
return x_368;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_387; lean_object* x_388; 
x_369 = lean_unsigned_to_nat(0u);
x_370 = l_Lean_Syntax_getArg(x_1, x_369);
lean_dec(x_1);
x_371 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_370);
x_372 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_371, x_3);
lean_dec_ref(x_371);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
lean_dec_ref(x_372);
x_374 = l_Lean_Syntax_getArg(x_361, x_369);
x_375 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_374);
x_376 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_375, x_373);
lean_dec_ref(x_375);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
lean_dec_ref(x_376);
x_378 = l_Lean_Syntax_getArg(x_361, x_360);
x_379 = lean_unsigned_to_nat(2u);
x_380 = l_Lean_Syntax_getArg(x_361, x_379);
lean_dec(x_361);
x_387 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_378);
x_388 = l_Lean_Syntax_decodeStrLit(x_387);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; 
x_389 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_381 = x_389;
goto block_386;
}
else
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_388, 0);
lean_inc(x_390);
lean_dec_ref(x_388);
x_381 = x_390;
goto block_386;
}
block_386:
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_382 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_381, x_377);
lean_dec_ref(x_381);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
lean_dec_ref(x_382);
x_384 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_380);
x_385 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_384, x_383);
lean_dec_ref(x_384);
return x_385;
}
}
}
}
else
{
lean_object* x_391; lean_object* x_392; uint8_t x_393; 
lean_dec(x_2);
x_391 = lean_unsigned_to_nat(1u);
x_392 = l_Lean_Syntax_getArg(x_1, x_391);
lean_inc(x_392);
x_393 = l_Lean_Syntax_isOfKind(x_392, x_58);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_392);
x_394 = lean_box(0);
x_395 = l_Lean_Syntax_formatStx(x_1, x_394, x_393);
x_396 = l_Std_Format_defWidth;
x_397 = lean_unsigned_to_nat(0u);
x_398 = l_Std_Format_pretty(x_395, x_396, x_397, x_397);
x_399 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_398, x_3);
lean_dec_ref(x_398);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_418; lean_object* x_419; 
x_400 = lean_unsigned_to_nat(0u);
x_401 = l_Lean_Syntax_getArg(x_1, x_400);
lean_dec(x_1);
x_402 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_401);
x_403 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_402, x_3);
lean_dec_ref(x_402);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
lean_dec_ref(x_403);
x_405 = l_Lean_Syntax_getArg(x_392, x_400);
x_406 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_405);
x_407 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_406, x_404);
lean_dec_ref(x_406);
x_408 = lean_ctor_get(x_407, 1);
lean_inc(x_408);
lean_dec_ref(x_407);
x_409 = l_Lean_Syntax_getArg(x_392, x_391);
x_410 = lean_unsigned_to_nat(2u);
x_411 = l_Lean_Syntax_getArg(x_392, x_410);
lean_dec(x_392);
x_418 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_409);
x_419 = l_Lean_Syntax_decodeStrLit(x_418);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; 
x_420 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_412 = x_420;
goto block_417;
}
else
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_419, 0);
lean_inc(x_421);
lean_dec_ref(x_419);
x_412 = x_421;
goto block_417;
}
block_417:
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_413 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_412, x_408);
lean_dec_ref(x_412);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
lean_dec_ref(x_413);
x_415 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_411);
x_416 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_415, x_414);
lean_dec_ref(x_415);
return x_416;
}
}
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_2);
x_422 = lean_unsigned_to_nat(1u);
x_423 = l_Lean_Syntax_getArg(x_1, x_422);
lean_dec(x_1);
x_424 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_423);
x_425 = l_Lean_Syntax_decodeStrLit(x_424);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; 
x_426 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_427 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_426, x_3);
return x_427;
}
else
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_425, 0);
lean_inc(x_428);
lean_dec_ref(x_425);
x_429 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_428, x_3);
lean_dec(x_428);
return x_429;
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_445; lean_object* x_446; 
lean_dec(x_2);
x_430 = lean_unsigned_to_nat(0u);
x_431 = l_Lean_Syntax_getArg(x_1, x_430);
x_432 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_431);
x_433 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_432, x_3);
lean_dec_ref(x_432);
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
lean_dec_ref(x_433);
x_435 = lean_unsigned_to_nat(1u);
x_436 = l_Lean_Syntax_getArg(x_1, x_435);
x_437 = lean_unsigned_to_nat(2u);
x_438 = l_Lean_Syntax_getArg(x_1, x_437);
lean_dec(x_1);
x_445 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_436);
x_446 = l_Lean_Syntax_decodeStrLit(x_445);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; 
x_447 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_439 = x_447;
goto block_444;
}
else
{
lean_object* x_448; 
x_448 = lean_ctor_get(x_446, 0);
lean_inc(x_448);
lean_dec_ref(x_446);
x_439 = x_448;
goto block_444;
}
block_444:
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_440 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_439, x_434);
lean_dec_ref(x_439);
x_441 = lean_ctor_get(x_440, 1);
lean_inc(x_441);
lean_dec_ref(x_440);
x_442 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_438);
x_443 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_442, x_441);
lean_dec_ref(x_442);
return x_443;
}
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_464; lean_object* x_465; 
lean_dec(x_2);
x_449 = lean_unsigned_to_nat(0u);
x_450 = l_Lean_Syntax_getArg(x_1, x_449);
x_451 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_450);
x_452 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_451, x_3);
lean_dec_ref(x_451);
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
lean_dec_ref(x_452);
x_454 = lean_unsigned_to_nat(1u);
x_455 = l_Lean_Syntax_getArg(x_1, x_454);
x_456 = lean_unsigned_to_nat(2u);
x_457 = l_Lean_Syntax_getArg(x_1, x_456);
lean_dec(x_1);
x_464 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_455);
x_465 = l_Lean_Syntax_decodeStrLit(x_464);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; 
x_466 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_458 = x_466;
goto block_463;
}
else
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_465, 0);
lean_inc(x_467);
lean_dec_ref(x_465);
x_458 = x_467;
goto block_463;
}
block_463:
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_459 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_458, x_453);
lean_dec_ref(x_458);
x_460 = lean_ctor_get(x_459, 1);
lean_inc(x_460);
lean_dec_ref(x_459);
x_461 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_457);
x_462 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_461, x_460);
lean_dec_ref(x_461);
return x_462;
}
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; size_t x_480; size_t x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; uint8_t x_492; 
x_468 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61));
x_469 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_468, x_3);
x_470 = lean_ctor_get(x_469, 1);
lean_inc(x_470);
lean_dec_ref(x_469);
x_471 = lean_unsigned_to_nat(1u);
x_472 = l_Lean_Syntax_getArg(x_1, x_471);
x_473 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(x_472);
x_474 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_473, x_470);
lean_dec_ref(x_473);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
lean_dec_ref(x_474);
x_476 = lean_unsigned_to_nat(2u);
x_477 = l_Lean_Syntax_getArg(x_1, x_476);
x_478 = l_Lean_Syntax_getArgs(x_477);
lean_dec(x_477);
x_479 = lean_box(0);
x_480 = lean_array_size(x_478);
x_481 = 0;
lean_inc(x_2);
x_482 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(x_478, x_480, x_481, x_479, x_2, x_475);
lean_dec_ref(x_478);
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
lean_dec_ref(x_482);
x_484 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66));
x_485 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_484, x_483);
x_486 = lean_ctor_get(x_485, 1);
lean_inc(x_486);
lean_dec_ref(x_485);
x_487 = lean_unsigned_to_nat(0u);
x_488 = lean_unsigned_to_nat(5u);
x_489 = l_Lean_Syntax_getArg(x_1, x_488);
lean_dec(x_1);
x_490 = l_Lean_Syntax_getArgs(x_489);
lean_dec(x_489);
x_491 = lean_array_get_size(x_490);
x_492 = lean_nat_dec_lt(x_487, x_491);
if (x_492 == 0)
{
lean_dec_ref(x_490);
lean_dec(x_2);
x_4 = x_486;
goto block_7;
}
else
{
uint8_t x_493; 
x_493 = lean_nat_dec_le(x_491, x_491);
if (x_493 == 0)
{
if (x_492 == 0)
{
lean_dec_ref(x_490);
lean_dec(x_2);
x_4 = x_486;
goto block_7;
}
else
{
size_t x_494; lean_object* x_495; 
x_494 = lean_usize_of_nat(x_491);
x_495 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_490, x_481, x_494, x_479, x_2, x_486);
lean_dec_ref(x_490);
x_8 = x_495;
goto block_10;
}
}
else
{
size_t x_496; lean_object* x_497; 
x_496 = lean_usize_of_nat(x_491);
x_497 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_490, x_481, x_496, x_479, x_2, x_486);
lean_dec_ref(x_490);
x_8 = x_497;
goto block_10;
}
}
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_517; lean_object* x_518; 
x_498 = lean_unsigned_to_nat(0u);
x_499 = l_Lean_Syntax_getArg(x_1, x_498);
x_500 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_499);
x_501 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_500, x_3);
lean_dec_ref(x_500);
x_502 = lean_ctor_get(x_501, 1);
lean_inc(x_502);
lean_dec_ref(x_501);
x_503 = lean_unsigned_to_nat(1u);
x_504 = l_Lean_Syntax_getArg(x_1, x_503);
x_505 = lean_unsigned_to_nat(2u);
x_506 = l_Lean_Syntax_getArg(x_1, x_505);
x_507 = lean_unsigned_to_nat(3u);
x_508 = l_Lean_Syntax_getArg(x_1, x_507);
lean_dec(x_1);
x_517 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_504);
x_518 = l_Lean_Syntax_decodeStrLit(x_517);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; 
x_519 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_509 = x_519;
goto block_516;
}
else
{
lean_object* x_520; 
x_520 = lean_ctor_get(x_518, 0);
lean_inc(x_520);
lean_dec_ref(x_518);
x_509 = x_520;
goto block_516;
}
block_516:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_510 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_509, x_502);
lean_dec_ref(x_509);
x_511 = lean_ctor_get(x_510, 1);
lean_inc(x_511);
lean_dec_ref(x_510);
x_512 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_506);
x_513 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_512, x_511);
lean_dec_ref(x_512);
x_514 = lean_ctor_get(x_513, 1);
lean_inc(x_514);
lean_dec_ref(x_513);
x_1 = x_508;
x_3 = x_514;
goto _start;
}
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_538; lean_object* x_541; lean_object* x_542; uint8_t x_543; 
x_521 = lean_unsigned_to_nat(0u);
x_522 = l_Lean_Syntax_getArg(x_1, x_521);
x_523 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_522);
x_524 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_523, x_3);
lean_dec_ref(x_523);
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
lean_dec_ref(x_524);
x_526 = lean_unsigned_to_nat(1u);
x_527 = l_Lean_Syntax_getArg(x_1, x_526);
x_528 = lean_unsigned_to_nat(2u);
x_529 = l_Lean_Syntax_getArg(x_1, x_528);
x_530 = lean_unsigned_to_nat(3u);
x_531 = l_Lean_Syntax_getArg(x_1, x_530);
lean_dec(x_1);
x_541 = l_Lean_Syntax_getArgs(x_527);
lean_dec(x_527);
x_542 = lean_array_get_size(x_541);
x_543 = lean_nat_dec_lt(x_521, x_542);
if (x_543 == 0)
{
lean_dec_ref(x_541);
x_532 = x_525;
goto block_537;
}
else
{
lean_object* x_544; uint8_t x_545; 
x_544 = lean_box(0);
x_545 = lean_nat_dec_le(x_542, x_542);
if (x_545 == 0)
{
if (x_543 == 0)
{
lean_dec_ref(x_541);
x_532 = x_525;
goto block_537;
}
else
{
size_t x_546; size_t x_547; lean_object* x_548; 
x_546 = 0;
x_547 = lean_usize_of_nat(x_542);
lean_inc(x_2);
x_548 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_541, x_546, x_547, x_544, x_2, x_525);
lean_dec_ref(x_541);
x_538 = x_548;
goto block_540;
}
}
else
{
size_t x_549; size_t x_550; lean_object* x_551; 
x_549 = 0;
x_550 = lean_usize_of_nat(x_542);
lean_inc(x_2);
x_551 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_541, x_549, x_550, x_544, x_2, x_525);
lean_dec_ref(x_541);
x_538 = x_551;
goto block_540;
}
}
block_537:
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_533 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_529);
x_534 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_533, x_532);
lean_dec_ref(x_533);
x_535 = lean_ctor_get(x_534, 1);
lean_inc(x_535);
lean_dec_ref(x_534);
x_1 = x_531;
x_3 = x_535;
goto _start;
}
block_540:
{
lean_object* x_539; 
x_539 = lean_ctor_get(x_538, 1);
lean_inc(x_539);
lean_dec_ref(x_538);
x_532 = x_539;
goto block_537;
}
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_565; lean_object* x_568; lean_object* x_569; uint8_t x_570; 
x_552 = lean_unsigned_to_nat(0u);
x_553 = l_Lean_Syntax_getArg(x_1, x_552);
x_554 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_553);
x_555 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_554, x_3);
lean_dec_ref(x_554);
x_556 = lean_ctor_get(x_555, 1);
lean_inc(x_556);
lean_dec_ref(x_555);
x_557 = lean_unsigned_to_nat(1u);
x_558 = l_Lean_Syntax_getArg(x_1, x_557);
x_559 = lean_unsigned_to_nat(2u);
x_560 = l_Lean_Syntax_getArg(x_1, x_559);
lean_dec(x_1);
x_568 = l_Lean_Syntax_getArgs(x_558);
lean_dec(x_558);
x_569 = lean_array_get_size(x_568);
x_570 = lean_nat_dec_lt(x_552, x_569);
if (x_570 == 0)
{
lean_dec_ref(x_568);
lean_dec(x_2);
x_561 = x_556;
goto block_564;
}
else
{
lean_object* x_571; uint8_t x_572; 
x_571 = lean_box(0);
x_572 = lean_nat_dec_le(x_569, x_569);
if (x_572 == 0)
{
if (x_570 == 0)
{
lean_dec_ref(x_568);
lean_dec(x_2);
x_561 = x_556;
goto block_564;
}
else
{
size_t x_573; size_t x_574; lean_object* x_575; 
x_573 = 0;
x_574 = lean_usize_of_nat(x_569);
x_575 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_568, x_573, x_574, x_571, x_2, x_556);
lean_dec_ref(x_568);
x_565 = x_575;
goto block_567;
}
}
else
{
size_t x_576; size_t x_577; lean_object* x_578; 
x_576 = 0;
x_577 = lean_usize_of_nat(x_569);
x_578 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_568, x_576, x_577, x_571, x_2, x_556);
lean_dec_ref(x_568);
x_565 = x_578;
goto block_567;
}
}
block_564:
{
lean_object* x_562; lean_object* x_563; 
x_562 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_560);
x_563 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_562, x_561);
lean_dec_ref(x_562);
return x_563;
}
block_567:
{
lean_object* x_566; 
x_566 = lean_ctor_get(x_565, 1);
lean_inc(x_566);
lean_dec_ref(x_565);
x_561 = x_566;
goto block_564;
}
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_592; lean_object* x_595; lean_object* x_596; uint8_t x_597; 
x_579 = lean_unsigned_to_nat(0u);
x_580 = l_Lean_Syntax_getArg(x_1, x_579);
x_581 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_580);
x_582 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_581, x_3);
lean_dec_ref(x_581);
x_583 = lean_ctor_get(x_582, 1);
lean_inc(x_583);
lean_dec_ref(x_582);
x_584 = lean_unsigned_to_nat(1u);
x_585 = l_Lean_Syntax_getArg(x_1, x_584);
x_586 = lean_unsigned_to_nat(2u);
x_587 = l_Lean_Syntax_getArg(x_1, x_586);
lean_dec(x_1);
x_595 = l_Lean_Syntax_getArgs(x_585);
lean_dec(x_585);
x_596 = lean_array_get_size(x_595);
x_597 = lean_nat_dec_lt(x_579, x_596);
if (x_597 == 0)
{
lean_dec_ref(x_595);
lean_dec(x_2);
x_588 = x_583;
goto block_591;
}
else
{
lean_object* x_598; uint8_t x_599; 
x_598 = lean_box(0);
x_599 = lean_nat_dec_le(x_596, x_596);
if (x_599 == 0)
{
if (x_597 == 0)
{
lean_dec_ref(x_595);
lean_dec(x_2);
x_588 = x_583;
goto block_591;
}
else
{
size_t x_600; size_t x_601; lean_object* x_602; 
x_600 = 0;
x_601 = lean_usize_of_nat(x_596);
x_602 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_595, x_600, x_601, x_598, x_2, x_583);
lean_dec_ref(x_595);
x_592 = x_602;
goto block_594;
}
}
else
{
size_t x_603; size_t x_604; lean_object* x_605; 
x_603 = 0;
x_604 = lean_usize_of_nat(x_596);
x_605 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_595, x_603, x_604, x_598, x_2, x_583);
lean_dec_ref(x_595);
x_592 = x_605;
goto block_594;
}
}
block_591:
{
lean_object* x_589; lean_object* x_590; 
x_589 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_587);
x_590 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_589, x_588);
lean_dec_ref(x_589);
return x_590;
}
block_594:
{
lean_object* x_593; 
x_593 = lean_ctor_get(x_592, 1);
lean_inc(x_593);
lean_dec_ref(x_592);
x_588 = x_593;
goto block_591;
}
}
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; uint8_t x_609; 
lean_dec(x_2);
x_606 = lean_unsigned_to_nat(0u);
x_607 = l_Lean_Syntax_getArg(x_1, x_606);
x_608 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68));
lean_inc(x_607);
x_609 = l_Lean_Syntax_isOfKind(x_607, x_608);
if (x_609 == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
lean_dec(x_607);
x_610 = lean_box(0);
x_611 = l_Lean_Syntax_formatStx(x_1, x_610, x_609);
x_612 = l_Std_Format_defWidth;
x_613 = l_Std_Format_pretty(x_611, x_612, x_606, x_606);
x_614 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_613, x_3);
lean_dec_ref(x_613);
return x_614;
}
else
{
lean_object* x_615; lean_object* x_616; 
lean_dec(x_1);
x_615 = l_Lean_TSyntax_getString(x_607);
lean_dec(x_607);
x_616 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_615, x_3);
lean_dec_ref(x_615);
return x_616;
}
}
}
else
{
lean_object* x_617; lean_object* x_618; 
x_617 = lean_unsigned_to_nat(0u);
x_618 = l_Lean_Syntax_getArg(x_1, x_617);
lean_dec(x_1);
x_1 = x_618;
goto _start;
}
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; uint8_t x_623; 
lean_dec(x_2);
x_620 = lean_unsigned_to_nat(1u);
x_621 = l_Lean_Syntax_getArg(x_1, x_620);
x_622 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70));
lean_inc(x_621);
x_623 = l_Lean_Syntax_isOfKind(x_621, x_622);
if (x_623 == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_621);
x_624 = lean_box(0);
x_625 = l_Lean_Syntax_formatStx(x_1, x_624, x_623);
x_626 = l_Std_Format_defWidth;
x_627 = lean_unsigned_to_nat(0u);
x_628 = l_Std_Format_pretty(x_625, x_626, x_627, x_627);
x_629 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_628, x_3);
lean_dec_ref(x_628);
return x_629;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_630 = lean_unsigned_to_nat(0u);
x_631 = l_Lean_Syntax_getArg(x_1, x_630);
lean_dec(x_1);
x_632 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_631);
x_633 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_632, x_3);
lean_dec_ref(x_632);
x_634 = lean_ctor_get(x_633, 1);
lean_inc(x_634);
lean_dec_ref(x_633);
x_635 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(x_621);
x_636 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_635, x_634);
lean_dec_ref(x_635);
return x_636;
}
}
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; 
lean_dec(x_2);
x_637 = lean_unsigned_to_nat(1u);
x_638 = l_Lean_Syntax_getArg(x_1, x_637);
x_639 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70));
lean_inc(x_638);
x_640 = l_Lean_Syntax_isOfKind(x_638, x_639);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
lean_dec(x_638);
x_641 = lean_box(0);
x_642 = l_Lean_Syntax_formatStx(x_1, x_641, x_640);
x_643 = l_Std_Format_defWidth;
x_644 = lean_unsigned_to_nat(0u);
x_645 = l_Std_Format_pretty(x_642, x_643, x_644, x_644);
x_646 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_645, x_3);
lean_dec_ref(x_645);
return x_646;
}
else
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_647 = lean_unsigned_to_nat(0u);
x_648 = l_Lean_Syntax_getArg(x_1, x_647);
lean_dec(x_1);
x_649 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_648);
x_650 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_649, x_3);
lean_dec_ref(x_649);
x_651 = lean_ctor_get(x_650, 1);
lean_inc(x_651);
lean_dec_ref(x_650);
x_652 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(x_638);
x_653 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_652, x_651);
lean_dec_ref(x_652);
return x_653;
}
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; 
x_654 = lean_unsigned_to_nat(0u);
x_655 = l_Lean_Syntax_getArg(x_1, x_654);
x_656 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70));
lean_inc(x_655);
x_657 = l_Lean_Syntax_isOfKind(x_655, x_656);
if (x_657 == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; 
lean_dec(x_655);
lean_dec(x_2);
x_658 = lean_box(0);
x_659 = l_Lean_Syntax_formatStx(x_1, x_658, x_657);
x_660 = l_Std_Format_defWidth;
x_661 = l_Std_Format_pretty(x_659, x_660, x_654, x_654);
x_662 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_661, x_3);
lean_dec_ref(x_661);
return x_662;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_663 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71));
x_664 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_663, x_3);
x_665 = lean_ctor_get(x_664, 1);
lean_inc(x_665);
lean_dec_ref(x_664);
x_666 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(x_655);
x_667 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_666, x_665);
lean_dec_ref(x_666);
x_668 = lean_ctor_get(x_667, 1);
lean_inc(x_668);
lean_dec_ref(x_667);
x_669 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72));
x_670 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_669, x_668);
x_671 = lean_ctor_get(x_670, 1);
lean_inc(x_671);
lean_dec_ref(x_670);
x_672 = lean_unsigned_to_nat(2u);
x_673 = l_Lean_Syntax_getArg(x_1, x_672);
lean_dec(x_1);
x_674 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(x_673, x_2, x_671);
x_675 = lean_ctor_get(x_674, 1);
lean_inc(x_675);
lean_dec_ref(x_674);
x_676 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73));
x_677 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_676, x_675);
return x_677;
}
}
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_678 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71));
x_679 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_678, x_3);
x_680 = lean_ctor_get(x_679, 1);
lean_inc(x_680);
lean_dec_ref(x_679);
x_681 = lean_unsigned_to_nat(1u);
x_682 = l_Lean_Syntax_getArg(x_1, x_681);
x_683 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(x_682);
x_684 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_683, x_680);
lean_dec_ref(x_683);
x_685 = lean_ctor_get(x_684, 1);
lean_inc(x_685);
lean_dec_ref(x_684);
x_686 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72));
x_687 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_686, x_685);
x_688 = lean_ctor_get(x_687, 1);
lean_inc(x_688);
lean_dec_ref(x_687);
x_689 = lean_unsigned_to_nat(3u);
x_690 = l_Lean_Syntax_getArg(x_1, x_689);
lean_dec(x_1);
x_691 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(x_690, x_2, x_688);
x_692 = lean_ctor_get(x_691, 1);
lean_inc(x_692);
lean_dec_ref(x_691);
x_693 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73));
x_694 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_693, x_692);
return x_694;
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; 
lean_dec(x_2);
x_695 = lean_unsigned_to_nat(0u);
x_696 = l_Lean_Syntax_getArg(x_1, x_695);
x_697 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70));
lean_inc(x_696);
x_698 = l_Lean_Syntax_isOfKind(x_696, x_697);
if (x_698 == 0)
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
lean_dec(x_696);
x_699 = lean_box(0);
x_700 = l_Lean_Syntax_formatStx(x_1, x_699, x_698);
x_701 = l_Std_Format_defWidth;
x_702 = l_Std_Format_pretty(x_700, x_701, x_695, x_695);
x_703 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_702, x_3);
lean_dec_ref(x_702);
return x_703;
}
else
{
lean_object* x_704; lean_object* x_705; 
lean_dec(x_1);
x_704 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(x_696);
x_705 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_704, x_3);
lean_dec_ref(x_704);
return x_705;
}
}
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; uint8_t x_709; 
lean_dec(x_2);
x_706 = lean_unsigned_to_nat(0u);
x_707 = l_Lean_Syntax_getArg(x_1, x_706);
x_708 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75));
lean_inc(x_707);
x_709 = l_Lean_Syntax_isOfKind(x_707, x_708);
if (x_709 == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
lean_dec(x_707);
x_710 = lean_box(0);
x_711 = l_Lean_Syntax_formatStx(x_1, x_710, x_709);
x_712 = l_Std_Format_defWidth;
x_713 = l_Std_Format_pretty(x_711, x_712, x_706, x_706);
x_714 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_713, x_3);
lean_dec_ref(x_713);
return x_714;
}
else
{
lean_object* x_715; lean_object* x_716; 
lean_dec(x_1);
x_715 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_707);
x_716 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_715, x_3);
lean_dec_ref(x_715);
return x_716;
}
}
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; uint8_t x_720; 
lean_dec(x_2);
x_717 = lean_unsigned_to_nat(0u);
x_718 = l_Lean_Syntax_getArg(x_1, x_717);
x_719 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68));
lean_inc(x_718);
x_720 = l_Lean_Syntax_isOfKind(x_718, x_719);
if (x_720 == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
lean_dec(x_718);
x_721 = lean_box(0);
x_722 = l_Lean_Syntax_formatStx(x_1, x_721, x_720);
x_723 = l_Std_Format_defWidth;
x_724 = l_Std_Format_pretty(x_722, x_723, x_717, x_717);
x_725 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_724, x_3);
lean_dec_ref(x_724);
return x_725;
}
else
{
lean_object* x_726; lean_object* x_727; 
lean_dec(x_1);
x_726 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(x_718);
x_727 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_726, x_3);
lean_dec_ref(x_726);
return x_727;
}
}
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; uint8_t x_732; 
x_728 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_729 = lean_unsigned_to_nat(0u);
x_730 = lean_array_get_size(x_728);
x_731 = lean_box(0);
x_732 = lean_nat_dec_lt(x_729, x_730);
if (x_732 == 0)
{
lean_object* x_733; 
lean_dec_ref(x_728);
lean_dec(x_2);
x_733 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_733, 0, x_731);
lean_ctor_set(x_733, 1, x_3);
return x_733;
}
else
{
uint8_t x_734; 
x_734 = lean_nat_dec_le(x_730, x_730);
if (x_734 == 0)
{
if (x_732 == 0)
{
lean_object* x_735; 
lean_dec_ref(x_728);
lean_dec(x_2);
x_735 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_735, 0, x_731);
lean_ctor_set(x_735, 1, x_3);
return x_735;
}
else
{
size_t x_736; size_t x_737; lean_object* x_738; 
x_736 = 0;
x_737 = lean_usize_of_nat(x_730);
x_738 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_728, x_736, x_737, x_731, x_2, x_3);
lean_dec_ref(x_728);
return x_738;
}
}
else
{
size_t x_739; size_t x_740; lean_object* x_741; 
x_739 = 0;
x_740 = lean_usize_of_nat(x_730);
x_741 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_728, x_739, x_740, x_731, x_2, x_3);
lean_dec_ref(x_728);
return x_741;
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0));
x_6 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(x_5, x_4);
return x_6;
}
block_10:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_4 = x_9;
goto block_7;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_12);
return x_13;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_16);
return x_17;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_20);
return x_21;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_6);
x_7 = lean_box(0);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_7, x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_8);
x_9 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_9);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_10 = l_Lean_Doc_Parser_metadataContents_formatter(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
x_11 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_11);
x_12 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_7, x_1, x_2, x_3, x_4);
return x_12;
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0));
x_7 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0));
x_4 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_nat_dec_lt(x_3, x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_box(0);
lean_inc(x_15);
x_21 = l_Lean_Syntax_getKind(x_15);
x_22 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1));
x_23 = lean_name_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString(x_15);
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 0, x_24);
x_25 = l_Lean_PrettyPrinter_Formatter_push___redArg(x_13, x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec_ref(x_25);
x_26 = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(x_5);
lean_dec_ref(x_26);
x_17 = lean_box(0);
goto block_20;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_25;
}
}
else
{
lean_object* x_27; 
lean_free_object(x_13);
lean_dec(x_15);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_27 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_dec_ref(x_27);
x_17 = lean_box(0);
goto block_20;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_27;
}
}
block_20:
{
lean_object* x_18; 
x_18 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_2 = x_16;
x_3 = x_18;
goto _start;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
lean_dec(x_13);
x_29 = lean_box(0);
lean_inc(x_28);
x_34 = l_Lean_Syntax_getKind(x_28);
x_35 = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1));
x_36 = lean_name_eq(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString(x_28);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_PrettyPrinter_Formatter_push___redArg(x_38, x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec_ref(x_39);
x_40 = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(x_5);
lean_dec_ref(x_40);
x_30 = lean_box(0);
goto block_33;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_39;
}
}
else
{
lean_object* x_41; 
lean_dec(x_28);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_41 = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_41) == 0)
{
lean_dec_ref(x_41);
x_30 = lean_box(0);
goto block_33;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_41;
}
}
block_33:
{
lean_object* x_31; 
x_31 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_2 = x_29;
x_3 = x_31;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
else
{
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Doc_Parser_document_formatter___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = lean_array_get_size(x_8);
lean_dec_ref(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___lam__0___boxed), 8, 3);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_10);
x_15 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_14, x_1, x_2, x_3, x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Doc_Parser_document_formatter___lam__1(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = ((lean_object*)(l_Lean_Doc_Parser_document_formatter___closed__0));
x_7 = l_Lean_PrettyPrinter_Formatter_concat(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Doc_Parser_document_formatter(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_11;
}
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
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
