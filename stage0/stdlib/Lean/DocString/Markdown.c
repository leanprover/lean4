// Lean compiler output
// Module: Lean.DocString.Markdown
// Imports: public import Lean.DocString.Types public import Init.Data.String.TakeDrop public import Init.Data.String.Search import Init.Data.ToString.Macro import Init.While
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_Inline_empty(lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_String_toSlice(lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep(lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(lean_object*);
lean_object* l_String_Slice_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Int_toNat(lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[^"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]:"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_push___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endsWith___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_push___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_push(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_push___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endsWith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endsWith___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endsWith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endsWith___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endBlock___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endBlock___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_MarkdownM_indent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l_Lean_Doc_MarkdownM_indent___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_MarkdownM_indent___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_indent___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_indent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_indent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instMarkdownInlineEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instMarkdownInlineEmpty___closed__0 = (const lean_object*)&l_Lean_Doc_instMarkdownInlineEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instMarkdownInlineEmpty = (const lean_object*)&l_Lean_Doc_instMarkdownInlineEmpty___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instMarkdownBlockEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instMarkdownBlockEmpty___closed__0 = (const lean_object*)&l_Lean_Doc_instMarkdownBlockEmpty___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(lean_object*, uint32_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "*_`-+.!<>[]{}()#"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2;
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__3 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__3_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__3_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__4 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "**"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "​"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_toSlice, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]("};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 3, .m_data = "[ˆ^"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__36 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__36_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__1_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__2 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_4_ = lean_string_utf8_byte_size(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__3(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__0));
v___x_6_ = lean_string_utf8_byte_size(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks(lean_object* v_prior_7_, lean_object* v_current_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_9_ = lean_string_utf8_byte_size(v_prior_7_);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_nat_dec_eq(v___x_9_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; uint8_t v___x_13_; 
v___x_12_ = lean_string_utf8_byte_size(v_current_8_);
v___x_13_ = lean_nat_dec_eq(v___x_12_, v___x_10_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; uint8_t v___y_19_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_14_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__0));
v___x_28_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__3, &l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__3_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__3);
v___x_29_ = lean_nat_dec_le(v___x_28_, v___x_9_);
if (v___x_29_ == 0)
{
v___y_19_ = v___x_13_;
goto v___jp_18_;
}
else
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = lean_nat_sub(v___x_9_, v___x_28_);
v___x_31_ = lean_string_memcmp(v_prior_7_, v___x_14_, v___x_30_, v___x_10_, v___x_28_);
lean_dec(v___x_30_);
v___y_19_ = v___x_31_;
goto v___jp_18_;
}
v___jp_15_:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_string_append(v_prior_7_, v___x_14_);
v___x_17_ = lean_string_append(v___x_16_, v_current_8_);
return v___x_17_;
}
v___jp_18_:
{
if (v___y_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_20_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_21_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2);
v___x_22_ = lean_nat_dec_le(v___x_21_, v___x_9_);
if (v___x_22_ == 0)
{
goto v___jp_15_;
}
else
{
lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_nat_sub(v___x_9_, v___x_21_);
v___x_24_ = lean_string_memcmp(v_prior_7_, v___x_20_, v___x_23_, v___x_10_, v___x_21_);
lean_dec(v___x_23_);
if (v___x_24_ == 0)
{
goto v___jp_15_;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_string_append(v_prior_7_, v___x_20_);
v___x_26_ = lean_string_append(v___x_25_, v_current_8_);
return v___x_26_;
}
}
}
else
{
lean_object* v___x_27_; 
v___x_27_ = lean_string_append(v_prior_7_, v_current_8_);
return v___x_27_;
}
}
}
else
{
return v_prior_7_;
}
}
else
{
lean_dec_ref(v_prior_7_);
lean_inc_ref(v_current_8_);
return v_current_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___boxed(lean_object* v_prior_32_, lean_object* v_current_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks(v_prior_32_, v_current_33_);
lean_dec_ref(v_current_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0(lean_object* v_as_37_, size_t v_i_38_, size_t v_stop_39_, lean_object* v_b_40_){
_start:
{
uint8_t v___x_41_; 
v___x_41_ = lean_usize_dec_eq(v_i_38_, v_stop_39_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; lean_object* v_fst_43_; lean_object* v_snd_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; size_t v___x_53_; size_t v___x_54_; 
v___x_42_ = lean_array_uget_borrowed(v_as_37_, v_i_38_);
v_fst_43_ = lean_ctor_get(v___x_42_, 0);
v_snd_44_ = lean_ctor_get(v___x_42_, 1);
v___x_45_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0___closed__0));
v___x_46_ = lean_string_append(v___x_45_, v_fst_43_);
v___x_47_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0___closed__1));
v___x_48_ = lean_string_append(v___x_46_, v___x_47_);
v___x_49_ = lean_string_append(v___x_48_, v_snd_44_);
v___x_50_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__0));
v___x_51_ = lean_string_append(v___x_49_, v___x_50_);
v___x_52_ = lean_string_append(v_b_40_, v___x_51_);
lean_dec_ref(v___x_51_);
v___x_53_ = ((size_t)1ULL);
v___x_54_ = lean_usize_add(v_i_38_, v___x_53_);
v_i_38_ = v___x_54_;
v_b_40_ = v___x_52_;
goto _start;
}
else
{
return v_b_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0___boxed(lean_object* v_as_56_, lean_object* v_i_57_, lean_object* v_stop_58_, lean_object* v_b_59_){
_start:
{
size_t v_i_boxed_60_; size_t v_stop_boxed_61_; lean_object* v_res_62_; 
v_i_boxed_60_ = lean_unbox_usize(v_i_57_);
lean_dec(v_i_57_);
v_stop_boxed_61_ = lean_unbox_usize(v_stop_58_);
lean_dec(v_stop_58_);
v_res_62_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0(v_as_56_, v_i_boxed_60_, v_stop_boxed_61_, v_b_59_);
lean_dec_ref(v_as_56_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock(lean_object* v_state_66_){
_start:
{
lean_object* v_priorBlocks_67_; lean_object* v_currentBlock_68_; lean_object* v_footnotes_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_95_; 
v_priorBlocks_67_ = lean_ctor_get(v_state_66_, 0);
v_currentBlock_68_ = lean_ctor_get(v_state_66_, 1);
v_footnotes_69_ = lean_ctor_get(v_state_66_, 2);
v_isSharedCheck_95_ = !lean_is_exclusive(v_state_66_);
if (v_isSharedCheck_95_ == 0)
{
v___x_71_ = v_state_66_;
v_isShared_72_ = v_isSharedCheck_95_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_footnotes_69_);
lean_inc(v_currentBlock_68_);
lean_inc(v_priorBlocks_67_);
lean_dec(v_state_66_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_95_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___y_75_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_73_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks(v_priorBlocks_67_, v_currentBlock_68_);
lean_dec_ref(v_currentBlock_68_);
v___x_82_ = lean_array_get_size(v_footnotes_69_);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_nat_dec_eq(v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__0));
v___x_86_ = lean_nat_dec_lt(v___x_83_, v___x_82_);
if (v___x_86_ == 0)
{
lean_dec_ref(v_footnotes_69_);
v___y_75_ = v___x_85_;
goto v___jp_74_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = lean_nat_dec_le(v___x_82_, v___x_82_);
if (v___x_87_ == 0)
{
if (v___x_86_ == 0)
{
lean_dec_ref(v_footnotes_69_);
v___y_75_ = v___x_85_;
goto v___jp_74_;
}
else
{
size_t v___x_88_; size_t v___x_89_; lean_object* v___x_90_; 
v___x_88_ = ((size_t)0ULL);
v___x_89_ = lean_usize_of_nat(v___x_82_);
v___x_90_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0(v_footnotes_69_, v___x_88_, v___x_89_, v___x_85_);
lean_dec_ref(v_footnotes_69_);
v___y_75_ = v___x_90_;
goto v___jp_74_;
}
}
else
{
size_t v___x_91_; size_t v___x_92_; lean_object* v___x_93_; 
v___x_91_ = ((size_t)0ULL);
v___x_92_ = lean_usize_of_nat(v___x_82_);
v___x_93_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock_spec__0(v_footnotes_69_, v___x_91_, v___x_92_, v___x_85_);
lean_dec_ref(v_footnotes_69_);
v___y_75_ = v___x_93_;
goto v___jp_74_;
}
}
}
else
{
lean_object* v___x_94_; 
lean_dec_ref(v_footnotes_69_);
v___x_94_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___y_75_ = v___x_94_;
goto v___jp_74_;
}
v___jp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_76_ = lean_string_append(v___x_73_, v___y_75_);
lean_dec_ref(v___y_75_);
v___x_77_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_78_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__1));
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 2, v___x_78_);
lean_ctor_set(v___x_71_, 1, v___x_77_);
lean_ctor_set(v___x_71_, 0, v___x_76_);
v___x_80_ = v___x_71_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_76_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(lean_object* v_state_96_){
_start:
{
lean_object* v___x_97_; lean_object* v_priorBlocks_98_; 
v___x_97_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock(v_state_96_);
v_priorBlocks_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_priorBlocks_98_);
lean_dec_ref(v___x_97_);
return v_priorBlocks_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_push(lean_object* v_state_99_, lean_object* v_txt_100_){
_start:
{
lean_object* v_priorBlocks_101_; lean_object* v_currentBlock_102_; lean_object* v_footnotes_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_111_; 
v_priorBlocks_101_ = lean_ctor_get(v_state_99_, 0);
v_currentBlock_102_ = lean_ctor_get(v_state_99_, 1);
v_footnotes_103_ = lean_ctor_get(v_state_99_, 2);
v_isSharedCheck_111_ = !lean_is_exclusive(v_state_99_);
if (v_isSharedCheck_111_ == 0)
{
v___x_105_ = v_state_99_;
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_footnotes_103_);
lean_inc(v_currentBlock_102_);
lean_inc(v_priorBlocks_101_);
lean_dec(v_state_99_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_string_append(v_currentBlock_102_, v_txt_100_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v___x_107_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_priorBlocks_101_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_110_, 2, v_footnotes_103_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_push___boxed(lean_object* v_state_112_, lean_object* v_txt_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_push(v_state_112_, v_txt_113_);
lean_dec_ref(v_txt_113_);
return v_res_114_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endsWith(lean_object* v_state_115_, lean_object* v_txt_116_){
_start:
{
lean_object* v_priorBlocks_117_; lean_object* v_currentBlock_118_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_priorBlocks_117_ = lean_ctor_get(v_state_115_, 0);
v_currentBlock_118_ = lean_ctor_get(v_state_115_, 1);
v___x_128_ = lean_string_utf8_byte_size(v_currentBlock_118_);
v___x_129_ = lean_string_utf8_byte_size(v_txt_116_);
v___x_130_ = lean_nat_dec_le(v___x_129_, v___x_128_);
if (v___x_130_ == 0)
{
goto v___jp_119_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_nat_sub(v___x_128_, v___x_129_);
v___x_133_ = lean_string_memcmp(v_currentBlock_118_, v_txt_116_, v___x_132_, v___x_131_, v___x_129_);
lean_dec(v___x_132_);
if (v___x_133_ == 0)
{
goto v___jp_119_;
}
else
{
return v___x_133_;
}
}
v___jp_119_:
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_string_utf8_byte_size(v_currentBlock_118_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_nat_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
return v___x_122_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_string_utf8_byte_size(v_priorBlocks_117_);
v___x_124_ = lean_string_utf8_byte_size(v_txt_116_);
v___x_125_ = lean_nat_dec_le(v___x_124_, v___x_123_);
if (v___x_125_ == 0)
{
return v___x_125_;
}
else
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_nat_sub(v___x_123_, v___x_124_);
v___x_127_ = lean_string_memcmp(v_priorBlocks_117_, v_txt_116_, v___x_126_, v___x_121_, v___x_124_);
lean_dec(v___x_126_);
return v___x_127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endsWith___boxed(lean_object* v_state_134_, lean_object* v_txt_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endsWith(v_state_134_, v_txt_135_);
lean_dec_ref(v_txt_135_);
lean_dec_ref(v_state_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run___redArg(lean_object* v_act_138_, lean_object* v_context_139_, lean_object* v_state_140_){
_start:
{
lean_object* v___x_141_; lean_object* v_fst_142_; lean_object* v_snd_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_151_; 
v___x_141_ = lean_apply_2(v_act_138_, v_context_139_, v_state_140_);
v_fst_142_ = lean_ctor_get(v___x_141_, 0);
v_snd_143_ = lean_ctor_get(v___x_141_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_151_ == 0)
{
v___x_145_ = v___x_141_;
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_snd_143_);
lean_inc(v_fst_142_);
lean_dec(v___x_141_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(v_snd_143_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_147_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_fst_142_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run(lean_object* v_00_u03b1_152_, lean_object* v_act_153_, lean_object* v_context_154_, lean_object* v_state_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Doc_MarkdownM_run___redArg(v_act_153_, v_context_154_, v_state_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run_x27(lean_object* v_act_157_, lean_object* v_context_158_, lean_object* v_state_159_){
_start:
{
lean_object* v___x_160_; lean_object* v_snd_161_; 
v___x_160_ = l_Lean_Doc_MarkdownM_run___redArg(v_act_157_, v_context_158_, v_state_159_);
v_snd_161_ = lean_ctor_get(v___x_160_, 1);
lean_inc(v_snd_161_);
lean_dec_ref(v___x_160_);
return v_snd_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_push___redArg(lean_object* v_txt_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_box(0);
v___x_165_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_push(v_a_163_, v_txt_162_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_push___redArg___boxed(lean_object* v_txt_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Doc_MarkdownM_push___redArg(v_txt_167_, v_a_168_);
lean_dec_ref(v_txt_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_push(lean_object* v_txt_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Doc_MarkdownM_push___redArg(v_txt_170_, v_a_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_push___boxed(lean_object* v_txt_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Doc_MarkdownM_push(v_txt_174_, v_a_175_, v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec_ref(v_txt_174_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endsWith___redArg(lean_object* v_txt_178_, lean_object* v_a_179_){
_start:
{
uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endsWith(v_a_179_, v_txt_178_);
v___x_181_ = lean_box(v___x_180_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_a_179_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endsWith___redArg___boxed(lean_object* v_txt_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v_txt_183_, v_a_184_);
lean_dec_ref(v_txt_183_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endsWith(lean_object* v_txt_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v_txt_186_, v_a_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endsWith___boxed(lean_object* v_txt_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Doc_MarkdownM_endsWith(v_txt_190_, v_a_191_, v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec_ref(v_txt_190_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endBlock___redArg(lean_object* v_a_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_box(0);
v___x_196_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock(v_a_194_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endBlock(lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_a_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_endBlock___boxed(lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Doc_MarkdownM_endBlock(v_a_201_, v_a_202_);
lean_dec_ref(v_a_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_indent___redArg(lean_object* v_x_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
uint8_t v_inEmph_208_; uint8_t v_inBold_209_; uint8_t v_inLink_210_; lean_object* v_linePrefix_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_inEmph_208_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*1);
v_inBold_209_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*1 + 1);
v_inLink_210_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*1 + 2);
v_linePrefix_211_ = lean_ctor_get(v_a_206_, 0);
lean_inc_ref(v_linePrefix_211_);
lean_dec_ref(v_a_206_);
v___x_212_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_213_ = lean_string_append(v_linePrefix_211_, v___x_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1, v_inEmph_208_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1 + 1, v_inBold_209_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1 + 2, v_inLink_210_);
v___x_215_ = lean_apply_2(v_x_205_, v___x_214_, v_a_207_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_indent(lean_object* v_00_u03b1_216_, lean_object* v_x_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v___x_220_; 
lean_inc_ref(v_a_218_);
v___x_220_ = l_Lean_Doc_MarkdownM_indent___redArg(v_x_217_, v_a_218_, v_a_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_indent___boxed(lean_object* v_00_u03b1_221_, lean_object* v_x_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Doc_MarkdownM_indent(v_00_u03b1_221_, v_x_222_, v_a_223_, v_a_224_);
lean_dec_ref(v_a_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object* v_a_226_, uint8_t v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
uint8_t v_a_15__boxed_236_; lean_object* v_res_237_; 
v_a_15__boxed_236_ = lean_unbox(v_a_232_);
v_res_237_ = l_Lean_Doc_instMarkdownInlineEmpty___lam__0(v_a_231_, v_a_15__boxed_236_, v_a_233_, v_a_234_, v_a_235_);
lean_dec_ref(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec_ref(v_a_231_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0(lean_object* v_a_240_, lean_object* v_a_241_, uint8_t v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed(lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
uint8_t v_a_19__boxed_252_; lean_object* v_res_253_; 
v_a_19__boxed_252_ = lean_unbox(v_a_248_);
v_res_253_ = l_Lean_Doc_instMarkdownBlockEmpty___lam__0(v_a_246_, v_a_247_, v_a_19__boxed_252_, v_a_249_, v_a_250_, v_a_251_);
lean_dec_ref(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec_ref(v_a_247_);
lean_dec_ref(v_a_246_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object* v_i_255_){
_start:
{
lean_object* v___f_256_; 
v___f_256_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___closed__0));
return v___f_256_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(lean_object* v_s_257_, uint32_t v_c_258_, lean_object* v_a_259_, uint8_t v_b_260_){
_start:
{
lean_object* v_str_261_; lean_object* v_startInclusive_262_; lean_object* v_endExclusive_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_str_261_ = lean_ctor_get(v_s_257_, 0);
v_startInclusive_262_ = lean_ctor_get(v_s_257_, 1);
v_endExclusive_263_ = lean_ctor_get(v_s_257_, 2);
v___x_264_ = lean_nat_sub(v_endExclusive_263_, v_startInclusive_262_);
v___x_265_ = lean_nat_dec_eq(v_a_259_, v___x_264_);
lean_dec(v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; uint32_t v___x_267_; uint8_t v___x_268_; 
v___x_266_ = lean_nat_add(v_startInclusive_262_, v_a_259_);
lean_dec(v_a_259_);
v___x_267_ = lean_string_utf8_get_fast(v_str_261_, v___x_266_);
v___x_268_ = lean_uint32_dec_eq(v___x_267_, v_c_258_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_string_utf8_next_fast(v_str_261_, v___x_266_);
lean_dec(v___x_266_);
v___x_270_ = lean_nat_sub(v___x_269_, v_startInclusive_262_);
v_a_259_ = v___x_270_;
v_b_260_ = v___x_268_;
goto _start;
}
else
{
lean_dec(v___x_266_);
return v___x_268_;
}
}
else
{
lean_dec(v_a_259_);
return v_b_260_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg___boxed(lean_object* v_s_272_, lean_object* v_c_273_, lean_object* v_a_274_, lean_object* v_b_275_){
_start:
{
uint32_t v_c_boxed_276_; uint8_t v_b_boxed_277_; uint8_t v_res_278_; lean_object* v_r_279_; 
v_c_boxed_276_ = lean_unbox_uint32(v_c_273_);
lean_dec(v_c_273_);
v_b_boxed_277_ = lean_unbox(v_b_275_);
v_res_278_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(v_s_272_, v_c_boxed_276_, v_a_274_, v_b_boxed_277_);
lean_dec_ref(v_s_272_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0(uint32_t v_c_280_, lean_object* v_s_281_){
_start:
{
lean_object* v_searcher_282_; uint8_t v___x_283_; uint8_t v___x_284_; 
v_searcher_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = 0;
v___x_284_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(v_s_281_, v_c_280_, v_searcher_282_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0___boxed(lean_object* v_c_285_, lean_object* v_s_286_){
_start:
{
uint32_t v_c_boxed_287_; uint8_t v_res_288_; lean_object* v_r_289_; 
v_c_boxed_287_ = lean_unbox_uint32(v_c_285_);
lean_dec(v_c_285_);
v_res_288_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0(v_c_boxed_287_, v_s_286_);
lean_dec_ref(v_s_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__0));
v___x_292_ = lean_string_utf8_byte_size(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_293_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__0));
v___x_296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_294_);
lean_ctor_set(v___x_296_, 2, v___x_293_);
return v___x_296_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial(uint32_t v_c_297_){
_start:
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2);
v___x_299_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0(v_c_297_, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___boxed(lean_object* v_c_300_){
_start:
{
uint32_t v_c_boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_c_boxed_301_ = lean_unbox_uint32(v_c_300_);
lean_dec(v_c_300_);
v_res_302_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial(v_c_boxed_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0(lean_object* v_s_304_, uint32_t v_c_305_, lean_object* v_inst_306_, lean_object* v_R_307_, lean_object* v_a_308_, uint8_t v_b_309_, lean_object* v_c_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(v_s_304_, v_c_305_, v_a_308_, v_b_309_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___boxed(lean_object* v_s_312_, lean_object* v_c_313_, lean_object* v_inst_314_, lean_object* v_R_315_, lean_object* v_a_316_, lean_object* v_b_317_, lean_object* v_c_318_){
_start:
{
uint32_t v_c_boxed_319_; uint8_t v_b_boxed_320_; uint8_t v_res_321_; lean_object* v_r_322_; 
v_c_boxed_319_ = lean_unbox_uint32(v_c_313_);
lean_dec(v_c_313_);
v_b_boxed_320_ = lean_unbox(v_b_317_);
v_res_321_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0(v_s_312_, v_c_boxed_319_, v_inst_314_, v_R_315_, v_a_316_, v_b_boxed_320_, v_c_318_);
lean_dec_ref(v_s_312_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object* v_s_323_, lean_object* v_b_324_){
_start:
{
lean_object* v_fst_325_; lean_object* v_snd_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_347_; 
v_fst_325_ = lean_ctor_get(v_b_324_, 0);
v_snd_326_ = lean_ctor_get(v_b_324_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_b_324_);
if (v_isSharedCheck_347_ == 0)
{
v___x_328_ = v_b_324_;
v_isShared_329_ = v_isSharedCheck_347_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_snd_326_);
lean_inc(v_fst_325_);
lean_dec(v_b_324_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_347_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_string_utf8_byte_size(v_s_323_);
v___x_331_ = lean_nat_dec_eq(v_snd_326_, v___x_330_);
if (v___x_331_ == 0)
{
uint32_t v_c_332_; lean_object* v_iter_333_; lean_object* v_s_x27_335_; uint8_t v___x_341_; 
v_c_332_ = lean_string_utf8_get_fast(v_s_323_, v_snd_326_);
v_iter_333_ = lean_string_utf8_next_fast(v_s_323_, v_snd_326_);
lean_dec(v_snd_326_);
v___x_341_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial(v_c_332_);
if (v___x_341_ == 0)
{
v_s_x27_335_ = v_fst_325_;
goto v___jp_334_;
}
else
{
uint32_t v___x_342_; lean_object* v_s_x27_343_; 
v___x_342_ = 92;
v_s_x27_343_ = lean_string_push(v_fst_325_, v___x_342_);
v_s_x27_335_ = v_s_x27_343_;
goto v___jp_334_;
}
v___jp_334_:
{
lean_object* v_s_x27_336_; lean_object* v___x_338_; 
v_s_x27_336_ = lean_string_push(v_s_x27_335_, v_c_332_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v_iter_333_);
lean_ctor_set(v___x_328_, 0, v_s_x27_336_);
v___x_338_ = v___x_328_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_s_x27_336_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_iter_333_);
v___x_338_ = v_reuseFailAlloc_340_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
v_b_324_ = v___x_338_;
goto _start;
}
}
}
else
{
lean_object* v___x_345_; 
if (v_isShared_329_ == 0)
{
v___x_345_ = v___x_328_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_fst_325_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_snd_326_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object* v_s_348_, lean_object* v_b_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_348_, v_b_349_);
lean_dec_ref(v_s_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object* v_s_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_fst_357_; 
v___x_355_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0));
v___x_356_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_354_, v___x_355_);
v_fst_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_fst_357_);
lean_dec_ref(v___x_356_);
return v_fst_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object* v_s_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_358_);
lean_dec_ref(v_s_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0(lean_object* v_str_360_, lean_object* v_b_361_){
_start:
{
lean_object* v_snd_362_; lean_object* v_fst_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_405_; 
v_snd_362_ = lean_ctor_get(v_b_361_, 1);
v_fst_363_ = lean_ctor_get(v_b_361_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v_b_361_);
if (v_isSharedCheck_405_ == 0)
{
v___x_365_ = v_b_361_;
v_isShared_366_ = v_isSharedCheck_405_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_snd_362_);
lean_inc(v_fst_363_);
lean_dec(v_b_361_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_405_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v_fst_367_; lean_object* v_snd_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_404_; 
v_fst_367_ = lean_ctor_get(v_snd_362_, 0);
v_snd_368_ = lean_ctor_get(v_snd_362_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_snd_362_);
if (v_isSharedCheck_404_ == 0)
{
v___x_370_ = v_snd_362_;
v_isShared_371_ = v_isSharedCheck_404_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_snd_368_);
lean_inc(v_fst_367_);
lean_dec(v_snd_362_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_404_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_string_utf8_byte_size(v_str_360_);
v___x_373_ = lean_nat_dec_eq(v_snd_368_, v___x_372_);
if (v___x_373_ == 0)
{
uint32_t v_c_374_; lean_object* v_iter_375_; uint32_t v___x_376_; uint8_t v___x_377_; 
v_c_374_ = lean_string_utf8_get_fast(v_str_360_, v_snd_368_);
v_iter_375_ = lean_string_utf8_next_fast(v_str_360_, v_snd_368_);
lean_dec(v_snd_368_);
v___x_376_ = 96;
v___x_377_ = lean_uint32_dec_eq(v_c_374_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v_current_378_; lean_object* v___y_380_; uint8_t v___x_388_; 
v_current_378_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_nat_dec_le(v_fst_363_, v_fst_367_);
if (v___x_388_ == 0)
{
lean_dec(v_fst_367_);
v___y_380_ = v_fst_363_;
goto v___jp_379_;
}
else
{
lean_dec(v_fst_363_);
v___y_380_ = v_fst_367_;
goto v___jp_379_;
}
v___jp_379_:
{
lean_object* v___x_382_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 1, v_iter_375_);
lean_ctor_set(v___x_370_, 0, v_current_378_);
v___x_382_ = v___x_370_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_current_378_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_iter_375_);
v___x_382_ = v_reuseFailAlloc_387_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_384_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v___x_382_);
lean_ctor_set(v___x_365_, 0, v___y_380_);
v___x_384_ = v___x_365_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___y_380_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v___x_382_);
v___x_384_ = v_reuseFailAlloc_386_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
v_b_361_ = v___x_384_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_389_; lean_object* v_current_390_; lean_object* v___x_392_; 
v___x_389_ = lean_unsigned_to_nat(1u);
v_current_390_ = lean_nat_add(v_fst_367_, v___x_389_);
lean_dec(v_fst_367_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 1, v_iter_375_);
lean_ctor_set(v___x_370_, 0, v_current_390_);
v___x_392_ = v___x_370_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_current_390_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_iter_375_);
v___x_392_ = v_reuseFailAlloc_397_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v___x_392_);
v___x_394_ = v___x_365_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_fst_363_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_392_);
v___x_394_ = v_reuseFailAlloc_396_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
v_b_361_ = v___x_394_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_399_; 
if (v_isShared_371_ == 0)
{
v___x_399_ = v___x_370_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_fst_367_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_snd_368_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v___x_399_);
v___x_401_ = v___x_365_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_fst_363_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0___boxed(lean_object* v_str_406_, lean_object* v_b_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0(v_str_406_, v_b_407_);
lean_dec_ref(v_str_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__1(lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
lean_object* v_zero_411_; uint8_t v_isZero_412_; 
v_zero_411_ = lean_unsigned_to_nat(0u);
v_isZero_412_ = lean_nat_dec_eq(v_x_409_, v_zero_411_);
if (v_isZero_412_ == 1)
{
lean_dec(v_x_409_);
return v_x_410_;
}
else
{
uint32_t v___x_413_; lean_object* v_one_414_; lean_object* v_n_415_; lean_object* v___x_416_; 
v___x_413_ = 96;
v_one_414_ = lean_unsigned_to_nat(1u);
v_n_415_ = lean_nat_sub(v_x_409_, v_one_414_);
lean_dec(v_x_409_);
v___x_416_ = lean_string_push(v_x_410_, v___x_413_);
v_x_409_ = v_n_415_;
v_x_410_ = v___x_416_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_421_ = lean_string_utf8_byte_size(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object* v_str_427_){
_start:
{
lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_434_; lean_object* v_current_438_; lean_object* v___y_440_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_snd_449_; lean_object* v_fst_450_; lean_object* v_fst_451_; lean_object* v___x_452_; lean_object* v___y_454_; uint8_t v___x_463_; 
v_current_438_ = lean_unsigned_to_nat(0u);
v___x_447_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__4));
v___x_448_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0(v_str_427_, v___x_447_);
v_snd_449_ = lean_ctor_get(v___x_448_, 1);
lean_inc(v_snd_449_);
v_fst_450_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_fst_450_);
lean_dec_ref(v___x_448_);
v_fst_451_ = lean_ctor_get(v_snd_449_, 0);
lean_inc(v_fst_451_);
lean_dec(v_snd_449_);
v___x_452_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_463_ = lean_nat_dec_le(v_fst_450_, v_fst_451_);
if (v___x_463_ == 0)
{
lean_dec(v_fst_451_);
v___y_454_ = v_fst_450_;
goto v___jp_453_;
}
else
{
lean_dec(v_fst_450_);
v___y_454_ = v_fst_451_;
goto v___jp_453_;
}
v___jp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_inc_ref(v___y_429_);
v___x_431_ = lean_string_append(v___y_429_, v___y_430_);
lean_dec_ref(v___y_430_);
v___x_432_ = lean_string_append(v___x_431_, v___y_429_);
lean_dec_ref(v___y_429_);
return v___x_432_;
}
v___jp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_436_ = lean_string_append(v___x_435_, v_str_427_);
lean_dec_ref(v_str_427_);
v___x_437_ = lean_string_append(v___x_436_, v___x_435_);
v___y_429_ = v___y_434_;
v___y_430_ = v___x_437_;
goto v___jp_428_;
}
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_441_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_442_ = lean_string_utf8_byte_size(v_str_427_);
v___x_443_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2);
v___x_444_ = lean_nat_dec_le(v___x_443_, v___x_442_);
if (v___x_444_ == 0)
{
v___y_429_ = v___y_440_;
v___y_430_ = v_str_427_;
goto v___jp_428_;
}
else
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_nat_sub(v___x_442_, v___x_443_);
v___x_446_ = lean_string_memcmp(v_str_427_, v___x_441_, v___x_445_, v_current_438_, v___x_443_);
lean_dec(v___x_445_);
if (v___x_446_ == 0)
{
v___y_429_ = v___y_440_;
v___y_430_ = v_str_427_;
goto v___jp_428_;
}
else
{
v___y_434_ = v___y_440_;
goto v___jp_433_;
}
}
}
v___jp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_add(v___y_454_, v___x_455_);
lean_dec(v___y_454_);
v___x_457_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__1(v___x_456_, v___x_452_);
v___x_458_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_459_ = lean_string_utf8_byte_size(v_str_427_);
v___x_460_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2);
v___x_461_ = lean_nat_dec_le(v___x_460_, v___x_459_);
if (v___x_461_ == 0)
{
v___y_440_ = v___x_457_;
goto v___jp_439_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = lean_string_memcmp(v_str_427_, v___x_458_, v_current_438_, v_current_438_, v___x_460_);
if (v___x_462_ == 0)
{
v___y_440_ = v___x_457_;
goto v___jp_439_;
}
else
{
v___y_434_ = v___x_457_;
goto v___jp_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_464_, lean_object* v_pos_465_){
_start:
{
lean_object* v_str_466_; lean_object* v_startInclusive_467_; lean_object* v_endExclusive_468_; lean_object* v___x_469_; uint8_t v___y_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v_str_466_ = lean_ctor_get(v_s_464_, 0);
v_startInclusive_467_ = lean_ctor_get(v_s_464_, 1);
v_endExclusive_468_ = lean_ctor_get(v_s_464_, 2);
v___x_469_ = lean_nat_add(v_startInclusive_467_, v_pos_465_);
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_nat_sub(v_endExclusive_468_, v___x_469_);
v___x_480_ = lean_nat_dec_eq(v___x_478_, v___x_479_);
lean_dec(v___x_479_);
if (v___x_480_ == 0)
{
uint32_t v___x_481_; uint8_t v___y_483_; uint32_t v___x_488_; uint8_t v___x_489_; 
v___x_481_ = lean_string_utf8_get_fast(v_str_466_, v___x_469_);
v___x_488_ = 32;
v___x_489_ = lean_uint32_dec_eq(v___x_481_, v___x_488_);
if (v___x_489_ == 0)
{
uint32_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = 9;
v___x_491_ = lean_uint32_dec_eq(v___x_481_, v___x_490_);
v___y_483_ = v___x_491_;
goto v___jp_482_;
}
else
{
v___y_483_ = v___x_489_;
goto v___jp_482_;
}
v___jp_482_:
{
if (v___y_483_ == 0)
{
uint32_t v___x_484_; uint8_t v___x_485_; 
v___x_484_ = 13;
v___x_485_ = lean_uint32_dec_eq(v___x_481_, v___x_484_);
if (v___x_485_ == 0)
{
uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = 10;
v___x_487_ = lean_uint32_dec_eq(v___x_481_, v___x_486_);
v___y_477_ = v___x_487_;
goto v___jp_476_;
}
else
{
v___y_477_ = v___x_485_;
goto v___jp_476_;
}
}
else
{
goto v___jp_470_;
}
}
}
else
{
lean_dec(v___x_469_);
return v_pos_465_;
}
v___jp_470_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_471_ = lean_string_utf8_next_fast(v_str_466_, v___x_469_);
v___x_472_ = lean_nat_sub(v___x_471_, v___x_469_);
lean_dec(v___x_469_);
v___x_473_ = lean_nat_add(v_pos_465_, v___x_472_);
lean_dec(v___x_472_);
v___x_474_ = l_String_instDecidableLtRaw___aux__1(v_pos_465_, v___x_473_);
if (v___x_474_ == 0)
{
lean_dec(v___x_473_);
return v_pos_465_;
}
else
{
lean_dec(v_pos_465_);
v_pos_465_ = v___x_473_;
goto _start;
}
}
v___jp_476_:
{
if (v___y_477_ == 0)
{
lean_dec(v___x_469_);
return v_pos_465_;
}
else
{
goto v___jp_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object* v_s_492_, lean_object* v_pos_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_492_, v_pos_493_);
lean_dec_ref(v_s_492_);
return v_res_494_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Doc_Inline_empty(lean_box(0));
return v___x_495_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_497_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v___x_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object* v_a_499_){
_start:
{
if (lean_obj_tag(v_a_499_) == 0)
{
lean_object* v___x_500_; 
v___x_500_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
return v___x_500_;
}
else
{
lean_object* v_head_501_; 
v_head_501_ = lean_ctor_get(v_a_499_, 0);
lean_inc(v_head_501_);
switch(lean_obj_tag(v_head_501_))
{
case 0:
{
lean_object* v_tail_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_549_; 
v_tail_502_ = lean_ctor_get(v_a_499_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_a_499_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v_a_499_, 0);
lean_dec(v_unused_550_);
v___x_504_ = v_a_499_;
v_isShared_505_ = v_isSharedCheck_549_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_tail_502_);
lean_dec(v_a_499_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_549_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_string_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_548_; 
v_string_506_ = lean_ctor_get(v_head_501_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_head_501_);
if (v_isSharedCheck_548_ == 0)
{
v___x_508_ = v_head_501_;
v_isShared_509_ = v_isSharedCheck_548_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_string_506_);
lean_dec(v_head_501_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_548_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_string_utf8_byte_size(v_string_506_);
lean_inc_ref(v_string_506_);
v___x_512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_512_, 0, v_string_506_);
lean_ctor_set(v___x_512_, 1, v___x_510_);
lean_ctor_set(v___x_512_, 2, v___x_511_);
v___x_513_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_512_, v___x_510_);
v___x_514_ = lean_nat_sub(v___x_511_, v___x_513_);
v___x_515_ = lean_nat_dec_eq(v___x_514_, v___x_510_);
lean_dec(v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v_s1_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v_s2_519_; lean_object* v___x_521_; 
v_s1_516_ = lean_string_utf8_extract(v_string_506_, v___x_510_, v___x_513_);
lean_dec(v___x_513_);
v___x_517_ = lean_string_length(v_s1_516_);
v___x_518_ = l_String_Slice_Pos_nextn(v___x_512_, v___x_510_, v___x_517_);
lean_dec_ref(v___x_512_);
v_s2_519_ = lean_string_utf8_extract(v_string_506_, v___x_518_, v___x_511_);
lean_dec(v___x_518_);
lean_dec_ref(v_string_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v_s2_519_);
v___x_521_ = v___x_508_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_s2_519_);
v___x_521_ = v_reuseFailAlloc_536_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = lean_array_mk(v_tail_502_);
v___x_523_ = lean_array_get_size(v___x_522_);
v___x_524_ = lean_nat_dec_eq(v___x_523_, v___x_510_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_mk_empty_array_with_capacity(v___x_525_);
v___x_527_ = lean_array_push(v___x_526_, v___x_521_);
v___x_528_ = l_Array_append___redArg(v___x_527_, v___x_522_);
lean_dec_ref(v___x_522_);
v___x_529_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 0);
lean_ctor_set(v___x_504_, 1, v___x_529_);
lean_ctor_set(v___x_504_, 0, v_s1_516_);
v___x_531_ = v___x_504_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_s1_516_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
else
{
lean_object* v___x_534_; 
lean_dec_ref(v___x_522_);
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 0);
lean_ctor_set(v___x_504_, 1, v___x_521_);
lean_ctor_set(v___x_504_, 0, v_s1_516_);
v___x_534_ = v___x_504_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_s1_516_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_521_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v___x_537_; lean_object* v_fst_538_; lean_object* v_snd_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_547_; 
lean_dec(v___x_513_);
lean_dec_ref(v___x_512_);
lean_del_object(v___x_508_);
lean_del_object(v___x_504_);
v___x_537_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_502_);
v_fst_538_ = lean_ctor_get(v___x_537_, 0);
v_snd_539_ = lean_ctor_get(v___x_537_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_547_ == 0)
{
v___x_541_ = v___x_537_;
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_snd_539_);
lean_inc(v_fst_538_);
lean_dec(v___x_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = lean_string_append(v_string_506_, v_fst_538_);
lean_dec(v_fst_538_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_snd_539_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_551_; lean_object* v_content_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_tail_551_ = lean_ctor_get(v_a_499_, 1);
lean_inc(v_tail_551_);
lean_dec_ref(v_a_499_);
v_content_552_ = lean_ctor_get(v_head_501_, 0);
lean_inc_ref(v_content_552_);
lean_dec_ref(v_head_501_);
v___x_553_ = lean_array_to_list(v_content_552_);
v___x_554_ = l_List_appendTR___redArg(v___x_553_, v_tail_551_);
v_a_499_ = v___x_554_;
goto _start;
}
default: 
{
lean_object* v_tail_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_594_; 
v_tail_556_ = lean_ctor_get(v_a_499_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_a_499_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_a_499_, 0);
lean_dec(v_unused_595_);
v___x_558_ = v_a_499_;
v_isShared_559_ = v_isSharedCheck_594_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_tail_556_);
lean_dec(v_a_499_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_594_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_561_ = lean_array_mk(v_tail_556_);
if (lean_obj_tag(v_head_501_) == 9)
{
lean_object* v_content_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_content_562_ = lean_ctor_get(v_head_501_, 0);
v___x_563_ = lean_array_get_size(v_content_562_);
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_nat_dec_eq(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_array_get_size(v___x_561_);
v___x_567_ = lean_nat_dec_eq(v___x_566_, v___x_564_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
lean_inc_ref(v_content_562_);
lean_dec_ref(v_head_501_);
v___x_568_ = l_Array_append___redArg(v_content_562_, v___x_561_);
lean_dec_ref(v___x_561_);
v___x_569_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
if (v_isShared_559_ == 0)
{
lean_ctor_set_tag(v___x_558_, 0);
lean_ctor_set(v___x_558_, 1, v___x_569_);
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_571_ = v___x_558_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
else
{
lean_object* v___x_574_; 
lean_dec_ref(v___x_561_);
if (v_isShared_559_ == 0)
{
lean_ctor_set_tag(v___x_558_, 0);
lean_ctor_set(v___x_558_, 1, v_head_501_);
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_574_ = v___x_558_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_head_501_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_578_; 
lean_dec_ref(v_head_501_);
v___x_576_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_561_);
if (v_isShared_559_ == 0)
{
lean_ctor_set_tag(v___x_558_, 0);
lean_ctor_set(v___x_558_, 1, v___x_576_);
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_578_ = v___x_558_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_array_get_size(v___x_561_);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_nat_dec_eq(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_mk_empty_array_with_capacity(v___x_583_);
v___x_585_ = lean_array_push(v___x_584_, v_head_501_);
v___x_586_ = l_Array_append___redArg(v___x_585_, v___x_561_);
lean_dec_ref(v___x_561_);
v___x_587_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
if (v_isShared_559_ == 0)
{
lean_ctor_set_tag(v___x_558_, 0);
lean_ctor_set(v___x_558_, 1, v___x_587_);
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_589_ = v___x_558_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
else
{
lean_object* v___x_592_; 
lean_dec_ref(v___x_561_);
if (v_isShared_559_ == 0)
{
lean_ctor_set_tag(v___x_558_, 0);
lean_ctor_set(v___x_558_, 1, v_head_501_);
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_592_ = v___x_558_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_head_501_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_box(0);
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v_inline_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_603_, lean_object* v_inline_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_606_, lean_object* v_pos_607_){
_start:
{
lean_object* v_str_608_; lean_object* v_startInclusive_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_str_608_ = lean_ctor_get(v_s_606_, 0);
v_startInclusive_609_ = lean_ctor_get(v_s_606_, 1);
v___x_610_ = lean_nat_add(v_startInclusive_609_, v_pos_607_);
v___x_611_ = lean_nat_sub(v___x_610_, v_startInclusive_609_);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_nat_dec_eq(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___y_622_; lean_object* v___x_623_; uint32_t v___x_624_; uint8_t v___y_626_; uint32_t v___x_631_; uint8_t v___x_632_; 
lean_inc(v_startInclusive_609_);
lean_inc_ref(v_str_608_);
v___x_614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_614_, 0, v_str_608_);
lean_ctor_set(v___x_614_, 1, v_startInclusive_609_);
lean_ctor_set(v___x_614_, 2, v___x_610_);
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_sub(v___x_611_, v___x_615_);
lean_dec(v___x_611_);
v___x_617_ = l_String_Slice_posLE(v___x_614_, v___x_616_);
lean_dec_ref(v___x_614_);
v___x_623_ = lean_nat_add(v_startInclusive_609_, v___x_617_);
v___x_624_ = lean_string_utf8_get_fast(v_str_608_, v___x_623_);
lean_dec(v___x_623_);
v___x_631_ = 32;
v___x_632_ = lean_uint32_dec_eq(v___x_624_, v___x_631_);
if (v___x_632_ == 0)
{
uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 9;
v___x_634_ = lean_uint32_dec_eq(v___x_624_, v___x_633_);
v___y_626_ = v___x_634_;
goto v___jp_625_;
}
else
{
v___y_626_ = v___x_632_;
goto v___jp_625_;
}
v___jp_618_:
{
uint8_t v___x_619_; 
v___x_619_ = l_String_instDecidableLtRaw___aux__1(v___x_617_, v_pos_607_);
if (v___x_619_ == 0)
{
lean_dec(v___x_617_);
return v_pos_607_;
}
else
{
lean_dec(v_pos_607_);
v_pos_607_ = v___x_617_;
goto _start;
}
}
v___jp_621_:
{
if (v___y_622_ == 0)
{
lean_dec(v___x_617_);
return v_pos_607_;
}
else
{
goto v___jp_618_;
}
}
v___jp_625_:
{
if (v___y_626_ == 0)
{
uint32_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = 13;
v___x_628_ = lean_uint32_dec_eq(v___x_624_, v___x_627_);
if (v___x_628_ == 0)
{
uint32_t v___x_629_; uint8_t v___x_630_; 
v___x_629_ = 10;
v___x_630_ = lean_uint32_dec_eq(v___x_624_, v___x_629_);
v___y_622_ = v___x_630_;
goto v___jp_621_;
}
else
{
v___y_622_ = v___x_628_;
goto v___jp_621_;
}
}
else
{
goto v___jp_618_;
}
}
}
else
{
lean_dec(v___x_611_);
lean_dec(v___x_610_);
return v_pos_607_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_635_, lean_object* v_pos_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_635_, v_pos_636_);
lean_dec_ref(v_s_635_);
return v_res_637_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_639_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___x_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_a_641_){
_start:
{
lean_object* v___y_643_; 
if (lean_obj_tag(v_a_641_) == 0)
{
lean_object* v___x_646_; 
v___x_646_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_646_;
}
else
{
lean_object* v_head_647_; 
v_head_647_ = lean_ctor_get(v_a_641_, 0);
lean_inc(v_head_647_);
switch(lean_obj_tag(v_head_647_))
{
case 0:
{
lean_object* v_tail_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_694_; 
v_tail_648_ = lean_ctor_get(v_a_641_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_a_641_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v_a_641_, 0);
lean_dec(v_unused_695_);
v___x_650_ = v_a_641_;
v_isShared_651_ = v_isSharedCheck_694_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_tail_648_);
lean_dec(v_a_641_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_694_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v_string_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_693_; 
v_string_652_ = lean_ctor_get(v_head_647_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v_head_647_);
if (v_isSharedCheck_693_ == 0)
{
v___x_654_ = v_head_647_;
v_isShared_655_ = v_isSharedCheck_693_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_string_652_);
lean_dec(v_head_647_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_693_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_string_utf8_byte_size(v_string_652_);
lean_inc_ref(v_string_652_);
v___x_658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_658_, 0, v_string_652_);
lean_ctor_set(v___x_658_, 1, v___x_656_);
lean_ctor_set(v___x_658_, 2, v___x_657_);
v___x_659_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_658_, v___x_656_);
v___x_660_ = lean_nat_sub(v___x_657_, v___x_659_);
lean_dec(v___x_659_);
v___x_661_ = lean_nat_dec_eq(v___x_660_, v___x_656_);
lean_dec(v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v_s1_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_s2_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_662_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_658_, v___x_657_);
v_s1_663_ = lean_string_utf8_extract(v_string_652_, v___x_662_, v___x_657_);
lean_dec(v___x_662_);
v___x_664_ = lean_string_length(v_s1_663_);
v___x_665_ = l_String_Slice_Pos_prevn(v___x_658_, v___x_657_, v___x_664_);
lean_dec_ref(v___x_658_);
v_s2_666_ = lean_string_utf8_extract(v_string_652_, v___x_656_, v___x_665_);
lean_dec(v___x_665_);
lean_dec_ref(v_string_652_);
v___x_667_ = lean_array_mk(v_tail_648_);
v___x_668_ = l_Array_reverse___redArg(v___x_667_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v_s2_666_);
v___x_670_ = v___x_654_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_s2_666_);
v___x_670_ = v_reuseFailAlloc_681_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_array_get_size(v___x_668_);
v___x_672_ = lean_nat_dec_eq(v___x_671_, v___x_656_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_673_ = lean_array_push(v___x_668_, v___x_670_);
v___x_674_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 0);
lean_ctor_set(v___x_650_, 1, v_s1_663_);
lean_ctor_set(v___x_650_, 0, v___x_674_);
v___x_676_ = v___x_650_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_s1_663_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
else
{
lean_object* v___x_679_; 
lean_dec_ref(v___x_668_);
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 0);
lean_ctor_set(v___x_650_, 1, v_s1_663_);
lean_ctor_set(v___x_650_, 0, v___x_670_);
v___x_679_ = v___x_650_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_s1_663_);
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
else
{
lean_object* v___x_682_; lean_object* v_fst_683_; lean_object* v_snd_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_692_; 
lean_dec_ref(v___x_658_);
lean_del_object(v___x_654_);
lean_del_object(v___x_650_);
v___x_682_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_tail_648_);
v_fst_683_ = lean_ctor_get(v___x_682_, 0);
v_snd_684_ = lean_ctor_get(v___x_682_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_692_ == 0)
{
v___x_686_ = v___x_682_;
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_snd_684_);
lean_inc(v_fst_683_);
lean_dec(v___x_682_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_string_append(v_snd_684_, v_string_652_);
lean_dec_ref(v_string_652_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_fst_683_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_696_; lean_object* v_content_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_tail_696_ = lean_ctor_get(v_a_641_, 1);
lean_inc(v_tail_696_);
lean_dec_ref(v_a_641_);
v_content_697_ = lean_ctor_get(v_head_647_, 0);
lean_inc_ref(v_content_697_);
lean_dec_ref(v_head_647_);
v___x_698_ = l_Array_reverse___redArg(v_content_697_);
v___x_699_ = lean_array_to_list(v___x_698_);
v___x_700_ = l_List_appendTR___redArg(v___x_699_, v_tail_696_);
v_a_641_ = v___x_700_;
goto _start;
}
default: 
{
lean_object* v_tail_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_tail_702_ = lean_ctor_get(v_a_641_, 1);
lean_inc(v_tail_702_);
lean_dec_ref(v_a_641_);
v___x_703_ = lean_array_mk(v_tail_702_);
v___x_704_ = l_Array_reverse___redArg(v___x_703_);
v___x_705_ = lean_array_get_size(v___x_704_);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_nat_dec_eq(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
if (lean_obj_tag(v_head_647_) == 9)
{
lean_object* v_content_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_content_708_ = lean_ctor_get(v_head_647_, 0);
lean_inc_ref(v_content_708_);
lean_dec_ref(v_head_647_);
v___x_709_ = lean_array_get_size(v_content_708_);
v___x_710_ = lean_nat_dec_eq(v___x_709_, v___x_706_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = l_Array_append___redArg(v___x_704_, v_content_708_);
lean_dec_ref(v_content_708_);
v___x_712_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
v___y_643_ = v___x_712_;
goto v___jp_642_;
}
else
{
lean_object* v___x_713_; 
lean_dec_ref(v_content_708_);
v___x_713_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_704_);
v___y_643_ = v___x_713_;
goto v___jp_642_;
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_array_push(v___x_704_, v_head_647_);
v___x_715_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
v___y_643_ = v___x_715_;
goto v___jp_642_;
}
}
else
{
lean_dec_ref(v___x_704_);
v___y_643_ = v_head_647_;
goto v___jp_642_;
}
}
}
}
v___jp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___y_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_a_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_box(0);
v___x_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_721_, 0, v_inline_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_723_, lean_object* v_inline_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_726_){
_start:
{
lean_object* v___x_727_; lean_object* v_fst_728_; lean_object* v_snd_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_737_; 
v___x_727_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_726_);
v_fst_728_ = lean_ctor_get(v___x_727_, 0);
v_snd_729_ = lean_ctor_get(v___x_727_, 1);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_737_ == 0)
{
v___x_731_ = v___x_727_;
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_snd_729_);
lean_inc(v_fst_728_);
lean_dec(v___x_727_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_733_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_729_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v___x_733_);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_fst_728_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_738_, lean_object* v_inline_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_739_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19));
v___x_787_ = l_ReaderT_instMonad___redArg(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_796_ = l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0(lean_object* v_inst_798_, lean_object* v___x_799_, lean_object* v_a_800_, lean_object* v_x_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_805_; lean_object* v_snd_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v___x_805_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_798_, v_a_800_, v___y_803_, v___y_804_);
v_snd_806_ = lean_ctor_get(v___x_805_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v___x_805_, 0);
lean_dec(v_unused_815_);
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_snd_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_799_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_snd_806_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed(lean_object* v_inst_816_, lean_object* v___x_817_, lean_object* v_a_818_, lean_object* v_x_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0(v_inst_816_, v___x_817_, v_a_818_, v_x_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec_ref(v___y_821_);
return v_res_823_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__1));
v___x_832_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_833_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
lean_ctor_set(v___x_833_, 2, v___x_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2___boxed(lean_object* v_inst_834_, lean_object* v_x_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2(v_inst_834_, v_x_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object* v_inst_841_, lean_object* v_x_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_841_, v_x_842_, v_a_843_, v_a_844_);
lean_dec_ref(v_a_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_846_, lean_object* v_x_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
switch(lean_obj_tag(v_x_847_))
{
case 0:
{
lean_object* v_string_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec_ref(v_inst_846_);
v_string_851_ = lean_ctor_get(v_x_847_, 0);
lean_inc_ref(v_string_851_);
lean_dec_ref(v_x_847_);
v___x_852_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_851_);
lean_dec_ref(v_string_851_);
v___x_853_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_852_, v_a_849_);
lean_dec_ref(v___x_852_);
return v___x_853_;
}
case 1:
{
lean_object* v_content_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_895_; 
v_content_854_ = lean_ctor_get(v_x_847_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v_x_847_);
if (v_isSharedCheck_895_ == 0)
{
v___x_856_ = v_x_847_;
v_isShared_857_ = v_isSharedCheck_895_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_content_854_);
lean_dec(v_x_847_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_895_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 9);
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_content_854_);
v___x_859_ = v_reuseFailAlloc_894_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v_snd_861_; lean_object* v_fst_862_; lean_object* v_fst_863_; lean_object* v_snd_864_; uint8_t v_inEmph_866_; uint8_t v_inBold_867_; uint8_t v_inLink_868_; lean_object* v_linePrefix_869_; lean_object* v___y_870_; lean_object* v___x_881_; uint8_t v_inEmph_882_; 
v___x_860_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_859_);
v_snd_861_ = lean_ctor_get(v___x_860_, 1);
lean_inc(v_snd_861_);
v_fst_862_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_fst_862_);
lean_dec_ref(v___x_860_);
v_fst_863_ = lean_ctor_get(v_snd_861_, 0);
lean_inc(v_fst_863_);
v_snd_864_ = lean_ctor_get(v_snd_861_, 1);
lean_inc(v_snd_864_);
lean_dec(v_snd_861_);
v___x_881_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_862_, v_a_849_);
lean_dec(v_fst_862_);
v_inEmph_882_ = lean_ctor_get_uint8(v_a_848_, sizeof(void*)*1);
if (v_inEmph_882_ == 0)
{
lean_object* v_snd_883_; uint8_t v_inBold_884_; uint8_t v_inLink_885_; lean_object* v_linePrefix_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_snd_889_; 
v_snd_883_ = lean_ctor_get(v___x_881_, 1);
lean_inc(v_snd_883_);
lean_dec_ref(v___x_881_);
v_inBold_884_ = lean_ctor_get_uint8(v_a_848_, sizeof(void*)*1 + 1);
v_inLink_885_ = lean_ctor_get_uint8(v_a_848_, sizeof(void*)*1 + 2);
v_linePrefix_886_ = lean_ctor_get(v_a_848_, 0);
v___x_887_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21));
v___x_888_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_887_, v_snd_883_);
v_snd_889_ = lean_ctor_get(v___x_888_, 1);
lean_inc(v_snd_889_);
lean_dec_ref(v___x_888_);
v_inEmph_866_ = v_inEmph_882_;
v_inBold_867_ = v_inBold_884_;
v_inLink_868_ = v_inLink_885_;
v_linePrefix_869_ = v_linePrefix_886_;
v___y_870_ = v_snd_889_;
goto v___jp_865_;
}
else
{
lean_object* v_snd_890_; uint8_t v_inBold_891_; uint8_t v_inLink_892_; lean_object* v_linePrefix_893_; 
v_snd_890_ = lean_ctor_get(v___x_881_, 1);
lean_inc(v_snd_890_);
lean_dec_ref(v___x_881_);
v_inBold_891_ = lean_ctor_get_uint8(v_a_848_, sizeof(void*)*1 + 1);
v_inLink_892_ = lean_ctor_get_uint8(v_a_848_, sizeof(void*)*1 + 2);
v_linePrefix_893_ = lean_ctor_get(v_a_848_, 0);
v_inEmph_866_ = v_inEmph_882_;
v_inBold_867_ = v_inBold_891_;
v_inLink_868_ = v_inLink_892_;
v_linePrefix_869_ = v_linePrefix_893_;
v___y_870_ = v_snd_890_;
goto v___jp_865_;
}
v___jp_865_:
{
uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = 1;
lean_inc_ref(v_linePrefix_869_);
v___x_872_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_872_, 0, v_linePrefix_869_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*1, v___x_871_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*1 + 1, v_inBold_867_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*1 + 2, v_inLink_868_);
v___x_873_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_846_, v_fst_863_, v___x_872_, v___y_870_);
lean_dec_ref(v___x_872_);
if (v_inEmph_866_ == 0)
{
lean_object* v_snd_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v_snd_877_; lean_object* v___x_878_; 
v_snd_874_ = lean_ctor_get(v___x_873_, 1);
lean_inc(v_snd_874_);
lean_dec_ref(v___x_873_);
v___x_875_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21));
v___x_876_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_875_, v_snd_874_);
v_snd_877_ = lean_ctor_get(v___x_876_, 1);
lean_inc(v_snd_877_);
lean_dec_ref(v___x_876_);
v___x_878_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_864_, v_snd_877_);
lean_dec(v_snd_864_);
return v___x_878_;
}
else
{
lean_object* v_snd_879_; lean_object* v___x_880_; 
v_snd_879_ = lean_ctor_get(v___x_873_, 1);
lean_inc(v_snd_879_);
lean_dec_ref(v___x_873_);
v___x_880_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_864_, v_snd_879_);
lean_dec(v_snd_864_);
return v___x_880_;
}
}
}
}
}
case 2:
{
lean_object* v_content_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_934_; 
v_content_896_ = lean_ctor_get(v_x_847_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v_x_847_);
if (v_isSharedCheck_934_ == 0)
{
v___x_898_ = v_x_847_;
v_isShared_899_ = v_isSharedCheck_934_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_content_896_);
lean_dec(v_x_847_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_934_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set_tag(v___x_898_, 9);
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_content_896_);
v___x_901_ = v_reuseFailAlloc_933_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; lean_object* v_snd_903_; lean_object* v_fst_904_; lean_object* v_fst_905_; lean_object* v_snd_906_; uint8_t v_inBold_908_; uint8_t v_inLink_909_; lean_object* v_linePrefix_910_; lean_object* v___y_911_; lean_object* v___x_922_; uint8_t v_inBold_923_; 
v___x_902_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_901_);
v_snd_903_ = lean_ctor_get(v___x_902_, 1);
lean_inc(v_snd_903_);
v_fst_904_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_fst_904_);
lean_dec_ref(v___x_902_);
v_fst_905_ = lean_ctor_get(v_snd_903_, 0);
lean_inc(v_fst_905_);
v_snd_906_ = lean_ctor_get(v_snd_903_, 1);
lean_inc(v_snd_906_);
lean_dec(v_snd_903_);
v___x_922_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_904_, v_a_849_);
lean_dec(v_fst_904_);
v_inBold_923_ = lean_ctor_get_uint8(v_a_848_, sizeof(void*)*1 + 1);
if (v_inBold_923_ == 0)
{
lean_object* v_snd_924_; uint8_t v_inLink_925_; lean_object* v_linePrefix_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_snd_929_; 
v_snd_924_ = lean_ctor_get(v___x_922_, 1);
lean_inc(v_snd_924_);
lean_dec_ref(v___x_922_);
v_inLink_925_ = lean_ctor_get_uint8(v_a_848_, sizeof(void*)*1 + 2);
v_linePrefix_926_ = lean_ctor_get(v_a_848_, 0);
v___x_927_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_928_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_927_, v_snd_924_);
v_snd_929_ = lean_ctor_get(v___x_928_, 1);
lean_inc(v_snd_929_);
lean_dec_ref(v___x_928_);
v_inBold_908_ = v_inBold_923_;
v_inLink_909_ = v_inLink_925_;
v_linePrefix_910_ = v_linePrefix_926_;
v___y_911_ = v_snd_929_;
goto v___jp_907_;
}
else
{
lean_object* v_snd_930_; uint8_t v_inLink_931_; lean_object* v_linePrefix_932_; 
v_snd_930_ = lean_ctor_get(v___x_922_, 1);
lean_inc(v_snd_930_);
lean_dec_ref(v___x_922_);
v_inLink_931_ = lean_ctor_get_uint8(v_a_848_, sizeof(void*)*1 + 2);
v_linePrefix_932_ = lean_ctor_get(v_a_848_, 0);
v_inBold_908_ = v_inBold_923_;
v_inLink_909_ = v_inLink_931_;
v_linePrefix_910_ = v_linePrefix_932_;
v___y_911_ = v_snd_930_;
goto v___jp_907_;
}
v___jp_907_:
{
uint8_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = 1;
lean_inc_ref(v_linePrefix_910_);
v___x_913_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_913_, 0, v_linePrefix_910_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*1, v___x_912_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*1 + 1, v_inBold_908_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*1 + 2, v_inLink_909_);
v___x_914_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_846_, v_fst_905_, v___x_913_, v___y_911_);
lean_dec_ref(v___x_913_);
if (v_inBold_908_ == 0)
{
lean_object* v_snd_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v_snd_918_; lean_object* v___x_919_; 
v_snd_915_ = lean_ctor_get(v___x_914_, 1);
lean_inc(v_snd_915_);
lean_dec_ref(v___x_914_);
v___x_916_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_917_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_916_, v_snd_915_);
v_snd_918_ = lean_ctor_get(v___x_917_, 1);
lean_inc(v_snd_918_);
lean_dec_ref(v___x_917_);
v___x_919_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_906_, v_snd_918_);
lean_dec(v_snd_906_);
return v___x_919_;
}
else
{
lean_object* v_snd_920_; lean_object* v___x_921_; 
v_snd_920_ = lean_ctor_get(v___x_914_, 1);
lean_inc(v_snd_920_);
lean_dec_ref(v___x_914_);
v___x_921_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_906_, v_snd_920_);
lean_dec(v_snd_906_);
return v___x_921_;
}
}
}
}
}
case 3:
{
lean_object* v_string_935_; lean_object* v___y_937_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_fst_942_; uint8_t v___x_943_; 
lean_dec_ref(v_inst_846_);
v_string_935_ = lean_ctor_get(v_x_847_, 0);
lean_inc_ref(v_string_935_);
lean_dec_ref(v_x_847_);
v___x_940_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_941_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v___x_940_, v_a_849_);
v_fst_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_fst_942_);
v___x_943_ = lean_unbox(v_fst_942_);
lean_dec(v_fst_942_);
if (v___x_943_ == 0)
{
lean_object* v_snd_944_; 
v_snd_944_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_snd_944_);
lean_dec_ref(v___x_941_);
v___y_937_ = v_snd_944_;
goto v___jp_936_;
}
else
{
lean_object* v_snd_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_snd_948_; 
v_snd_945_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_snd_945_);
lean_dec_ref(v___x_941_);
v___x_946_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23));
v___x_947_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_946_, v_snd_945_);
v_snd_948_ = lean_ctor_get(v___x_947_, 1);
lean_inc(v_snd_948_);
lean_dec_ref(v___x_947_);
v___y_937_ = v_snd_948_;
goto v___jp_936_;
}
v___jp_936_:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_935_);
v___x_939_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_938_, v___y_937_);
lean_dec_ref(v___x_938_);
return v___x_939_;
}
}
case 4:
{
uint8_t v_mode_949_; 
lean_dec_ref(v_inst_846_);
v_mode_949_ = lean_ctor_get_uint8(v_x_847_, sizeof(void*)*1);
if (v_mode_949_ == 0)
{
lean_object* v_string_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_string_950_ = lean_ctor_get(v_x_847_, 0);
lean_inc_ref(v_string_950_);
lean_dec_ref(v_x_847_);
v___x_951_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24));
v___x_952_ = lean_string_append(v___x_951_, v_string_950_);
lean_dec_ref(v_string_950_);
v___x_953_ = lean_string_append(v___x_952_, v___x_951_);
v___x_954_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_953_, v_a_849_);
lean_dec_ref(v___x_953_);
return v___x_954_;
}
else
{
lean_object* v_string_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_string_955_ = lean_ctor_get(v_x_847_, 0);
lean_inc_ref(v_string_955_);
lean_dec_ref(v_x_847_);
v___x_956_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25));
v___x_957_ = lean_string_append(v___x_956_, v_string_955_);
lean_dec_ref(v_string_955_);
v___x_958_ = lean_string_append(v___x_957_, v___x_956_);
v___x_959_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_958_, v_a_849_);
lean_dec_ref(v___x_958_);
return v___x_959_;
}
}
case 5:
{
lean_object* v_string_960_; lean_object* v_linePrefix_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec_ref(v_inst_846_);
v_string_960_ = lean_ctor_get(v_x_847_, 0);
lean_inc_ref(v_string_960_);
lean_dec_ref(v_x_847_);
v_linePrefix_961_ = lean_ctor_get(v_a_848_, 0);
v___x_962_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26));
v___x_963_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27));
v___x_964_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_965_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28);
v___x_966_ = lean_string_append(v___x_964_, v_linePrefix_961_);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_string_utf8_byte_size(v_string_960_);
v___x_969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_969_, 0, v_string_960_);
lean_ctor_set(v___x_969_, 1, v___x_967_);
lean_ctor_set(v___x_969_, 2, v___x_968_);
v___x_970_ = l_String_Slice_replace___redArg(v___x_963_, v___x_962_, v___x_969_, v___x_965_, v___x_966_);
v___x_971_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_970_, v_a_849_);
lean_dec_ref(v___x_970_);
return v___x_971_;
}
case 6:
{
uint8_t v_inLink_972_; 
v_inLink_972_ = lean_ctor_get_uint8(v_a_848_, sizeof(void*)*1 + 2);
if (v_inLink_972_ == 0)
{
lean_object* v_content_973_; lean_object* v_url_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_snd_977_; lean_object* v___x_978_; lean_object* v___f_979_; size_t v_sz_980_; size_t v___x_981_; lean_object* v___x_12052__overap_982_; lean_object* v___x_983_; lean_object* v_snd_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_snd_987_; lean_object* v___x_988_; lean_object* v_snd_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_content_973_ = lean_ctor_get(v_x_847_, 0);
lean_inc_ref(v_content_973_);
v_url_974_ = lean_ctor_get(v_x_847_, 1);
lean_inc_ref(v_url_974_);
lean_dec_ref(v_x_847_);
v___x_975_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29));
v___x_976_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_975_, v_a_849_);
v_snd_977_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_snd_977_);
lean_dec_ref(v___x_976_);
v___x_978_ = lean_box(0);
v___f_979_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_979_, 0, v_inst_846_);
lean_closure_set(v___f_979_, 1, v___x_978_);
v_sz_980_ = lean_array_size(v_content_973_);
v___x_981_ = ((size_t)0ULL);
v___x_12052__overap_982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_850_, v_content_973_, v___f_979_, v_sz_980_, v___x_981_, v___x_978_);
lean_inc_ref(v_a_848_);
v___x_983_ = lean_apply_2(v___x_12052__overap_982_, v_a_848_, v_snd_977_);
v_snd_984_ = lean_ctor_get(v___x_983_, 1);
lean_inc(v_snd_984_);
lean_dec_ref(v___x_983_);
v___x_985_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30));
v___x_986_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_985_, v_snd_984_);
v_snd_987_ = lean_ctor_get(v___x_986_, 1);
lean_inc(v_snd_987_);
lean_dec_ref(v___x_986_);
v___x_988_ = l_Lean_Doc_MarkdownM_push___redArg(v_url_974_, v_snd_987_);
lean_dec_ref(v_url_974_);
v_snd_989_ = lean_ctor_get(v___x_988_, 1);
lean_inc(v_snd_989_);
lean_dec_ref(v___x_988_);
v___x_990_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31));
v___x_991_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_990_, v_snd_989_);
return v___x_991_;
}
else
{
lean_object* v_content_992_; lean_object* v___x_993_; lean_object* v___f_994_; size_t v_sz_995_; size_t v___x_996_; lean_object* v___x_12076__overap_997_; lean_object* v___x_998_; lean_object* v_snd_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
v_content_992_ = lean_ctor_get(v_x_847_, 0);
lean_inc_ref(v_content_992_);
lean_dec_ref(v_x_847_);
v___x_993_ = lean_box(0);
v___f_994_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_994_, 0, v_inst_846_);
lean_closure_set(v___f_994_, 1, v___x_993_);
v_sz_995_ = lean_array_size(v_content_992_);
v___x_996_ = ((size_t)0ULL);
v___x_12076__overap_997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_850_, v_content_992_, v___f_994_, v_sz_995_, v___x_996_, v___x_993_);
lean_inc_ref(v_a_848_);
v___x_998_ = lean_apply_2(v___x_12076__overap_997_, v_a_848_, v_a_849_);
v_snd_999_ = lean_ctor_get(v___x_998_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; 
v_unused_1007_ = lean_ctor_get(v___x_998_, 0);
lean_dec(v_unused_1007_);
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_snd_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_993_);
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_snd_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
case 7:
{
lean_object* v_name_1008_; lean_object* v_content_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v_snd_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1057_; 
v_name_1008_ = lean_ctor_get(v_x_847_, 0);
lean_inc_ref(v_name_1008_);
v_content_1009_ = lean_ctor_get(v_x_847_, 1);
lean_inc_ref(v_content_1009_);
lean_dec_ref(v_x_847_);
v___x_1010_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32));
v___x_1011_ = lean_string_append(v___x_1010_, v_name_1008_);
v___x_1012_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33));
v___x_1013_ = lean_string_append(v___x_1011_, v___x_1012_);
v___x_1014_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1013_, v_a_849_);
lean_dec_ref(v___x_1013_);
v_snd_1015_ = lean_ctor_get(v___x_1014_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v___x_1014_, 0);
lean_dec(v_unused_1058_);
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1057_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_snd_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1057_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_snd_1020_; lean_object* v___y_1039_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_array_get_size(v_content_1009_);
v___x_1043_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34));
v___x_1044_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35);
v___x_1045_ = lean_nat_dec_lt(v___x_1041_, v___x_1042_);
if (v___x_1045_ == 0)
{
lean_dec_ref(v_content_1009_);
lean_dec_ref(v_inst_846_);
v_snd_1020_ = v___x_1044_;
goto v___jp_1019_;
}
else
{
lean_object* v___x_1046_; lean_object* v___f_1047_; uint8_t v___x_1048_; 
v___x_1046_ = lean_box(0);
v___f_1047_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_1047_, 0, v_inst_846_);
v___x_1048_ = lean_nat_dec_le(v___x_1042_, v___x_1042_);
if (v___x_1048_ == 0)
{
if (v___x_1045_ == 0)
{
lean_dec_ref(v___f_1047_);
lean_dec_ref(v_content_1009_);
v_snd_1020_ = v___x_1044_;
goto v___jp_1019_;
}
else
{
size_t v___x_1049_; size_t v___x_1050_; lean_object* v___x_11895__overap_1051_; lean_object* v___x_1052_; 
v___x_1049_ = ((size_t)0ULL);
v___x_1050_ = lean_usize_of_nat(v___x_1042_);
v___x_11895__overap_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_850_, v___f_1047_, v_content_1009_, v___x_1049_, v___x_1050_, v___x_1046_);
v___x_1052_ = lean_apply_2(v___x_11895__overap_1051_, v___x_1043_, v___x_1044_);
v___y_1039_ = v___x_1052_;
goto v___jp_1038_;
}
}
else
{
size_t v___x_1053_; size_t v___x_1054_; lean_object* v___x_11899__overap_1055_; lean_object* v___x_1056_; 
v___x_1053_ = ((size_t)0ULL);
v___x_1054_ = lean_usize_of_nat(v___x_1042_);
v___x_11899__overap_1055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_850_, v___f_1047_, v_content_1009_, v___x_1053_, v___x_1054_, v___x_1046_);
v___x_1056_ = lean_apply_2(v___x_11899__overap_1055_, v___x_1043_, v___x_1044_);
v___y_1039_ = v___x_1056_;
goto v___jp_1038_;
}
}
v___jp_1019_:
{
lean_object* v_priorBlocks_1021_; lean_object* v_currentBlock_1022_; lean_object* v_footnotes_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1037_; 
v_priorBlocks_1021_ = lean_ctor_get(v_snd_1015_, 0);
v_currentBlock_1022_ = lean_ctor_get(v_snd_1015_, 1);
v_footnotes_1023_ = lean_ctor_get(v_snd_1015_, 2);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_snd_1015_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1025_ = v_snd_1015_;
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_footnotes_1023_);
lean_inc(v_currentBlock_1022_);
lean_inc(v_priorBlocks_1021_);
lean_dec(v_snd_1015_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1027_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(v_snd_1020_);
v___x_1028_ = lean_box(0);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 1, v___x_1027_);
lean_ctor_set(v___x_1017_, 0, v_name_1008_);
v___x_1030_ = v___x_1017_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_name_1008_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v___x_1027_);
v___x_1030_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_array_push(v_footnotes_1023_, v___x_1030_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 2, v___x_1031_);
v___x_1033_ = v___x_1025_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_priorBlocks_1021_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_currentBlock_1022_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1028_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
return v___x_1034_;
}
}
}
}
v___jp_1038_:
{
lean_object* v_snd_1040_; 
v_snd_1040_ = lean_ctor_get(v___y_1039_, 1);
lean_inc(v_snd_1040_);
lean_dec_ref(v___y_1039_);
v_snd_1020_ = v_snd_1040_;
goto v___jp_1019_;
}
}
}
case 8:
{
lean_object* v_alt_1059_; lean_object* v_url_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_dec_ref(v_inst_846_);
v_alt_1059_ = lean_ctor_get(v_x_847_, 0);
lean_inc_ref(v_alt_1059_);
v_url_1060_ = lean_ctor_get(v_x_847_, 1);
lean_inc_ref(v_url_1060_);
lean_dec_ref(v_x_847_);
v___x_1061_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__36));
v___x_1062_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1059_);
lean_dec_ref(v_alt_1059_);
v___x_1063_ = lean_string_append(v___x_1061_, v___x_1062_);
lean_dec_ref(v___x_1062_);
v___x_1064_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30));
v___x_1065_ = lean_string_append(v___x_1063_, v___x_1064_);
v___x_1066_ = lean_string_append(v___x_1065_, v_url_1060_);
lean_dec_ref(v_url_1060_);
v___x_1067_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31));
v___x_1068_ = lean_string_append(v___x_1066_, v___x_1067_);
v___x_1069_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1068_, v_a_849_);
lean_dec_ref(v___x_1068_);
return v___x_1069_;
}
case 9:
{
lean_object* v_content_1070_; lean_object* v___x_1071_; lean_object* v___f_1072_; size_t v_sz_1073_; size_t v___x_1074_; lean_object* v___x_11990__overap_1075_; lean_object* v___x_1076_; lean_object* v_snd_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_content_1070_ = lean_ctor_get(v_x_847_, 0);
lean_inc_ref(v_content_1070_);
lean_dec_ref(v_x_847_);
v___x_1071_ = lean_box(0);
v___f_1072_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1072_, 0, v_inst_846_);
lean_closure_set(v___f_1072_, 1, v___x_1071_);
v_sz_1073_ = lean_array_size(v_content_1070_);
v___x_1074_ = ((size_t)0ULL);
v___x_11990__overap_1075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_850_, v_content_1070_, v___f_1072_, v_sz_1073_, v___x_1074_, v___x_1071_);
lean_inc_ref(v_a_848_);
v___x_1076_ = lean_apply_2(v___x_11990__overap_1075_, v_a_848_, v_a_849_);
v_snd_1077_ = lean_ctor_get(v___x_1076_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v___x_1076_, 0);
lean_dec(v_unused_1085_);
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_snd_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1071_);
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_snd_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
default: 
{
lean_object* v_container_1086_; lean_object* v_content_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_container_1086_ = lean_ctor_get(v_x_847_, 0);
lean_inc(v_container_1086_);
v_content_1087_ = lean_ctor_get(v_x_847_, 1);
lean_inc_ref(v_content_1087_);
lean_dec_ref(v_x_847_);
lean_inc_ref(v_inst_846_);
v___x_1088_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 4, 1);
lean_closure_set(v___x_1088_, 0, v_inst_846_);
lean_inc_ref(v_a_848_);
v___x_1089_ = lean_apply_5(v_inst_846_, v___x_1088_, v_container_1086_, v_content_1087_, v_a_848_, v_a_849_);
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2(lean_object* v_inst_1090_, lean_object* v_x_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1090_, v___y_1092_, v___y_1093_, v___y_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1096_, lean_object* v_inst_1097_, lean_object* v_x_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1097_, v_x_1098_, v_a_1099_, v_a_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object* v_i_1102_, lean_object* v_inst_1103_, lean_object* v_x_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(v_i_1102_, v_inst_1103_, v_x_1104_, v_a_1105_, v_a_1106_);
lean_dec_ref(v_a_1105_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1108_, lean_object* v_inline_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1108_, v_inline_1109_, v_a_1110_, v_a_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object* v_inst_1113_, lean_object* v_inline_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(v_inst_1113_, v_inline_1114_, v_a_1115_, v_a_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1118_, lean_object* v_inst_1119_, lean_object* v_inline_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1119_, v_inline_1120_, v_a_1121_, v_a_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object* v_i_1124_, lean_object* v_inst_1125_, lean_object* v_inline_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(v_i_1124_, v_inst_1125_, v_inline_1126_, v_a_1127_, v_a_1128_);
lean_dec_ref(v_a_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0(lean_object* v_inst_1130_, lean_object* v_inline_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1130_, v_inline_1131_, v___y_1132_, v___y_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0___boxed(lean_object* v_inst_1135_, lean_object* v_inline_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0(v_inst_1135_, v_inline_1136_, v___y_1137_, v___y_1138_);
lean_dec_ref(v___y_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1140_){
_start:
{
lean_object* v___f_1141_; 
v___f_1141_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1141_, 0, v_inst_1140_);
return v___f_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1142_, lean_object* v_inst_1143_){
_start:
{
lean_object* v___f_1144_; 
v___f_1144_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1144_, 0, v_inst_1143_);
return v___f_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(lean_object* v_x_1145_, lean_object* v_x_1146_){
_start:
{
lean_object* v_zero_1147_; uint8_t v_isZero_1148_; 
v_zero_1147_ = lean_unsigned_to_nat(0u);
v_isZero_1148_ = lean_nat_dec_eq(v_x_1145_, v_zero_1147_);
if (v_isZero_1148_ == 1)
{
lean_dec(v_x_1145_);
return v_x_1146_;
}
else
{
uint32_t v___x_1149_; lean_object* v_one_1150_; lean_object* v_n_1151_; lean_object* v___x_1152_; 
v___x_1149_ = 32;
v_one_1150_ = lean_unsigned_to_nat(1u);
v_n_1151_ = lean_nat_sub(v_x_1145_, v_one_1150_);
lean_dec(v_x_1145_);
v___x_1152_ = lean_string_push(v_x_1146_, v___x_1149_);
v_x_1145_ = v_n_1151_;
v_x_1146_ = v___x_1152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(lean_object* v_str_1154_, lean_object* v_indent_1155_, lean_object* v_b_1156_){
_start:
{
lean_object* v_snd_1157_; lean_object* v_snd_1158_; lean_object* v_fst_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1221_; 
v_snd_1157_ = lean_ctor_get(v_b_1156_, 1);
lean_inc(v_snd_1157_);
v_snd_1158_ = lean_ctor_get(v_snd_1157_, 1);
lean_inc(v_snd_1158_);
v_fst_1159_ = lean_ctor_get(v_b_1156_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_b_1156_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v_b_1156_, 1);
lean_dec(v_unused_1222_);
v___x_1161_ = v_b_1156_;
v_isShared_1162_ = v_isSharedCheck_1221_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_fst_1159_);
lean_dec(v_b_1156_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1221_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_fst_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1219_; 
v_fst_1163_ = lean_ctor_get(v_snd_1157_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_snd_1157_);
if (v_isSharedCheck_1219_ == 0)
{
lean_object* v_unused_1220_; 
v_unused_1220_ = lean_ctor_get(v_snd_1157_, 1);
lean_dec(v_unused_1220_);
v___x_1165_ = v_snd_1157_;
v_isShared_1166_ = v_isSharedCheck_1219_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_fst_1163_);
lean_dec(v_snd_1157_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1219_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_fst_1167_; lean_object* v_snd_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1218_; 
v_fst_1167_ = lean_ctor_get(v_snd_1158_, 0);
v_snd_1168_ = lean_ctor_get(v_snd_1158_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_snd_1158_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1170_ = v_snd_1158_;
v_isShared_1171_ = v_isSharedCheck_1218_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_snd_1168_);
lean_inc(v_fst_1167_);
lean_dec(v_snd_1158_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1218_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = lean_string_utf8_byte_size(v_str_1154_);
v___x_1173_ = lean_nat_dec_eq(v_fst_1167_, v___x_1172_);
if (v___x_1173_ == 0)
{
uint32_t v_c_1174_; lean_object* v_iter_1175_; lean_object* v_longest_1177_; lean_object* v_current_1178_; uint32_t v___x_1203_; uint8_t v___x_1204_; 
v_c_1174_ = lean_string_utf8_get_fast(v_str_1154_, v_fst_1167_);
v_iter_1175_ = lean_string_utf8_next_fast(v_str_1154_, v_fst_1167_);
lean_dec(v_fst_1167_);
v___x_1203_ = 96;
v___x_1204_ = lean_uint32_dec_eq(v_c_1174_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v_current_1205_; uint8_t v___x_1206_; 
v_current_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_nat_dec_le(v_fst_1159_, v_fst_1163_);
if (v___x_1206_ == 0)
{
lean_dec(v_fst_1163_);
v_longest_1177_ = v_fst_1159_;
v_current_1178_ = v_current_1205_;
goto v___jp_1176_;
}
else
{
lean_dec(v_fst_1159_);
v_longest_1177_ = v_fst_1163_;
v_current_1178_ = v_current_1205_;
goto v___jp_1176_;
}
}
else
{
lean_object* v___x_1207_; lean_object* v_current_1208_; 
v___x_1207_ = lean_unsigned_to_nat(1u);
v_current_1208_ = lean_nat_add(v_fst_1163_, v___x_1207_);
lean_dec(v_fst_1163_);
v_longest_1177_ = v_fst_1159_;
v_current_1178_ = v_current_1208_;
goto v___jp_1176_;
}
v___jp_1176_:
{
lean_object* v_out_1179_; uint32_t v___x_1180_; uint8_t v___x_1181_; 
v_out_1179_ = lean_string_push(v_snd_1168_, v_c_1174_);
v___x_1180_ = 10;
v___x_1181_ = lean_uint32_dec_eq(v_c_1174_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1183_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_out_1179_);
lean_ctor_set(v___x_1170_, 0, v_iter_1175_);
v___x_1183_ = v___x_1170_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_iter_1175_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_out_1179_);
v___x_1183_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1185_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v___x_1183_);
lean_ctor_set(v___x_1165_, 0, v_current_1178_);
v___x_1185_ = v___x_1165_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_current_1178_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1185_);
lean_ctor_set(v___x_1161_, 0, v_longest_1177_);
v___x_1187_ = v___x_1161_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_longest_1177_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
v_b_1156_ = v___x_1187_;
goto _start;
}
}
}
}
else
{
lean_object* v_out_1192_; lean_object* v___x_1194_; 
lean_inc(v_indent_1155_);
v_out_1192_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(v_indent_1155_, v_out_1179_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_out_1192_);
lean_ctor_set(v___x_1170_, 0, v_iter_1175_);
v___x_1194_ = v___x_1170_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_iter_1175_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_out_1192_);
v___x_1194_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1196_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v___x_1194_);
lean_ctor_set(v___x_1165_, 0, v_current_1178_);
v___x_1196_ = v___x_1165_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_current_1178_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1196_);
lean_ctor_set(v___x_1161_, 0, v_longest_1177_);
v___x_1198_ = v___x_1161_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_longest_1177_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
v_b_1156_ = v___x_1198_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_1210_; 
lean_dec(v_indent_1155_);
if (v_isShared_1171_ == 0)
{
v___x_1210_ = v___x_1170_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_fst_1167_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_snd_1168_);
v___x_1210_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1212_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v___x_1210_);
v___x_1212_ = v___x_1165_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_fst_1163_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1214_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1212_);
v___x_1214_ = v___x_1161_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_fst_1159_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1___boxed(lean_object* v_str_1223_, lean_object* v_indent_1224_, lean_object* v_b_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(v_str_1223_, v_indent_1224_, v_b_1225_);
lean_dec_ref(v_str_1223_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(lean_object* v_indent_1236_, lean_object* v_str_1237_){
_start:
{
lean_object* v_current_1238_; lean_object* v_out_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v_snd_1242_; lean_object* v_snd_1243_; lean_object* v_fst_1244_; lean_object* v_fst_1245_; lean_object* v_snd_1246_; lean_object* v___x_1247_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1260_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_current_1238_ = lean_unsigned_to_nat(0u);
v_out_1239_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_1240_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__2));
lean_inc(v_indent_1236_);
v___x_1241_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(v_str_1237_, v_indent_1236_, v___x_1240_);
v_snd_1242_ = lean_ctor_get(v___x_1241_, 1);
lean_inc(v_snd_1242_);
v_snd_1243_ = lean_ctor_get(v_snd_1242_, 1);
lean_inc(v_snd_1243_);
v_fst_1244_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_fst_1244_);
lean_dec_ref(v___x_1241_);
v_fst_1245_ = lean_ctor_get(v_snd_1242_, 0);
lean_inc(v_fst_1245_);
lean_dec(v_snd_1242_);
v_snd_1246_ = lean_ctor_get(v_snd_1243_, 1);
lean_inc(v_snd_1246_);
lean_dec(v_snd_1243_);
v___x_1247_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1266_ = lean_string_utf8_byte_size(v_snd_1246_);
v___x_1267_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2);
v___x_1268_ = lean_nat_dec_le(v___x_1267_, v___x_1266_);
if (v___x_1268_ == 0)
{
goto v___jp_1263_;
}
else
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = lean_nat_sub(v___x_1266_, v___x_1267_);
v___x_1270_ = lean_string_memcmp(v_snd_1246_, v___x_1247_, v___x_1269_, v_current_1238_, v___x_1267_);
lean_dec(v___x_1269_);
if (v___x_1270_ == 0)
{
goto v___jp_1263_;
}
else
{
v___y_1260_ = v_snd_1246_;
goto v___jp_1259_;
}
}
v___jp_1248_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_nat_add(v___y_1251_, v___x_1252_);
lean_dec(v___y_1251_);
v___x_1254_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__1(v___x_1253_, v___y_1249_);
lean_inc_ref(v___x_1254_);
v___x_1255_ = lean_string_append(v___x_1254_, v___x_1247_);
v___x_1256_ = lean_string_append(v___x_1255_, v___y_1250_);
lean_dec_ref(v___y_1250_);
v___x_1257_ = lean_string_append(v___x_1256_, v___x_1254_);
lean_dec_ref(v___x_1254_);
v___x_1258_ = lean_string_append(v___x_1257_, v___x_1247_);
return v___x_1258_;
}
v___jp_1259_:
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(v_indent_1236_, v_out_1239_);
v___x_1262_ = lean_nat_dec_le(v_fst_1244_, v_fst_1245_);
if (v___x_1262_ == 0)
{
lean_dec(v_fst_1245_);
v___y_1249_ = v___x_1261_;
v___y_1250_ = v___y_1260_;
v___y_1251_ = v_fst_1244_;
goto v___jp_1248_;
}
else
{
lean_dec(v_fst_1244_);
v___y_1249_ = v___x_1261_;
v___y_1250_ = v___y_1260_;
v___y_1251_ = v_fst_1245_;
goto v___jp_1248_;
}
}
v___jp_1263_:
{
uint32_t v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = 10;
v___x_1265_ = lean_string_push(v_snd_1246_, v___x_1264_);
v___y_1260_ = v___x_1265_;
goto v___jp_1259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___boxed(lean_object* v_indent_1271_, lean_object* v_str_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v_indent_1271_, v_str_1272_);
lean_dec_ref(v_str_1272_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v___x_1275_, lean_object* v___f_1276_, lean_object* v___x_1277_, lean_object* v_a_1278_, lean_object* v_x_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
uint8_t v_inEmph_1283_; uint8_t v_inBold_1284_; uint8_t v_inLink_1285_; lean_object* v_linePrefix_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v_snd_1290_; size_t v_sz_1291_; size_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_13712__overap_1296_; lean_object* v___x_1297_; lean_object* v_snd_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1306_; 
v_inEmph_1283_ = lean_ctor_get_uint8(v___y_1281_, sizeof(void*)*1);
v_inBold_1284_ = lean_ctor_get_uint8(v___y_1281_, sizeof(void*)*1 + 1);
v_inLink_1285_ = lean_ctor_get_uint8(v___y_1281_, sizeof(void*)*1 + 2);
v_linePrefix_1286_ = lean_ctor_get(v___y_1281_, 0);
lean_inc_ref(v_linePrefix_1286_);
lean_dec_ref(v___y_1281_);
v___x_1287_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
lean_inc_ref(v_linePrefix_1286_);
v___x_1288_ = lean_string_append(v_linePrefix_1286_, v___x_1287_);
v___x_1289_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1288_, v___y_1282_);
lean_dec_ref(v___x_1288_);
v_snd_1290_ = lean_ctor_get(v___x_1289_, 1);
lean_inc(v_snd_1290_);
lean_dec_ref(v___x_1289_);
v_sz_1291_ = lean_array_size(v_a_1278_);
v___x_1292_ = ((size_t)0ULL);
v___x_1293_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1294_ = lean_string_append(v_linePrefix_1286_, v___x_1293_);
v___x_1295_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*1, v_inEmph_1283_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*1 + 1, v_inBold_1284_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*1 + 2, v_inLink_1285_);
v___x_13712__overap_1296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1275_, v_a_1278_, v___f_1276_, v_sz_1291_, v___x_1292_, v___x_1277_);
v___x_1297_ = lean_apply_2(v___x_13712__overap_1296_, v___x_1295_, v_snd_1290_);
v_snd_1298_ = lean_ctor_get(v___x_1297_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v___x_1297_, 0);
lean_dec(v_unused_1307_);
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_snd_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1277_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1302_);
v___x_1304_ = v___x_1300_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_snd_1298_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v___x_1310_, lean_object* v_a_1311_, lean_object* v_x_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v_inst_1308_, v_inst_1309_, v___x_1310_, v_a_1311_, v_x_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v___x_1320_, lean_object* v___x_1321_, lean_object* v_a_1322_, lean_object* v_x_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
uint8_t v_inEmph_1327_; uint8_t v_inBold_1328_; uint8_t v_inLink_1329_; lean_object* v_linePrefix_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_snd_1336_; lean_object* v___x_1337_; lean_object* v___f_1338_; size_t v_sz_1339_; size_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_13750__overap_1344_; lean_object* v___x_1345_; lean_object* v_snd_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1355_; 
v_inEmph_1327_ = lean_ctor_get_uint8(v___y_1325_, sizeof(void*)*1);
v_inBold_1328_ = lean_ctor_get_uint8(v___y_1325_, sizeof(void*)*1 + 1);
v_inLink_1329_ = lean_ctor_get_uint8(v___y_1325_, sizeof(void*)*1 + 2);
v_linePrefix_1330_ = lean_ctor_get(v___y_1325_, 0);
lean_inc_ref(v_linePrefix_1330_);
lean_dec_ref(v___y_1325_);
lean_inc(v___y_1324_);
v___x_1331_ = l_Nat_reprFast(v___y_1324_);
v___x_1332_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0));
v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
lean_inc_ref(v_linePrefix_1330_);
v___x_1334_ = lean_string_append(v_linePrefix_1330_, v___x_1333_);
lean_dec_ref(v___x_1333_);
v___x_1335_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1334_, v___y_1326_);
lean_dec_ref(v___x_1334_);
v_snd_1336_ = lean_ctor_get(v___x_1335_, 1);
lean_inc(v_snd_1336_);
lean_dec_ref(v___x_1335_);
v___x_1337_ = lean_box(0);
v___f_1338_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1338_, 0, v_inst_1318_);
lean_closure_set(v___f_1338_, 1, v_inst_1319_);
lean_closure_set(v___f_1338_, 2, v___x_1337_);
v_sz_1339_ = lean_array_size(v_a_1322_);
v___x_1340_ = ((size_t)0ULL);
v___x_1341_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1342_ = lean_string_append(v_linePrefix_1330_, v___x_1341_);
v___x_1343_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set_uint8(v___x_1343_, sizeof(void*)*1, v_inEmph_1327_);
lean_ctor_set_uint8(v___x_1343_, sizeof(void*)*1 + 1, v_inBold_1328_);
lean_ctor_set_uint8(v___x_1343_, sizeof(void*)*1 + 2, v_inLink_1329_);
v___x_13750__overap_1344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1320_, v_a_1322_, v___f_1338_, v_sz_1339_, v___x_1340_, v___x_1337_);
v___x_1345_ = lean_apply_2(v___x_13750__overap_1344_, v___x_1343_, v_snd_1336_);
v_snd_1346_ = lean_ctor_get(v___x_1345_, 1);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; 
v_unused_1356_ = lean_ctor_get(v___x_1345_, 0);
lean_dec(v_unused_1356_);
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1355_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_snd_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1355_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = lean_nat_add(v___y_1324_, v___x_1321_);
lean_dec(v___y_1324_);
v___x_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1351_);
v___x_1353_ = v___x_1348_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_snd_1346_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v_a_1361_, lean_object* v_x_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1357_, v_inst_1358_, v___x_1359_, v___x_1360_, v_a_1361_, v_x_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___x_1360_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1370_, lean_object* v_inst_1371_, lean_object* v___x_1372_, lean_object* v_a_1373_, lean_object* v_x_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
uint8_t v_inEmph_1378_; uint8_t v_inBold_1379_; uint8_t v_inLink_1380_; lean_object* v_linePrefix_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v_snd_1385_; lean_object* v_term_1386_; lean_object* v_desc_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_snd_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_snd_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v_snd_1399_; lean_object* v___x_1400_; lean_object* v_snd_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v_snd_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1412_; 
v_inEmph_1378_ = lean_ctor_get_uint8(v___y_1376_, sizeof(void*)*1);
v_inBold_1379_ = lean_ctor_get_uint8(v___y_1376_, sizeof(void*)*1 + 1);
v_inLink_1380_ = lean_ctor_get_uint8(v___y_1376_, sizeof(void*)*1 + 2);
v_linePrefix_1381_ = lean_ctor_get(v___y_1376_, 0);
lean_inc_ref(v_linePrefix_1381_);
lean_dec_ref(v___y_1376_);
v___x_1382_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
lean_inc_ref(v_linePrefix_1381_);
v___x_1383_ = lean_string_append(v_linePrefix_1381_, v___x_1382_);
v___x_1384_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1383_, v___y_1377_);
lean_dec_ref(v___x_1383_);
v_snd_1385_ = lean_ctor_get(v___x_1384_, 1);
lean_inc(v_snd_1385_);
lean_dec_ref(v___x_1384_);
v_term_1386_ = lean_ctor_get(v_a_1373_, 0);
v_desc_1387_ = lean_ctor_get(v_a_1373_, 1);
lean_inc_ref(v_term_1386_);
v___x_1388_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_term_1386_);
v___x_1389_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1390_ = lean_string_append(v_linePrefix_1381_, v___x_1389_);
lean_inc_ref(v___x_1390_);
v___x_1391_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*1, v_inEmph_1378_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*1 + 1, v_inBold_1379_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*1 + 2, v_inLink_1380_);
lean_inc_ref(v_inst_1370_);
v___x_1392_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1370_, v___x_1388_, v___x_1391_, v_snd_1385_);
v_snd_1393_ = lean_ctor_get(v___x_1392_, 1);
lean_inc(v_snd_1393_);
lean_dec_ref(v___x_1392_);
v___x_1394_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1));
lean_inc_ref(v_inst_1370_);
v___x_1395_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1370_, v___x_1394_, v___x_1391_, v_snd_1393_);
v_snd_1396_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_snd_1396_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1398_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1397_, v_snd_1396_);
v_snd_1399_ = lean_ctor_get(v___x_1398_, 1);
lean_inc(v_snd_1399_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1390_, v_snd_1399_);
lean_dec_ref(v___x_1390_);
v_snd_1401_ = lean_ctor_get(v___x_1400_, 1);
lean_inc(v_snd_1401_);
lean_dec_ref(v___x_1400_);
lean_inc_ref(v_desc_1387_);
v___x_1402_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_desc_1387_);
v___x_1403_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1370_, v_inst_1371_, v___x_1402_, v___x_1391_, v_snd_1401_);
v_snd_1404_ = lean_ctor_get(v___x_1403_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v___x_1403_, 0);
lean_dec(v_unused_1413_);
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1372_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1408_);
v___x_1410_ = v___x_1406_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_snd_1404_);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1414_, lean_object* v_inst_1415_, lean_object* v___x_1416_, lean_object* v_a_1417_, lean_object* v_x_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1414_, v_inst_1415_, v___x_1416_, v_a_1417_, v_x_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec_ref(v_a_1417_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1424_, lean_object* v_inst_1425_, lean_object* v_x_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
switch(lean_obj_tag(v_x_1426_))
{
case 0:
{
lean_object* v_contents_1430_; lean_object* v___x_1431_; lean_object* v___f_1432_; size_t v_sz_1433_; size_t v___x_1434_; lean_object* v___x_12962__overap_1435_; lean_object* v___x_1436_; lean_object* v_snd_1437_; lean_object* v___x_1438_; 
lean_dec_ref(v_inst_1425_);
v_contents_1430_ = lean_ctor_get(v_x_1426_, 0);
lean_inc_ref(v_contents_1430_);
lean_dec_ref(v_x_1426_);
v___x_1431_ = lean_box(0);
v___f_1432_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1432_, 0, v_inst_1424_);
lean_closure_set(v___f_1432_, 1, v___x_1431_);
v_sz_1433_ = lean_array_size(v_contents_1430_);
v___x_1434_ = ((size_t)0ULL);
v___x_12962__overap_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1429_, v_contents_1430_, v___f_1432_, v_sz_1433_, v___x_1434_, v___x_1431_);
v___x_1436_ = lean_apply_2(v___x_12962__overap_1435_, v_a_1427_, v_a_1428_);
v_snd_1437_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_snd_1437_);
lean_dec_ref(v___x_1436_);
v___x_1438_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1437_);
return v___x_1438_;
}
case 1:
{
lean_object* v_content_1439_; lean_object* v___y_1441_; lean_object* v___y_1442_; uint8_t v___y_1450_; lean_object* v_currentBlock_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
lean_dec_ref(v_inst_1425_);
lean_dec_ref(v_inst_1424_);
v_content_1439_ = lean_ctor_get(v_x_1426_, 0);
lean_inc_ref(v_content_1439_);
lean_dec_ref(v_x_1426_);
v_currentBlock_1454_ = lean_ctor_get(v_a_1428_, 1);
v___x_1455_ = lean_string_utf8_byte_size(v_currentBlock_1454_);
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = lean_nat_dec_eq(v___x_1455_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1458_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1459_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2);
v___x_1460_ = lean_nat_dec_le(v___x_1459_, v___x_1455_);
if (v___x_1460_ == 0)
{
v___y_1450_ = v___x_1457_;
goto v___jp_1449_;
}
else
{
lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1461_ = lean_nat_sub(v___x_1455_, v___x_1459_);
v___x_1462_ = lean_string_memcmp(v_currentBlock_1454_, v___x_1458_, v___x_1461_, v___x_1456_, v___x_1459_);
lean_dec(v___x_1461_);
v___y_1450_ = v___x_1462_;
goto v___jp_1449_;
}
}
else
{
v___y_1450_ = v___x_1457_;
goto v___jp_1449_;
}
v___jp_1440_:
{
lean_object* v_linePrefix_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_snd_1447_; lean_object* v___x_1448_; 
v_linePrefix_1443_ = lean_ctor_get(v___y_1441_, 0);
lean_inc_ref(v_linePrefix_1443_);
lean_dec_ref(v___y_1441_);
v___x_1444_ = lean_string_length(v_linePrefix_1443_);
lean_dec_ref(v_linePrefix_1443_);
v___x_1445_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v___x_1444_, v_content_1439_);
lean_dec_ref(v_content_1439_);
v___x_1446_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1445_, v___y_1442_);
lean_dec_ref(v___x_1445_);
v_snd_1447_ = lean_ctor_get(v___x_1446_, 1);
lean_inc(v_snd_1447_);
lean_dec_ref(v___x_1446_);
v___x_1448_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1447_);
return v___x_1448_;
}
v___jp_1449_:
{
if (v___y_1450_ == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v_snd_1453_; 
v___x_1451_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1452_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1451_, v_a_1428_);
v_snd_1453_ = lean_ctor_get(v___x_1452_, 1);
lean_inc(v_snd_1453_);
lean_dec_ref(v___x_1452_);
v___y_1441_ = v_a_1427_;
v___y_1442_ = v_snd_1453_;
goto v___jp_1440_;
}
else
{
v___y_1441_ = v_a_1427_;
v___y_1442_ = v_a_1428_;
goto v___jp_1440_;
}
}
}
case 2:
{
lean_object* v_items_1463_; lean_object* v___x_1464_; lean_object* v___f_1465_; lean_object* v___f_1466_; size_t v_sz_1467_; size_t v___x_1468_; lean_object* v___x_13190__overap_1469_; lean_object* v___x_1470_; lean_object* v_snd_1471_; lean_object* v___x_1472_; 
v_items_1463_ = lean_ctor_get(v_x_1426_, 0);
lean_inc_ref(v_items_1463_);
lean_dec_ref(v_x_1426_);
v___x_1464_ = lean_box(0);
v___f_1465_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1465_, 0, v_inst_1424_);
lean_closure_set(v___f_1465_, 1, v_inst_1425_);
lean_closure_set(v___f_1465_, 2, v___x_1464_);
v___f_1466_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0), 8, 3);
lean_closure_set(v___f_1466_, 0, v___x_1429_);
lean_closure_set(v___f_1466_, 1, v___f_1465_);
lean_closure_set(v___f_1466_, 2, v___x_1464_);
v_sz_1467_ = lean_array_size(v_items_1463_);
v___x_1468_ = ((size_t)0ULL);
v___x_13190__overap_1469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1429_, v_items_1463_, v___f_1466_, v_sz_1467_, v___x_1468_, v___x_1464_);
v___x_1470_ = lean_apply_2(v___x_13190__overap_1469_, v_a_1427_, v_a_1428_);
v_snd_1471_ = lean_ctor_get(v___x_1470_, 1);
lean_inc(v_snd_1471_);
lean_dec_ref(v___x_1470_);
v___x_1472_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1471_);
return v___x_1472_;
}
case 3:
{
lean_object* v_start_1473_; lean_object* v_items_1474_; lean_object* v___x_1475_; lean_object* v___f_1476_; lean_object* v___y_1478_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v_start_1473_ = lean_ctor_get(v_x_1426_, 0);
lean_inc(v_start_1473_);
v_items_1474_ = lean_ctor_get(v_x_1426_, 1);
lean_inc_ref(v_items_1474_);
lean_dec_ref(v_x_1426_);
v___x_1475_ = lean_unsigned_to_nat(1u);
v___f_1476_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 9, 4);
lean_closure_set(v___f_1476_, 0, v_inst_1424_);
lean_closure_set(v___f_1476_, 1, v_inst_1425_);
lean_closure_set(v___f_1476_, 2, v___x_1429_);
lean_closure_set(v___f_1476_, 3, v___x_1475_);
v___x_1485_ = l_Int_toNat(v_start_1473_);
lean_dec(v_start_1473_);
v___x_1486_ = lean_nat_dec_le(v___x_1475_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_dec(v___x_1485_);
v___y_1478_ = v___x_1475_;
goto v___jp_1477_;
}
else
{
v___y_1478_ = v___x_1485_;
goto v___jp_1477_;
}
v___jp_1477_:
{
size_t v_sz_1479_; size_t v___x_1480_; lean_object* v___x_13284__overap_1481_; lean_object* v___x_1482_; lean_object* v_snd_1483_; lean_object* v___x_1484_; 
v_sz_1479_ = lean_array_size(v_items_1474_);
v___x_1480_ = ((size_t)0ULL);
v___x_13284__overap_1481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1429_, v_items_1474_, v___f_1476_, v_sz_1479_, v___x_1480_, v___y_1478_);
v___x_1482_ = lean_apply_2(v___x_13284__overap_1481_, v_a_1427_, v_a_1428_);
v_snd_1483_ = lean_ctor_get(v___x_1482_, 1);
lean_inc(v_snd_1483_);
lean_dec_ref(v___x_1482_);
v___x_1484_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1483_);
return v___x_1484_;
}
}
case 4:
{
lean_object* v_items_1487_; lean_object* v___x_1488_; lean_object* v___f_1489_; size_t v_sz_1490_; size_t v___x_1491_; lean_object* v___x_13387__overap_1492_; lean_object* v___x_1493_; lean_object* v_snd_1494_; lean_object* v___x_1495_; 
v_items_1487_ = lean_ctor_get(v_x_1426_, 0);
lean_inc_ref(v_items_1487_);
lean_dec_ref(v_x_1426_);
v___x_1488_ = lean_box(0);
v___f_1489_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 8, 3);
lean_closure_set(v___f_1489_, 0, v_inst_1424_);
lean_closure_set(v___f_1489_, 1, v_inst_1425_);
lean_closure_set(v___f_1489_, 2, v___x_1488_);
v_sz_1490_ = lean_array_size(v_items_1487_);
v___x_1491_ = ((size_t)0ULL);
v___x_13387__overap_1492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1429_, v_items_1487_, v___f_1489_, v_sz_1490_, v___x_1491_, v___x_1488_);
v___x_1493_ = lean_apply_2(v___x_13387__overap_1492_, v_a_1427_, v_a_1428_);
v_snd_1494_ = lean_ctor_get(v___x_1493_, 1);
lean_inc(v_snd_1494_);
lean_dec_ref(v___x_1493_);
v___x_1495_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1494_);
return v___x_1495_;
}
case 5:
{
lean_object* v_items_1496_; uint8_t v_inEmph_1497_; uint8_t v_inBold_1498_; uint8_t v_inLink_1499_; lean_object* v_linePrefix_1500_; lean_object* v___x_1501_; lean_object* v___f_1502_; size_t v_sz_1503_; size_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_13493__overap_1508_; lean_object* v___x_1509_; lean_object* v_snd_1510_; lean_object* v___x_1511_; 
v_items_1496_ = lean_ctor_get(v_x_1426_, 0);
lean_inc_ref(v_items_1496_);
lean_dec_ref(v_x_1426_);
v_inEmph_1497_ = lean_ctor_get_uint8(v_a_1427_, sizeof(void*)*1);
v_inBold_1498_ = lean_ctor_get_uint8(v_a_1427_, sizeof(void*)*1 + 1);
v_inLink_1499_ = lean_ctor_get_uint8(v_a_1427_, sizeof(void*)*1 + 2);
v_linePrefix_1500_ = lean_ctor_get(v_a_1427_, 0);
lean_inc_ref(v_linePrefix_1500_);
lean_dec_ref(v_a_1427_);
v___x_1501_ = lean_box(0);
v___f_1502_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1502_, 0, v_inst_1424_);
lean_closure_set(v___f_1502_, 1, v_inst_1425_);
lean_closure_set(v___f_1502_, 2, v___x_1501_);
v_sz_1503_ = lean_array_size(v_items_1496_);
v___x_1504_ = ((size_t)0ULL);
v___x_1505_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_1506_ = lean_string_append(v_linePrefix_1500_, v___x_1505_);
v___x_1507_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*1, v_inEmph_1497_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*1 + 1, v_inBold_1498_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*1 + 2, v_inLink_1499_);
v___x_13493__overap_1508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1429_, v_items_1496_, v___f_1502_, v_sz_1503_, v___x_1504_, v___x_1501_);
v___x_1509_ = lean_apply_2(v___x_13493__overap_1508_, v___x_1507_, v_a_1428_);
v_snd_1510_ = lean_ctor_get(v___x_1509_, 1);
lean_inc(v_snd_1510_);
lean_dec_ref(v___x_1509_);
v___x_1511_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1510_);
return v___x_1511_;
}
case 6:
{
lean_object* v_content_1512_; lean_object* v___x_1513_; lean_object* v___f_1514_; size_t v_sz_1515_; size_t v___x_1516_; lean_object* v___x_13529__overap_1517_; lean_object* v___x_1518_; lean_object* v_snd_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
v_content_1512_ = lean_ctor_get(v_x_1426_, 0);
lean_inc_ref(v_content_1512_);
lean_dec_ref(v_x_1426_);
v___x_1513_ = lean_box(0);
v___f_1514_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1514_, 0, v_inst_1424_);
lean_closure_set(v___f_1514_, 1, v_inst_1425_);
lean_closure_set(v___f_1514_, 2, v___x_1513_);
v_sz_1515_ = lean_array_size(v_content_1512_);
v___x_1516_ = ((size_t)0ULL);
v___x_13529__overap_1517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1429_, v_content_1512_, v___f_1514_, v_sz_1515_, v___x_1516_, v___x_1513_);
v___x_1518_ = lean_apply_2(v___x_13529__overap_1517_, v_a_1427_, v_a_1428_);
v_snd_1519_ = lean_ctor_get(v___x_1518_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v___x_1518_, 0);
lean_dec(v_unused_1527_);
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_snd_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1513_);
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_snd_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
default: 
{
lean_object* v_container_1528_; lean_object* v_content_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_container_1528_ = lean_ctor_get(v_x_1426_, 0);
lean_inc(v_container_1528_);
v_content_1529_ = lean_ctor_get(v_x_1426_, 1);
lean_inc_ref(v_content_1529_);
lean_dec_ref(v_x_1426_);
lean_inc_ref(v_inst_1424_);
v___x_1530_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed), 5, 2);
lean_closure_set(v___x_1530_, 0, lean_box(0));
lean_closure_set(v___x_1530_, 1, v_inst_1424_);
lean_inc_ref(v_inst_1425_);
v___x_1531_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg), 5, 2);
lean_closure_set(v___x_1531_, 0, v_inst_1424_);
lean_closure_set(v___x_1531_, 1, v_inst_1425_);
v___x_1532_ = lean_apply_6(v_inst_1425_, v___x_1530_, v___x_1531_, v_container_1528_, v_content_1529_, v_a_1427_, v_a_1428_);
return v___x_1532_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(lean_object* v_inst_1533_, lean_object* v_inst_1534_, lean_object* v___x_1535_, lean_object* v_a_1536_, lean_object* v_x_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1541_; lean_object* v_snd_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1550_; 
lean_inc_ref(v___y_1539_);
v___x_1541_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1533_, v_inst_1534_, v_a_1536_, v___y_1539_, v___y_1540_);
v_snd_1542_ = lean_ctor_get(v___x_1541_, 1);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v___x_1541_, 0);
lean_dec(v_unused_1551_);
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1550_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_snd_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1550_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1535_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1546_);
v___x_1548_ = v___x_1544_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_snd_1542_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1552_, lean_object* v_b_1553_, lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_x_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v___x_1559_; 
lean_inc_ref(v_a_1557_);
v___x_1559_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1554_, v_inst_1555_, v_x_1556_, v_a_1557_, v_a_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object* v_i_1560_, lean_object* v_b_1561_, lean_object* v_inst_1562_, lean_object* v_inst_1563_, lean_object* v_x_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(v_i_1560_, v_b_1561_, v_inst_1562_, v_inst_1563_, v_x_1564_, v_a_1565_, v_a_1566_);
lean_dec_ref(v_a_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1568_, lean_object* v_inst_1569_, lean_object* v_block_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v___x_1573_; 
lean_inc_ref(v_a_1571_);
v___x_1573_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1568_, v_inst_1569_, v_block_1570_, v_a_1571_, v_a_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_block_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1574_, v_inst_1575_, v_block_1576_, v_a_1577_, v_a_1578_);
lean_dec_ref(v_a_1577_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1580_, lean_object* v_b_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_block_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v___x_1587_; 
lean_inc_ref(v_a_1585_);
v___x_1587_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1582_, v_inst_1583_, v_block_1584_, v_a_1585_, v_a_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1588_, lean_object* v_b_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_block_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1588_, v_b_1589_, v_inst_1590_, v_inst_1591_, v_block_1592_, v_a_1593_, v_a_1594_);
lean_dec_ref(v_a_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_block_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1601_; 
lean_inc_ref(v___y_1599_);
v___x_1601_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1596_, v_inst_1597_, v_block_1598_, v___y_1599_, v___y_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_1602_, lean_object* v_inst_1603_, lean_object* v_block_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_1602_, v_inst_1603_, v_block_1604_, v___y_1605_, v___y_1606_);
lean_dec_ref(v___y_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1608_, lean_object* v_inst_1609_){
_start:
{
lean_object* v___f_1610_; 
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1610_, 0, v_inst_1608_);
lean_closure_set(v___f_1610_, 1, v_inst_1609_);
return v___f_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1611_, lean_object* v_b_1612_, lean_object* v_inst_1613_, lean_object* v_inst_1614_){
_start:
{
lean_object* v___f_1615_; 
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1615_, 0, v_inst_1613_);
lean_closure_set(v___f_1615_, 1, v_inst_1614_);
return v___f_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0(uint32_t v___x_1616_, lean_object* v_s_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_string_push(v_s_1617_, v___x_1616_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0___boxed(lean_object* v___x_1619_, lean_object* v_s_1620_){
_start:
{
uint32_t v___x_4128__boxed_1621_; lean_object* v_res_1622_; 
v___x_4128__boxed_1621_ = lean_unbox_uint32(v___x_1619_);
lean_dec(v___x_1619_);
v_res_1622_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0(v___x_4128__boxed_1621_, v_s_1620_);
return v_res_1622_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = 35;
v___x_1624_ = lean_box_uint32(v___x_1623_);
return v___x_1624_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___f_1626_; 
v___x_1625_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1626_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1626_, 0, v___x_1625_);
return v___f_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v___x_1629_, lean_object* v___x_1630_, lean_object* v_a_1631_, lean_object* v_x_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3(v_inst_1627_, v_inst_1628_, v___x_1629_, v___x_1630_, v_a_1631_, v_x_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___x_1629_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_level_1639_, lean_object* v_part_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___f_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_snd_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v_snd_1653_; lean_object* v_title_1654_; lean_object* v_content_1655_; lean_object* v_subParts_1656_; lean_object* v___x_1657_; lean_object* v___f_1658_; size_t v_sz_1659_; size_t v___x_1660_; lean_object* v___x_3967__overap_1661_; lean_object* v___x_1662_; lean_object* v_snd_1663_; lean_object* v___x_1664_; lean_object* v_snd_1665_; lean_object* v___f_1666_; size_t v_sz_1667_; lean_object* v___x_3985__overap_1668_; lean_object* v___x_1669_; lean_object* v_snd_1670_; lean_object* v___x_1671_; lean_object* v_snd_1672_; lean_object* v___f_1673_; size_t v_sz_1674_; lean_object* v___x_4003__overap_1675_; lean_object* v___x_1676_; lean_object* v_snd_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v___x_1643_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
v___x_1644_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___f_1645_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0);
v___x_1646_ = lean_unsigned_to_nat(1u);
v___x_1647_ = lean_nat_add(v_level_1639_, v___x_1646_);
lean_inc(v___x_1647_);
v___x_1648_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1645_, v___x_1647_, v___x_1644_);
v___x_1649_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1648_, v_a_1642_);
lean_dec(v___x_1648_);
v_snd_1650_ = lean_ctor_get(v___x_1649_, 1);
lean_inc(v_snd_1650_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_1652_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1651_, v_snd_1650_);
v_snd_1653_ = lean_ctor_get(v___x_1652_, 1);
lean_inc(v_snd_1653_);
lean_dec_ref(v___x_1652_);
v_title_1654_ = lean_ctor_get(v_part_1640_, 0);
lean_inc_ref(v_title_1654_);
v_content_1655_ = lean_ctor_get(v_part_1640_, 3);
lean_inc_ref(v_content_1655_);
v_subParts_1656_ = lean_ctor_get(v_part_1640_, 4);
lean_inc_ref(v_subParts_1656_);
lean_dec_ref(v_part_1640_);
v___x_1657_ = lean_box(0);
lean_inc_ref(v_inst_1637_);
v___f_1658_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1658_, 0, v_inst_1637_);
lean_closure_set(v___f_1658_, 1, v___x_1657_);
v_sz_1659_ = lean_array_size(v_title_1654_);
v___x_1660_ = ((size_t)0ULL);
v___x_3967__overap_1661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1643_, v_title_1654_, v___f_1658_, v_sz_1659_, v___x_1660_, v___x_1657_);
lean_inc_ref(v_a_1641_);
v___x_1662_ = lean_apply_2(v___x_3967__overap_1661_, v_a_1641_, v_snd_1653_);
v_snd_1663_ = lean_ctor_get(v___x_1662_, 1);
lean_inc(v_snd_1663_);
lean_dec_ref(v___x_1662_);
v___x_1664_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1663_);
v_snd_1665_ = lean_ctor_get(v___x_1664_, 1);
lean_inc(v_snd_1665_);
lean_dec_ref(v___x_1664_);
lean_inc_ref(v_inst_1638_);
lean_inc_ref(v_inst_1637_);
v___f_1666_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1666_, 0, v_inst_1637_);
lean_closure_set(v___f_1666_, 1, v_inst_1638_);
lean_closure_set(v___f_1666_, 2, v___x_1657_);
v_sz_1667_ = lean_array_size(v_content_1655_);
v___x_3985__overap_1668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1643_, v_content_1655_, v___f_1666_, v_sz_1667_, v___x_1660_, v___x_1657_);
lean_inc_ref(v_a_1641_);
v___x_1669_ = lean_apply_2(v___x_3985__overap_1668_, v_a_1641_, v_snd_1665_);
v_snd_1670_ = lean_ctor_get(v___x_1669_, 1);
lean_inc(v_snd_1670_);
lean_dec_ref(v___x_1669_);
v___x_1671_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1670_);
v_snd_1672_ = lean_ctor_get(v___x_1671_, 1);
lean_inc(v_snd_1672_);
lean_dec_ref(v___x_1671_);
v___f_1673_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3___boxed), 9, 4);
lean_closure_set(v___f_1673_, 0, v_inst_1637_);
lean_closure_set(v___f_1673_, 1, v_inst_1638_);
lean_closure_set(v___f_1673_, 2, v___x_1647_);
lean_closure_set(v___f_1673_, 3, v___x_1657_);
v_sz_1674_ = lean_array_size(v_subParts_1656_);
v___x_4003__overap_1675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1643_, v_subParts_1656_, v___f_1673_, v_sz_1674_, v___x_1660_, v___x_1657_);
lean_inc_ref(v_a_1641_);
v___x_1676_ = lean_apply_2(v___x_4003__overap_1675_, v_a_1641_, v_snd_1672_);
v_snd_1677_ = lean_ctor_get(v___x_1676_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v___x_1676_, 0);
lean_dec(v_unused_1685_);
v___x_1679_ = v___x_1676_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_snd_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v___x_1657_);
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_snd_1677_);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3(lean_object* v_inst_1686_, lean_object* v_inst_1687_, lean_object* v___x_1688_, lean_object* v___x_1689_, lean_object* v_a_1690_, lean_object* v_x_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1695_; lean_object* v_snd_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1704_; 
v___x_1695_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1686_, v_inst_1687_, v___x_1688_, v_a_1690_, v___y_1693_, v___y_1694_);
v_snd_1696_ = lean_ctor_get(v___x_1695_, 1);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; 
v_unused_1705_ = lean_ctor_get(v___x_1695_, 0);
lean_dec(v_unused_1705_);
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_snd_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1689_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1700_);
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_snd_1696_);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_level_1708_, lean_object* v_part_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1706_, v_inst_1707_, v_level_1708_, v_part_1709_, v_a_1710_, v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_level_1708_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown(lean_object* v_i_1713_, lean_object* v_b_1714_, lean_object* v_p_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_level_1718_, lean_object* v_part_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1716_, v_inst_1717_, v_level_1718_, v_part_1719_, v_a_1720_, v_a_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___boxed(lean_object* v_i_1723_, lean_object* v_b_1724_, lean_object* v_p_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_level_1728_, lean_object* v_part_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown(v_i_1723_, v_b_1724_, v_p_1725_, v_inst_1726_, v_inst_1727_, v_level_1728_, v_part_1729_, v_a_1730_, v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_level_1728_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_part_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_unsigned_to_nat(0u);
v___x_1739_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1733_, v_inst_1734_, v___x_1738_, v_part_1735_, v_a_1736_, v_a_1737_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_part_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1740_, v_inst_1741_, v_part_1742_, v_a_1743_, v_a_1744_);
lean_dec_ref(v_a_1743_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1746_, lean_object* v_b_1747_, lean_object* v_p_1748_, lean_object* v_inst_1749_, lean_object* v_inst_1750_, lean_object* v_part_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1749_, v_inst_1750_, v___x_1754_, v_part_1751_, v_a_1752_, v_a_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1756_, lean_object* v_b_1757_, lean_object* v_p_1758_, lean_object* v_inst_1759_, lean_object* v_inst_1760_, lean_object* v_part_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1756_, v_b_1757_, v_p_1758_, v_inst_1759_, v_inst_1760_, v_part_1761_, v_a_1762_, v_a_1763_);
lean_dec_ref(v_a_1762_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_part_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1765_, v_inst_1766_, v___x_1770_, v_part_1767_, v___y_1768_, v___y_1769_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_part_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_1772_, v_inst_1773_, v_part_1774_, v___y_1775_, v___y_1776_);
lean_dec_ref(v___y_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1778_, lean_object* v_inst_1779_){
_start:
{
lean_object* v___f_1780_; 
v___f_1780_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1780_, 0, v_inst_1778_);
lean_closure_set(v___f_1780_, 1, v_inst_1779_);
return v___f_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1781_, lean_object* v_b_1782_, lean_object* v_p_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_){
_start:
{
lean_object* v___f_1786_; 
v___f_1786_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1786_, 0, v_inst_1784_);
lean_closure_set(v___f_1786_, 1, v_inst_1785_);
return v___f_1786_;
}
}
lean_object* runtime_initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Markdown(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1 = _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Markdown(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Markdown(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Markdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Markdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Markdown(builtin);
}
#ifdef __cplusplus
}
#endif
