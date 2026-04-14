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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Doc_Inline_empty(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_indent___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__1_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35_value;
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_212_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
lean_inc_ref(v_linePrefix_211_);
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
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_indent___redArg___boxed(lean_object* v_x_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Doc_MarkdownM_indent___redArg(v_x_216_, v_a_217_, v_a_218_);
lean_dec_ref(v_a_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_indent(lean_object* v_00_u03b1_220_, lean_object* v_x_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Doc_MarkdownM_indent___redArg(v_x_221_, v_a_222_, v_a_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_indent___boxed(lean_object* v_00_u03b1_225_, lean_object* v_x_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Doc_MarkdownM_indent(v_00_u03b1_225_, v_x_226_, v_a_227_, v_a_228_);
lean_dec_ref(v_a_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object* v_a_230_, uint8_t v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
uint8_t v_a_15__boxed_240_; lean_object* v_res_241_; 
v_a_15__boxed_240_ = lean_unbox(v_a_236_);
v_res_241_ = l_Lean_Doc_instMarkdownInlineEmpty___lam__0(v_a_235_, v_a_15__boxed_240_, v_a_237_, v_a_238_, v_a_239_);
lean_dec_ref(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec_ref(v_a_235_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0(lean_object* v_a_244_, lean_object* v_a_245_, uint8_t v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed(lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
uint8_t v_a_19__boxed_256_; lean_object* v_res_257_; 
v_a_19__boxed_256_ = lean_unbox(v_a_252_);
v_res_257_ = l_Lean_Doc_instMarkdownBlockEmpty___lam__0(v_a_250_, v_a_251_, v_a_19__boxed_256_, v_a_253_, v_a_254_, v_a_255_);
lean_dec_ref(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec_ref(v_a_251_);
lean_dec_ref(v_a_250_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object* v_i_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___closed__0));
return v___f_260_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(lean_object* v_s_261_, uint32_t v_c_262_, lean_object* v_a_263_, uint8_t v_b_264_){
_start:
{
lean_object* v_str_265_; lean_object* v_startInclusive_266_; lean_object* v_endExclusive_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_str_265_ = lean_ctor_get(v_s_261_, 0);
v_startInclusive_266_ = lean_ctor_get(v_s_261_, 1);
v_endExclusive_267_ = lean_ctor_get(v_s_261_, 2);
v___x_268_ = lean_nat_sub(v_endExclusive_267_, v_startInclusive_266_);
v___x_269_ = lean_nat_dec_eq(v_a_263_, v___x_268_);
lean_dec(v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; uint32_t v___x_271_; uint8_t v___x_272_; 
v___x_270_ = lean_nat_add(v_startInclusive_266_, v_a_263_);
lean_dec(v_a_263_);
v___x_271_ = lean_string_utf8_get_fast(v_str_265_, v___x_270_);
v___x_272_ = lean_uint32_dec_eq(v___x_271_, v_c_262_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_string_utf8_next_fast(v_str_265_, v___x_270_);
lean_dec(v___x_270_);
v___x_274_ = lean_nat_sub(v___x_273_, v_startInclusive_266_);
v_a_263_ = v___x_274_;
v_b_264_ = v___x_272_;
goto _start;
}
else
{
lean_dec(v___x_270_);
return v___x_272_;
}
}
else
{
lean_dec(v_a_263_);
return v_b_264_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg___boxed(lean_object* v_s_276_, lean_object* v_c_277_, lean_object* v_a_278_, lean_object* v_b_279_){
_start:
{
uint32_t v_c_boxed_280_; uint8_t v_b_boxed_281_; uint8_t v_res_282_; lean_object* v_r_283_; 
v_c_boxed_280_ = lean_unbox_uint32(v_c_277_);
lean_dec(v_c_277_);
v_b_boxed_281_ = lean_unbox(v_b_279_);
v_res_282_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(v_s_276_, v_c_boxed_280_, v_a_278_, v_b_boxed_281_);
lean_dec_ref(v_s_276_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0(uint32_t v_c_284_, lean_object* v_s_285_){
_start:
{
lean_object* v_searcher_286_; uint8_t v___x_287_; uint8_t v___x_288_; 
v_searcher_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = 0;
v___x_288_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(v_s_285_, v_c_284_, v_searcher_286_, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0___boxed(lean_object* v_c_289_, lean_object* v_s_290_){
_start:
{
uint32_t v_c_boxed_291_; uint8_t v_res_292_; lean_object* v_r_293_; 
v_c_boxed_291_ = lean_unbox_uint32(v_c_289_);
lean_dec(v_c_289_);
v_res_292_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0(v_c_boxed_291_, v_s_290_);
lean_dec_ref(v_s_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__0));
v___x_296_ = lean_string_utf8_byte_size(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__0));
v___x_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
lean_ctor_set(v___x_300_, 2, v___x_297_);
return v___x_300_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial(uint32_t v_c_301_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2);
v___x_303_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0(v_c_301_, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___boxed(lean_object* v_c_304_){
_start:
{
uint32_t v_c_boxed_305_; uint8_t v_res_306_; lean_object* v_r_307_; 
v_c_boxed_305_ = lean_unbox_uint32(v_c_304_);
lean_dec(v_c_304_);
v_res_306_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial(v_c_boxed_305_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0(lean_object* v_s_308_, uint32_t v_c_309_, lean_object* v_inst_310_, lean_object* v_R_311_, lean_object* v_a_312_, uint8_t v_b_313_, lean_object* v_c_314_){
_start:
{
uint8_t v___x_315_; 
v___x_315_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(v_s_308_, v_c_309_, v_a_312_, v_b_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___boxed(lean_object* v_s_316_, lean_object* v_c_317_, lean_object* v_inst_318_, lean_object* v_R_319_, lean_object* v_a_320_, lean_object* v_b_321_, lean_object* v_c_322_){
_start:
{
uint32_t v_c_boxed_323_; uint8_t v_b_boxed_324_; uint8_t v_res_325_; lean_object* v_r_326_; 
v_c_boxed_323_ = lean_unbox_uint32(v_c_317_);
lean_dec(v_c_317_);
v_b_boxed_324_ = lean_unbox(v_b_321_);
v_res_325_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0(v_s_316_, v_c_boxed_323_, v_inst_318_, v_R_319_, v_a_320_, v_b_boxed_324_, v_c_322_);
lean_dec_ref(v_s_316_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object* v_s_327_, lean_object* v_b_328_){
_start:
{
lean_object* v_fst_329_; lean_object* v_snd_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_351_; 
v_fst_329_ = lean_ctor_get(v_b_328_, 0);
v_snd_330_ = lean_ctor_get(v_b_328_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v_b_328_);
if (v_isSharedCheck_351_ == 0)
{
v___x_332_ = v_b_328_;
v_isShared_333_ = v_isSharedCheck_351_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_snd_330_);
lean_inc(v_fst_329_);
lean_dec(v_b_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_351_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_string_utf8_byte_size(v_s_327_);
v___x_335_ = lean_nat_dec_eq(v_snd_330_, v___x_334_);
if (v___x_335_ == 0)
{
uint32_t v_c_336_; lean_object* v_iter_337_; lean_object* v_s_x27_339_; uint8_t v___x_345_; 
v_c_336_ = lean_string_utf8_get_fast(v_s_327_, v_snd_330_);
v_iter_337_ = lean_string_utf8_next_fast(v_s_327_, v_snd_330_);
lean_dec(v_snd_330_);
v___x_345_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial(v_c_336_);
if (v___x_345_ == 0)
{
v_s_x27_339_ = v_fst_329_;
goto v___jp_338_;
}
else
{
uint32_t v___x_346_; lean_object* v_s_x27_347_; 
v___x_346_ = 92;
v_s_x27_347_ = lean_string_push(v_fst_329_, v___x_346_);
v_s_x27_339_ = v_s_x27_347_;
goto v___jp_338_;
}
v___jp_338_:
{
lean_object* v_s_x27_340_; lean_object* v___x_342_; 
v_s_x27_340_ = lean_string_push(v_s_x27_339_, v_c_336_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_iter_337_);
lean_ctor_set(v___x_332_, 0, v_s_x27_340_);
v___x_342_ = v___x_332_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_s_x27_340_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_iter_337_);
v___x_342_ = v_reuseFailAlloc_344_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
v_b_328_ = v___x_342_;
goto _start;
}
}
}
else
{
lean_object* v___x_349_; 
if (v_isShared_333_ == 0)
{
v___x_349_ = v___x_332_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_fst_329_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_snd_330_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object* v_s_352_, lean_object* v_b_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_352_, v_b_353_);
lean_dec_ref(v_s_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object* v_s_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_fst_361_; 
v___x_359_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0));
v___x_360_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_358_, v___x_359_);
v_fst_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_fst_361_);
lean_dec_ref(v___x_360_);
return v_fst_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object* v_s_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_362_);
lean_dec_ref(v_s_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0(lean_object* v_str_364_, lean_object* v_b_365_){
_start:
{
lean_object* v_snd_366_; lean_object* v_fst_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_409_; 
v_snd_366_ = lean_ctor_get(v_b_365_, 1);
v_fst_367_ = lean_ctor_get(v_b_365_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_b_365_);
if (v_isSharedCheck_409_ == 0)
{
v___x_369_ = v_b_365_;
v_isShared_370_ = v_isSharedCheck_409_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_snd_366_);
lean_inc(v_fst_367_);
lean_dec(v_b_365_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_409_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v_fst_371_; lean_object* v_snd_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_408_; 
v_fst_371_ = lean_ctor_get(v_snd_366_, 0);
v_snd_372_ = lean_ctor_get(v_snd_366_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v_snd_366_);
if (v_isSharedCheck_408_ == 0)
{
v___x_374_ = v_snd_366_;
v_isShared_375_ = v_isSharedCheck_408_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_snd_372_);
lean_inc(v_fst_371_);
lean_dec(v_snd_366_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_408_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = lean_string_utf8_byte_size(v_str_364_);
v___x_377_ = lean_nat_dec_eq(v_snd_372_, v___x_376_);
if (v___x_377_ == 0)
{
uint32_t v_c_378_; lean_object* v_iter_379_; uint32_t v___x_380_; uint8_t v___x_381_; 
v_c_378_ = lean_string_utf8_get_fast(v_str_364_, v_snd_372_);
v_iter_379_ = lean_string_utf8_next_fast(v_str_364_, v_snd_372_);
lean_dec(v_snd_372_);
v___x_380_ = 96;
v___x_381_ = lean_uint32_dec_eq(v_c_378_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v_current_382_; lean_object* v___y_384_; uint8_t v___x_392_; 
v_current_382_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_nat_dec_le(v_fst_367_, v_fst_371_);
if (v___x_392_ == 0)
{
lean_dec(v_fst_371_);
v___y_384_ = v_fst_367_;
goto v___jp_383_;
}
else
{
lean_dec(v_fst_367_);
v___y_384_ = v_fst_371_;
goto v___jp_383_;
}
v___jp_383_:
{
lean_object* v___x_386_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 1, v_iter_379_);
lean_ctor_set(v___x_374_, 0, v_current_382_);
v___x_386_ = v___x_374_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_current_382_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_iter_379_);
v___x_386_ = v_reuseFailAlloc_391_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_388_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_386_);
lean_ctor_set(v___x_369_, 0, v___y_384_);
v___x_388_ = v___x_369_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___y_384_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___x_386_);
v___x_388_ = v_reuseFailAlloc_390_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
v_b_365_ = v___x_388_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_393_; lean_object* v_current_394_; lean_object* v___x_396_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v_current_394_ = lean_nat_add(v_fst_371_, v___x_393_);
lean_dec(v_fst_371_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 1, v_iter_379_);
lean_ctor_set(v___x_374_, 0, v_current_394_);
v___x_396_ = v___x_374_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_current_394_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_iter_379_);
v___x_396_ = v_reuseFailAlloc_401_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_398_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_396_);
v___x_398_ = v___x_369_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_fst_367_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v___x_396_);
v___x_398_ = v_reuseFailAlloc_400_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
v_b_365_ = v___x_398_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_403_; 
if (v_isShared_375_ == 0)
{
v___x_403_ = v___x_374_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_fst_371_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_snd_372_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_403_);
v___x_405_ = v___x_369_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_fst_367_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0___boxed(lean_object* v_str_410_, lean_object* v_b_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0(v_str_410_, v_b_411_);
lean_dec_ref(v_str_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__1(lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
lean_object* v_zero_415_; uint8_t v_isZero_416_; 
v_zero_415_ = lean_unsigned_to_nat(0u);
v_isZero_416_ = lean_nat_dec_eq(v_x_413_, v_zero_415_);
if (v_isZero_416_ == 1)
{
lean_dec(v_x_413_);
return v_x_414_;
}
else
{
uint32_t v___x_417_; lean_object* v_one_418_; lean_object* v_n_419_; lean_object* v___x_420_; 
v___x_417_ = 96;
v_one_418_ = lean_unsigned_to_nat(1u);
v_n_419_ = lean_nat_sub(v_x_413_, v_one_418_);
lean_dec(v_x_413_);
v___x_420_ = lean_string_push(v_x_414_, v___x_417_);
v_x_413_ = v_n_419_;
v_x_414_ = v___x_420_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_425_ = lean_string_utf8_byte_size(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object* v_str_431_){
_start:
{
lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_438_; lean_object* v_current_442_; lean_object* v___y_444_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v_snd_453_; lean_object* v_fst_454_; lean_object* v_fst_455_; lean_object* v___x_456_; lean_object* v___y_458_; uint8_t v___x_467_; 
v_current_442_ = lean_unsigned_to_nat(0u);
v___x_451_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__4));
v___x_452_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0(v_str_431_, v___x_451_);
v_snd_453_ = lean_ctor_get(v___x_452_, 1);
lean_inc(v_snd_453_);
v_fst_454_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_fst_454_);
lean_dec_ref(v___x_452_);
v_fst_455_ = lean_ctor_get(v_snd_453_, 0);
lean_inc(v_fst_455_);
lean_dec(v_snd_453_);
v___x_456_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_467_ = lean_nat_dec_le(v_fst_454_, v_fst_455_);
if (v___x_467_ == 0)
{
lean_dec(v_fst_455_);
v___y_458_ = v_fst_454_;
goto v___jp_457_;
}
else
{
lean_dec(v_fst_454_);
v___y_458_ = v_fst_455_;
goto v___jp_457_;
}
v___jp_432_:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_inc_ref(v___y_433_);
v___x_435_ = lean_string_append(v___y_433_, v___y_434_);
lean_dec_ref(v___y_434_);
v___x_436_ = lean_string_append(v___x_435_, v___y_433_);
lean_dec_ref(v___y_433_);
return v___x_436_;
}
v___jp_437_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_440_ = lean_string_append(v___x_439_, v_str_431_);
lean_dec_ref(v_str_431_);
v___x_441_ = lean_string_append(v___x_440_, v___x_439_);
v___y_433_ = v___y_438_;
v___y_434_ = v___x_441_;
goto v___jp_432_;
}
v___jp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_445_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_446_ = lean_string_utf8_byte_size(v_str_431_);
v___x_447_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2);
v___x_448_ = lean_nat_dec_le(v___x_447_, v___x_446_);
if (v___x_448_ == 0)
{
v___y_433_ = v___y_444_;
v___y_434_ = v_str_431_;
goto v___jp_432_;
}
else
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_nat_sub(v___x_446_, v___x_447_);
v___x_450_ = lean_string_memcmp(v_str_431_, v___x_445_, v___x_449_, v_current_442_, v___x_447_);
lean_dec(v___x_449_);
if (v___x_450_ == 0)
{
v___y_433_ = v___y_444_;
v___y_434_ = v_str_431_;
goto v___jp_432_;
}
else
{
v___y_438_ = v___y_444_;
goto v___jp_437_;
}
}
}
v___jp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_add(v___y_458_, v___x_459_);
lean_dec(v___y_458_);
v___x_461_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__1(v___x_460_, v___x_456_);
v___x_462_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_463_ = lean_string_utf8_byte_size(v_str_431_);
v___x_464_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2);
v___x_465_ = lean_nat_dec_le(v___x_464_, v___x_463_);
if (v___x_465_ == 0)
{
v___y_444_ = v___x_461_;
goto v___jp_443_;
}
else
{
uint8_t v___x_466_; 
v___x_466_ = lean_string_memcmp(v_str_431_, v___x_462_, v_current_442_, v_current_442_, v___x_464_);
if (v___x_466_ == 0)
{
v___y_444_ = v___x_461_;
goto v___jp_443_;
}
else
{
v___y_438_ = v___x_461_;
goto v___jp_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_468_, lean_object* v_pos_469_){
_start:
{
lean_object* v_str_470_; lean_object* v_startInclusive_471_; lean_object* v_endExclusive_472_; lean_object* v___x_473_; uint8_t v___y_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_str_470_ = lean_ctor_get(v_s_468_, 0);
v_startInclusive_471_ = lean_ctor_get(v_s_468_, 1);
v_endExclusive_472_ = lean_ctor_get(v_s_468_, 2);
v___x_473_ = lean_nat_add(v_startInclusive_471_, v_pos_469_);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_nat_sub(v_endExclusive_472_, v___x_473_);
v___x_484_ = lean_nat_dec_eq(v___x_482_, v___x_483_);
lean_dec(v___x_483_);
if (v___x_484_ == 0)
{
uint32_t v___x_485_; uint8_t v___y_487_; uint32_t v___x_492_; uint8_t v___x_493_; 
v___x_485_ = lean_string_utf8_get_fast(v_str_470_, v___x_473_);
v___x_492_ = 32;
v___x_493_ = lean_uint32_dec_eq(v___x_485_, v___x_492_);
if (v___x_493_ == 0)
{
uint32_t v___x_494_; uint8_t v___x_495_; 
v___x_494_ = 9;
v___x_495_ = lean_uint32_dec_eq(v___x_485_, v___x_494_);
v___y_487_ = v___x_495_;
goto v___jp_486_;
}
else
{
v___y_487_ = v___x_493_;
goto v___jp_486_;
}
v___jp_486_:
{
if (v___y_487_ == 0)
{
uint32_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 13;
v___x_489_ = lean_uint32_dec_eq(v___x_485_, v___x_488_);
if (v___x_489_ == 0)
{
uint32_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = 10;
v___x_491_ = lean_uint32_dec_eq(v___x_485_, v___x_490_);
v___y_481_ = v___x_491_;
goto v___jp_480_;
}
else
{
v___y_481_ = v___x_489_;
goto v___jp_480_;
}
}
else
{
goto v___jp_474_;
}
}
}
else
{
lean_dec(v___x_473_);
return v_pos_469_;
}
v___jp_474_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_475_ = lean_string_utf8_next_fast(v_str_470_, v___x_473_);
v___x_476_ = lean_nat_sub(v___x_475_, v___x_473_);
lean_dec(v___x_473_);
v___x_477_ = lean_nat_add(v_pos_469_, v___x_476_);
lean_dec(v___x_476_);
v___x_478_ = lean_nat_dec_lt(v_pos_469_, v___x_477_);
if (v___x_478_ == 0)
{
lean_dec(v___x_477_);
return v_pos_469_;
}
else
{
lean_dec(v_pos_469_);
v_pos_469_ = v___x_477_;
goto _start;
}
}
v___jp_480_:
{
if (v___y_481_ == 0)
{
lean_dec(v___x_473_);
return v_pos_469_;
}
else
{
goto v___jp_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object* v_s_496_, lean_object* v_pos_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_496_, v_pos_497_);
lean_dec_ref(v_s_496_);
return v_res_498_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Doc_Inline_empty(lean_box(0));
return v___x_499_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_501_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v___x_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object* v_a_503_){
_start:
{
if (lean_obj_tag(v_a_503_) == 0)
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
return v___x_504_;
}
else
{
lean_object* v_head_505_; 
v_head_505_ = lean_ctor_get(v_a_503_, 0);
lean_inc(v_head_505_);
switch(lean_obj_tag(v_head_505_))
{
case 0:
{
lean_object* v_tail_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_552_; 
v_tail_506_ = lean_ctor_get(v_a_503_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_a_503_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v_a_503_, 0);
lean_dec(v_unused_553_);
v___x_508_ = v_a_503_;
v_isShared_509_ = v_isSharedCheck_552_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_tail_506_);
lean_dec(v_a_503_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_552_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_string_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_551_; 
v_string_510_ = lean_ctor_get(v_head_505_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v_head_505_);
if (v_isSharedCheck_551_ == 0)
{
v___x_512_ = v_head_505_;
v_isShared_513_ = v_isSharedCheck_551_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_string_510_);
lean_dec(v_head_505_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_551_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_string_utf8_byte_size(v_string_510_);
lean_inc_ref(v_string_510_);
v___x_516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_516_, 0, v_string_510_);
lean_ctor_set(v___x_516_, 1, v___x_514_);
lean_ctor_set(v___x_516_, 2, v___x_515_);
v___x_517_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_516_, v___x_514_);
v___x_518_ = lean_nat_dec_eq(v___x_517_, v___x_515_);
if (v___x_518_ == 0)
{
lean_object* v_s1_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_s2_522_; lean_object* v___x_524_; 
v_s1_519_ = lean_string_utf8_extract(v_string_510_, v___x_514_, v___x_517_);
lean_dec(v___x_517_);
v___x_520_ = lean_string_length(v_s1_519_);
v___x_521_ = l_String_Slice_Pos_nextn(v___x_516_, v___x_514_, v___x_520_);
lean_dec_ref(v___x_516_);
v_s2_522_ = lean_string_utf8_extract(v_string_510_, v___x_521_, v___x_515_);
lean_dec(v___x_521_);
lean_dec_ref(v_string_510_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v_s2_522_);
v___x_524_ = v___x_512_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_s2_522_);
v___x_524_ = v_reuseFailAlloc_539_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_525_ = lean_array_mk(v_tail_506_);
v___x_526_ = lean_array_get_size(v___x_525_);
v___x_527_ = lean_nat_dec_eq(v___x_526_, v___x_514_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_mk_empty_array_with_capacity(v___x_528_);
v___x_530_ = lean_array_push(v___x_529_, v___x_524_);
v___x_531_ = l_Array_append___redArg(v___x_530_, v___x_525_);
lean_dec_ref(v___x_525_);
v___x_532_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 0);
lean_ctor_set(v___x_508_, 1, v___x_532_);
lean_ctor_set(v___x_508_, 0, v_s1_519_);
v___x_534_ = v___x_508_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_s1_519_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
else
{
lean_object* v___x_537_; 
lean_dec_ref(v___x_525_);
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 0);
lean_ctor_set(v___x_508_, 1, v___x_524_);
lean_ctor_set(v___x_508_, 0, v_s1_519_);
v___x_537_ = v___x_508_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_s1_519_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_524_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v___x_540_; lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_550_; 
lean_dec(v___x_517_);
lean_dec_ref(v___x_516_);
lean_del_object(v___x_512_);
lean_del_object(v___x_508_);
v___x_540_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_506_);
v_fst_541_ = lean_ctor_get(v___x_540_, 0);
v_snd_542_ = lean_ctor_get(v___x_540_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_550_ == 0)
{
v___x_544_ = v___x_540_;
v_isShared_545_ = v_isSharedCheck_550_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_snd_542_);
lean_inc(v_fst_541_);
lean_dec(v___x_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_550_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = lean_string_append(v_string_510_, v_fst_541_);
lean_dec(v_fst_541_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_546_);
v___x_548_ = v___x_544_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_snd_542_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_554_; lean_object* v_content_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_tail_554_ = lean_ctor_get(v_a_503_, 1);
lean_inc(v_tail_554_);
lean_dec_ref(v_a_503_);
v_content_555_ = lean_ctor_get(v_head_505_, 0);
lean_inc_ref(v_content_555_);
lean_dec_ref(v_head_505_);
v___x_556_ = lean_array_to_list(v_content_555_);
v___x_557_ = l_List_appendTR___redArg(v___x_556_, v_tail_554_);
v_a_503_ = v___x_557_;
goto _start;
}
default: 
{
lean_object* v_tail_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_597_; 
v_tail_559_ = lean_ctor_get(v_a_503_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_a_503_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v_a_503_, 0);
lean_dec(v_unused_598_);
v___x_561_ = v_a_503_;
v_isShared_562_ = v_isSharedCheck_597_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_tail_559_);
lean_dec(v_a_503_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_597_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_564_ = lean_array_mk(v_tail_559_);
if (lean_obj_tag(v_head_505_) == 9)
{
lean_object* v_content_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_content_565_ = lean_ctor_get(v_head_505_, 0);
v___x_566_ = lean_array_get_size(v_content_565_);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_nat_dec_eq(v___x_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_array_get_size(v___x_564_);
v___x_570_ = lean_nat_dec_eq(v___x_569_, v___x_567_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
lean_inc_ref(v_content_565_);
lean_dec_ref(v_head_505_);
v___x_571_ = l_Array_append___redArg(v_content_565_, v___x_564_);
lean_dec_ref(v___x_564_);
v___x_572_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 0);
lean_ctor_set(v___x_561_, 1, v___x_572_);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_574_ = v___x_561_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
else
{
lean_object* v___x_577_; 
lean_dec_ref(v___x_564_);
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 0);
lean_ctor_set(v___x_561_, 1, v_head_505_);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_577_ = v___x_561_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_head_505_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
lean_object* v___x_579_; lean_object* v___x_581_; 
lean_dec_ref(v_head_505_);
v___x_579_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_564_);
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 0);
lean_ctor_set(v___x_561_, 1, v___x_579_);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_581_ = v___x_561_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_583_ = lean_array_get_size(v___x_564_);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_nat_dec_eq(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_mk_empty_array_with_capacity(v___x_586_);
v___x_588_ = lean_array_push(v___x_587_, v_head_505_);
v___x_589_ = l_Array_append___redArg(v___x_588_, v___x_564_);
lean_dec_ref(v___x_564_);
v___x_590_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 0);
lean_ctor_set(v___x_561_, 1, v___x_590_);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_592_ = v___x_561_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
else
{
lean_object* v___x_595_; 
lean_dec_ref(v___x_564_);
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 0);
lean_ctor_set(v___x_561_, 1, v_head_505_);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_595_ = v___x_561_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_head_505_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_599_, lean_object* v_a_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_602_){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_box(0);
v___x_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_604_, 0, v_inline_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_606_, lean_object* v_inline_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_609_, lean_object* v_pos_610_){
_start:
{
lean_object* v_str_611_; lean_object* v_startInclusive_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_str_611_ = lean_ctor_get(v_s_609_, 0);
v_startInclusive_612_ = lean_ctor_get(v_s_609_, 1);
v___x_613_ = lean_nat_add(v_startInclusive_612_, v_pos_610_);
v___x_614_ = lean_nat_sub(v___x_613_, v_startInclusive_612_);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_nat_dec_eq(v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___y_625_; lean_object* v___x_626_; uint32_t v___x_627_; uint8_t v___y_629_; uint32_t v___x_634_; uint8_t v___x_635_; 
lean_inc(v_startInclusive_612_);
lean_inc_ref(v_str_611_);
v___x_617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_617_, 0, v_str_611_);
lean_ctor_set(v___x_617_, 1, v_startInclusive_612_);
lean_ctor_set(v___x_617_, 2, v___x_613_);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_sub(v___x_614_, v___x_618_);
lean_dec(v___x_614_);
v___x_620_ = l_String_Slice_posLE(v___x_617_, v___x_619_);
lean_dec_ref(v___x_617_);
v___x_626_ = lean_nat_add(v_startInclusive_612_, v___x_620_);
v___x_627_ = lean_string_utf8_get_fast(v_str_611_, v___x_626_);
lean_dec(v___x_626_);
v___x_634_ = 32;
v___x_635_ = lean_uint32_dec_eq(v___x_627_, v___x_634_);
if (v___x_635_ == 0)
{
uint32_t v___x_636_; uint8_t v___x_637_; 
v___x_636_ = 9;
v___x_637_ = lean_uint32_dec_eq(v___x_627_, v___x_636_);
v___y_629_ = v___x_637_;
goto v___jp_628_;
}
else
{
v___y_629_ = v___x_635_;
goto v___jp_628_;
}
v___jp_621_:
{
uint8_t v___x_622_; 
v___x_622_ = lean_nat_dec_lt(v___x_620_, v_pos_610_);
if (v___x_622_ == 0)
{
lean_dec(v___x_620_);
return v_pos_610_;
}
else
{
lean_dec(v_pos_610_);
v_pos_610_ = v___x_620_;
goto _start;
}
}
v___jp_624_:
{
if (v___y_625_ == 0)
{
lean_dec(v___x_620_);
return v_pos_610_;
}
else
{
goto v___jp_621_;
}
}
v___jp_628_:
{
if (v___y_629_ == 0)
{
uint32_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = 13;
v___x_631_ = lean_uint32_dec_eq(v___x_627_, v___x_630_);
if (v___x_631_ == 0)
{
uint32_t v___x_632_; uint8_t v___x_633_; 
v___x_632_ = 10;
v___x_633_ = lean_uint32_dec_eq(v___x_627_, v___x_632_);
v___y_625_ = v___x_633_;
goto v___jp_624_;
}
else
{
v___y_625_ = v___x_631_;
goto v___jp_624_;
}
}
else
{
goto v___jp_621_;
}
}
}
else
{
lean_dec(v___x_614_);
lean_dec(v___x_613_);
return v_pos_610_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_638_, lean_object* v_pos_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_638_, v_pos_639_);
lean_dec_ref(v_s_638_);
return v_res_640_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_642_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_a_644_){
_start:
{
lean_object* v___y_646_; 
if (lean_obj_tag(v_a_644_) == 0)
{
lean_object* v___x_649_; 
v___x_649_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_649_;
}
else
{
lean_object* v_head_650_; 
v_head_650_ = lean_ctor_get(v_a_644_, 0);
lean_inc(v_head_650_);
switch(lean_obj_tag(v_head_650_))
{
case 0:
{
lean_object* v_tail_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_696_; 
v_tail_651_ = lean_ctor_get(v_a_644_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_a_644_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v_a_644_, 0);
lean_dec(v_unused_697_);
v___x_653_ = v_a_644_;
v_isShared_654_ = v_isSharedCheck_696_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_tail_651_);
lean_dec(v_a_644_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_696_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_string_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_695_; 
v_string_655_ = lean_ctor_get(v_head_650_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v_head_650_);
if (v_isSharedCheck_695_ == 0)
{
v___x_657_ = v_head_650_;
v_isShared_658_ = v_isSharedCheck_695_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_string_655_);
lean_dec(v_head_650_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_695_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_string_utf8_byte_size(v_string_655_);
lean_inc_ref(v_string_655_);
v___x_661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_661_, 0, v_string_655_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
lean_ctor_set(v___x_661_, 2, v___x_660_);
v___x_662_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_661_, v___x_659_);
v___x_663_ = lean_nat_dec_eq(v___x_662_, v___x_660_);
lean_dec(v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v_s1_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_s2_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_664_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_661_, v___x_660_);
v_s1_665_ = lean_string_utf8_extract(v_string_655_, v___x_664_, v___x_660_);
lean_dec(v___x_664_);
v___x_666_ = lean_string_length(v_s1_665_);
v___x_667_ = l_String_Slice_Pos_prevn(v___x_661_, v___x_660_, v___x_666_);
lean_dec_ref(v___x_661_);
v_s2_668_ = lean_string_utf8_extract(v_string_655_, v___x_659_, v___x_667_);
lean_dec(v___x_667_);
lean_dec_ref(v_string_655_);
v___x_669_ = lean_array_mk(v_tail_651_);
v___x_670_ = l_Array_reverse___redArg(v___x_669_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_s2_668_);
v___x_672_ = v___x_657_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_s2_668_);
v___x_672_ = v_reuseFailAlloc_683_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = lean_array_get_size(v___x_670_);
v___x_674_ = lean_nat_dec_eq(v___x_673_, v___x_659_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_675_ = lean_array_push(v___x_670_, v___x_672_);
v___x_676_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 0);
lean_ctor_set(v___x_653_, 1, v_s1_665_);
lean_ctor_set(v___x_653_, 0, v___x_676_);
v___x_678_ = v___x_653_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_s1_665_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
else
{
lean_object* v___x_681_; 
lean_dec_ref(v___x_670_);
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 0);
lean_ctor_set(v___x_653_, 1, v_s1_665_);
lean_ctor_set(v___x_653_, 0, v___x_672_);
v___x_681_ = v___x_653_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_s1_665_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
else
{
lean_object* v___x_684_; lean_object* v_fst_685_; lean_object* v_snd_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref(v___x_661_);
lean_del_object(v___x_657_);
lean_del_object(v___x_653_);
v___x_684_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_tail_651_);
v_fst_685_ = lean_ctor_get(v___x_684_, 0);
v_snd_686_ = lean_ctor_get(v___x_684_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_694_ == 0)
{
v___x_688_ = v___x_684_;
v_isShared_689_ = v_isSharedCheck_694_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_snd_686_);
lean_inc(v_fst_685_);
lean_dec(v___x_684_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_694_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = lean_string_append(v_snd_686_, v_string_655_);
lean_dec_ref(v_string_655_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_690_);
v___x_692_ = v___x_688_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_fst_685_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_698_; lean_object* v_content_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_tail_698_ = lean_ctor_get(v_a_644_, 1);
lean_inc(v_tail_698_);
lean_dec_ref(v_a_644_);
v_content_699_ = lean_ctor_get(v_head_650_, 0);
lean_inc_ref(v_content_699_);
lean_dec_ref(v_head_650_);
v___x_700_ = l_Array_reverse___redArg(v_content_699_);
v___x_701_ = lean_array_to_list(v___x_700_);
v___x_702_ = l_List_appendTR___redArg(v___x_701_, v_tail_698_);
v_a_644_ = v___x_702_;
goto _start;
}
default: 
{
lean_object* v_tail_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_tail_704_ = lean_ctor_get(v_a_644_, 1);
lean_inc(v_tail_704_);
lean_dec_ref(v_a_644_);
v___x_705_ = lean_array_mk(v_tail_704_);
v___x_706_ = l_Array_reverse___redArg(v___x_705_);
v___x_707_ = lean_array_get_size(v___x_706_);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_nat_dec_eq(v___x_707_, v___x_708_);
if (v___x_709_ == 0)
{
if (lean_obj_tag(v_head_650_) == 9)
{
lean_object* v_content_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_content_710_ = lean_ctor_get(v_head_650_, 0);
lean_inc_ref(v_content_710_);
lean_dec_ref(v_head_650_);
v___x_711_ = lean_array_get_size(v_content_710_);
v___x_712_ = lean_nat_dec_eq(v___x_711_, v___x_708_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = l_Array_append___redArg(v___x_706_, v_content_710_);
lean_dec_ref(v_content_710_);
v___x_714_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
v___y_646_ = v___x_714_;
goto v___jp_645_;
}
else
{
lean_object* v___x_715_; 
lean_dec_ref(v_content_710_);
v___x_715_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_706_);
v___y_646_ = v___x_715_;
goto v___jp_645_;
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_array_push(v___x_706_, v_head_650_);
v___x_717_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
v___y_646_ = v___x_717_;
goto v___jp_645_;
}
}
else
{
lean_dec_ref(v___x_706_);
v___y_646_ = v_head_650_;
goto v___jp_645_;
}
}
}
}
v___jp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v___y_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_718_, lean_object* v_a_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_a_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_721_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_box(0);
v___x_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_723_, 0, v_inline_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_725_, lean_object* v_inline_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_728_){
_start:
{
lean_object* v___x_729_; lean_object* v_fst_730_; lean_object* v_snd_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_739_; 
v___x_729_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_728_);
v_fst_730_ = lean_ctor_get(v___x_729_, 0);
v_snd_731_ = lean_ctor_get(v___x_729_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_739_ == 0)
{
v___x_733_ = v___x_729_;
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_snd_731_);
lean_inc(v_fst_730_);
lean_dec(v___x_729_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_731_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_fst_730_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_740_, lean_object* v_inline_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_741_);
return v___x_742_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19));
v___x_789_ = l_ReaderT_instMonad___redArg(v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_798_ = l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0(lean_object* v_inst_800_, lean_object* v___x_801_, lean_object* v_a_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___x_807_; lean_object* v_snd_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_816_; 
v___x_807_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_800_, v_a_802_, v___y_805_, v___y_806_);
v_snd_808_ = lean_ctor_get(v___x_807_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v___x_807_, 0);
lean_dec(v_unused_817_);
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_816_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_snd_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_816_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_801_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_812_);
v___x_814_ = v___x_810_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_snd_808_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed(lean_object* v_inst_818_, lean_object* v___x_819_, lean_object* v_a_820_, lean_object* v_x_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0(v_inst_818_, v___x_819_, v_a_820_, v_x_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2___boxed(lean_object* v_inst_836_, lean_object* v_x_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2(v_inst_836_, v_x_837_, v___y_838_, v___y_839_, v___y_840_);
lean_dec_ref(v___y_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object* v_inst_843_, lean_object* v_x_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_843_, v_x_844_, v_a_845_, v_a_846_);
lean_dec_ref(v_a_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_848_, lean_object* v_x_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
switch(lean_obj_tag(v_x_849_))
{
case 0:
{
lean_object* v_string_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec_ref(v_inst_848_);
v_string_853_ = lean_ctor_get(v_x_849_, 0);
lean_inc_ref(v_string_853_);
lean_dec_ref(v_x_849_);
v___x_854_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_853_);
lean_dec_ref(v_string_853_);
v___x_855_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_854_, v_a_851_);
lean_dec_ref(v___x_854_);
return v___x_855_;
}
case 1:
{
lean_object* v_content_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_897_; 
v_content_856_ = lean_ctor_get(v_x_849_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_897_ == 0)
{
v___x_858_ = v_x_849_;
v_isShared_859_ = v_isSharedCheck_897_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_content_856_);
lean_dec(v_x_849_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_897_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 9);
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_content_856_);
v___x_861_ = v_reuseFailAlloc_896_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v_snd_863_; lean_object* v_fst_864_; lean_object* v_fst_865_; lean_object* v_snd_866_; uint8_t v_inEmph_868_; uint8_t v_inBold_869_; uint8_t v_inLink_870_; lean_object* v_linePrefix_871_; lean_object* v___y_872_; lean_object* v___x_883_; uint8_t v_inEmph_884_; 
v___x_862_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_861_);
v_snd_863_ = lean_ctor_get(v___x_862_, 1);
lean_inc(v_snd_863_);
v_fst_864_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_fst_864_);
lean_dec_ref(v___x_862_);
v_fst_865_ = lean_ctor_get(v_snd_863_, 0);
lean_inc(v_fst_865_);
v_snd_866_ = lean_ctor_get(v_snd_863_, 1);
lean_inc(v_snd_866_);
lean_dec(v_snd_863_);
v___x_883_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_864_, v_a_851_);
lean_dec(v_fst_864_);
v_inEmph_884_ = lean_ctor_get_uint8(v_a_850_, sizeof(void*)*1);
if (v_inEmph_884_ == 0)
{
lean_object* v_snd_885_; uint8_t v_inBold_886_; uint8_t v_inLink_887_; lean_object* v_linePrefix_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v_snd_891_; 
v_snd_885_ = lean_ctor_get(v___x_883_, 1);
lean_inc(v_snd_885_);
lean_dec_ref(v___x_883_);
v_inBold_886_ = lean_ctor_get_uint8(v_a_850_, sizeof(void*)*1 + 1);
v_inLink_887_ = lean_ctor_get_uint8(v_a_850_, sizeof(void*)*1 + 2);
v_linePrefix_888_ = lean_ctor_get(v_a_850_, 0);
v___x_889_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21));
v___x_890_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_889_, v_snd_885_);
v_snd_891_ = lean_ctor_get(v___x_890_, 1);
lean_inc(v_snd_891_);
lean_dec_ref(v___x_890_);
v_inEmph_868_ = v_inEmph_884_;
v_inBold_869_ = v_inBold_886_;
v_inLink_870_ = v_inLink_887_;
v_linePrefix_871_ = v_linePrefix_888_;
v___y_872_ = v_snd_891_;
goto v___jp_867_;
}
else
{
lean_object* v_snd_892_; uint8_t v_inBold_893_; uint8_t v_inLink_894_; lean_object* v_linePrefix_895_; 
v_snd_892_ = lean_ctor_get(v___x_883_, 1);
lean_inc(v_snd_892_);
lean_dec_ref(v___x_883_);
v_inBold_893_ = lean_ctor_get_uint8(v_a_850_, sizeof(void*)*1 + 1);
v_inLink_894_ = lean_ctor_get_uint8(v_a_850_, sizeof(void*)*1 + 2);
v_linePrefix_895_ = lean_ctor_get(v_a_850_, 0);
v_inEmph_868_ = v_inEmph_884_;
v_inBold_869_ = v_inBold_893_;
v_inLink_870_ = v_inLink_894_;
v_linePrefix_871_ = v_linePrefix_895_;
v___y_872_ = v_snd_892_;
goto v___jp_867_;
}
v___jp_867_:
{
uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = 1;
lean_inc_ref(v_linePrefix_871_);
v___x_874_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_874_, 0, v_linePrefix_871_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*1, v___x_873_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*1 + 1, v_inBold_869_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*1 + 2, v_inLink_870_);
v___x_875_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_848_, v_fst_865_, v___x_874_, v___y_872_);
lean_dec_ref(v___x_874_);
if (v_inEmph_868_ == 0)
{
lean_object* v_snd_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v_snd_879_; lean_object* v___x_880_; 
v_snd_876_ = lean_ctor_get(v___x_875_, 1);
lean_inc(v_snd_876_);
lean_dec_ref(v___x_875_);
v___x_877_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21));
v___x_878_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_877_, v_snd_876_);
v_snd_879_ = lean_ctor_get(v___x_878_, 1);
lean_inc(v_snd_879_);
lean_dec_ref(v___x_878_);
v___x_880_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_866_, v_snd_879_);
lean_dec(v_snd_866_);
return v___x_880_;
}
else
{
lean_object* v_snd_881_; lean_object* v___x_882_; 
v_snd_881_ = lean_ctor_get(v___x_875_, 1);
lean_inc(v_snd_881_);
lean_dec_ref(v___x_875_);
v___x_882_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_866_, v_snd_881_);
lean_dec(v_snd_866_);
return v___x_882_;
}
}
}
}
}
case 2:
{
lean_object* v_content_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_936_; 
v_content_898_ = lean_ctor_get(v_x_849_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_936_ == 0)
{
v___x_900_ = v_x_849_;
v_isShared_901_ = v_isSharedCheck_936_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_content_898_);
lean_dec(v_x_849_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_936_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 9);
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_content_898_);
v___x_903_ = v_reuseFailAlloc_935_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v_snd_905_; lean_object* v_fst_906_; lean_object* v_fst_907_; lean_object* v_snd_908_; uint8_t v_inBold_910_; uint8_t v_inLink_911_; lean_object* v_linePrefix_912_; lean_object* v___y_913_; lean_object* v___x_924_; uint8_t v_inBold_925_; 
v___x_904_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_903_);
v_snd_905_ = lean_ctor_get(v___x_904_, 1);
lean_inc(v_snd_905_);
v_fst_906_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_fst_906_);
lean_dec_ref(v___x_904_);
v_fst_907_ = lean_ctor_get(v_snd_905_, 0);
lean_inc(v_fst_907_);
v_snd_908_ = lean_ctor_get(v_snd_905_, 1);
lean_inc(v_snd_908_);
lean_dec(v_snd_905_);
v___x_924_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_906_, v_a_851_);
lean_dec(v_fst_906_);
v_inBold_925_ = lean_ctor_get_uint8(v_a_850_, sizeof(void*)*1 + 1);
if (v_inBold_925_ == 0)
{
lean_object* v_snd_926_; uint8_t v_inLink_927_; lean_object* v_linePrefix_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_snd_931_; 
v_snd_926_ = lean_ctor_get(v___x_924_, 1);
lean_inc(v_snd_926_);
lean_dec_ref(v___x_924_);
v_inLink_927_ = lean_ctor_get_uint8(v_a_850_, sizeof(void*)*1 + 2);
v_linePrefix_928_ = lean_ctor_get(v_a_850_, 0);
v___x_929_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_930_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_929_, v_snd_926_);
v_snd_931_ = lean_ctor_get(v___x_930_, 1);
lean_inc(v_snd_931_);
lean_dec_ref(v___x_930_);
v_inBold_910_ = v_inBold_925_;
v_inLink_911_ = v_inLink_927_;
v_linePrefix_912_ = v_linePrefix_928_;
v___y_913_ = v_snd_931_;
goto v___jp_909_;
}
else
{
lean_object* v_snd_932_; uint8_t v_inLink_933_; lean_object* v_linePrefix_934_; 
v_snd_932_ = lean_ctor_get(v___x_924_, 1);
lean_inc(v_snd_932_);
lean_dec_ref(v___x_924_);
v_inLink_933_ = lean_ctor_get_uint8(v_a_850_, sizeof(void*)*1 + 2);
v_linePrefix_934_ = lean_ctor_get(v_a_850_, 0);
v_inBold_910_ = v_inBold_925_;
v_inLink_911_ = v_inLink_933_;
v_linePrefix_912_ = v_linePrefix_934_;
v___y_913_ = v_snd_932_;
goto v___jp_909_;
}
v___jp_909_:
{
uint8_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = 1;
lean_inc_ref(v_linePrefix_912_);
v___x_915_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_915_, 0, v_linePrefix_912_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*1, v___x_914_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*1 + 1, v_inBold_910_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*1 + 2, v_inLink_911_);
v___x_916_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_848_, v_fst_907_, v___x_915_, v___y_913_);
lean_dec_ref(v___x_915_);
if (v_inBold_910_ == 0)
{
lean_object* v_snd_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_snd_920_; lean_object* v___x_921_; 
v_snd_917_ = lean_ctor_get(v___x_916_, 1);
lean_inc(v_snd_917_);
lean_dec_ref(v___x_916_);
v___x_918_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_919_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_918_, v_snd_917_);
v_snd_920_ = lean_ctor_get(v___x_919_, 1);
lean_inc(v_snd_920_);
lean_dec_ref(v___x_919_);
v___x_921_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_908_, v_snd_920_);
lean_dec(v_snd_908_);
return v___x_921_;
}
else
{
lean_object* v_snd_922_; lean_object* v___x_923_; 
v_snd_922_ = lean_ctor_get(v___x_916_, 1);
lean_inc(v_snd_922_);
lean_dec_ref(v___x_916_);
v___x_923_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_908_, v_snd_922_);
lean_dec(v_snd_908_);
return v___x_923_;
}
}
}
}
}
case 3:
{
lean_object* v_string_937_; lean_object* v___y_939_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_fst_944_; uint8_t v___x_945_; 
lean_dec_ref(v_inst_848_);
v_string_937_ = lean_ctor_get(v_x_849_, 0);
lean_inc_ref(v_string_937_);
lean_dec_ref(v_x_849_);
v___x_942_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_943_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v___x_942_, v_a_851_);
v_fst_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_fst_944_);
v___x_945_ = lean_unbox(v_fst_944_);
lean_dec(v_fst_944_);
if (v___x_945_ == 0)
{
lean_object* v_snd_946_; 
v_snd_946_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_snd_946_);
lean_dec_ref(v___x_943_);
v___y_939_ = v_snd_946_;
goto v___jp_938_;
}
else
{
lean_object* v_snd_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_snd_950_; 
v_snd_947_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_snd_947_);
lean_dec_ref(v___x_943_);
v___x_948_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23));
v___x_949_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_948_, v_snd_947_);
v_snd_950_ = lean_ctor_get(v___x_949_, 1);
lean_inc(v_snd_950_);
lean_dec_ref(v___x_949_);
v___y_939_ = v_snd_950_;
goto v___jp_938_;
}
v___jp_938_:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_937_);
v___x_941_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_940_, v___y_939_);
lean_dec_ref(v___x_940_);
return v___x_941_;
}
}
case 4:
{
uint8_t v_mode_951_; 
lean_dec_ref(v_inst_848_);
v_mode_951_ = lean_ctor_get_uint8(v_x_849_, sizeof(void*)*1);
if (v_mode_951_ == 0)
{
lean_object* v_string_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_string_952_ = lean_ctor_get(v_x_849_, 0);
lean_inc_ref(v_string_952_);
lean_dec_ref(v_x_849_);
v___x_953_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24));
v___x_954_ = lean_string_append(v___x_953_, v_string_952_);
lean_dec_ref(v_string_952_);
v___x_955_ = lean_string_append(v___x_954_, v___x_953_);
v___x_956_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_955_, v_a_851_);
lean_dec_ref(v___x_955_);
return v___x_956_;
}
else
{
lean_object* v_string_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_string_957_ = lean_ctor_get(v_x_849_, 0);
lean_inc_ref(v_string_957_);
lean_dec_ref(v_x_849_);
v___x_958_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25));
v___x_959_ = lean_string_append(v___x_958_, v_string_957_);
lean_dec_ref(v_string_957_);
v___x_960_ = lean_string_append(v___x_959_, v___x_958_);
v___x_961_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_960_, v_a_851_);
lean_dec_ref(v___x_960_);
return v___x_961_;
}
}
case 5:
{
lean_object* v_string_962_; lean_object* v_linePrefix_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec_ref(v_inst_848_);
v_string_962_ = lean_ctor_get(v_x_849_, 0);
lean_inc_ref(v_string_962_);
lean_dec_ref(v_x_849_);
v_linePrefix_963_ = lean_ctor_get(v_a_850_, 0);
v___x_964_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26));
v___x_965_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27));
v___x_966_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_967_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28);
v___x_968_ = lean_string_append(v___x_966_, v_linePrefix_963_);
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = lean_string_utf8_byte_size(v_string_962_);
v___x_971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_971_, 0, v_string_962_);
lean_ctor_set(v___x_971_, 1, v___x_969_);
lean_ctor_set(v___x_971_, 2, v___x_970_);
v___x_972_ = l_String_Slice_replace___redArg(v___x_965_, v___x_964_, v___x_971_, v___x_967_, v___x_968_);
v___x_973_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_972_, v_a_851_);
lean_dec_ref(v___x_972_);
return v___x_973_;
}
case 6:
{
uint8_t v_inLink_974_; 
v_inLink_974_ = lean_ctor_get_uint8(v_a_850_, sizeof(void*)*1 + 2);
if (v_inLink_974_ == 0)
{
lean_object* v_content_975_; lean_object* v_url_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v_snd_979_; lean_object* v___x_980_; lean_object* v___f_981_; size_t v_sz_982_; size_t v___x_983_; lean_object* v___x_12052__overap_984_; lean_object* v___x_985_; lean_object* v_snd_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_snd_989_; lean_object* v___x_990_; lean_object* v_snd_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_content_975_ = lean_ctor_get(v_x_849_, 0);
lean_inc_ref(v_content_975_);
v_url_976_ = lean_ctor_get(v_x_849_, 1);
lean_inc_ref(v_url_976_);
lean_dec_ref(v_x_849_);
v___x_977_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29));
v___x_978_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_977_, v_a_851_);
v_snd_979_ = lean_ctor_get(v___x_978_, 1);
lean_inc(v_snd_979_);
lean_dec_ref(v___x_978_);
v___x_980_ = lean_box(0);
v___f_981_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_981_, 0, v_inst_848_);
lean_closure_set(v___f_981_, 1, v___x_980_);
v_sz_982_ = lean_array_size(v_content_975_);
v___x_983_ = ((size_t)0ULL);
v___x_12052__overap_984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_852_, v_content_975_, v___f_981_, v_sz_982_, v___x_983_, v___x_980_);
lean_inc_ref(v_a_850_);
v___x_985_ = lean_apply_2(v___x_12052__overap_984_, v_a_850_, v_snd_979_);
v_snd_986_ = lean_ctor_get(v___x_985_, 1);
lean_inc(v_snd_986_);
lean_dec_ref(v___x_985_);
v___x_987_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30));
v___x_988_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_987_, v_snd_986_);
v_snd_989_ = lean_ctor_get(v___x_988_, 1);
lean_inc(v_snd_989_);
lean_dec_ref(v___x_988_);
v___x_990_ = l_Lean_Doc_MarkdownM_push___redArg(v_url_976_, v_snd_989_);
lean_dec_ref(v_url_976_);
v_snd_991_ = lean_ctor_get(v___x_990_, 1);
lean_inc(v_snd_991_);
lean_dec_ref(v___x_990_);
v___x_992_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31));
v___x_993_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_992_, v_snd_991_);
return v___x_993_;
}
else
{
lean_object* v_content_994_; lean_object* v___x_995_; lean_object* v___f_996_; size_t v_sz_997_; size_t v___x_998_; lean_object* v___x_12076__overap_999_; lean_object* v___x_1000_; lean_object* v_snd_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
v_content_994_ = lean_ctor_get(v_x_849_, 0);
lean_inc_ref(v_content_994_);
lean_dec_ref(v_x_849_);
v___x_995_ = lean_box(0);
v___f_996_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_996_, 0, v_inst_848_);
lean_closure_set(v___f_996_, 1, v___x_995_);
v_sz_997_ = lean_array_size(v_content_994_);
v___x_998_ = ((size_t)0ULL);
v___x_12076__overap_999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_852_, v_content_994_, v___f_996_, v_sz_997_, v___x_998_, v___x_995_);
lean_inc_ref(v_a_850_);
v___x_1000_ = lean_apply_2(v___x_12076__overap_999_, v_a_850_, v_a_851_);
v_snd_1001_ = lean_ctor_get(v___x_1000_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1008_ == 0)
{
lean_object* v_unused_1009_; 
v_unused_1009_ = lean_ctor_get(v___x_1000_, 0);
lean_dec(v_unused_1009_);
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_snd_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_995_);
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_snd_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
case 7:
{
lean_object* v_name_1010_; lean_object* v_content_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v_snd_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1059_; 
v_name_1010_ = lean_ctor_get(v_x_849_, 0);
lean_inc_ref(v_name_1010_);
v_content_1011_ = lean_ctor_get(v_x_849_, 1);
lean_inc_ref(v_content_1011_);
lean_dec_ref(v_x_849_);
v___x_1012_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32));
v___x_1013_ = lean_string_append(v___x_1012_, v_name_1010_);
v___x_1014_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33));
v___x_1015_ = lean_string_append(v___x_1013_, v___x_1014_);
v___x_1016_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1015_, v_a_851_);
lean_dec_ref(v___x_1015_);
v_snd_1017_ = lean_ctor_get(v___x_1016_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v___x_1016_, 0);
lean_dec(v_unused_1060_);
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1059_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_snd_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1059_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v_snd_1022_; lean_object* v___y_1041_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = lean_array_get_size(v_content_1011_);
v___x_1045_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34));
v___x_1046_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35));
v___x_1047_ = lean_nat_dec_lt(v___x_1043_, v___x_1044_);
if (v___x_1047_ == 0)
{
lean_dec_ref(v_content_1011_);
lean_dec_ref(v_inst_848_);
v_snd_1022_ = v___x_1046_;
goto v___jp_1021_;
}
else
{
lean_object* v___x_1048_; lean_object* v___f_1049_; uint8_t v___x_1050_; 
v___x_1048_ = lean_box(0);
v___f_1049_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_1049_, 0, v_inst_848_);
v___x_1050_ = lean_nat_dec_le(v___x_1044_, v___x_1044_);
if (v___x_1050_ == 0)
{
if (v___x_1047_ == 0)
{
lean_dec_ref(v___f_1049_);
lean_dec_ref(v_content_1011_);
v_snd_1022_ = v___x_1046_;
goto v___jp_1021_;
}
else
{
size_t v___x_1051_; size_t v___x_1052_; lean_object* v___x_11895__overap_1053_; lean_object* v___x_1054_; 
v___x_1051_ = ((size_t)0ULL);
v___x_1052_ = lean_usize_of_nat(v___x_1044_);
v___x_11895__overap_1053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_852_, v___f_1049_, v_content_1011_, v___x_1051_, v___x_1052_, v___x_1048_);
v___x_1054_ = lean_apply_2(v___x_11895__overap_1053_, v___x_1045_, v___x_1046_);
v___y_1041_ = v___x_1054_;
goto v___jp_1040_;
}
}
else
{
size_t v___x_1055_; size_t v___x_1056_; lean_object* v___x_11899__overap_1057_; lean_object* v___x_1058_; 
v___x_1055_ = ((size_t)0ULL);
v___x_1056_ = lean_usize_of_nat(v___x_1044_);
v___x_11899__overap_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_852_, v___f_1049_, v_content_1011_, v___x_1055_, v___x_1056_, v___x_1048_);
v___x_1058_ = lean_apply_2(v___x_11899__overap_1057_, v___x_1045_, v___x_1046_);
v___y_1041_ = v___x_1058_;
goto v___jp_1040_;
}
}
v___jp_1021_:
{
lean_object* v_priorBlocks_1023_; lean_object* v_currentBlock_1024_; lean_object* v_footnotes_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1039_; 
v_priorBlocks_1023_ = lean_ctor_get(v_snd_1017_, 0);
v_currentBlock_1024_ = lean_ctor_get(v_snd_1017_, 1);
v_footnotes_1025_ = lean_ctor_get(v_snd_1017_, 2);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_snd_1017_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1027_ = v_snd_1017_;
v_isShared_1028_ = v_isSharedCheck_1039_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_footnotes_1025_);
lean_inc(v_currentBlock_1024_);
lean_inc(v_priorBlocks_1023_);
lean_dec(v_snd_1017_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1039_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1029_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(v_snd_1022_);
v___x_1030_ = lean_box(0);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v___x_1029_);
lean_ctor_set(v___x_1019_, 0, v_name_1010_);
v___x_1032_ = v___x_1019_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_name_1010_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v___x_1029_);
v___x_1032_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = lean_array_push(v_footnotes_1025_, v___x_1032_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 2, v___x_1033_);
v___x_1035_ = v___x_1027_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_priorBlocks_1023_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_currentBlock_1024_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1030_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
return v___x_1036_;
}
}
}
}
v___jp_1040_:
{
lean_object* v_snd_1042_; 
v_snd_1042_ = lean_ctor_get(v___y_1041_, 1);
lean_inc(v_snd_1042_);
lean_dec_ref(v___y_1041_);
v_snd_1022_ = v_snd_1042_;
goto v___jp_1021_;
}
}
}
case 8:
{
lean_object* v_alt_1061_; lean_object* v_url_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_dec_ref(v_inst_848_);
v_alt_1061_ = lean_ctor_get(v_x_849_, 0);
lean_inc_ref(v_alt_1061_);
v_url_1062_ = lean_ctor_get(v_x_849_, 1);
lean_inc_ref(v_url_1062_);
lean_dec_ref(v_x_849_);
v___x_1063_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__36));
v___x_1064_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1061_);
lean_dec_ref(v_alt_1061_);
v___x_1065_ = lean_string_append(v___x_1063_, v___x_1064_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30));
v___x_1067_ = lean_string_append(v___x_1065_, v___x_1066_);
v___x_1068_ = lean_string_append(v___x_1067_, v_url_1062_);
lean_dec_ref(v_url_1062_);
v___x_1069_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31));
v___x_1070_ = lean_string_append(v___x_1068_, v___x_1069_);
v___x_1071_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1070_, v_a_851_);
lean_dec_ref(v___x_1070_);
return v___x_1071_;
}
case 9:
{
lean_object* v_content_1072_; lean_object* v___x_1073_; lean_object* v___f_1074_; size_t v_sz_1075_; size_t v___x_1076_; lean_object* v___x_11990__overap_1077_; lean_object* v___x_1078_; lean_object* v_snd_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_content_1072_ = lean_ctor_get(v_x_849_, 0);
lean_inc_ref(v_content_1072_);
lean_dec_ref(v_x_849_);
v___x_1073_ = lean_box(0);
v___f_1074_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1074_, 0, v_inst_848_);
lean_closure_set(v___f_1074_, 1, v___x_1073_);
v_sz_1075_ = lean_array_size(v_content_1072_);
v___x_1076_ = ((size_t)0ULL);
v___x_11990__overap_1077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_852_, v_content_1072_, v___f_1074_, v_sz_1075_, v___x_1076_, v___x_1073_);
lean_inc_ref(v_a_850_);
v___x_1078_ = lean_apply_2(v___x_11990__overap_1077_, v_a_850_, v_a_851_);
v_snd_1079_ = lean_ctor_get(v___x_1078_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; 
v_unused_1087_ = lean_ctor_get(v___x_1078_, 0);
lean_dec(v_unused_1087_);
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_snd_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1073_);
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_snd_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
default: 
{
lean_object* v_container_1088_; lean_object* v_content_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_container_1088_ = lean_ctor_get(v_x_849_, 0);
lean_inc(v_container_1088_);
v_content_1089_ = lean_ctor_get(v_x_849_, 1);
lean_inc_ref(v_content_1089_);
lean_dec_ref(v_x_849_);
lean_inc_ref(v_inst_848_);
v___x_1090_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 4, 1);
lean_closure_set(v___x_1090_, 0, v_inst_848_);
lean_inc_ref(v_a_850_);
v___x_1091_ = lean_apply_5(v_inst_848_, v___x_1090_, v_container_1088_, v_content_1089_, v_a_850_, v_a_851_);
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2(lean_object* v_inst_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1092_, v___y_1094_, v___y_1095_, v___y_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1098_, lean_object* v_inst_1099_, lean_object* v_x_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1099_, v_x_1100_, v_a_1101_, v_a_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object* v_i_1104_, lean_object* v_inst_1105_, lean_object* v_x_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(v_i_1104_, v_inst_1105_, v_x_1106_, v_a_1107_, v_a_1108_);
lean_dec_ref(v_a_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1110_, lean_object* v_inline_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1110_, v_inline_1111_, v_a_1112_, v_a_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object* v_inst_1115_, lean_object* v_inline_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(v_inst_1115_, v_inline_1116_, v_a_1117_, v_a_1118_);
lean_dec_ref(v_a_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1120_, lean_object* v_inst_1121_, lean_object* v_inline_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1121_, v_inline_1122_, v_a_1123_, v_a_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object* v_i_1126_, lean_object* v_inst_1127_, lean_object* v_inline_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(v_i_1126_, v_inst_1127_, v_inline_1128_, v_a_1129_, v_a_1130_);
lean_dec_ref(v_a_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0(lean_object* v_inst_1132_, lean_object* v_inline_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1132_, v_inline_1133_, v___y_1134_, v___y_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0___boxed(lean_object* v_inst_1137_, lean_object* v_inline_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0(v_inst_1137_, v_inline_1138_, v___y_1139_, v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1142_){
_start:
{
lean_object* v___f_1143_; 
v___f_1143_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1143_, 0, v_inst_1142_);
return v___f_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1144_, lean_object* v_inst_1145_){
_start:
{
lean_object* v___f_1146_; 
v___f_1146_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1146_, 0, v_inst_1145_);
return v___f_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
lean_object* v_zero_1149_; uint8_t v_isZero_1150_; 
v_zero_1149_ = lean_unsigned_to_nat(0u);
v_isZero_1150_ = lean_nat_dec_eq(v_x_1147_, v_zero_1149_);
if (v_isZero_1150_ == 1)
{
lean_dec(v_x_1147_);
return v_x_1148_;
}
else
{
uint32_t v___x_1151_; lean_object* v_one_1152_; lean_object* v_n_1153_; lean_object* v___x_1154_; 
v___x_1151_ = 32;
v_one_1152_ = lean_unsigned_to_nat(1u);
v_n_1153_ = lean_nat_sub(v_x_1147_, v_one_1152_);
lean_dec(v_x_1147_);
v___x_1154_ = lean_string_push(v_x_1148_, v___x_1151_);
v_x_1147_ = v_n_1153_;
v_x_1148_ = v___x_1154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(lean_object* v_str_1156_, lean_object* v_indent_1157_, lean_object* v_b_1158_){
_start:
{
lean_object* v_snd_1159_; lean_object* v_snd_1160_; lean_object* v_fst_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1223_; 
v_snd_1159_ = lean_ctor_get(v_b_1158_, 1);
lean_inc(v_snd_1159_);
v_snd_1160_ = lean_ctor_get(v_snd_1159_, 1);
lean_inc(v_snd_1160_);
v_fst_1161_ = lean_ctor_get(v_b_1158_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_b_1158_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v_b_1158_, 1);
lean_dec(v_unused_1224_);
v___x_1163_ = v_b_1158_;
v_isShared_1164_ = v_isSharedCheck_1223_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_fst_1161_);
lean_dec(v_b_1158_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1223_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v_fst_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1221_; 
v_fst_1165_ = lean_ctor_get(v_snd_1159_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_snd_1159_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v_snd_1159_, 1);
lean_dec(v_unused_1222_);
v___x_1167_ = v_snd_1159_;
v_isShared_1168_ = v_isSharedCheck_1221_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_fst_1165_);
lean_dec(v_snd_1159_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1221_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_fst_1169_; lean_object* v_snd_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1220_; 
v_fst_1169_ = lean_ctor_get(v_snd_1160_, 0);
v_snd_1170_ = lean_ctor_get(v_snd_1160_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_snd_1160_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1172_ = v_snd_1160_;
v_isShared_1173_ = v_isSharedCheck_1220_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_snd_1170_);
lean_inc(v_fst_1169_);
lean_dec(v_snd_1160_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1220_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = lean_string_utf8_byte_size(v_str_1156_);
v___x_1175_ = lean_nat_dec_eq(v_fst_1169_, v___x_1174_);
if (v___x_1175_ == 0)
{
uint32_t v_c_1176_; lean_object* v_iter_1177_; lean_object* v_longest_1179_; lean_object* v_current_1180_; uint32_t v___x_1205_; uint8_t v___x_1206_; 
v_c_1176_ = lean_string_utf8_get_fast(v_str_1156_, v_fst_1169_);
v_iter_1177_ = lean_string_utf8_next_fast(v_str_1156_, v_fst_1169_);
lean_dec(v_fst_1169_);
v___x_1205_ = 96;
v___x_1206_ = lean_uint32_dec_eq(v_c_1176_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v_current_1207_; uint8_t v___x_1208_; 
v_current_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_nat_dec_le(v_fst_1161_, v_fst_1165_);
if (v___x_1208_ == 0)
{
lean_dec(v_fst_1165_);
v_longest_1179_ = v_fst_1161_;
v_current_1180_ = v_current_1207_;
goto v___jp_1178_;
}
else
{
lean_dec(v_fst_1161_);
v_longest_1179_ = v_fst_1165_;
v_current_1180_ = v_current_1207_;
goto v___jp_1178_;
}
}
else
{
lean_object* v___x_1209_; lean_object* v_current_1210_; 
v___x_1209_ = lean_unsigned_to_nat(1u);
v_current_1210_ = lean_nat_add(v_fst_1165_, v___x_1209_);
lean_dec(v_fst_1165_);
v_longest_1179_ = v_fst_1161_;
v_current_1180_ = v_current_1210_;
goto v___jp_1178_;
}
v___jp_1178_:
{
lean_object* v_out_1181_; uint32_t v___x_1182_; uint8_t v___x_1183_; 
v_out_1181_ = lean_string_push(v_snd_1170_, v_c_1176_);
v___x_1182_ = 10;
v___x_1183_ = lean_uint32_dec_eq(v_c_1176_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1185_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_out_1181_);
lean_ctor_set(v___x_1172_, 0, v_iter_1177_);
v___x_1185_ = v___x_1172_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_iter_1177_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_out_1181_);
v___x_1185_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1185_);
lean_ctor_set(v___x_1167_, 0, v_current_1180_);
v___x_1187_ = v___x_1167_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_current_1180_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1187_);
lean_ctor_set(v___x_1163_, 0, v_longest_1179_);
v___x_1189_ = v___x_1163_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_longest_1179_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
v_b_1158_ = v___x_1189_;
goto _start;
}
}
}
}
else
{
lean_object* v_out_1194_; lean_object* v___x_1196_; 
lean_inc(v_indent_1157_);
v_out_1194_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(v_indent_1157_, v_out_1181_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_out_1194_);
lean_ctor_set(v___x_1172_, 0, v_iter_1177_);
v___x_1196_ = v___x_1172_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_iter_1177_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_out_1194_);
v___x_1196_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1196_);
lean_ctor_set(v___x_1167_, 0, v_current_1180_);
v___x_1198_ = v___x_1167_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_current_1180_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1198_);
lean_ctor_set(v___x_1163_, 0, v_longest_1179_);
v___x_1200_ = v___x_1163_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_longest_1179_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
v_b_1158_ = v___x_1200_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_1212_; 
lean_dec(v_indent_1157_);
if (v_isShared_1173_ == 0)
{
v___x_1212_ = v___x_1172_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_fst_1169_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_snd_1170_);
v___x_1212_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1214_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1212_);
v___x_1214_ = v___x_1167_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_fst_1165_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1214_);
v___x_1216_ = v___x_1163_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_fst_1161_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1___boxed(lean_object* v_str_1225_, lean_object* v_indent_1226_, lean_object* v_b_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(v_str_1225_, v_indent_1226_, v_b_1227_);
lean_dec_ref(v_str_1225_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(lean_object* v_indent_1238_, lean_object* v_str_1239_){
_start:
{
lean_object* v_current_1240_; lean_object* v_out_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_snd_1244_; lean_object* v_snd_1245_; lean_object* v_fst_1246_; lean_object* v_fst_1247_; lean_object* v_snd_1248_; lean_object* v___x_1249_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1262_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_current_1240_ = lean_unsigned_to_nat(0u);
v_out_1241_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_1242_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__2));
lean_inc(v_indent_1238_);
v___x_1243_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(v_str_1239_, v_indent_1238_, v___x_1242_);
v_snd_1244_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_snd_1244_);
v_snd_1245_ = lean_ctor_get(v_snd_1244_, 1);
lean_inc(v_snd_1245_);
v_fst_1246_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_fst_1246_);
lean_dec_ref(v___x_1243_);
v_fst_1247_ = lean_ctor_get(v_snd_1244_, 0);
lean_inc(v_fst_1247_);
lean_dec(v_snd_1244_);
v_snd_1248_ = lean_ctor_get(v_snd_1245_, 1);
lean_inc(v_snd_1248_);
lean_dec(v_snd_1245_);
v___x_1249_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1268_ = lean_string_utf8_byte_size(v_snd_1248_);
v___x_1269_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2);
v___x_1270_ = lean_nat_dec_le(v___x_1269_, v___x_1268_);
if (v___x_1270_ == 0)
{
goto v___jp_1265_;
}
else
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = lean_nat_sub(v___x_1268_, v___x_1269_);
v___x_1272_ = lean_string_memcmp(v_snd_1248_, v___x_1249_, v___x_1271_, v_current_1240_, v___x_1269_);
lean_dec(v___x_1271_);
if (v___x_1272_ == 0)
{
goto v___jp_1265_;
}
else
{
v___y_1262_ = v_snd_1248_;
goto v___jp_1261_;
}
}
v___jp_1250_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1254_ = lean_unsigned_to_nat(1u);
v___x_1255_ = lean_nat_add(v___y_1253_, v___x_1254_);
lean_dec(v___y_1253_);
v___x_1256_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__1(v___x_1255_, v___y_1252_);
lean_inc_ref(v___x_1256_);
v___x_1257_ = lean_string_append(v___x_1256_, v___x_1249_);
v___x_1258_ = lean_string_append(v___x_1257_, v___y_1251_);
lean_dec_ref(v___y_1251_);
v___x_1259_ = lean_string_append(v___x_1258_, v___x_1256_);
lean_dec_ref(v___x_1256_);
v___x_1260_ = lean_string_append(v___x_1259_, v___x_1249_);
return v___x_1260_;
}
v___jp_1261_:
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(v_indent_1238_, v_out_1241_);
v___x_1264_ = lean_nat_dec_le(v_fst_1246_, v_fst_1247_);
if (v___x_1264_ == 0)
{
lean_dec(v_fst_1247_);
v___y_1251_ = v___y_1262_;
v___y_1252_ = v___x_1263_;
v___y_1253_ = v_fst_1246_;
goto v___jp_1250_;
}
else
{
lean_dec(v_fst_1246_);
v___y_1251_ = v___y_1262_;
v___y_1252_ = v___x_1263_;
v___y_1253_ = v_fst_1247_;
goto v___jp_1250_;
}
}
v___jp_1265_:
{
uint32_t v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = 10;
v___x_1267_ = lean_string_push(v_snd_1248_, v___x_1266_);
v___y_1262_ = v___x_1267_;
goto v___jp_1261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___boxed(lean_object* v_indent_1273_, lean_object* v_str_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v_indent_1273_, v_str_1274_);
lean_dec_ref(v_str_1274_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v___x_1277_, lean_object* v___f_1278_, lean_object* v___x_1279_, lean_object* v_a_1280_, lean_object* v_x_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v_inEmph_1285_; uint8_t v_inBold_1286_; uint8_t v_inLink_1287_; lean_object* v_linePrefix_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v_snd_1292_; size_t v_sz_1293_; size_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_13712__overap_1298_; lean_object* v___x_1299_; lean_object* v_snd_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1308_; 
v_inEmph_1285_ = lean_ctor_get_uint8(v___y_1283_, sizeof(void*)*1);
v_inBold_1286_ = lean_ctor_get_uint8(v___y_1283_, sizeof(void*)*1 + 1);
v_inLink_1287_ = lean_ctor_get_uint8(v___y_1283_, sizeof(void*)*1 + 2);
v_linePrefix_1288_ = lean_ctor_get(v___y_1283_, 0);
v___x_1289_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
lean_inc_ref_n(v_linePrefix_1288_, 2);
v___x_1290_ = lean_string_append(v_linePrefix_1288_, v___x_1289_);
v___x_1291_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1290_, v___y_1284_);
lean_dec_ref(v___x_1290_);
v_snd_1292_ = lean_ctor_get(v___x_1291_, 1);
lean_inc(v_snd_1292_);
lean_dec_ref(v___x_1291_);
v_sz_1293_ = lean_array_size(v_a_1280_);
v___x_1294_ = ((size_t)0ULL);
v___x_1295_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1296_ = lean_string_append(v_linePrefix_1288_, v___x_1295_);
v___x_1297_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*1, v_inEmph_1285_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*1 + 1, v_inBold_1286_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*1 + 2, v_inLink_1287_);
v___x_13712__overap_1298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1277_, v_a_1280_, v___f_1278_, v_sz_1293_, v___x_1294_, v___x_1279_);
v___x_1299_ = lean_apply_2(v___x_13712__overap_1298_, v___x_1297_, v_snd_1292_);
v_snd_1300_ = lean_ctor_get(v___x_1299_, 1);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; 
v_unused_1309_ = lean_ctor_get(v___x_1299_, 0);
lean_dec(v_unused_1309_);
v___x_1302_ = v___x_1299_;
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_snd_1300_);
lean_dec(v___x_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1279_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1304_);
v___x_1306_ = v___x_1302_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_snd_1300_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed(lean_object* v___x_1310_, lean_object* v___f_1311_, lean_object* v___x_1312_, lean_object* v_a_1313_, lean_object* v_x_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(v___x_1310_, v___f_1311_, v___x_1312_, v_a_1313_, v_x_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v___x_1321_, lean_object* v_a_1322_, lean_object* v_x_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v_inst_1319_, v_inst_1320_, v___x_1321_, v_a_1322_, v_x_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v___x_1331_, lean_object* v___x_1332_, lean_object* v_a_1333_, lean_object* v_x_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
uint8_t v_inEmph_1338_; uint8_t v_inBold_1339_; uint8_t v_inLink_1340_; lean_object* v_linePrefix_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v_snd_1347_; lean_object* v___x_1348_; lean_object* v___f_1349_; size_t v_sz_1350_; size_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_13750__overap_1355_; lean_object* v___x_1356_; lean_object* v_snd_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1366_; 
v_inEmph_1338_ = lean_ctor_get_uint8(v___y_1336_, sizeof(void*)*1);
v_inBold_1339_ = lean_ctor_get_uint8(v___y_1336_, sizeof(void*)*1 + 1);
v_inLink_1340_ = lean_ctor_get_uint8(v___y_1336_, sizeof(void*)*1 + 2);
v_linePrefix_1341_ = lean_ctor_get(v___y_1336_, 0);
lean_inc(v___y_1335_);
v___x_1342_ = l_Nat_reprFast(v___y_1335_);
v___x_1343_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0));
v___x_1344_ = lean_string_append(v___x_1342_, v___x_1343_);
lean_inc_ref_n(v_linePrefix_1341_, 2);
v___x_1345_ = lean_string_append(v_linePrefix_1341_, v___x_1344_);
lean_dec_ref(v___x_1344_);
v___x_1346_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1345_, v___y_1337_);
lean_dec_ref(v___x_1345_);
v_snd_1347_ = lean_ctor_get(v___x_1346_, 1);
lean_inc(v_snd_1347_);
lean_dec_ref(v___x_1346_);
v___x_1348_ = lean_box(0);
v___f_1349_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1349_, 0, v_inst_1329_);
lean_closure_set(v___f_1349_, 1, v_inst_1330_);
lean_closure_set(v___f_1349_, 2, v___x_1348_);
v_sz_1350_ = lean_array_size(v_a_1333_);
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1353_ = lean_string_append(v_linePrefix_1341_, v___x_1352_);
v___x_1354_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*1, v_inEmph_1338_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*1 + 1, v_inBold_1339_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*1 + 2, v_inLink_1340_);
v___x_13750__overap_1355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1331_, v_a_1333_, v___f_1349_, v_sz_1350_, v___x_1351_, v___x_1348_);
v___x_1356_ = lean_apply_2(v___x_13750__overap_1355_, v___x_1354_, v_snd_1347_);
v_snd_1357_ = lean_ctor_get(v___x_1356_, 1);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v___x_1356_, 0);
lean_dec(v_unused_1367_);
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1366_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_snd_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1366_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1361_ = lean_nat_add(v___y_1335_, v___x_1332_);
lean_dec(v___y_1335_);
v___x_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1362_);
v___x_1364_ = v___x_1359_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_snd_1357_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v___x_1370_, lean_object* v___x_1371_, lean_object* v_a_1372_, lean_object* v_x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1368_, v_inst_1369_, v___x_1370_, v___x_1371_, v_a_1372_, v_x_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___x_1371_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v___x_1383_, lean_object* v_a_1384_, lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
uint8_t v_inEmph_1389_; uint8_t v_inBold_1390_; uint8_t v_inLink_1391_; lean_object* v_linePrefix_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_snd_1396_; lean_object* v_term_1397_; lean_object* v_desc_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v_snd_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_snd_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v_snd_1410_; lean_object* v___x_1411_; lean_object* v_snd_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v_snd_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1423_; 
v_inEmph_1389_ = lean_ctor_get_uint8(v___y_1387_, sizeof(void*)*1);
v_inBold_1390_ = lean_ctor_get_uint8(v___y_1387_, sizeof(void*)*1 + 1);
v_inLink_1391_ = lean_ctor_get_uint8(v___y_1387_, sizeof(void*)*1 + 2);
v_linePrefix_1392_ = lean_ctor_get(v___y_1387_, 0);
v___x_1393_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
lean_inc_ref_n(v_linePrefix_1392_, 2);
v___x_1394_ = lean_string_append(v_linePrefix_1392_, v___x_1393_);
v___x_1395_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1394_, v___y_1388_);
lean_dec_ref(v___x_1394_);
v_snd_1396_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_snd_1396_);
lean_dec_ref(v___x_1395_);
v_term_1397_ = lean_ctor_get(v_a_1384_, 0);
v_desc_1398_ = lean_ctor_get(v_a_1384_, 1);
lean_inc_ref(v_term_1397_);
v___x_1399_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1399_, 0, v_term_1397_);
v___x_1400_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1401_ = lean_string_append(v_linePrefix_1392_, v___x_1400_);
lean_inc_ref(v___x_1401_);
v___x_1402_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*1, v_inEmph_1389_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*1 + 1, v_inBold_1390_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*1 + 2, v_inLink_1391_);
lean_inc_ref_n(v_inst_1381_, 2);
v___x_1403_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1381_, v___x_1399_, v___x_1402_, v_snd_1396_);
v_snd_1404_ = lean_ctor_get(v___x_1403_, 1);
lean_inc(v_snd_1404_);
lean_dec_ref(v___x_1403_);
v___x_1405_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1));
v___x_1406_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1381_, v___x_1405_, v___x_1402_, v_snd_1404_);
v_snd_1407_ = lean_ctor_get(v___x_1406_, 1);
lean_inc(v_snd_1407_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1409_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1408_, v_snd_1407_);
v_snd_1410_ = lean_ctor_get(v___x_1409_, 1);
lean_inc(v_snd_1410_);
lean_dec_ref(v___x_1409_);
v___x_1411_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1401_, v_snd_1410_);
lean_dec_ref(v___x_1401_);
v_snd_1412_ = lean_ctor_get(v___x_1411_, 1);
lean_inc(v_snd_1412_);
lean_dec_ref(v___x_1411_);
lean_inc_ref(v_desc_1398_);
v___x_1413_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1413_, 0, v_desc_1398_);
v___x_1414_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1381_, v_inst_1382_, v___x_1413_, v___x_1402_, v_snd_1412_);
lean_dec_ref(v___x_1402_);
v_snd_1415_ = lean_ctor_get(v___x_1414_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v___x_1414_, 0);
lean_dec(v_unused_1424_);
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_snd_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1383_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1419_);
v___x_1421_ = v___x_1417_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_snd_1415_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v___x_1427_, lean_object* v_a_1428_, lean_object* v_x_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1425_, v_inst_1426_, v___x_1427_, v_a_1428_, v_x_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec_ref(v_a_1428_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed(lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_x_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1435_, v_inst_1436_, v_x_1437_, v_a_1438_, v_a_1439_);
lean_dec_ref(v_a_1438_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1441_, lean_object* v_inst_1442_, lean_object* v_x_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
switch(lean_obj_tag(v_x_1443_))
{
case 0:
{
lean_object* v_contents_1447_; lean_object* v___x_1448_; lean_object* v___f_1449_; size_t v_sz_1450_; size_t v___x_1451_; lean_object* v___x_12962__overap_1452_; lean_object* v___x_1453_; lean_object* v_snd_1454_; lean_object* v___x_1455_; 
lean_dec_ref(v_inst_1442_);
v_contents_1447_ = lean_ctor_get(v_x_1443_, 0);
lean_inc_ref(v_contents_1447_);
lean_dec_ref(v_x_1443_);
v___x_1448_ = lean_box(0);
v___f_1449_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1449_, 0, v_inst_1441_);
lean_closure_set(v___f_1449_, 1, v___x_1448_);
v_sz_1450_ = lean_array_size(v_contents_1447_);
v___x_1451_ = ((size_t)0ULL);
v___x_12962__overap_1452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1446_, v_contents_1447_, v___f_1449_, v_sz_1450_, v___x_1451_, v___x_1448_);
lean_inc_ref(v_a_1444_);
v___x_1453_ = lean_apply_2(v___x_12962__overap_1452_, v_a_1444_, v_a_1445_);
v_snd_1454_ = lean_ctor_get(v___x_1453_, 1);
lean_inc(v_snd_1454_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1454_);
return v___x_1455_;
}
case 1:
{
lean_object* v_content_1456_; lean_object* v___y_1458_; lean_object* v___y_1459_; uint8_t v___y_1467_; lean_object* v_currentBlock_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
lean_dec_ref(v_inst_1442_);
lean_dec_ref(v_inst_1441_);
v_content_1456_ = lean_ctor_get(v_x_1443_, 0);
lean_inc_ref(v_content_1456_);
lean_dec_ref(v_x_1443_);
v_currentBlock_1471_ = lean_ctor_get(v_a_1445_, 1);
v___x_1472_ = lean_string_utf8_byte_size(v_currentBlock_1471_);
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = lean_nat_dec_eq(v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1475_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1476_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2);
v___x_1477_ = lean_nat_dec_le(v___x_1476_, v___x_1472_);
if (v___x_1477_ == 0)
{
v___y_1467_ = v___x_1474_;
goto v___jp_1466_;
}
else
{
lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = lean_nat_sub(v___x_1472_, v___x_1476_);
v___x_1479_ = lean_string_memcmp(v_currentBlock_1471_, v___x_1475_, v___x_1478_, v___x_1473_, v___x_1476_);
lean_dec(v___x_1478_);
v___y_1467_ = v___x_1479_;
goto v___jp_1466_;
}
}
else
{
v___y_1467_ = v___x_1474_;
goto v___jp_1466_;
}
v___jp_1457_:
{
lean_object* v_linePrefix_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_snd_1464_; lean_object* v___x_1465_; 
v_linePrefix_1460_ = lean_ctor_get(v___y_1458_, 0);
v___x_1461_ = lean_string_length(v_linePrefix_1460_);
v___x_1462_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v___x_1461_, v_content_1456_);
lean_dec_ref(v_content_1456_);
v___x_1463_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1462_, v___y_1459_);
lean_dec_ref(v___x_1462_);
v_snd_1464_ = lean_ctor_get(v___x_1463_, 1);
lean_inc(v_snd_1464_);
lean_dec_ref(v___x_1463_);
v___x_1465_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1464_);
return v___x_1465_;
}
v___jp_1466_:
{
if (v___y_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v_snd_1470_; 
v___x_1468_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1469_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1468_, v_a_1445_);
v_snd_1470_ = lean_ctor_get(v___x_1469_, 1);
lean_inc(v_snd_1470_);
lean_dec_ref(v___x_1469_);
v___y_1458_ = v_a_1444_;
v___y_1459_ = v_snd_1470_;
goto v___jp_1457_;
}
else
{
v___y_1458_ = v_a_1444_;
v___y_1459_ = v_a_1445_;
goto v___jp_1457_;
}
}
}
case 2:
{
lean_object* v_items_1480_; lean_object* v___x_1481_; lean_object* v___f_1482_; lean_object* v___f_1483_; size_t v_sz_1484_; size_t v___x_1485_; lean_object* v___x_13190__overap_1486_; lean_object* v___x_1487_; lean_object* v_snd_1488_; lean_object* v___x_1489_; 
v_items_1480_ = lean_ctor_get(v_x_1443_, 0);
lean_inc_ref(v_items_1480_);
lean_dec_ref(v_x_1443_);
v___x_1481_ = lean_box(0);
v___f_1482_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1482_, 0, v_inst_1441_);
lean_closure_set(v___f_1482_, 1, v_inst_1442_);
lean_closure_set(v___f_1482_, 2, v___x_1481_);
v___f_1483_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1483_, 0, v___x_1446_);
lean_closure_set(v___f_1483_, 1, v___f_1482_);
lean_closure_set(v___f_1483_, 2, v___x_1481_);
v_sz_1484_ = lean_array_size(v_items_1480_);
v___x_1485_ = ((size_t)0ULL);
v___x_13190__overap_1486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1446_, v_items_1480_, v___f_1483_, v_sz_1484_, v___x_1485_, v___x_1481_);
lean_inc_ref(v_a_1444_);
v___x_1487_ = lean_apply_2(v___x_13190__overap_1486_, v_a_1444_, v_a_1445_);
v_snd_1488_ = lean_ctor_get(v___x_1487_, 1);
lean_inc(v_snd_1488_);
lean_dec_ref(v___x_1487_);
v___x_1489_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1488_);
return v___x_1489_;
}
case 3:
{
lean_object* v_start_1490_; lean_object* v_items_1491_; lean_object* v___x_1492_; lean_object* v___f_1493_; lean_object* v___y_1495_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v_start_1490_ = lean_ctor_get(v_x_1443_, 0);
lean_inc(v_start_1490_);
v_items_1491_ = lean_ctor_get(v_x_1443_, 1);
lean_inc_ref(v_items_1491_);
lean_dec_ref(v_x_1443_);
v___x_1492_ = lean_unsigned_to_nat(1u);
v___f_1493_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 9, 4);
lean_closure_set(v___f_1493_, 0, v_inst_1441_);
lean_closure_set(v___f_1493_, 1, v_inst_1442_);
lean_closure_set(v___f_1493_, 2, v___x_1446_);
lean_closure_set(v___f_1493_, 3, v___x_1492_);
v___x_1502_ = l_Int_toNat(v_start_1490_);
lean_dec(v_start_1490_);
v___x_1503_ = lean_nat_dec_le(v___x_1492_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_dec(v___x_1502_);
v___y_1495_ = v___x_1492_;
goto v___jp_1494_;
}
else
{
v___y_1495_ = v___x_1502_;
goto v___jp_1494_;
}
v___jp_1494_:
{
size_t v_sz_1496_; size_t v___x_1497_; lean_object* v___x_13284__overap_1498_; lean_object* v___x_1499_; lean_object* v_snd_1500_; lean_object* v___x_1501_; 
v_sz_1496_ = lean_array_size(v_items_1491_);
v___x_1497_ = ((size_t)0ULL);
v___x_13284__overap_1498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1446_, v_items_1491_, v___f_1493_, v_sz_1496_, v___x_1497_, v___y_1495_);
lean_inc_ref(v_a_1444_);
v___x_1499_ = lean_apply_2(v___x_13284__overap_1498_, v_a_1444_, v_a_1445_);
v_snd_1500_ = lean_ctor_get(v___x_1499_, 1);
lean_inc(v_snd_1500_);
lean_dec_ref(v___x_1499_);
v___x_1501_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1500_);
return v___x_1501_;
}
}
case 4:
{
lean_object* v_items_1504_; lean_object* v___x_1505_; lean_object* v___f_1506_; size_t v_sz_1507_; size_t v___x_1508_; lean_object* v___x_13387__overap_1509_; lean_object* v___x_1510_; lean_object* v_snd_1511_; lean_object* v___x_1512_; 
v_items_1504_ = lean_ctor_get(v_x_1443_, 0);
lean_inc_ref(v_items_1504_);
lean_dec_ref(v_x_1443_);
v___x_1505_ = lean_box(0);
v___f_1506_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 8, 3);
lean_closure_set(v___f_1506_, 0, v_inst_1441_);
lean_closure_set(v___f_1506_, 1, v_inst_1442_);
lean_closure_set(v___f_1506_, 2, v___x_1505_);
v_sz_1507_ = lean_array_size(v_items_1504_);
v___x_1508_ = ((size_t)0ULL);
v___x_13387__overap_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1446_, v_items_1504_, v___f_1506_, v_sz_1507_, v___x_1508_, v___x_1505_);
lean_inc_ref(v_a_1444_);
v___x_1510_ = lean_apply_2(v___x_13387__overap_1509_, v_a_1444_, v_a_1445_);
v_snd_1511_ = lean_ctor_get(v___x_1510_, 1);
lean_inc(v_snd_1511_);
lean_dec_ref(v___x_1510_);
v___x_1512_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1511_);
return v___x_1512_;
}
case 5:
{
lean_object* v_items_1513_; uint8_t v_inEmph_1514_; uint8_t v_inBold_1515_; uint8_t v_inLink_1516_; lean_object* v_linePrefix_1517_; lean_object* v___x_1518_; lean_object* v___f_1519_; size_t v_sz_1520_; size_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_13493__overap_1525_; lean_object* v___x_1526_; lean_object* v_snd_1527_; lean_object* v___x_1528_; 
v_items_1513_ = lean_ctor_get(v_x_1443_, 0);
lean_inc_ref(v_items_1513_);
lean_dec_ref(v_x_1443_);
v_inEmph_1514_ = lean_ctor_get_uint8(v_a_1444_, sizeof(void*)*1);
v_inBold_1515_ = lean_ctor_get_uint8(v_a_1444_, sizeof(void*)*1 + 1);
v_inLink_1516_ = lean_ctor_get_uint8(v_a_1444_, sizeof(void*)*1 + 2);
v_linePrefix_1517_ = lean_ctor_get(v_a_1444_, 0);
v___x_1518_ = lean_box(0);
v___f_1519_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1519_, 0, v_inst_1441_);
lean_closure_set(v___f_1519_, 1, v_inst_1442_);
lean_closure_set(v___f_1519_, 2, v___x_1518_);
v_sz_1520_ = lean_array_size(v_items_1513_);
v___x_1521_ = ((size_t)0ULL);
v___x_1522_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
lean_inc_ref(v_linePrefix_1517_);
v___x_1523_ = lean_string_append(v_linePrefix_1517_, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set_uint8(v___x_1524_, sizeof(void*)*1, v_inEmph_1514_);
lean_ctor_set_uint8(v___x_1524_, sizeof(void*)*1 + 1, v_inBold_1515_);
lean_ctor_set_uint8(v___x_1524_, sizeof(void*)*1 + 2, v_inLink_1516_);
v___x_13493__overap_1525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1446_, v_items_1513_, v___f_1519_, v_sz_1520_, v___x_1521_, v___x_1518_);
v___x_1526_ = lean_apply_2(v___x_13493__overap_1525_, v___x_1524_, v_a_1445_);
v_snd_1527_ = lean_ctor_get(v___x_1526_, 1);
lean_inc(v_snd_1527_);
lean_dec_ref(v___x_1526_);
v___x_1528_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1527_);
return v___x_1528_;
}
case 6:
{
lean_object* v_content_1529_; lean_object* v___x_1530_; lean_object* v___f_1531_; size_t v_sz_1532_; size_t v___x_1533_; lean_object* v___x_13529__overap_1534_; lean_object* v___x_1535_; lean_object* v_snd_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
v_content_1529_ = lean_ctor_get(v_x_1443_, 0);
lean_inc_ref(v_content_1529_);
lean_dec_ref(v_x_1443_);
v___x_1530_ = lean_box(0);
v___f_1531_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1531_, 0, v_inst_1441_);
lean_closure_set(v___f_1531_, 1, v_inst_1442_);
lean_closure_set(v___f_1531_, 2, v___x_1530_);
v_sz_1532_ = lean_array_size(v_content_1529_);
v___x_1533_ = ((size_t)0ULL);
v___x_13529__overap_1534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1446_, v_content_1529_, v___f_1531_, v_sz_1532_, v___x_1533_, v___x_1530_);
lean_inc_ref(v_a_1444_);
v___x_1535_ = lean_apply_2(v___x_13529__overap_1534_, v_a_1444_, v_a_1445_);
v_snd_1536_ = lean_ctor_get(v___x_1535_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v___x_1535_, 0);
lean_dec(v_unused_1544_);
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_snd_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1530_);
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_snd_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
default: 
{
lean_object* v_container_1545_; lean_object* v_content_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_container_1545_ = lean_ctor_get(v_x_1443_, 0);
lean_inc(v_container_1545_);
v_content_1546_ = lean_ctor_get(v_x_1443_, 1);
lean_inc_ref(v_content_1546_);
lean_dec_ref(v_x_1443_);
lean_inc_ref(v_inst_1441_);
v___x_1547_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed), 5, 2);
lean_closure_set(v___x_1547_, 0, lean_box(0));
lean_closure_set(v___x_1547_, 1, v_inst_1441_);
lean_inc_ref(v_inst_1442_);
v___x_1548_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 5, 2);
lean_closure_set(v___x_1548_, 0, v_inst_1441_);
lean_closure_set(v___x_1548_, 1, v_inst_1442_);
lean_inc_ref(v_a_1444_);
v___x_1549_ = lean_apply_6(v_inst_1442_, v___x_1547_, v___x_1548_, v_container_1545_, v_content_1546_, v_a_1444_, v_a_1445_);
return v___x_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(lean_object* v_inst_1550_, lean_object* v_inst_1551_, lean_object* v___x_1552_, lean_object* v_a_1553_, lean_object* v_x_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v___x_1558_; lean_object* v_snd_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1567_; 
v___x_1558_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1550_, v_inst_1551_, v_a_1553_, v___y_1556_, v___y_1557_);
v_snd_1559_ = lean_ctor_get(v___x_1558_, 1);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; 
v_unused_1568_ = lean_ctor_get(v___x_1558_, 0);
lean_dec(v_unused_1568_);
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_snd_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1552_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1563_);
v___x_1565_ = v___x_1561_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_snd_1559_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1569_, lean_object* v_b_1570_, lean_object* v_inst_1571_, lean_object* v_inst_1572_, lean_object* v_x_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1571_, v_inst_1572_, v_x_1573_, v_a_1574_, v_a_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object* v_i_1577_, lean_object* v_b_1578_, lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_x_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(v_i_1577_, v_b_1578_, v_inst_1579_, v_inst_1580_, v_x_1581_, v_a_1582_, v_a_1583_);
lean_dec_ref(v_a_1582_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_block_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1585_, v_inst_1586_, v_block_1587_, v_a_1588_, v_a_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_block_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1591_, v_inst_1592_, v_block_1593_, v_a_1594_, v_a_1595_);
lean_dec_ref(v_a_1594_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1597_, lean_object* v_b_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_block_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1599_, v_inst_1600_, v_block_1601_, v_a_1602_, v_a_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1605_, lean_object* v_b_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_block_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1605_, v_b_1606_, v_inst_1607_, v_inst_1608_, v_block_1609_, v_a_1610_, v_a_1611_);
lean_dec_ref(v_a_1610_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_block_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1613_, v_inst_1614_, v_block_1615_, v___y_1616_, v___y_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_block_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_1619_, v_inst_1620_, v_block_1621_, v___y_1622_, v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1625_, lean_object* v_inst_1626_){
_start:
{
lean_object* v___f_1627_; 
v___f_1627_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1627_, 0, v_inst_1625_);
lean_closure_set(v___f_1627_, 1, v_inst_1626_);
return v___f_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1628_, lean_object* v_b_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_){
_start:
{
lean_object* v___f_1632_; 
v___f_1632_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1632_, 0, v_inst_1630_);
lean_closure_set(v___f_1632_, 1, v_inst_1631_);
return v___f_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0(uint32_t v___x_1633_, lean_object* v_s_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_string_push(v_s_1634_, v___x_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0___boxed(lean_object* v___x_1636_, lean_object* v_s_1637_){
_start:
{
uint32_t v___x_4128__boxed_1638_; lean_object* v_res_1639_; 
v___x_4128__boxed_1638_ = lean_unbox_uint32(v___x_1636_);
lean_dec(v___x_1636_);
v_res_1639_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0(v___x_4128__boxed_1638_, v_s_1637_);
return v_res_1639_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = 35;
v___x_1641_ = lean_box_uint32(v___x_1640_);
return v___x_1641_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___f_1643_; 
v___x_1642_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1643_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1643_, 0, v___x_1642_);
return v___f_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v___x_1646_, lean_object* v___x_1647_, lean_object* v_a_1648_, lean_object* v_x_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3(v_inst_1644_, v_inst_1645_, v___x_1646_, v___x_1647_, v_a_1648_, v_x_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___x_1646_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_level_1656_, lean_object* v_part_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___f_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v_snd_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v_snd_1670_; lean_object* v_title_1671_; lean_object* v_content_1672_; lean_object* v_subParts_1673_; lean_object* v___x_1674_; lean_object* v___f_1675_; size_t v_sz_1676_; size_t v___x_1677_; lean_object* v___x_3967__overap_1678_; lean_object* v___x_1679_; lean_object* v_snd_1680_; lean_object* v___x_1681_; lean_object* v_snd_1682_; lean_object* v___f_1683_; size_t v_sz_1684_; lean_object* v___x_3985__overap_1685_; lean_object* v___x_1686_; lean_object* v_snd_1687_; lean_object* v___x_1688_; lean_object* v_snd_1689_; lean_object* v___f_1690_; size_t v_sz_1691_; lean_object* v___x_4003__overap_1692_; lean_object* v___x_1693_; lean_object* v_snd_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
v___x_1660_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
v___x_1661_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___f_1662_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0);
v___x_1663_ = lean_unsigned_to_nat(1u);
v___x_1664_ = lean_nat_add(v_level_1656_, v___x_1663_);
lean_inc(v___x_1664_);
v___x_1665_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1662_, v___x_1664_, v___x_1661_);
v___x_1666_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1665_, v_a_1659_);
lean_dec(v___x_1665_);
v_snd_1667_ = lean_ctor_get(v___x_1666_, 1);
lean_inc(v_snd_1667_);
lean_dec_ref(v___x_1666_);
v___x_1668_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_1669_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1668_, v_snd_1667_);
v_snd_1670_ = lean_ctor_get(v___x_1669_, 1);
lean_inc(v_snd_1670_);
lean_dec_ref(v___x_1669_);
v_title_1671_ = lean_ctor_get(v_part_1657_, 0);
lean_inc_ref(v_title_1671_);
v_content_1672_ = lean_ctor_get(v_part_1657_, 3);
lean_inc_ref(v_content_1672_);
v_subParts_1673_ = lean_ctor_get(v_part_1657_, 4);
lean_inc_ref(v_subParts_1673_);
lean_dec_ref(v_part_1657_);
v___x_1674_ = lean_box(0);
lean_inc_ref_n(v_inst_1654_, 2);
v___f_1675_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1675_, 0, v_inst_1654_);
lean_closure_set(v___f_1675_, 1, v___x_1674_);
v_sz_1676_ = lean_array_size(v_title_1671_);
v___x_1677_ = ((size_t)0ULL);
v___x_3967__overap_1678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1660_, v_title_1671_, v___f_1675_, v_sz_1676_, v___x_1677_, v___x_1674_);
lean_inc_ref_n(v_a_1658_, 3);
v___x_1679_ = lean_apply_2(v___x_3967__overap_1678_, v_a_1658_, v_snd_1670_);
v_snd_1680_ = lean_ctor_get(v___x_1679_, 1);
lean_inc(v_snd_1680_);
lean_dec_ref(v___x_1679_);
v___x_1681_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1680_);
v_snd_1682_ = lean_ctor_get(v___x_1681_, 1);
lean_inc(v_snd_1682_);
lean_dec_ref(v___x_1681_);
lean_inc_ref(v_inst_1655_);
v___f_1683_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1683_, 0, v_inst_1654_);
lean_closure_set(v___f_1683_, 1, v_inst_1655_);
lean_closure_set(v___f_1683_, 2, v___x_1674_);
v_sz_1684_ = lean_array_size(v_content_1672_);
v___x_3985__overap_1685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1660_, v_content_1672_, v___f_1683_, v_sz_1684_, v___x_1677_, v___x_1674_);
v___x_1686_ = lean_apply_2(v___x_3985__overap_1685_, v_a_1658_, v_snd_1682_);
v_snd_1687_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_snd_1687_);
lean_dec_ref(v___x_1686_);
v___x_1688_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1687_);
v_snd_1689_ = lean_ctor_get(v___x_1688_, 1);
lean_inc(v_snd_1689_);
lean_dec_ref(v___x_1688_);
v___f_1690_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3___boxed), 9, 4);
lean_closure_set(v___f_1690_, 0, v_inst_1654_);
lean_closure_set(v___f_1690_, 1, v_inst_1655_);
lean_closure_set(v___f_1690_, 2, v___x_1664_);
lean_closure_set(v___f_1690_, 3, v___x_1674_);
v_sz_1691_ = lean_array_size(v_subParts_1673_);
v___x_4003__overap_1692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1660_, v_subParts_1673_, v___f_1690_, v_sz_1691_, v___x_1677_, v___x_1674_);
v___x_1693_ = lean_apply_2(v___x_4003__overap_1692_, v_a_1658_, v_snd_1689_);
v_snd_1694_ = lean_ctor_get(v___x_1693_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v___x_1693_, 0);
lean_dec(v_unused_1702_);
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_snd_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1674_);
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_snd_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3(lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v___x_1705_, lean_object* v___x_1706_, lean_object* v_a_1707_, lean_object* v_x_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1712_; lean_object* v_snd_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1721_; 
v___x_1712_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1703_, v_inst_1704_, v___x_1705_, v_a_1707_, v___y_1710_, v___y_1711_);
v_snd_1713_ = lean_ctor_get(v___x_1712_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1721_ == 0)
{
lean_object* v_unused_1722_; 
v_unused_1722_ = lean_ctor_get(v___x_1712_, 0);
lean_dec(v_unused_1722_);
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1721_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_snd_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1721_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1706_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1717_);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_snd_1713_);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_level_1725_, lean_object* v_part_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1723_, v_inst_1724_, v_level_1725_, v_part_1726_, v_a_1727_, v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_level_1725_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown(lean_object* v_i_1730_, lean_object* v_b_1731_, lean_object* v_p_1732_, lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_level_1735_, lean_object* v_part_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1733_, v_inst_1734_, v_level_1735_, v_part_1736_, v_a_1737_, v_a_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___boxed(lean_object* v_i_1740_, lean_object* v_b_1741_, lean_object* v_p_1742_, lean_object* v_inst_1743_, lean_object* v_inst_1744_, lean_object* v_level_1745_, lean_object* v_part_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown(v_i_1740_, v_b_1741_, v_p_1742_, v_inst_1743_, v_inst_1744_, v_level_1745_, v_part_1746_, v_a_1747_, v_a_1748_);
lean_dec_ref(v_a_1747_);
lean_dec(v_level_1745_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1750_, lean_object* v_inst_1751_, lean_object* v_part_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1756_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1750_, v_inst_1751_, v___x_1755_, v_part_1752_, v_a_1753_, v_a_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_part_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1757_, v_inst_1758_, v_part_1759_, v_a_1760_, v_a_1761_);
lean_dec_ref(v_a_1760_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1763_, lean_object* v_b_1764_, lean_object* v_p_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_part_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1766_, v_inst_1767_, v___x_1771_, v_part_1768_, v_a_1769_, v_a_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1773_, lean_object* v_b_1774_, lean_object* v_p_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_part_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1773_, v_b_1774_, v_p_1775_, v_inst_1776_, v_inst_1777_, v_part_1778_, v_a_1779_, v_a_1780_);
lean_dec_ref(v_a_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_part_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1782_, v_inst_1783_, v___x_1787_, v_part_1784_, v___y_1785_, v___y_1786_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_part_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_1789_, v_inst_1790_, v_part_1791_, v___y_1792_, v___y_1793_);
lean_dec_ref(v___y_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1795_, lean_object* v_inst_1796_){
_start:
{
lean_object* v___f_1797_; 
v___f_1797_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1797_, 0, v_inst_1795_);
lean_closure_set(v___f_1797_, 1, v_inst_1796_);
return v___f_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1798_, lean_object* v_b_1799_, lean_object* v_p_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_){
_start:
{
lean_object* v___f_1803_; 
v___f_1803_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1803_, 0, v_inst_1801_);
lean_closure_set(v___f_1803_, 1, v_inst_1802_);
return v___f_1803_;
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
