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
v___x_478_ = l_String_instDecidableLtRaw___aux__1(v_pos_469_, v___x_477_);
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
lean_object* v_tail_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_553_; 
v_tail_506_ = lean_ctor_get(v_a_503_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_a_503_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v_a_503_, 0);
lean_dec(v_unused_554_);
v___x_508_ = v_a_503_;
v_isShared_509_ = v_isSharedCheck_553_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_tail_506_);
lean_dec(v_a_503_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_553_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_string_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_552_; 
v_string_510_ = lean_ctor_get(v_head_505_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_head_505_);
if (v_isSharedCheck_552_ == 0)
{
v___x_512_ = v_head_505_;
v_isShared_513_ = v_isSharedCheck_552_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_string_510_);
lean_dec(v_head_505_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_552_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_string_utf8_byte_size(v_string_510_);
lean_inc_ref(v_string_510_);
v___x_516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_516_, 0, v_string_510_);
lean_ctor_set(v___x_516_, 1, v___x_514_);
lean_ctor_set(v___x_516_, 2, v___x_515_);
v___x_517_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_516_, v___x_514_);
v___x_518_ = lean_nat_sub(v___x_515_, v___x_517_);
v___x_519_ = lean_nat_dec_eq(v___x_518_, v___x_514_);
lean_dec(v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v_s1_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v_s2_523_; lean_object* v___x_525_; 
v_s1_520_ = lean_string_utf8_extract(v_string_510_, v___x_514_, v___x_517_);
lean_dec(v___x_517_);
v___x_521_ = lean_string_length(v_s1_520_);
v___x_522_ = l_String_Slice_Pos_nextn(v___x_516_, v___x_514_, v___x_521_);
lean_dec_ref(v___x_516_);
v_s2_523_ = lean_string_utf8_extract(v_string_510_, v___x_522_, v___x_515_);
lean_dec(v___x_522_);
lean_dec_ref(v_string_510_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v_s2_523_);
v___x_525_ = v___x_512_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_s2_523_);
v___x_525_ = v_reuseFailAlloc_540_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_526_ = lean_array_mk(v_tail_506_);
v___x_527_ = lean_array_get_size(v___x_526_);
v___x_528_ = lean_nat_dec_eq(v___x_527_, v___x_514_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = lean_mk_empty_array_with_capacity(v___x_529_);
v___x_531_ = lean_array_push(v___x_530_, v___x_525_);
v___x_532_ = l_Array_append___redArg(v___x_531_, v___x_526_);
lean_dec_ref(v___x_526_);
v___x_533_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 0);
lean_ctor_set(v___x_508_, 1, v___x_533_);
lean_ctor_set(v___x_508_, 0, v_s1_520_);
v___x_535_ = v___x_508_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_s1_520_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
else
{
lean_object* v___x_538_; 
lean_dec_ref(v___x_526_);
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 0);
lean_ctor_set(v___x_508_, 1, v___x_525_);
lean_ctor_set(v___x_508_, 0, v_s1_520_);
v___x_538_ = v___x_508_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_s1_520_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_525_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v___x_541_; lean_object* v_fst_542_; lean_object* v_snd_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_551_; 
lean_dec(v___x_517_);
lean_dec_ref(v___x_516_);
lean_del_object(v___x_512_);
lean_del_object(v___x_508_);
v___x_541_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_506_);
v_fst_542_ = lean_ctor_get(v___x_541_, 0);
v_snd_543_ = lean_ctor_get(v___x_541_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_551_ == 0)
{
v___x_545_ = v___x_541_;
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_snd_543_);
lean_inc(v_fst_542_);
lean_dec(v___x_541_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_string_append(v_string_510_, v_fst_542_);
lean_dec(v_fst_542_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_snd_543_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_555_; lean_object* v_content_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_tail_555_ = lean_ctor_get(v_a_503_, 1);
lean_inc(v_tail_555_);
lean_dec_ref(v_a_503_);
v_content_556_ = lean_ctor_get(v_head_505_, 0);
lean_inc_ref(v_content_556_);
lean_dec_ref(v_head_505_);
v___x_557_ = lean_array_to_list(v_content_556_);
v___x_558_ = l_List_appendTR___redArg(v___x_557_, v_tail_555_);
v_a_503_ = v___x_558_;
goto _start;
}
default: 
{
lean_object* v_tail_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_598_; 
v_tail_560_ = lean_ctor_get(v_a_503_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_a_503_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v_a_503_, 0);
lean_dec(v_unused_599_);
v___x_562_ = v_a_503_;
v_isShared_563_ = v_isSharedCheck_598_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_tail_560_);
lean_dec(v_a_503_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_598_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_565_ = lean_array_mk(v_tail_560_);
if (lean_obj_tag(v_head_505_) == 9)
{
lean_object* v_content_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_content_566_ = lean_ctor_get(v_head_505_, 0);
v___x_567_ = lean_array_get_size(v_content_566_);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_nat_dec_eq(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_array_get_size(v___x_565_);
v___x_571_ = lean_nat_dec_eq(v___x_570_, v___x_568_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
lean_inc_ref(v_content_566_);
lean_dec_ref(v_head_505_);
v___x_572_ = l_Array_append___redArg(v_content_566_, v___x_565_);
lean_dec_ref(v___x_565_);
v___x_573_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
lean_ctor_set(v___x_562_, 1, v___x_573_);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_575_ = v___x_562_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
else
{
lean_object* v___x_578_; 
lean_dec_ref(v___x_565_);
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
lean_ctor_set(v___x_562_, 1, v_head_505_);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_578_ = v___x_562_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_head_505_);
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
lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec_ref(v_head_505_);
v___x_580_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_565_);
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
lean_ctor_set(v___x_562_, 1, v___x_580_);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_582_ = v___x_562_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_584_ = lean_array_get_size(v___x_565_);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_nat_dec_eq(v___x_584_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = lean_mk_empty_array_with_capacity(v___x_587_);
v___x_589_ = lean_array_push(v___x_588_, v_head_505_);
v___x_590_ = l_Array_append___redArg(v___x_589_, v___x_565_);
lean_dec_ref(v___x_565_);
v___x_591_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
lean_ctor_set(v___x_562_, 1, v___x_591_);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_593_ = v___x_562_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
else
{
lean_object* v___x_596_; 
lean_dec_ref(v___x_565_);
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
lean_ctor_set(v___x_562_, 1, v_head_505_);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_596_ = v___x_562_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_head_505_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_box(0);
v___x_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_605_, 0, v_inline_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_607_, lean_object* v_inline_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_610_, lean_object* v_pos_611_){
_start:
{
lean_object* v_str_612_; lean_object* v_startInclusive_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_str_612_ = lean_ctor_get(v_s_610_, 0);
v_startInclusive_613_ = lean_ctor_get(v_s_610_, 1);
v___x_614_ = lean_nat_add(v_startInclusive_613_, v_pos_611_);
v___x_615_ = lean_nat_sub(v___x_614_, v_startInclusive_613_);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_nat_dec_eq(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___y_626_; lean_object* v___x_627_; uint32_t v___x_628_; uint8_t v___y_630_; uint32_t v___x_635_; uint8_t v___x_636_; 
lean_inc(v_startInclusive_613_);
lean_inc_ref(v_str_612_);
v___x_618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_618_, 0, v_str_612_);
lean_ctor_set(v___x_618_, 1, v_startInclusive_613_);
lean_ctor_set(v___x_618_, 2, v___x_614_);
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_nat_sub(v___x_615_, v___x_619_);
lean_dec(v___x_615_);
v___x_621_ = l_String_Slice_posLE(v___x_618_, v___x_620_);
lean_dec_ref(v___x_618_);
v___x_627_ = lean_nat_add(v_startInclusive_613_, v___x_621_);
v___x_628_ = lean_string_utf8_get_fast(v_str_612_, v___x_627_);
lean_dec(v___x_627_);
v___x_635_ = 32;
v___x_636_ = lean_uint32_dec_eq(v___x_628_, v___x_635_);
if (v___x_636_ == 0)
{
uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 9;
v___x_638_ = lean_uint32_dec_eq(v___x_628_, v___x_637_);
v___y_630_ = v___x_638_;
goto v___jp_629_;
}
else
{
v___y_630_ = v___x_636_;
goto v___jp_629_;
}
v___jp_622_:
{
uint8_t v___x_623_; 
v___x_623_ = l_String_instDecidableLtRaw___aux__1(v___x_621_, v_pos_611_);
if (v___x_623_ == 0)
{
lean_dec(v___x_621_);
return v_pos_611_;
}
else
{
lean_dec(v_pos_611_);
v_pos_611_ = v___x_621_;
goto _start;
}
}
v___jp_625_:
{
if (v___y_626_ == 0)
{
lean_dec(v___x_621_);
return v_pos_611_;
}
else
{
goto v___jp_622_;
}
}
v___jp_629_:
{
if (v___y_630_ == 0)
{
uint32_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 13;
v___x_632_ = lean_uint32_dec_eq(v___x_628_, v___x_631_);
if (v___x_632_ == 0)
{
uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 10;
v___x_634_ = lean_uint32_dec_eq(v___x_628_, v___x_633_);
v___y_626_ = v___x_634_;
goto v___jp_625_;
}
else
{
v___y_626_ = v___x_632_;
goto v___jp_625_;
}
}
else
{
goto v___jp_622_;
}
}
}
else
{
lean_dec(v___x_615_);
lean_dec(v___x_614_);
return v_pos_611_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_639_, lean_object* v_pos_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_639_, v_pos_640_);
lean_dec_ref(v_s_639_);
return v_res_641_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_643_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_a_645_){
_start:
{
lean_object* v___y_647_; 
if (lean_obj_tag(v_a_645_) == 0)
{
lean_object* v___x_650_; 
v___x_650_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_650_;
}
else
{
lean_object* v_head_651_; 
v_head_651_ = lean_ctor_get(v_a_645_, 0);
lean_inc(v_head_651_);
switch(lean_obj_tag(v_head_651_))
{
case 0:
{
lean_object* v_tail_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_698_; 
v_tail_652_ = lean_ctor_get(v_a_645_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_a_645_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v_a_645_, 0);
lean_dec(v_unused_699_);
v___x_654_ = v_a_645_;
v_isShared_655_ = v_isSharedCheck_698_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_tail_652_);
lean_dec(v_a_645_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_698_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_string_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_697_; 
v_string_656_ = lean_ctor_get(v_head_651_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v_head_651_);
if (v_isSharedCheck_697_ == 0)
{
v___x_658_ = v_head_651_;
v_isShared_659_ = v_isSharedCheck_697_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_string_656_);
lean_dec(v_head_651_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_697_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_string_utf8_byte_size(v_string_656_);
lean_inc_ref(v_string_656_);
v___x_662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_662_, 0, v_string_656_);
lean_ctor_set(v___x_662_, 1, v___x_660_);
lean_ctor_set(v___x_662_, 2, v___x_661_);
v___x_663_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_662_, v___x_660_);
v___x_664_ = lean_nat_sub(v___x_661_, v___x_663_);
lean_dec(v___x_663_);
v___x_665_ = lean_nat_dec_eq(v___x_664_, v___x_660_);
lean_dec(v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v_s1_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_s2_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_666_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_662_, v___x_661_);
v_s1_667_ = lean_string_utf8_extract(v_string_656_, v___x_666_, v___x_661_);
lean_dec(v___x_666_);
v___x_668_ = lean_string_length(v_s1_667_);
v___x_669_ = l_String_Slice_Pos_prevn(v___x_662_, v___x_661_, v___x_668_);
lean_dec_ref(v___x_662_);
v_s2_670_ = lean_string_utf8_extract(v_string_656_, v___x_660_, v___x_669_);
lean_dec(v___x_669_);
lean_dec_ref(v_string_656_);
v___x_671_ = lean_array_mk(v_tail_652_);
v___x_672_ = l_Array_reverse___redArg(v___x_671_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v_s2_670_);
v___x_674_ = v___x_658_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_s2_670_);
v___x_674_ = v_reuseFailAlloc_685_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_array_get_size(v___x_672_);
v___x_676_ = lean_nat_dec_eq(v___x_675_, v___x_660_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_677_ = lean_array_push(v___x_672_, v___x_674_);
v___x_678_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 0);
lean_ctor_set(v___x_654_, 1, v_s1_667_);
lean_ctor_set(v___x_654_, 0, v___x_678_);
v___x_680_ = v___x_654_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_s1_667_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
else
{
lean_object* v___x_683_; 
lean_dec_ref(v___x_672_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 0);
lean_ctor_set(v___x_654_, 1, v_s1_667_);
lean_ctor_set(v___x_654_, 0, v___x_674_);
v___x_683_ = v___x_654_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_s1_667_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v___x_686_; lean_object* v_fst_687_; lean_object* v_snd_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v___x_662_);
lean_del_object(v___x_658_);
lean_del_object(v___x_654_);
v___x_686_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_tail_652_);
v_fst_687_ = lean_ctor_get(v___x_686_, 0);
v_snd_688_ = lean_ctor_get(v___x_686_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_696_ == 0)
{
v___x_690_ = v___x_686_;
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_snd_688_);
lean_inc(v_fst_687_);
lean_dec(v___x_686_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = lean_string_append(v_snd_688_, v_string_656_);
lean_dec_ref(v_string_656_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_fst_687_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_700_; lean_object* v_content_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_tail_700_ = lean_ctor_get(v_a_645_, 1);
lean_inc(v_tail_700_);
lean_dec_ref(v_a_645_);
v_content_701_ = lean_ctor_get(v_head_651_, 0);
lean_inc_ref(v_content_701_);
lean_dec_ref(v_head_651_);
v___x_702_ = l_Array_reverse___redArg(v_content_701_);
v___x_703_ = lean_array_to_list(v___x_702_);
v___x_704_ = l_List_appendTR___redArg(v___x_703_, v_tail_700_);
v_a_645_ = v___x_704_;
goto _start;
}
default: 
{
lean_object* v_tail_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_tail_706_ = lean_ctor_get(v_a_645_, 1);
lean_inc(v_tail_706_);
lean_dec_ref(v_a_645_);
v___x_707_ = lean_array_mk(v_tail_706_);
v___x_708_ = l_Array_reverse___redArg(v___x_707_);
v___x_709_ = lean_array_get_size(v___x_708_);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_nat_dec_eq(v___x_709_, v___x_710_);
if (v___x_711_ == 0)
{
if (lean_obj_tag(v_head_651_) == 9)
{
lean_object* v_content_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_content_712_ = lean_ctor_get(v_head_651_, 0);
lean_inc_ref(v_content_712_);
lean_dec_ref(v_head_651_);
v___x_713_ = lean_array_get_size(v_content_712_);
v___x_714_ = lean_nat_dec_eq(v___x_713_, v___x_710_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = l_Array_append___redArg(v___x_708_, v_content_712_);
lean_dec_ref(v_content_712_);
v___x_716_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
v___y_647_ = v___x_716_;
goto v___jp_646_;
}
else
{
lean_object* v___x_717_; 
lean_dec_ref(v_content_712_);
v___x_717_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_708_);
v___y_647_ = v___x_717_;
goto v___jp_646_;
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_array_push(v___x_708_, v_head_651_);
v___x_719_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
v___y_647_ = v___x_719_;
goto v___jp_646_;
}
}
else
{
lean_dec_ref(v___x_708_);
v___y_647_ = v_head_651_;
goto v___jp_646_;
}
}
}
}
v___jp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___y_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_a_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = lean_box(0);
v___x_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_725_, 0, v_inline_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_727_, lean_object* v_inline_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_730_){
_start:
{
lean_object* v___x_731_; lean_object* v_fst_732_; lean_object* v_snd_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_741_; 
v___x_731_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_730_);
v_fst_732_ = lean_ctor_get(v___x_731_, 0);
v_snd_733_ = lean_ctor_get(v___x_731_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_741_ == 0)
{
v___x_735_ = v___x_731_;
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_snd_733_);
lean_inc(v_fst_732_);
lean_dec(v___x_731_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_733_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_fst_732_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_742_, lean_object* v_inline_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_743_);
return v___x_744_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19));
v___x_791_ = l_ReaderT_instMonad___redArg(v___x_790_);
return v___x_791_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_800_ = l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0(lean_object* v_inst_802_, lean_object* v___x_803_, lean_object* v_a_804_, lean_object* v_x_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_809_; lean_object* v_snd_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_818_; 
v___x_809_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_802_, v_a_804_, v___y_807_, v___y_808_);
v_snd_810_ = lean_ctor_get(v___x_809_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v___x_809_, 0);
lean_dec(v_unused_819_);
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_818_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_snd_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_818_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_803_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_814_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_snd_810_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed(lean_object* v_inst_820_, lean_object* v___x_821_, lean_object* v_a_822_, lean_object* v_x_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0(v_inst_820_, v___x_821_, v_a_822_, v_x_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec_ref(v___y_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2___boxed(lean_object* v_inst_838_, lean_object* v_x_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2(v_inst_838_, v_x_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec_ref(v___y_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object* v_inst_845_, lean_object* v_x_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_845_, v_x_846_, v_a_847_, v_a_848_);
lean_dec_ref(v_a_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_850_, lean_object* v_x_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
switch(lean_obj_tag(v_x_851_))
{
case 0:
{
lean_object* v_string_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec_ref(v_inst_850_);
v_string_855_ = lean_ctor_get(v_x_851_, 0);
lean_inc_ref(v_string_855_);
lean_dec_ref(v_x_851_);
v___x_856_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_855_);
lean_dec_ref(v_string_855_);
v___x_857_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_856_, v_a_853_);
lean_dec_ref(v___x_856_);
return v___x_857_;
}
case 1:
{
lean_object* v_content_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_899_; 
v_content_858_ = lean_ctor_get(v_x_851_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v_x_851_);
if (v_isSharedCheck_899_ == 0)
{
v___x_860_ = v_x_851_;
v_isShared_861_ = v_isSharedCheck_899_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_content_858_);
lean_dec(v_x_851_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_899_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set_tag(v___x_860_, 9);
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_content_858_);
v___x_863_ = v_reuseFailAlloc_898_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; lean_object* v_snd_865_; lean_object* v_fst_866_; lean_object* v_fst_867_; lean_object* v_snd_868_; uint8_t v_inEmph_870_; uint8_t v_inBold_871_; uint8_t v_inLink_872_; lean_object* v_linePrefix_873_; lean_object* v___y_874_; lean_object* v___x_885_; uint8_t v_inEmph_886_; 
v___x_864_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_863_);
v_snd_865_ = lean_ctor_get(v___x_864_, 1);
lean_inc(v_snd_865_);
v_fst_866_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_fst_866_);
lean_dec_ref(v___x_864_);
v_fst_867_ = lean_ctor_get(v_snd_865_, 0);
lean_inc(v_fst_867_);
v_snd_868_ = lean_ctor_get(v_snd_865_, 1);
lean_inc(v_snd_868_);
lean_dec(v_snd_865_);
v___x_885_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_866_, v_a_853_);
lean_dec(v_fst_866_);
v_inEmph_886_ = lean_ctor_get_uint8(v_a_852_, sizeof(void*)*1);
if (v_inEmph_886_ == 0)
{
lean_object* v_snd_887_; uint8_t v_inBold_888_; uint8_t v_inLink_889_; lean_object* v_linePrefix_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_snd_893_; 
v_snd_887_ = lean_ctor_get(v___x_885_, 1);
lean_inc(v_snd_887_);
lean_dec_ref(v___x_885_);
v_inBold_888_ = lean_ctor_get_uint8(v_a_852_, sizeof(void*)*1 + 1);
v_inLink_889_ = lean_ctor_get_uint8(v_a_852_, sizeof(void*)*1 + 2);
v_linePrefix_890_ = lean_ctor_get(v_a_852_, 0);
v___x_891_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21));
v___x_892_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_891_, v_snd_887_);
v_snd_893_ = lean_ctor_get(v___x_892_, 1);
lean_inc(v_snd_893_);
lean_dec_ref(v___x_892_);
v_inEmph_870_ = v_inEmph_886_;
v_inBold_871_ = v_inBold_888_;
v_inLink_872_ = v_inLink_889_;
v_linePrefix_873_ = v_linePrefix_890_;
v___y_874_ = v_snd_893_;
goto v___jp_869_;
}
else
{
lean_object* v_snd_894_; uint8_t v_inBold_895_; uint8_t v_inLink_896_; lean_object* v_linePrefix_897_; 
v_snd_894_ = lean_ctor_get(v___x_885_, 1);
lean_inc(v_snd_894_);
lean_dec_ref(v___x_885_);
v_inBold_895_ = lean_ctor_get_uint8(v_a_852_, sizeof(void*)*1 + 1);
v_inLink_896_ = lean_ctor_get_uint8(v_a_852_, sizeof(void*)*1 + 2);
v_linePrefix_897_ = lean_ctor_get(v_a_852_, 0);
v_inEmph_870_ = v_inEmph_886_;
v_inBold_871_ = v_inBold_895_;
v_inLink_872_ = v_inLink_896_;
v_linePrefix_873_ = v_linePrefix_897_;
v___y_874_ = v_snd_894_;
goto v___jp_869_;
}
v___jp_869_:
{
uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = 1;
lean_inc_ref(v_linePrefix_873_);
v___x_876_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_876_, 0, v_linePrefix_873_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*1, v___x_875_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*1 + 1, v_inBold_871_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*1 + 2, v_inLink_872_);
v___x_877_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_850_, v_fst_867_, v___x_876_, v___y_874_);
lean_dec_ref(v___x_876_);
if (v_inEmph_870_ == 0)
{
lean_object* v_snd_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_snd_881_; lean_object* v___x_882_; 
v_snd_878_ = lean_ctor_get(v___x_877_, 1);
lean_inc(v_snd_878_);
lean_dec_ref(v___x_877_);
v___x_879_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21));
v___x_880_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_879_, v_snd_878_);
v_snd_881_ = lean_ctor_get(v___x_880_, 1);
lean_inc(v_snd_881_);
lean_dec_ref(v___x_880_);
v___x_882_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_868_, v_snd_881_);
lean_dec(v_snd_868_);
return v___x_882_;
}
else
{
lean_object* v_snd_883_; lean_object* v___x_884_; 
v_snd_883_ = lean_ctor_get(v___x_877_, 1);
lean_inc(v_snd_883_);
lean_dec_ref(v___x_877_);
v___x_884_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_868_, v_snd_883_);
lean_dec(v_snd_868_);
return v___x_884_;
}
}
}
}
}
case 2:
{
lean_object* v_content_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_938_; 
v_content_900_ = lean_ctor_get(v_x_851_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v_x_851_);
if (v_isSharedCheck_938_ == 0)
{
v___x_902_ = v_x_851_;
v_isShared_903_ = v_isSharedCheck_938_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_content_900_);
lean_dec(v_x_851_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_938_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 9);
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_content_900_);
v___x_905_ = v_reuseFailAlloc_937_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; lean_object* v_snd_907_; lean_object* v_fst_908_; lean_object* v_fst_909_; lean_object* v_snd_910_; uint8_t v_inBold_912_; uint8_t v_inLink_913_; lean_object* v_linePrefix_914_; lean_object* v___y_915_; lean_object* v___x_926_; uint8_t v_inBold_927_; 
v___x_906_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_905_);
v_snd_907_ = lean_ctor_get(v___x_906_, 1);
lean_inc(v_snd_907_);
v_fst_908_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_fst_908_);
lean_dec_ref(v___x_906_);
v_fst_909_ = lean_ctor_get(v_snd_907_, 0);
lean_inc(v_fst_909_);
v_snd_910_ = lean_ctor_get(v_snd_907_, 1);
lean_inc(v_snd_910_);
lean_dec(v_snd_907_);
v___x_926_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_908_, v_a_853_);
lean_dec(v_fst_908_);
v_inBold_927_ = lean_ctor_get_uint8(v_a_852_, sizeof(void*)*1 + 1);
if (v_inBold_927_ == 0)
{
lean_object* v_snd_928_; uint8_t v_inLink_929_; lean_object* v_linePrefix_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v_snd_933_; 
v_snd_928_ = lean_ctor_get(v___x_926_, 1);
lean_inc(v_snd_928_);
lean_dec_ref(v___x_926_);
v_inLink_929_ = lean_ctor_get_uint8(v_a_852_, sizeof(void*)*1 + 2);
v_linePrefix_930_ = lean_ctor_get(v_a_852_, 0);
v___x_931_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_932_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_931_, v_snd_928_);
v_snd_933_ = lean_ctor_get(v___x_932_, 1);
lean_inc(v_snd_933_);
lean_dec_ref(v___x_932_);
v_inBold_912_ = v_inBold_927_;
v_inLink_913_ = v_inLink_929_;
v_linePrefix_914_ = v_linePrefix_930_;
v___y_915_ = v_snd_933_;
goto v___jp_911_;
}
else
{
lean_object* v_snd_934_; uint8_t v_inLink_935_; lean_object* v_linePrefix_936_; 
v_snd_934_ = lean_ctor_get(v___x_926_, 1);
lean_inc(v_snd_934_);
lean_dec_ref(v___x_926_);
v_inLink_935_ = lean_ctor_get_uint8(v_a_852_, sizeof(void*)*1 + 2);
v_linePrefix_936_ = lean_ctor_get(v_a_852_, 0);
v_inBold_912_ = v_inBold_927_;
v_inLink_913_ = v_inLink_935_;
v_linePrefix_914_ = v_linePrefix_936_;
v___y_915_ = v_snd_934_;
goto v___jp_911_;
}
v___jp_911_:
{
uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = 1;
lean_inc_ref(v_linePrefix_914_);
v___x_917_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_917_, 0, v_linePrefix_914_);
lean_ctor_set_uint8(v___x_917_, sizeof(void*)*1, v___x_916_);
lean_ctor_set_uint8(v___x_917_, sizeof(void*)*1 + 1, v_inBold_912_);
lean_ctor_set_uint8(v___x_917_, sizeof(void*)*1 + 2, v_inLink_913_);
v___x_918_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_850_, v_fst_909_, v___x_917_, v___y_915_);
lean_dec_ref(v___x_917_);
if (v_inBold_912_ == 0)
{
lean_object* v_snd_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_snd_922_; lean_object* v___x_923_; 
v_snd_919_ = lean_ctor_get(v___x_918_, 1);
lean_inc(v_snd_919_);
lean_dec_ref(v___x_918_);
v___x_920_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_921_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_920_, v_snd_919_);
v_snd_922_ = lean_ctor_get(v___x_921_, 1);
lean_inc(v_snd_922_);
lean_dec_ref(v___x_921_);
v___x_923_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_910_, v_snd_922_);
lean_dec(v_snd_910_);
return v___x_923_;
}
else
{
lean_object* v_snd_924_; lean_object* v___x_925_; 
v_snd_924_ = lean_ctor_get(v___x_918_, 1);
lean_inc(v_snd_924_);
lean_dec_ref(v___x_918_);
v___x_925_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_910_, v_snd_924_);
lean_dec(v_snd_910_);
return v___x_925_;
}
}
}
}
}
case 3:
{
lean_object* v_string_939_; lean_object* v___y_941_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_fst_946_; uint8_t v___x_947_; 
lean_dec_ref(v_inst_850_);
v_string_939_ = lean_ctor_get(v_x_851_, 0);
lean_inc_ref(v_string_939_);
lean_dec_ref(v_x_851_);
v___x_944_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_945_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v___x_944_, v_a_853_);
v_fst_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_fst_946_);
v___x_947_ = lean_unbox(v_fst_946_);
lean_dec(v_fst_946_);
if (v___x_947_ == 0)
{
lean_object* v_snd_948_; 
v_snd_948_ = lean_ctor_get(v___x_945_, 1);
lean_inc(v_snd_948_);
lean_dec_ref(v___x_945_);
v___y_941_ = v_snd_948_;
goto v___jp_940_;
}
else
{
lean_object* v_snd_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_snd_952_; 
v_snd_949_ = lean_ctor_get(v___x_945_, 1);
lean_inc(v_snd_949_);
lean_dec_ref(v___x_945_);
v___x_950_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23));
v___x_951_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_950_, v_snd_949_);
v_snd_952_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_snd_952_);
lean_dec_ref(v___x_951_);
v___y_941_ = v_snd_952_;
goto v___jp_940_;
}
v___jp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_939_);
v___x_943_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_942_, v___y_941_);
lean_dec_ref(v___x_942_);
return v___x_943_;
}
}
case 4:
{
uint8_t v_mode_953_; 
lean_dec_ref(v_inst_850_);
v_mode_953_ = lean_ctor_get_uint8(v_x_851_, sizeof(void*)*1);
if (v_mode_953_ == 0)
{
lean_object* v_string_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_string_954_ = lean_ctor_get(v_x_851_, 0);
lean_inc_ref(v_string_954_);
lean_dec_ref(v_x_851_);
v___x_955_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24));
v___x_956_ = lean_string_append(v___x_955_, v_string_954_);
lean_dec_ref(v_string_954_);
v___x_957_ = lean_string_append(v___x_956_, v___x_955_);
v___x_958_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_957_, v_a_853_);
lean_dec_ref(v___x_957_);
return v___x_958_;
}
else
{
lean_object* v_string_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_string_959_ = lean_ctor_get(v_x_851_, 0);
lean_inc_ref(v_string_959_);
lean_dec_ref(v_x_851_);
v___x_960_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25));
v___x_961_ = lean_string_append(v___x_960_, v_string_959_);
lean_dec_ref(v_string_959_);
v___x_962_ = lean_string_append(v___x_961_, v___x_960_);
v___x_963_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_962_, v_a_853_);
lean_dec_ref(v___x_962_);
return v___x_963_;
}
}
case 5:
{
lean_object* v_string_964_; lean_object* v_linePrefix_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec_ref(v_inst_850_);
v_string_964_ = lean_ctor_get(v_x_851_, 0);
lean_inc_ref(v_string_964_);
lean_dec_ref(v_x_851_);
v_linePrefix_965_ = lean_ctor_get(v_a_852_, 0);
v___x_966_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26));
v___x_967_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27));
v___x_968_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_969_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28);
v___x_970_ = lean_string_append(v___x_968_, v_linePrefix_965_);
v___x_971_ = lean_unsigned_to_nat(0u);
v___x_972_ = lean_string_utf8_byte_size(v_string_964_);
v___x_973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_973_, 0, v_string_964_);
lean_ctor_set(v___x_973_, 1, v___x_971_);
lean_ctor_set(v___x_973_, 2, v___x_972_);
v___x_974_ = l_String_Slice_replace___redArg(v___x_967_, v___x_966_, v___x_973_, v___x_969_, v___x_970_);
v___x_975_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_974_, v_a_853_);
lean_dec_ref(v___x_974_);
return v___x_975_;
}
case 6:
{
uint8_t v_inLink_976_; 
v_inLink_976_ = lean_ctor_get_uint8(v_a_852_, sizeof(void*)*1 + 2);
if (v_inLink_976_ == 0)
{
lean_object* v_content_977_; lean_object* v_url_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_snd_981_; lean_object* v___x_982_; lean_object* v___f_983_; size_t v_sz_984_; size_t v___x_985_; lean_object* v___x_12052__overap_986_; lean_object* v___x_987_; lean_object* v_snd_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v_snd_991_; lean_object* v___x_992_; lean_object* v_snd_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_content_977_ = lean_ctor_get(v_x_851_, 0);
lean_inc_ref(v_content_977_);
v_url_978_ = lean_ctor_get(v_x_851_, 1);
lean_inc_ref(v_url_978_);
lean_dec_ref(v_x_851_);
v___x_979_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29));
v___x_980_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_979_, v_a_853_);
v_snd_981_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_snd_981_);
lean_dec_ref(v___x_980_);
v___x_982_ = lean_box(0);
v___f_983_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_983_, 0, v_inst_850_);
lean_closure_set(v___f_983_, 1, v___x_982_);
v_sz_984_ = lean_array_size(v_content_977_);
v___x_985_ = ((size_t)0ULL);
v___x_12052__overap_986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_854_, v_content_977_, v___f_983_, v_sz_984_, v___x_985_, v___x_982_);
lean_inc_ref(v_a_852_);
v___x_987_ = lean_apply_2(v___x_12052__overap_986_, v_a_852_, v_snd_981_);
v_snd_988_ = lean_ctor_get(v___x_987_, 1);
lean_inc(v_snd_988_);
lean_dec_ref(v___x_987_);
v___x_989_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30));
v___x_990_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_989_, v_snd_988_);
v_snd_991_ = lean_ctor_get(v___x_990_, 1);
lean_inc(v_snd_991_);
lean_dec_ref(v___x_990_);
v___x_992_ = l_Lean_Doc_MarkdownM_push___redArg(v_url_978_, v_snd_991_);
lean_dec_ref(v_url_978_);
v_snd_993_ = lean_ctor_get(v___x_992_, 1);
lean_inc(v_snd_993_);
lean_dec_ref(v___x_992_);
v___x_994_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31));
v___x_995_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_994_, v_snd_993_);
return v___x_995_;
}
else
{
lean_object* v_content_996_; lean_object* v___x_997_; lean_object* v___f_998_; size_t v_sz_999_; size_t v___x_1000_; lean_object* v___x_12076__overap_1001_; lean_object* v___x_1002_; lean_object* v_snd_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
v_content_996_ = lean_ctor_get(v_x_851_, 0);
lean_inc_ref(v_content_996_);
lean_dec_ref(v_x_851_);
v___x_997_ = lean_box(0);
v___f_998_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_998_, 0, v_inst_850_);
lean_closure_set(v___f_998_, 1, v___x_997_);
v_sz_999_ = lean_array_size(v_content_996_);
v___x_1000_ = ((size_t)0ULL);
v___x_12076__overap_1001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_854_, v_content_996_, v___f_998_, v_sz_999_, v___x_1000_, v___x_997_);
lean_inc_ref(v_a_852_);
v___x_1002_ = lean_apply_2(v___x_12076__overap_1001_, v_a_852_, v_a_853_);
v_snd_1003_ = lean_ctor_get(v___x_1002_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v___x_1002_, 0);
lean_dec(v_unused_1011_);
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_snd_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_997_);
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_snd_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
case 7:
{
lean_object* v_name_1012_; lean_object* v_content_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_snd_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1061_; 
v_name_1012_ = lean_ctor_get(v_x_851_, 0);
lean_inc_ref(v_name_1012_);
v_content_1013_ = lean_ctor_get(v_x_851_, 1);
lean_inc_ref(v_content_1013_);
lean_dec_ref(v_x_851_);
v___x_1014_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32));
v___x_1015_ = lean_string_append(v___x_1014_, v_name_1012_);
v___x_1016_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33));
v___x_1017_ = lean_string_append(v___x_1015_, v___x_1016_);
v___x_1018_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1017_, v_a_853_);
lean_dec_ref(v___x_1017_);
v_snd_1019_ = lean_ctor_get(v___x_1018_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v___x_1018_, 0);
lean_dec(v_unused_1062_);
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1061_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_snd_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1061_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_snd_1024_; lean_object* v___y_1043_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = lean_array_get_size(v_content_1013_);
v___x_1047_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34));
v___x_1048_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35));
v___x_1049_ = lean_nat_dec_lt(v___x_1045_, v___x_1046_);
if (v___x_1049_ == 0)
{
lean_dec_ref(v_content_1013_);
lean_dec_ref(v_inst_850_);
v_snd_1024_ = v___x_1048_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1050_; lean_object* v___f_1051_; uint8_t v___x_1052_; 
v___x_1050_ = lean_box(0);
v___f_1051_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_1051_, 0, v_inst_850_);
v___x_1052_ = lean_nat_dec_le(v___x_1046_, v___x_1046_);
if (v___x_1052_ == 0)
{
if (v___x_1049_ == 0)
{
lean_dec_ref(v___f_1051_);
lean_dec_ref(v_content_1013_);
v_snd_1024_ = v___x_1048_;
goto v___jp_1023_;
}
else
{
size_t v___x_1053_; size_t v___x_1054_; lean_object* v___x_11895__overap_1055_; lean_object* v___x_1056_; 
v___x_1053_ = ((size_t)0ULL);
v___x_1054_ = lean_usize_of_nat(v___x_1046_);
v___x_11895__overap_1055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_854_, v___f_1051_, v_content_1013_, v___x_1053_, v___x_1054_, v___x_1050_);
v___x_1056_ = lean_apply_2(v___x_11895__overap_1055_, v___x_1047_, v___x_1048_);
v___y_1043_ = v___x_1056_;
goto v___jp_1042_;
}
}
else
{
size_t v___x_1057_; size_t v___x_1058_; lean_object* v___x_11899__overap_1059_; lean_object* v___x_1060_; 
v___x_1057_ = ((size_t)0ULL);
v___x_1058_ = lean_usize_of_nat(v___x_1046_);
v___x_11899__overap_1059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_854_, v___f_1051_, v_content_1013_, v___x_1057_, v___x_1058_, v___x_1050_);
v___x_1060_ = lean_apply_2(v___x_11899__overap_1059_, v___x_1047_, v___x_1048_);
v___y_1043_ = v___x_1060_;
goto v___jp_1042_;
}
}
v___jp_1023_:
{
lean_object* v_priorBlocks_1025_; lean_object* v_currentBlock_1026_; lean_object* v_footnotes_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1041_; 
v_priorBlocks_1025_ = lean_ctor_get(v_snd_1019_, 0);
v_currentBlock_1026_ = lean_ctor_get(v_snd_1019_, 1);
v_footnotes_1027_ = lean_ctor_get(v_snd_1019_, 2);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_snd_1019_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1029_ = v_snd_1019_;
v_isShared_1030_ = v_isSharedCheck_1041_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_footnotes_1027_);
lean_inc(v_currentBlock_1026_);
lean_inc(v_priorBlocks_1025_);
lean_dec(v_snd_1019_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1041_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1031_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(v_snd_1024_);
v___x_1032_ = lean_box(0);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v___x_1031_);
lean_ctor_set(v___x_1021_, 0, v_name_1012_);
v___x_1034_ = v___x_1021_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_name_1012_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1031_);
v___x_1034_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_array_push(v_footnotes_1027_, v___x_1034_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 2, v___x_1035_);
v___x_1037_ = v___x_1029_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_priorBlocks_1025_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_currentBlock_1026_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1032_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
return v___x_1038_;
}
}
}
}
v___jp_1042_:
{
lean_object* v_snd_1044_; 
v_snd_1044_ = lean_ctor_get(v___y_1043_, 1);
lean_inc(v_snd_1044_);
lean_dec_ref(v___y_1043_);
v_snd_1024_ = v_snd_1044_;
goto v___jp_1023_;
}
}
}
case 8:
{
lean_object* v_alt_1063_; lean_object* v_url_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_dec_ref(v_inst_850_);
v_alt_1063_ = lean_ctor_get(v_x_851_, 0);
lean_inc_ref(v_alt_1063_);
v_url_1064_ = lean_ctor_get(v_x_851_, 1);
lean_inc_ref(v_url_1064_);
lean_dec_ref(v_x_851_);
v___x_1065_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__36));
v___x_1066_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1063_);
lean_dec_ref(v_alt_1063_);
v___x_1067_ = lean_string_append(v___x_1065_, v___x_1066_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30));
v___x_1069_ = lean_string_append(v___x_1067_, v___x_1068_);
v___x_1070_ = lean_string_append(v___x_1069_, v_url_1064_);
lean_dec_ref(v_url_1064_);
v___x_1071_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31));
v___x_1072_ = lean_string_append(v___x_1070_, v___x_1071_);
v___x_1073_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1072_, v_a_853_);
lean_dec_ref(v___x_1072_);
return v___x_1073_;
}
case 9:
{
lean_object* v_content_1074_; lean_object* v___x_1075_; lean_object* v___f_1076_; size_t v_sz_1077_; size_t v___x_1078_; lean_object* v___x_11990__overap_1079_; lean_object* v___x_1080_; lean_object* v_snd_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
v_content_1074_ = lean_ctor_get(v_x_851_, 0);
lean_inc_ref(v_content_1074_);
lean_dec_ref(v_x_851_);
v___x_1075_ = lean_box(0);
v___f_1076_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1076_, 0, v_inst_850_);
lean_closure_set(v___f_1076_, 1, v___x_1075_);
v_sz_1077_ = lean_array_size(v_content_1074_);
v___x_1078_ = ((size_t)0ULL);
v___x_11990__overap_1079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_854_, v_content_1074_, v___f_1076_, v_sz_1077_, v___x_1078_, v___x_1075_);
lean_inc_ref(v_a_852_);
v___x_1080_ = lean_apply_2(v___x_11990__overap_1079_, v_a_852_, v_a_853_);
v_snd_1081_ = lean_ctor_get(v___x_1080_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v___x_1080_, 0);
lean_dec(v_unused_1089_);
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_snd_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1075_);
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_snd_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
default: 
{
lean_object* v_container_1090_; lean_object* v_content_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_container_1090_ = lean_ctor_get(v_x_851_, 0);
lean_inc(v_container_1090_);
v_content_1091_ = lean_ctor_get(v_x_851_, 1);
lean_inc_ref(v_content_1091_);
lean_dec_ref(v_x_851_);
lean_inc_ref(v_inst_850_);
v___x_1092_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 4, 1);
lean_closure_set(v___x_1092_, 0, v_inst_850_);
lean_inc_ref(v_a_852_);
v___x_1093_ = lean_apply_5(v_inst_850_, v___x_1092_, v_container_1090_, v_content_1091_, v_a_852_, v_a_853_);
return v___x_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2(lean_object* v_inst_1094_, lean_object* v_x_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1094_, v___y_1096_, v___y_1097_, v___y_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1100_, lean_object* v_inst_1101_, lean_object* v_x_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1101_, v_x_1102_, v_a_1103_, v_a_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object* v_i_1106_, lean_object* v_inst_1107_, lean_object* v_x_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(v_i_1106_, v_inst_1107_, v_x_1108_, v_a_1109_, v_a_1110_);
lean_dec_ref(v_a_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1112_, lean_object* v_inline_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1112_, v_inline_1113_, v_a_1114_, v_a_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object* v_inst_1117_, lean_object* v_inline_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(v_inst_1117_, v_inline_1118_, v_a_1119_, v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1122_, lean_object* v_inst_1123_, lean_object* v_inline_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1123_, v_inline_1124_, v_a_1125_, v_a_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object* v_i_1128_, lean_object* v_inst_1129_, lean_object* v_inline_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(v_i_1128_, v_inst_1129_, v_inline_1130_, v_a_1131_, v_a_1132_);
lean_dec_ref(v_a_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0(lean_object* v_inst_1134_, lean_object* v_inline_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1134_, v_inline_1135_, v___y_1136_, v___y_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0___boxed(lean_object* v_inst_1139_, lean_object* v_inline_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0(v_inst_1139_, v_inline_1140_, v___y_1141_, v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1144_){
_start:
{
lean_object* v___f_1145_; 
v___f_1145_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1145_, 0, v_inst_1144_);
return v___f_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1146_, lean_object* v_inst_1147_){
_start:
{
lean_object* v___f_1148_; 
v___f_1148_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1148_, 0, v_inst_1147_);
return v___f_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
lean_object* v_zero_1151_; uint8_t v_isZero_1152_; 
v_zero_1151_ = lean_unsigned_to_nat(0u);
v_isZero_1152_ = lean_nat_dec_eq(v_x_1149_, v_zero_1151_);
if (v_isZero_1152_ == 1)
{
lean_dec(v_x_1149_);
return v_x_1150_;
}
else
{
uint32_t v___x_1153_; lean_object* v_one_1154_; lean_object* v_n_1155_; lean_object* v___x_1156_; 
v___x_1153_ = 32;
v_one_1154_ = lean_unsigned_to_nat(1u);
v_n_1155_ = lean_nat_sub(v_x_1149_, v_one_1154_);
lean_dec(v_x_1149_);
v___x_1156_ = lean_string_push(v_x_1150_, v___x_1153_);
v_x_1149_ = v_n_1155_;
v_x_1150_ = v___x_1156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(lean_object* v_str_1158_, lean_object* v_indent_1159_, lean_object* v_b_1160_){
_start:
{
lean_object* v_snd_1161_; lean_object* v_snd_1162_; lean_object* v_fst_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1225_; 
v_snd_1161_ = lean_ctor_get(v_b_1160_, 1);
lean_inc(v_snd_1161_);
v_snd_1162_ = lean_ctor_get(v_snd_1161_, 1);
lean_inc(v_snd_1162_);
v_fst_1163_ = lean_ctor_get(v_b_1160_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_b_1160_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v_b_1160_, 1);
lean_dec(v_unused_1226_);
v___x_1165_ = v_b_1160_;
v_isShared_1166_ = v_isSharedCheck_1225_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_fst_1163_);
lean_dec(v_b_1160_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1225_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_fst_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1223_; 
v_fst_1167_ = lean_ctor_get(v_snd_1161_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_snd_1161_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v_snd_1161_, 1);
lean_dec(v_unused_1224_);
v___x_1169_ = v_snd_1161_;
v_isShared_1170_ = v_isSharedCheck_1223_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_fst_1167_);
lean_dec(v_snd_1161_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1223_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_fst_1171_; lean_object* v_snd_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1222_; 
v_fst_1171_ = lean_ctor_get(v_snd_1162_, 0);
v_snd_1172_ = lean_ctor_get(v_snd_1162_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_snd_1162_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1174_ = v_snd_1162_;
v_isShared_1175_ = v_isSharedCheck_1222_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_snd_1172_);
lean_inc(v_fst_1171_);
lean_dec(v_snd_1162_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1222_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_string_utf8_byte_size(v_str_1158_);
v___x_1177_ = lean_nat_dec_eq(v_fst_1171_, v___x_1176_);
if (v___x_1177_ == 0)
{
uint32_t v_c_1178_; lean_object* v_iter_1179_; lean_object* v_longest_1181_; lean_object* v_current_1182_; uint32_t v___x_1207_; uint8_t v___x_1208_; 
v_c_1178_ = lean_string_utf8_get_fast(v_str_1158_, v_fst_1171_);
v_iter_1179_ = lean_string_utf8_next_fast(v_str_1158_, v_fst_1171_);
lean_dec(v_fst_1171_);
v___x_1207_ = 96;
v___x_1208_ = lean_uint32_dec_eq(v_c_1178_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_object* v_current_1209_; uint8_t v___x_1210_; 
v_current_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_nat_dec_le(v_fst_1163_, v_fst_1167_);
if (v___x_1210_ == 0)
{
lean_dec(v_fst_1167_);
v_longest_1181_ = v_fst_1163_;
v_current_1182_ = v_current_1209_;
goto v___jp_1180_;
}
else
{
lean_dec(v_fst_1163_);
v_longest_1181_ = v_fst_1167_;
v_current_1182_ = v_current_1209_;
goto v___jp_1180_;
}
}
else
{
lean_object* v___x_1211_; lean_object* v_current_1212_; 
v___x_1211_ = lean_unsigned_to_nat(1u);
v_current_1212_ = lean_nat_add(v_fst_1167_, v___x_1211_);
lean_dec(v_fst_1167_);
v_longest_1181_ = v_fst_1163_;
v_current_1182_ = v_current_1212_;
goto v___jp_1180_;
}
v___jp_1180_:
{
lean_object* v_out_1183_; uint32_t v___x_1184_; uint8_t v___x_1185_; 
v_out_1183_ = lean_string_push(v_snd_1172_, v_c_1178_);
v___x_1184_ = 10;
v___x_1185_ = lean_uint32_dec_eq(v_c_1178_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1187_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v_out_1183_);
lean_ctor_set(v___x_1174_, 0, v_iter_1179_);
v___x_1187_ = v___x_1174_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_iter_1179_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_out_1183_);
v___x_1187_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1187_);
lean_ctor_set(v___x_1169_, 0, v_current_1182_);
v___x_1189_ = v___x_1169_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_current_1182_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1191_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v___x_1189_);
lean_ctor_set(v___x_1165_, 0, v_longest_1181_);
v___x_1191_ = v___x_1165_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_longest_1181_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v_b_1160_ = v___x_1191_;
goto _start;
}
}
}
}
else
{
lean_object* v_out_1196_; lean_object* v___x_1198_; 
lean_inc(v_indent_1159_);
v_out_1196_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(v_indent_1159_, v_out_1183_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v_out_1196_);
lean_ctor_set(v___x_1174_, 0, v_iter_1179_);
v___x_1198_ = v___x_1174_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_iter_1179_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_out_1196_);
v___x_1198_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1198_);
lean_ctor_set(v___x_1169_, 0, v_current_1182_);
v___x_1200_ = v___x_1169_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_current_1182_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v___x_1200_);
lean_ctor_set(v___x_1165_, 0, v_longest_1181_);
v___x_1202_ = v___x_1165_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_longest_1181_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
v_b_1160_ = v___x_1202_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_1214_; 
lean_dec(v_indent_1159_);
if (v_isShared_1175_ == 0)
{
v___x_1214_ = v___x_1174_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_fst_1171_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_snd_1172_);
v___x_1214_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1214_);
v___x_1216_ = v___x_1169_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_fst_1167_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v___x_1216_);
v___x_1218_ = v___x_1165_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_fst_1163_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1___boxed(lean_object* v_str_1227_, lean_object* v_indent_1228_, lean_object* v_b_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(v_str_1227_, v_indent_1228_, v_b_1229_);
lean_dec_ref(v_str_1227_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(lean_object* v_indent_1240_, lean_object* v_str_1241_){
_start:
{
lean_object* v_current_1242_; lean_object* v_out_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_snd_1246_; lean_object* v_snd_1247_; lean_object* v_fst_1248_; lean_object* v_fst_1249_; lean_object* v_snd_1250_; lean_object* v___x_1251_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1264_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_current_1242_ = lean_unsigned_to_nat(0u);
v_out_1243_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_1244_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__2));
lean_inc(v_indent_1240_);
v___x_1245_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(v_str_1241_, v_indent_1240_, v___x_1244_);
v_snd_1246_ = lean_ctor_get(v___x_1245_, 1);
lean_inc(v_snd_1246_);
v_snd_1247_ = lean_ctor_get(v_snd_1246_, 1);
lean_inc(v_snd_1247_);
v_fst_1248_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_fst_1248_);
lean_dec_ref(v___x_1245_);
v_fst_1249_ = lean_ctor_get(v_snd_1246_, 0);
lean_inc(v_fst_1249_);
lean_dec(v_snd_1246_);
v_snd_1250_ = lean_ctor_get(v_snd_1247_, 1);
lean_inc(v_snd_1250_);
lean_dec(v_snd_1247_);
v___x_1251_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1270_ = lean_string_utf8_byte_size(v_snd_1250_);
v___x_1271_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2);
v___x_1272_ = lean_nat_dec_le(v___x_1271_, v___x_1270_);
if (v___x_1272_ == 0)
{
goto v___jp_1267_;
}
else
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = lean_nat_sub(v___x_1270_, v___x_1271_);
v___x_1274_ = lean_string_memcmp(v_snd_1250_, v___x_1251_, v___x_1273_, v_current_1242_, v___x_1271_);
lean_dec(v___x_1273_);
if (v___x_1274_ == 0)
{
goto v___jp_1267_;
}
else
{
v___y_1264_ = v_snd_1250_;
goto v___jp_1263_;
}
}
v___jp_1252_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_add(v___y_1255_, v___x_1256_);
lean_dec(v___y_1255_);
v___x_1258_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__1(v___x_1257_, v___y_1253_);
lean_inc_ref(v___x_1258_);
v___x_1259_ = lean_string_append(v___x_1258_, v___x_1251_);
v___x_1260_ = lean_string_append(v___x_1259_, v___y_1254_);
lean_dec_ref(v___y_1254_);
v___x_1261_ = lean_string_append(v___x_1260_, v___x_1258_);
lean_dec_ref(v___x_1258_);
v___x_1262_ = lean_string_append(v___x_1261_, v___x_1251_);
return v___x_1262_;
}
v___jp_1263_:
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1265_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(v_indent_1240_, v_out_1243_);
v___x_1266_ = lean_nat_dec_le(v_fst_1248_, v_fst_1249_);
if (v___x_1266_ == 0)
{
lean_dec(v_fst_1249_);
v___y_1253_ = v___x_1265_;
v___y_1254_ = v___y_1264_;
v___y_1255_ = v_fst_1248_;
goto v___jp_1252_;
}
else
{
lean_dec(v_fst_1248_);
v___y_1253_ = v___x_1265_;
v___y_1254_ = v___y_1264_;
v___y_1255_ = v_fst_1249_;
goto v___jp_1252_;
}
}
v___jp_1267_:
{
uint32_t v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = 10;
v___x_1269_ = lean_string_push(v_snd_1250_, v___x_1268_);
v___y_1264_ = v___x_1269_;
goto v___jp_1263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___boxed(lean_object* v_indent_1275_, lean_object* v_str_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v_indent_1275_, v_str_1276_);
lean_dec_ref(v_str_1276_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v___x_1279_, lean_object* v___f_1280_, lean_object* v___x_1281_, lean_object* v_a_1282_, lean_object* v_x_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
uint8_t v_inEmph_1287_; uint8_t v_inBold_1288_; uint8_t v_inLink_1289_; lean_object* v_linePrefix_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v_snd_1294_; size_t v_sz_1295_; size_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_13712__overap_1300_; lean_object* v___x_1301_; lean_object* v_snd_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1310_; 
v_inEmph_1287_ = lean_ctor_get_uint8(v___y_1285_, sizeof(void*)*1);
v_inBold_1288_ = lean_ctor_get_uint8(v___y_1285_, sizeof(void*)*1 + 1);
v_inLink_1289_ = lean_ctor_get_uint8(v___y_1285_, sizeof(void*)*1 + 2);
v_linePrefix_1290_ = lean_ctor_get(v___y_1285_, 0);
v___x_1291_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
lean_inc_ref_n(v_linePrefix_1290_, 2);
v___x_1292_ = lean_string_append(v_linePrefix_1290_, v___x_1291_);
v___x_1293_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1292_, v___y_1286_);
lean_dec_ref(v___x_1292_);
v_snd_1294_ = lean_ctor_get(v___x_1293_, 1);
lean_inc(v_snd_1294_);
lean_dec_ref(v___x_1293_);
v_sz_1295_ = lean_array_size(v_a_1282_);
v___x_1296_ = ((size_t)0ULL);
v___x_1297_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1298_ = lean_string_append(v_linePrefix_1290_, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*1, v_inEmph_1287_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*1 + 1, v_inBold_1288_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*1 + 2, v_inLink_1289_);
v___x_13712__overap_1300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1279_, v_a_1282_, v___f_1280_, v_sz_1295_, v___x_1296_, v___x_1281_);
v___x_1301_ = lean_apply_2(v___x_13712__overap_1300_, v___x_1299_, v_snd_1294_);
v_snd_1302_ = lean_ctor_get(v___x_1301_, 1);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; 
v_unused_1311_ = lean_ctor_get(v___x_1301_, 0);
lean_dec(v_unused_1311_);
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1310_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_snd_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1310_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1281_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1306_);
v___x_1308_ = v___x_1304_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_snd_1302_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed(lean_object* v___x_1312_, lean_object* v___f_1313_, lean_object* v___x_1314_, lean_object* v_a_1315_, lean_object* v_x_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(v___x_1312_, v___f_1313_, v___x_1314_, v_a_1315_, v_x_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v___x_1323_, lean_object* v_a_1324_, lean_object* v_x_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v_inst_1321_, v_inst_1322_, v___x_1323_, v_a_1324_, v_x_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v___x_1333_, lean_object* v___x_1334_, lean_object* v_a_1335_, lean_object* v_x_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v_inEmph_1340_; uint8_t v_inBold_1341_; uint8_t v_inLink_1342_; lean_object* v_linePrefix_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v_snd_1349_; lean_object* v___x_1350_; lean_object* v___f_1351_; size_t v_sz_1352_; size_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_13750__overap_1357_; lean_object* v___x_1358_; lean_object* v_snd_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1368_; 
v_inEmph_1340_ = lean_ctor_get_uint8(v___y_1338_, sizeof(void*)*1);
v_inBold_1341_ = lean_ctor_get_uint8(v___y_1338_, sizeof(void*)*1 + 1);
v_inLink_1342_ = lean_ctor_get_uint8(v___y_1338_, sizeof(void*)*1 + 2);
v_linePrefix_1343_ = lean_ctor_get(v___y_1338_, 0);
lean_inc(v___y_1337_);
v___x_1344_ = l_Nat_reprFast(v___y_1337_);
v___x_1345_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0));
v___x_1346_ = lean_string_append(v___x_1344_, v___x_1345_);
lean_inc_ref_n(v_linePrefix_1343_, 2);
v___x_1347_ = lean_string_append(v_linePrefix_1343_, v___x_1346_);
lean_dec_ref(v___x_1346_);
v___x_1348_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1347_, v___y_1339_);
lean_dec_ref(v___x_1347_);
v_snd_1349_ = lean_ctor_get(v___x_1348_, 1);
lean_inc(v_snd_1349_);
lean_dec_ref(v___x_1348_);
v___x_1350_ = lean_box(0);
v___f_1351_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1351_, 0, v_inst_1331_);
lean_closure_set(v___f_1351_, 1, v_inst_1332_);
lean_closure_set(v___f_1351_, 2, v___x_1350_);
v_sz_1352_ = lean_array_size(v_a_1335_);
v___x_1353_ = ((size_t)0ULL);
v___x_1354_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1355_ = lean_string_append(v_linePrefix_1343_, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*1, v_inEmph_1340_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*1 + 1, v_inBold_1341_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*1 + 2, v_inLink_1342_);
v___x_13750__overap_1357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1333_, v_a_1335_, v___f_1351_, v_sz_1352_, v___x_1353_, v___x_1350_);
v___x_1358_ = lean_apply_2(v___x_13750__overap_1357_, v___x_1356_, v_snd_1349_);
v_snd_1359_ = lean_ctor_get(v___x_1358_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; 
v_unused_1369_ = lean_ctor_get(v___x_1358_, 0);
lean_dec(v_unused_1369_);
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1368_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_snd_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1368_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1363_ = lean_nat_add(v___y_1337_, v___x_1334_);
lean_dec(v___y_1337_);
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1364_);
v___x_1366_ = v___x_1361_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_snd_1359_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1370_, lean_object* v_inst_1371_, lean_object* v___x_1372_, lean_object* v___x_1373_, lean_object* v_a_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1370_, v_inst_1371_, v___x_1372_, v___x_1373_, v_a_1374_, v_x_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___x_1373_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1383_, lean_object* v_inst_1384_, lean_object* v___x_1385_, lean_object* v_a_1386_, lean_object* v_x_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v_inEmph_1391_; uint8_t v_inBold_1392_; uint8_t v_inLink_1393_; lean_object* v_linePrefix_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_snd_1398_; lean_object* v_term_1399_; lean_object* v_desc_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_snd_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_snd_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v_snd_1412_; lean_object* v___x_1413_; lean_object* v_snd_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_snd_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1425_; 
v_inEmph_1391_ = lean_ctor_get_uint8(v___y_1389_, sizeof(void*)*1);
v_inBold_1392_ = lean_ctor_get_uint8(v___y_1389_, sizeof(void*)*1 + 1);
v_inLink_1393_ = lean_ctor_get_uint8(v___y_1389_, sizeof(void*)*1 + 2);
v_linePrefix_1394_ = lean_ctor_get(v___y_1389_, 0);
v___x_1395_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
lean_inc_ref_n(v_linePrefix_1394_, 2);
v___x_1396_ = lean_string_append(v_linePrefix_1394_, v___x_1395_);
v___x_1397_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1396_, v___y_1390_);
lean_dec_ref(v___x_1396_);
v_snd_1398_ = lean_ctor_get(v___x_1397_, 1);
lean_inc(v_snd_1398_);
lean_dec_ref(v___x_1397_);
v_term_1399_ = lean_ctor_get(v_a_1386_, 0);
v_desc_1400_ = lean_ctor_get(v_a_1386_, 1);
lean_inc_ref(v_term_1399_);
v___x_1401_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_term_1399_);
v___x_1402_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1403_ = lean_string_append(v_linePrefix_1394_, v___x_1402_);
lean_inc_ref(v___x_1403_);
v___x_1404_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
lean_ctor_set_uint8(v___x_1404_, sizeof(void*)*1, v_inEmph_1391_);
lean_ctor_set_uint8(v___x_1404_, sizeof(void*)*1 + 1, v_inBold_1392_);
lean_ctor_set_uint8(v___x_1404_, sizeof(void*)*1 + 2, v_inLink_1393_);
lean_inc_ref_n(v_inst_1383_, 2);
v___x_1405_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1383_, v___x_1401_, v___x_1404_, v_snd_1398_);
v_snd_1406_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_snd_1406_);
lean_dec_ref(v___x_1405_);
v___x_1407_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1));
v___x_1408_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1383_, v___x_1407_, v___x_1404_, v_snd_1406_);
v_snd_1409_ = lean_ctor_get(v___x_1408_, 1);
lean_inc(v_snd_1409_);
lean_dec_ref(v___x_1408_);
v___x_1410_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1411_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1410_, v_snd_1409_);
v_snd_1412_ = lean_ctor_get(v___x_1411_, 1);
lean_inc(v_snd_1412_);
lean_dec_ref(v___x_1411_);
v___x_1413_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1403_, v_snd_1412_);
lean_dec_ref(v___x_1403_);
v_snd_1414_ = lean_ctor_get(v___x_1413_, 1);
lean_inc(v_snd_1414_);
lean_dec_ref(v___x_1413_);
lean_inc_ref(v_desc_1400_);
v___x_1415_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1415_, 0, v_desc_1400_);
v___x_1416_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1383_, v_inst_1384_, v___x_1415_, v___x_1404_, v_snd_1414_);
lean_dec_ref(v___x_1404_);
v_snd_1417_ = lean_ctor_get(v___x_1416_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v___x_1416_, 0);
lean_dec(v_unused_1426_);
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_snd_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1385_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1421_);
v___x_1423_ = v___x_1419_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_snd_1417_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v___x_1429_, lean_object* v_a_1430_, lean_object* v_x_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1427_, v_inst_1428_, v___x_1429_, v_a_1430_, v_x_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec_ref(v_a_1430_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed(lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_x_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1437_, v_inst_1438_, v_x_1439_, v_a_1440_, v_a_1441_);
lean_dec_ref(v_a_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_x_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
switch(lean_obj_tag(v_x_1445_))
{
case 0:
{
lean_object* v_contents_1449_; lean_object* v___x_1450_; lean_object* v___f_1451_; size_t v_sz_1452_; size_t v___x_1453_; lean_object* v___x_12962__overap_1454_; lean_object* v___x_1455_; lean_object* v_snd_1456_; lean_object* v___x_1457_; 
lean_dec_ref(v_inst_1444_);
v_contents_1449_ = lean_ctor_get(v_x_1445_, 0);
lean_inc_ref(v_contents_1449_);
lean_dec_ref(v_x_1445_);
v___x_1450_ = lean_box(0);
v___f_1451_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1451_, 0, v_inst_1443_);
lean_closure_set(v___f_1451_, 1, v___x_1450_);
v_sz_1452_ = lean_array_size(v_contents_1449_);
v___x_1453_ = ((size_t)0ULL);
v___x_12962__overap_1454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1448_, v_contents_1449_, v___f_1451_, v_sz_1452_, v___x_1453_, v___x_1450_);
lean_inc_ref(v_a_1446_);
v___x_1455_ = lean_apply_2(v___x_12962__overap_1454_, v_a_1446_, v_a_1447_);
v_snd_1456_ = lean_ctor_get(v___x_1455_, 1);
lean_inc(v_snd_1456_);
lean_dec_ref(v___x_1455_);
v___x_1457_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1456_);
return v___x_1457_;
}
case 1:
{
lean_object* v_content_1458_; lean_object* v___y_1460_; lean_object* v___y_1461_; uint8_t v___y_1469_; lean_object* v_currentBlock_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
lean_dec_ref(v_inst_1444_);
lean_dec_ref(v_inst_1443_);
v_content_1458_ = lean_ctor_get(v_x_1445_, 0);
lean_inc_ref(v_content_1458_);
lean_dec_ref(v_x_1445_);
v_currentBlock_1473_ = lean_ctor_get(v_a_1447_, 1);
v___x_1474_ = lean_string_utf8_byte_size(v_currentBlock_1473_);
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = lean_nat_dec_eq(v___x_1474_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1477_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1478_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2);
v___x_1479_ = lean_nat_dec_le(v___x_1478_, v___x_1474_);
if (v___x_1479_ == 0)
{
v___y_1469_ = v___x_1476_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = lean_nat_sub(v___x_1474_, v___x_1478_);
v___x_1481_ = lean_string_memcmp(v_currentBlock_1473_, v___x_1477_, v___x_1480_, v___x_1475_, v___x_1478_);
lean_dec(v___x_1480_);
v___y_1469_ = v___x_1481_;
goto v___jp_1468_;
}
}
else
{
v___y_1469_ = v___x_1476_;
goto v___jp_1468_;
}
v___jp_1459_:
{
lean_object* v_linePrefix_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v_snd_1466_; lean_object* v___x_1467_; 
v_linePrefix_1462_ = lean_ctor_get(v___y_1460_, 0);
v___x_1463_ = lean_string_length(v_linePrefix_1462_);
v___x_1464_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v___x_1463_, v_content_1458_);
lean_dec_ref(v_content_1458_);
v___x_1465_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1464_, v___y_1461_);
lean_dec_ref(v___x_1464_);
v_snd_1466_ = lean_ctor_get(v___x_1465_, 1);
lean_inc(v_snd_1466_);
lean_dec_ref(v___x_1465_);
v___x_1467_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1466_);
return v___x_1467_;
}
v___jp_1468_:
{
if (v___y_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v_snd_1472_; 
v___x_1470_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1471_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1470_, v_a_1447_);
v_snd_1472_ = lean_ctor_get(v___x_1471_, 1);
lean_inc(v_snd_1472_);
lean_dec_ref(v___x_1471_);
v___y_1460_ = v_a_1446_;
v___y_1461_ = v_snd_1472_;
goto v___jp_1459_;
}
else
{
v___y_1460_ = v_a_1446_;
v___y_1461_ = v_a_1447_;
goto v___jp_1459_;
}
}
}
case 2:
{
lean_object* v_items_1482_; lean_object* v___x_1483_; lean_object* v___f_1484_; lean_object* v___f_1485_; size_t v_sz_1486_; size_t v___x_1487_; lean_object* v___x_13190__overap_1488_; lean_object* v___x_1489_; lean_object* v_snd_1490_; lean_object* v___x_1491_; 
v_items_1482_ = lean_ctor_get(v_x_1445_, 0);
lean_inc_ref(v_items_1482_);
lean_dec_ref(v_x_1445_);
v___x_1483_ = lean_box(0);
v___f_1484_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1484_, 0, v_inst_1443_);
lean_closure_set(v___f_1484_, 1, v_inst_1444_);
lean_closure_set(v___f_1484_, 2, v___x_1483_);
v___f_1485_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1485_, 0, v___x_1448_);
lean_closure_set(v___f_1485_, 1, v___f_1484_);
lean_closure_set(v___f_1485_, 2, v___x_1483_);
v_sz_1486_ = lean_array_size(v_items_1482_);
v___x_1487_ = ((size_t)0ULL);
v___x_13190__overap_1488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1448_, v_items_1482_, v___f_1485_, v_sz_1486_, v___x_1487_, v___x_1483_);
lean_inc_ref(v_a_1446_);
v___x_1489_ = lean_apply_2(v___x_13190__overap_1488_, v_a_1446_, v_a_1447_);
v_snd_1490_ = lean_ctor_get(v___x_1489_, 1);
lean_inc(v_snd_1490_);
lean_dec_ref(v___x_1489_);
v___x_1491_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1490_);
return v___x_1491_;
}
case 3:
{
lean_object* v_start_1492_; lean_object* v_items_1493_; lean_object* v___x_1494_; lean_object* v___f_1495_; lean_object* v___y_1497_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v_start_1492_ = lean_ctor_get(v_x_1445_, 0);
lean_inc(v_start_1492_);
v_items_1493_ = lean_ctor_get(v_x_1445_, 1);
lean_inc_ref(v_items_1493_);
lean_dec_ref(v_x_1445_);
v___x_1494_ = lean_unsigned_to_nat(1u);
v___f_1495_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 9, 4);
lean_closure_set(v___f_1495_, 0, v_inst_1443_);
lean_closure_set(v___f_1495_, 1, v_inst_1444_);
lean_closure_set(v___f_1495_, 2, v___x_1448_);
lean_closure_set(v___f_1495_, 3, v___x_1494_);
v___x_1504_ = l_Int_toNat(v_start_1492_);
lean_dec(v_start_1492_);
v___x_1505_ = lean_nat_dec_le(v___x_1494_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_dec(v___x_1504_);
v___y_1497_ = v___x_1494_;
goto v___jp_1496_;
}
else
{
v___y_1497_ = v___x_1504_;
goto v___jp_1496_;
}
v___jp_1496_:
{
size_t v_sz_1498_; size_t v___x_1499_; lean_object* v___x_13284__overap_1500_; lean_object* v___x_1501_; lean_object* v_snd_1502_; lean_object* v___x_1503_; 
v_sz_1498_ = lean_array_size(v_items_1493_);
v___x_1499_ = ((size_t)0ULL);
v___x_13284__overap_1500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1448_, v_items_1493_, v___f_1495_, v_sz_1498_, v___x_1499_, v___y_1497_);
lean_inc_ref(v_a_1446_);
v___x_1501_ = lean_apply_2(v___x_13284__overap_1500_, v_a_1446_, v_a_1447_);
v_snd_1502_ = lean_ctor_get(v___x_1501_, 1);
lean_inc(v_snd_1502_);
lean_dec_ref(v___x_1501_);
v___x_1503_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1502_);
return v___x_1503_;
}
}
case 4:
{
lean_object* v_items_1506_; lean_object* v___x_1507_; lean_object* v___f_1508_; size_t v_sz_1509_; size_t v___x_1510_; lean_object* v___x_13387__overap_1511_; lean_object* v___x_1512_; lean_object* v_snd_1513_; lean_object* v___x_1514_; 
v_items_1506_ = lean_ctor_get(v_x_1445_, 0);
lean_inc_ref(v_items_1506_);
lean_dec_ref(v_x_1445_);
v___x_1507_ = lean_box(0);
v___f_1508_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 8, 3);
lean_closure_set(v___f_1508_, 0, v_inst_1443_);
lean_closure_set(v___f_1508_, 1, v_inst_1444_);
lean_closure_set(v___f_1508_, 2, v___x_1507_);
v_sz_1509_ = lean_array_size(v_items_1506_);
v___x_1510_ = ((size_t)0ULL);
v___x_13387__overap_1511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1448_, v_items_1506_, v___f_1508_, v_sz_1509_, v___x_1510_, v___x_1507_);
lean_inc_ref(v_a_1446_);
v___x_1512_ = lean_apply_2(v___x_13387__overap_1511_, v_a_1446_, v_a_1447_);
v_snd_1513_ = lean_ctor_get(v___x_1512_, 1);
lean_inc(v_snd_1513_);
lean_dec_ref(v___x_1512_);
v___x_1514_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1513_);
return v___x_1514_;
}
case 5:
{
lean_object* v_items_1515_; uint8_t v_inEmph_1516_; uint8_t v_inBold_1517_; uint8_t v_inLink_1518_; lean_object* v_linePrefix_1519_; lean_object* v___x_1520_; lean_object* v___f_1521_; size_t v_sz_1522_; size_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_13493__overap_1527_; lean_object* v___x_1528_; lean_object* v_snd_1529_; lean_object* v___x_1530_; 
v_items_1515_ = lean_ctor_get(v_x_1445_, 0);
lean_inc_ref(v_items_1515_);
lean_dec_ref(v_x_1445_);
v_inEmph_1516_ = lean_ctor_get_uint8(v_a_1446_, sizeof(void*)*1);
v_inBold_1517_ = lean_ctor_get_uint8(v_a_1446_, sizeof(void*)*1 + 1);
v_inLink_1518_ = lean_ctor_get_uint8(v_a_1446_, sizeof(void*)*1 + 2);
v_linePrefix_1519_ = lean_ctor_get(v_a_1446_, 0);
v___x_1520_ = lean_box(0);
v___f_1521_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1521_, 0, v_inst_1443_);
lean_closure_set(v___f_1521_, 1, v_inst_1444_);
lean_closure_set(v___f_1521_, 2, v___x_1520_);
v_sz_1522_ = lean_array_size(v_items_1515_);
v___x_1523_ = ((size_t)0ULL);
v___x_1524_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
lean_inc_ref(v_linePrefix_1519_);
v___x_1525_ = lean_string_append(v_linePrefix_1519_, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*1, v_inEmph_1516_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*1 + 1, v_inBold_1517_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*1 + 2, v_inLink_1518_);
v___x_13493__overap_1527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1448_, v_items_1515_, v___f_1521_, v_sz_1522_, v___x_1523_, v___x_1520_);
v___x_1528_ = lean_apply_2(v___x_13493__overap_1527_, v___x_1526_, v_a_1447_);
v_snd_1529_ = lean_ctor_get(v___x_1528_, 1);
lean_inc(v_snd_1529_);
lean_dec_ref(v___x_1528_);
v___x_1530_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1529_);
return v___x_1530_;
}
case 6:
{
lean_object* v_content_1531_; lean_object* v___x_1532_; lean_object* v___f_1533_; size_t v_sz_1534_; size_t v___x_1535_; lean_object* v___x_13529__overap_1536_; lean_object* v___x_1537_; lean_object* v_snd_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_content_1531_ = lean_ctor_get(v_x_1445_, 0);
lean_inc_ref(v_content_1531_);
lean_dec_ref(v_x_1445_);
v___x_1532_ = lean_box(0);
v___f_1533_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1533_, 0, v_inst_1443_);
lean_closure_set(v___f_1533_, 1, v_inst_1444_);
lean_closure_set(v___f_1533_, 2, v___x_1532_);
v_sz_1534_ = lean_array_size(v_content_1531_);
v___x_1535_ = ((size_t)0ULL);
v___x_13529__overap_1536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1448_, v_content_1531_, v___f_1533_, v_sz_1534_, v___x_1535_, v___x_1532_);
lean_inc_ref(v_a_1446_);
v___x_1537_ = lean_apply_2(v___x_13529__overap_1536_, v_a_1446_, v_a_1447_);
v_snd_1538_ = lean_ctor_get(v___x_1537_, 1);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; 
v_unused_1546_ = lean_ctor_get(v___x_1537_, 0);
lean_dec(v_unused_1546_);
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_snd_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1532_);
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_snd_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
default: 
{
lean_object* v_container_1547_; lean_object* v_content_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_container_1547_ = lean_ctor_get(v_x_1445_, 0);
lean_inc(v_container_1547_);
v_content_1548_ = lean_ctor_get(v_x_1445_, 1);
lean_inc_ref(v_content_1548_);
lean_dec_ref(v_x_1445_);
lean_inc_ref(v_inst_1443_);
v___x_1549_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed), 5, 2);
lean_closure_set(v___x_1549_, 0, lean_box(0));
lean_closure_set(v___x_1549_, 1, v_inst_1443_);
lean_inc_ref(v_inst_1444_);
v___x_1550_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 5, 2);
lean_closure_set(v___x_1550_, 0, v_inst_1443_);
lean_closure_set(v___x_1550_, 1, v_inst_1444_);
lean_inc_ref(v_a_1446_);
v___x_1551_ = lean_apply_6(v_inst_1444_, v___x_1549_, v___x_1550_, v_container_1547_, v_content_1548_, v_a_1446_, v_a_1447_);
return v___x_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v___x_1554_, lean_object* v_a_1555_, lean_object* v_x_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v_snd_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1569_; 
v___x_1560_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1552_, v_inst_1553_, v_a_1555_, v___y_1558_, v___y_1559_);
v_snd_1561_ = lean_ctor_get(v___x_1560_, 1);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v___x_1560_, 0);
lean_dec(v_unused_1570_);
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1569_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_snd_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1569_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1554_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1565_);
v___x_1567_ = v___x_1563_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_snd_1561_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1571_, lean_object* v_b_1572_, lean_object* v_inst_1573_, lean_object* v_inst_1574_, lean_object* v_x_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1573_, v_inst_1574_, v_x_1575_, v_a_1576_, v_a_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object* v_i_1579_, lean_object* v_b_1580_, lean_object* v_inst_1581_, lean_object* v_inst_1582_, lean_object* v_x_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(v_i_1579_, v_b_1580_, v_inst_1581_, v_inst_1582_, v_x_1583_, v_a_1584_, v_a_1585_);
lean_dec_ref(v_a_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_block_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1587_, v_inst_1588_, v_block_1589_, v_a_1590_, v_a_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_block_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1593_, v_inst_1594_, v_block_1595_, v_a_1596_, v_a_1597_);
lean_dec_ref(v_a_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1599_, lean_object* v_b_1600_, lean_object* v_inst_1601_, lean_object* v_inst_1602_, lean_object* v_block_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1601_, v_inst_1602_, v_block_1603_, v_a_1604_, v_a_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1607_, lean_object* v_b_1608_, lean_object* v_inst_1609_, lean_object* v_inst_1610_, lean_object* v_block_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1607_, v_b_1608_, v_inst_1609_, v_inst_1610_, v_block_1611_, v_a_1612_, v_a_1613_);
lean_dec_ref(v_a_1612_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_block_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1615_, v_inst_1616_, v_block_1617_, v___y_1618_, v___y_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_block_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_1621_, v_inst_1622_, v_block_1623_, v___y_1624_, v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1627_, lean_object* v_inst_1628_){
_start:
{
lean_object* v___f_1629_; 
v___f_1629_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1629_, 0, v_inst_1627_);
lean_closure_set(v___f_1629_, 1, v_inst_1628_);
return v___f_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1630_, lean_object* v_b_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_){
_start:
{
lean_object* v___f_1634_; 
v___f_1634_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1634_, 0, v_inst_1632_);
lean_closure_set(v___f_1634_, 1, v_inst_1633_);
return v___f_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0(uint32_t v___x_1635_, lean_object* v_s_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_string_push(v_s_1636_, v___x_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0___boxed(lean_object* v___x_1638_, lean_object* v_s_1639_){
_start:
{
uint32_t v___x_4128__boxed_1640_; lean_object* v_res_1641_; 
v___x_4128__boxed_1640_ = lean_unbox_uint32(v___x_1638_);
lean_dec(v___x_1638_);
v_res_1641_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0(v___x_4128__boxed_1640_, v_s_1639_);
return v_res_1641_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = 35;
v___x_1643_ = lean_box_uint32(v___x_1642_);
return v___x_1643_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___f_1645_; 
v___x_1644_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1645_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1645_, 0, v___x_1644_);
return v___f_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1646_, lean_object* v_inst_1647_, lean_object* v___x_1648_, lean_object* v___x_1649_, lean_object* v_a_1650_, lean_object* v_x_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3(v_inst_1646_, v_inst_1647_, v___x_1648_, v___x_1649_, v_a_1650_, v_x_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___x_1648_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_level_1658_, lean_object* v_part_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v_snd_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v_snd_1672_; lean_object* v_title_1673_; lean_object* v_content_1674_; lean_object* v_subParts_1675_; lean_object* v___x_1676_; lean_object* v___f_1677_; size_t v_sz_1678_; size_t v___x_1679_; lean_object* v___x_3967__overap_1680_; lean_object* v___x_1681_; lean_object* v_snd_1682_; lean_object* v___x_1683_; lean_object* v_snd_1684_; lean_object* v___f_1685_; size_t v_sz_1686_; lean_object* v___x_3985__overap_1687_; lean_object* v___x_1688_; lean_object* v_snd_1689_; lean_object* v___x_1690_; lean_object* v_snd_1691_; lean_object* v___f_1692_; size_t v_sz_1693_; lean_object* v___x_4003__overap_1694_; lean_object* v___x_1695_; lean_object* v_snd_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v___x_1662_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
v___x_1663_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___f_1664_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0);
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = lean_nat_add(v_level_1658_, v___x_1665_);
lean_inc(v___x_1666_);
v___x_1667_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1664_, v___x_1666_, v___x_1663_);
v___x_1668_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1667_, v_a_1661_);
lean_dec(v___x_1667_);
v_snd_1669_ = lean_ctor_get(v___x_1668_, 1);
lean_inc(v_snd_1669_);
lean_dec_ref(v___x_1668_);
v___x_1670_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_1671_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1670_, v_snd_1669_);
v_snd_1672_ = lean_ctor_get(v___x_1671_, 1);
lean_inc(v_snd_1672_);
lean_dec_ref(v___x_1671_);
v_title_1673_ = lean_ctor_get(v_part_1659_, 0);
lean_inc_ref(v_title_1673_);
v_content_1674_ = lean_ctor_get(v_part_1659_, 3);
lean_inc_ref(v_content_1674_);
v_subParts_1675_ = lean_ctor_get(v_part_1659_, 4);
lean_inc_ref(v_subParts_1675_);
lean_dec_ref(v_part_1659_);
v___x_1676_ = lean_box(0);
lean_inc_ref_n(v_inst_1656_, 2);
v___f_1677_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1677_, 0, v_inst_1656_);
lean_closure_set(v___f_1677_, 1, v___x_1676_);
v_sz_1678_ = lean_array_size(v_title_1673_);
v___x_1679_ = ((size_t)0ULL);
v___x_3967__overap_1680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1662_, v_title_1673_, v___f_1677_, v_sz_1678_, v___x_1679_, v___x_1676_);
lean_inc_ref_n(v_a_1660_, 3);
v___x_1681_ = lean_apply_2(v___x_3967__overap_1680_, v_a_1660_, v_snd_1672_);
v_snd_1682_ = lean_ctor_get(v___x_1681_, 1);
lean_inc(v_snd_1682_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1682_);
v_snd_1684_ = lean_ctor_get(v___x_1683_, 1);
lean_inc(v_snd_1684_);
lean_dec_ref(v___x_1683_);
lean_inc_ref(v_inst_1657_);
v___f_1685_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1685_, 0, v_inst_1656_);
lean_closure_set(v___f_1685_, 1, v_inst_1657_);
lean_closure_set(v___f_1685_, 2, v___x_1676_);
v_sz_1686_ = lean_array_size(v_content_1674_);
v___x_3985__overap_1687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1662_, v_content_1674_, v___f_1685_, v_sz_1686_, v___x_1679_, v___x_1676_);
v___x_1688_ = lean_apply_2(v___x_3985__overap_1687_, v_a_1660_, v_snd_1684_);
v_snd_1689_ = lean_ctor_get(v___x_1688_, 1);
lean_inc(v_snd_1689_);
lean_dec_ref(v___x_1688_);
v___x_1690_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1689_);
v_snd_1691_ = lean_ctor_get(v___x_1690_, 1);
lean_inc(v_snd_1691_);
lean_dec_ref(v___x_1690_);
v___f_1692_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3___boxed), 9, 4);
lean_closure_set(v___f_1692_, 0, v_inst_1656_);
lean_closure_set(v___f_1692_, 1, v_inst_1657_);
lean_closure_set(v___f_1692_, 2, v___x_1666_);
lean_closure_set(v___f_1692_, 3, v___x_1676_);
v_sz_1693_ = lean_array_size(v_subParts_1675_);
v___x_4003__overap_1694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1662_, v_subParts_1675_, v___f_1692_, v_sz_1693_, v___x_1679_, v___x_1676_);
v___x_1695_ = lean_apply_2(v___x_4003__overap_1694_, v_a_1660_, v_snd_1691_);
v_snd_1696_ = lean_ctor_get(v___x_1695_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; 
v_unused_1704_ = lean_ctor_get(v___x_1695_, 0);
lean_dec(v_unused_1704_);
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_snd_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1676_);
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_snd_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3(lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v___x_1707_, lean_object* v___x_1708_, lean_object* v_a_1709_, lean_object* v_x_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1714_; lean_object* v_snd_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1723_; 
v___x_1714_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1705_, v_inst_1706_, v___x_1707_, v_a_1709_, v___y_1712_, v___y_1713_);
v_snd_1715_ = lean_ctor_get(v___x_1714_, 1);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v___x_1714_, 0);
lean_dec(v_unused_1724_);
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_snd_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1708_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1719_);
v___x_1721_ = v___x_1717_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_snd_1715_);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_level_1727_, lean_object* v_part_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1725_, v_inst_1726_, v_level_1727_, v_part_1728_, v_a_1729_, v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_level_1727_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown(lean_object* v_i_1732_, lean_object* v_b_1733_, lean_object* v_p_1734_, lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_level_1737_, lean_object* v_part_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1735_, v_inst_1736_, v_level_1737_, v_part_1738_, v_a_1739_, v_a_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___boxed(lean_object* v_i_1742_, lean_object* v_b_1743_, lean_object* v_p_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_level_1747_, lean_object* v_part_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown(v_i_1742_, v_b_1743_, v_p_1744_, v_inst_1745_, v_inst_1746_, v_level_1747_, v_part_1748_, v_a_1749_, v_a_1750_);
lean_dec_ref(v_a_1749_);
lean_dec(v_level_1747_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1752_, lean_object* v_inst_1753_, lean_object* v_part_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1752_, v_inst_1753_, v___x_1757_, v_part_1754_, v_a_1755_, v_a_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1759_, lean_object* v_inst_1760_, lean_object* v_part_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1759_, v_inst_1760_, v_part_1761_, v_a_1762_, v_a_1763_);
lean_dec_ref(v_a_1762_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1765_, lean_object* v_b_1766_, lean_object* v_p_1767_, lean_object* v_inst_1768_, lean_object* v_inst_1769_, lean_object* v_part_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1768_, v_inst_1769_, v___x_1773_, v_part_1770_, v_a_1771_, v_a_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1775_, lean_object* v_b_1776_, lean_object* v_p_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_part_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1775_, v_b_1776_, v_p_1777_, v_inst_1778_, v_inst_1779_, v_part_1780_, v_a_1781_, v_a_1782_);
lean_dec_ref(v_a_1781_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_part_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1784_, v_inst_1785_, v___x_1789_, v_part_1786_, v___y_1787_, v___y_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_part_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_1791_, v_inst_1792_, v_part_1793_, v___y_1794_, v___y_1795_);
lean_dec_ref(v___y_1794_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1797_, lean_object* v_inst_1798_){
_start:
{
lean_object* v___f_1799_; 
v___f_1799_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1799_, 0, v_inst_1797_);
lean_closure_set(v___f_1799_, 1, v_inst_1798_);
return v___f_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1800_, lean_object* v_b_1801_, lean_object* v_p_1802_, lean_object* v_inst_1803_, lean_object* v_inst_1804_){
_start:
{
lean_object* v___f_1805_; 
v___f_1805_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1805_, 0, v_inst_1803_);
lean_closure_set(v___f_1805_, 1, v_inst_1804_);
return v___f_1805_;
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
