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
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__36 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__36_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_inEmph_208_; uint8_t v_inBold_209_; uint8_t v_inLink_210_; lean_object* v_linePrefix_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_221_; 
v_inEmph_208_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*1);
v_inBold_209_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*1 + 1);
v_inLink_210_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*1 + 2);
v_linePrefix_211_ = lean_ctor_get(v_a_206_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v_a_206_);
if (v_isSharedCheck_221_ == 0)
{
v___x_213_ = v_a_206_;
v_isShared_214_ = v_isSharedCheck_221_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_linePrefix_211_);
lean_dec(v_a_206_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_221_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_215_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_216_ = lean_string_append(v_linePrefix_211_, v___x_215_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_216_);
v___x_218_ = v___x_213_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_216_);
lean_ctor_set_uint8(v_reuseFailAlloc_220_, sizeof(void*)*1, v_inEmph_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_220_, sizeof(void*)*1 + 1, v_inBold_209_);
lean_ctor_set_uint8(v_reuseFailAlloc_220_, sizeof(void*)*1 + 2, v_inLink_210_);
v___x_218_ = v_reuseFailAlloc_220_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_219_; 
v___x_219_ = lean_apply_2(v_x_205_, v___x_218_, v_a_207_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_indent(lean_object* v_00_u03b1_222_, lean_object* v_x_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Doc_MarkdownM_indent___redArg(v_x_223_, v_a_224_, v_a_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object* v_a_227_, uint8_t v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
uint8_t v_a_15__boxed_237_; lean_object* v_res_238_; 
v_a_15__boxed_237_ = lean_unbox(v_a_233_);
v_res_238_ = l_Lean_Doc_instMarkdownInlineEmpty___lam__0(v_a_232_, v_a_15__boxed_237_, v_a_234_, v_a_235_, v_a_236_);
lean_dec_ref(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec_ref(v_a_232_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0(lean_object* v_a_241_, lean_object* v_a_242_, uint8_t v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed(lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
uint8_t v_a_19__boxed_253_; lean_object* v_res_254_; 
v_a_19__boxed_253_ = lean_unbox(v_a_249_);
v_res_254_ = l_Lean_Doc_instMarkdownBlockEmpty___lam__0(v_a_247_, v_a_248_, v_a_19__boxed_253_, v_a_250_, v_a_251_, v_a_252_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec_ref(v_a_248_);
lean_dec_ref(v_a_247_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object* v_i_256_){
_start:
{
lean_object* v___f_257_; 
v___f_257_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___closed__0));
return v___f_257_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(lean_object* v_s_258_, uint32_t v_c_259_, lean_object* v_a_260_, uint8_t v_b_261_){
_start:
{
lean_object* v_str_262_; lean_object* v_startInclusive_263_; lean_object* v_endExclusive_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_str_262_ = lean_ctor_get(v_s_258_, 0);
v_startInclusive_263_ = lean_ctor_get(v_s_258_, 1);
v_endExclusive_264_ = lean_ctor_get(v_s_258_, 2);
v___x_265_ = lean_nat_sub(v_endExclusive_264_, v_startInclusive_263_);
v___x_266_ = lean_nat_dec_eq(v_a_260_, v___x_265_);
lean_dec(v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_267_ = lean_nat_add(v_startInclusive_263_, v_a_260_);
lean_dec(v_a_260_);
v___x_268_ = lean_string_utf8_get_fast(v_str_262_, v___x_267_);
v___x_269_ = lean_uint32_dec_eq(v___x_268_, v_c_259_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_string_utf8_next_fast(v_str_262_, v___x_267_);
lean_dec(v___x_267_);
v___x_271_ = lean_nat_sub(v___x_270_, v_startInclusive_263_);
v_a_260_ = v___x_271_;
v_b_261_ = v___x_269_;
goto _start;
}
else
{
lean_dec(v___x_267_);
return v___x_269_;
}
}
else
{
lean_dec(v_a_260_);
return v_b_261_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg___boxed(lean_object* v_s_273_, lean_object* v_c_274_, lean_object* v_a_275_, lean_object* v_b_276_){
_start:
{
uint32_t v_c_boxed_277_; uint8_t v_b_boxed_278_; uint8_t v_res_279_; lean_object* v_r_280_; 
v_c_boxed_277_ = lean_unbox_uint32(v_c_274_);
lean_dec(v_c_274_);
v_b_boxed_278_ = lean_unbox(v_b_276_);
v_res_279_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(v_s_273_, v_c_boxed_277_, v_a_275_, v_b_boxed_278_);
lean_dec_ref(v_s_273_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0(uint32_t v_c_281_, lean_object* v_s_282_){
_start:
{
lean_object* v_searcher_283_; uint8_t v___x_284_; uint8_t v___x_285_; 
v_searcher_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = 0;
v___x_285_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(v_s_282_, v_c_281_, v_searcher_283_, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0___boxed(lean_object* v_c_286_, lean_object* v_s_287_){
_start:
{
uint32_t v_c_boxed_288_; uint8_t v_res_289_; lean_object* v_r_290_; 
v_c_boxed_288_ = lean_unbox_uint32(v_c_286_);
lean_dec(v_c_286_);
v_res_289_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0(v_c_boxed_288_, v_s_287_);
lean_dec_ref(v_s_287_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__0));
v___x_293_ = lean_string_utf8_byte_size(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_294_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__1);
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__0));
v___x_297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
lean_ctor_set(v___x_297_, 2, v___x_294_);
return v___x_297_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial(uint32_t v_c_298_){
_start:
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___closed__2);
v___x_300_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0(v_c_298_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial___boxed(lean_object* v_c_301_){
_start:
{
uint32_t v_c_boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v_c_boxed_302_ = lean_unbox_uint32(v_c_301_);
lean_dec(v_c_301_);
v_res_303_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial(v_c_boxed_302_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0(lean_object* v_s_305_, uint32_t v_c_306_, lean_object* v_inst_307_, lean_object* v_R_308_, lean_object* v_a_309_, uint8_t v_b_310_, lean_object* v_c_311_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___redArg(v_s_305_, v_c_306_, v_a_309_, v_b_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0___boxed(lean_object* v_s_313_, lean_object* v_c_314_, lean_object* v_inst_315_, lean_object* v_R_316_, lean_object* v_a_317_, lean_object* v_b_318_, lean_object* v_c_319_){
_start:
{
uint32_t v_c_boxed_320_; uint8_t v_b_boxed_321_; uint8_t v_res_322_; lean_object* v_r_323_; 
v_c_boxed_320_ = lean_unbox_uint32(v_c_314_);
lean_dec(v_c_314_);
v_b_boxed_321_ = lean_unbox(v_b_318_);
v_res_322_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial_spec__0_spec__0(v_s_313_, v_c_boxed_320_, v_inst_315_, v_R_316_, v_a_317_, v_b_boxed_321_, v_c_319_);
lean_dec_ref(v_s_313_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object* v_s_324_, lean_object* v_b_325_){
_start:
{
lean_object* v_fst_326_; lean_object* v_snd_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_348_; 
v_fst_326_ = lean_ctor_get(v_b_325_, 0);
v_snd_327_ = lean_ctor_get(v_b_325_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_b_325_);
if (v_isSharedCheck_348_ == 0)
{
v___x_329_ = v_b_325_;
v_isShared_330_ = v_isSharedCheck_348_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_snd_327_);
lean_inc(v_fst_326_);
lean_dec(v_b_325_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_348_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = lean_string_utf8_byte_size(v_s_324_);
v___x_332_ = lean_nat_dec_eq(v_snd_327_, v___x_331_);
if (v___x_332_ == 0)
{
uint32_t v_c_333_; lean_object* v_iter_334_; lean_object* v_s_x27_336_; uint8_t v___x_342_; 
v_c_333_ = lean_string_utf8_get_fast(v_s_324_, v_snd_327_);
v_iter_334_ = lean_string_utf8_next_fast(v_s_324_, v_snd_327_);
lean_dec(v_snd_327_);
v___x_342_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape_isSpecial(v_c_333_);
if (v___x_342_ == 0)
{
v_s_x27_336_ = v_fst_326_;
goto v___jp_335_;
}
else
{
uint32_t v___x_343_; lean_object* v_s_x27_344_; 
v___x_343_ = 92;
v_s_x27_344_ = lean_string_push(v_fst_326_, v___x_343_);
v_s_x27_336_ = v_s_x27_344_;
goto v___jp_335_;
}
v___jp_335_:
{
lean_object* v_s_x27_337_; lean_object* v___x_339_; 
v_s_x27_337_ = lean_string_push(v_s_x27_336_, v_c_333_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v_iter_334_);
lean_ctor_set(v___x_329_, 0, v_s_x27_337_);
v___x_339_ = v___x_329_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_s_x27_337_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_iter_334_);
v___x_339_ = v_reuseFailAlloc_341_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
v_b_325_ = v___x_339_;
goto _start;
}
}
}
else
{
lean_object* v___x_346_; 
if (v_isShared_330_ == 0)
{
v___x_346_ = v___x_329_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_fst_326_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_snd_327_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object* v_s_349_, lean_object* v_b_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_349_, v_b_350_);
lean_dec_ref(v_s_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object* v_s_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_fst_358_; 
v___x_356_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0));
v___x_357_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_355_, v___x_356_);
v_fst_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_fst_358_);
lean_dec_ref(v___x_357_);
return v_fst_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object* v_s_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_359_);
lean_dec_ref(v_s_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0(lean_object* v_str_361_, lean_object* v_b_362_){
_start:
{
lean_object* v_snd_363_; lean_object* v_fst_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_406_; 
v_snd_363_ = lean_ctor_get(v_b_362_, 1);
v_fst_364_ = lean_ctor_get(v_b_362_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_b_362_);
if (v_isSharedCheck_406_ == 0)
{
v___x_366_ = v_b_362_;
v_isShared_367_ = v_isSharedCheck_406_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_snd_363_);
lean_inc(v_fst_364_);
lean_dec(v_b_362_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_406_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_fst_368_; lean_object* v_snd_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_405_; 
v_fst_368_ = lean_ctor_get(v_snd_363_, 0);
v_snd_369_ = lean_ctor_get(v_snd_363_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_snd_363_);
if (v_isSharedCheck_405_ == 0)
{
v___x_371_ = v_snd_363_;
v_isShared_372_ = v_isSharedCheck_405_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_snd_369_);
lean_inc(v_fst_368_);
lean_dec(v_snd_363_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_405_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = lean_string_utf8_byte_size(v_str_361_);
v___x_374_ = lean_nat_dec_eq(v_snd_369_, v___x_373_);
if (v___x_374_ == 0)
{
uint32_t v_c_375_; lean_object* v_iter_376_; uint32_t v___x_377_; uint8_t v___x_378_; 
v_c_375_ = lean_string_utf8_get_fast(v_str_361_, v_snd_369_);
v_iter_376_ = lean_string_utf8_next_fast(v_str_361_, v_snd_369_);
lean_dec(v_snd_369_);
v___x_377_ = 96;
v___x_378_ = lean_uint32_dec_eq(v_c_375_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v_current_379_; lean_object* v___y_381_; uint8_t v___x_389_; 
v_current_379_ = lean_unsigned_to_nat(0u);
v___x_389_ = lean_nat_dec_le(v_fst_364_, v_fst_368_);
if (v___x_389_ == 0)
{
lean_dec(v_fst_368_);
v___y_381_ = v_fst_364_;
goto v___jp_380_;
}
else
{
lean_dec(v_fst_364_);
v___y_381_ = v_fst_368_;
goto v___jp_380_;
}
v___jp_380_:
{
lean_object* v___x_383_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v_iter_376_);
lean_ctor_set(v___x_371_, 0, v_current_379_);
v___x_383_ = v___x_371_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_current_379_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_iter_376_);
v___x_383_ = v_reuseFailAlloc_388_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_385_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v___x_383_);
lean_ctor_set(v___x_366_, 0, v___y_381_);
v___x_385_ = v___x_366_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___y_381_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v___x_383_);
v___x_385_ = v_reuseFailAlloc_387_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
v_b_362_ = v___x_385_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_390_; lean_object* v_current_391_; lean_object* v___x_393_; 
v___x_390_ = lean_unsigned_to_nat(1u);
v_current_391_ = lean_nat_add(v_fst_368_, v___x_390_);
lean_dec(v_fst_368_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v_iter_376_);
lean_ctor_set(v___x_371_, 0, v_current_391_);
v___x_393_ = v___x_371_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_current_391_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_iter_376_);
v___x_393_ = v_reuseFailAlloc_398_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_395_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v___x_393_);
v___x_395_ = v___x_366_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_fst_364_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_397_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
v_b_362_ = v___x_395_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_400_; 
if (v_isShared_372_ == 0)
{
v___x_400_ = v___x_371_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_fst_368_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_snd_369_);
v___x_400_ = v_reuseFailAlloc_404_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v___x_400_);
v___x_402_ = v___x_366_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_fst_364_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0___boxed(lean_object* v_str_407_, lean_object* v_b_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0(v_str_407_, v_b_408_);
lean_dec_ref(v_str_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__1(lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
lean_object* v_zero_412_; uint8_t v_isZero_413_; 
v_zero_412_ = lean_unsigned_to_nat(0u);
v_isZero_413_ = lean_nat_dec_eq(v_x_410_, v_zero_412_);
if (v_isZero_413_ == 1)
{
lean_dec(v_x_410_);
return v_x_411_;
}
else
{
uint32_t v___x_414_; lean_object* v_one_415_; lean_object* v_n_416_; lean_object* v___x_417_; 
v___x_414_ = 96;
v_one_415_ = lean_unsigned_to_nat(1u);
v_n_416_ = lean_nat_sub(v_x_410_, v_one_415_);
lean_dec(v_x_410_);
v___x_417_ = lean_string_push(v_x_411_, v___x_414_);
v_x_410_ = v_n_416_;
v_x_411_ = v___x_417_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_422_ = lean_string_utf8_byte_size(v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object* v_str_428_){
_start:
{
lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_435_; lean_object* v_current_439_; lean_object* v___y_441_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v_snd_450_; lean_object* v_fst_451_; lean_object* v_fst_452_; lean_object* v___x_453_; lean_object* v___y_455_; uint8_t v___x_464_; 
v_current_439_ = lean_unsigned_to_nat(0u);
v___x_448_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__4));
v___x_449_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__0(v_str_428_, v___x_448_);
v_snd_450_ = lean_ctor_get(v___x_449_, 1);
lean_inc(v_snd_450_);
v_fst_451_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_fst_451_);
lean_dec_ref(v___x_449_);
v_fst_452_ = lean_ctor_get(v_snd_450_, 0);
lean_inc(v_fst_452_);
lean_dec(v_snd_450_);
v___x_453_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_464_ = lean_nat_dec_le(v_fst_451_, v_fst_452_);
if (v___x_464_ == 0)
{
lean_dec(v_fst_452_);
v___y_455_ = v_fst_451_;
goto v___jp_454_;
}
else
{
lean_dec(v_fst_451_);
v___y_455_ = v_fst_452_;
goto v___jp_454_;
}
v___jp_429_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_inc_ref(v___y_430_);
v___x_432_ = lean_string_append(v___y_430_, v___y_431_);
lean_dec_ref(v___y_431_);
v___x_433_ = lean_string_append(v___x_432_, v___y_430_);
lean_dec_ref(v___y_430_);
return v___x_433_;
}
v___jp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_437_ = lean_string_append(v___x_436_, v_str_428_);
lean_dec_ref(v_str_428_);
v___x_438_ = lean_string_append(v___x_437_, v___x_436_);
v___y_430_ = v___y_435_;
v___y_431_ = v___x_438_;
goto v___jp_429_;
}
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_442_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_443_ = lean_string_utf8_byte_size(v_str_428_);
v___x_444_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2);
v___x_445_ = lean_nat_dec_le(v___x_444_, v___x_443_);
if (v___x_445_ == 0)
{
v___y_430_ = v___y_441_;
v___y_431_ = v_str_428_;
goto v___jp_429_;
}
else
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_nat_sub(v___x_443_, v___x_444_);
v___x_447_ = lean_string_memcmp(v_str_428_, v___x_442_, v___x_446_, v_current_439_, v___x_444_);
lean_dec(v___x_446_);
if (v___x_447_ == 0)
{
v___y_430_ = v___y_441_;
v___y_431_ = v_str_428_;
goto v___jp_429_;
}
else
{
v___y_435_ = v___y_441_;
goto v___jp_434_;
}
}
}
v___jp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_nat_add(v___y_455_, v___x_456_);
lean_dec(v___y_455_);
v___x_458_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__1(v___x_457_, v___x_453_);
v___x_459_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_460_ = lean_string_utf8_byte_size(v_str_428_);
v___x_461_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__2);
v___x_462_ = lean_nat_dec_le(v___x_461_, v___x_460_);
if (v___x_462_ == 0)
{
v___y_441_ = v___x_458_;
goto v___jp_440_;
}
else
{
uint8_t v___x_463_; 
v___x_463_ = lean_string_memcmp(v_str_428_, v___x_459_, v_current_439_, v_current_439_, v___x_461_);
if (v___x_463_ == 0)
{
v___y_441_ = v___x_458_;
goto v___jp_440_;
}
else
{
v___y_435_ = v___x_458_;
goto v___jp_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_465_, lean_object* v_pos_466_){
_start:
{
lean_object* v_str_467_; lean_object* v_startInclusive_468_; lean_object* v_endExclusive_469_; lean_object* v___x_470_; uint8_t v___y_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v_str_467_ = lean_ctor_get(v_s_465_, 0);
v_startInclusive_468_ = lean_ctor_get(v_s_465_, 1);
v_endExclusive_469_ = lean_ctor_get(v_s_465_, 2);
v___x_470_ = lean_nat_add(v_startInclusive_468_, v_pos_466_);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = lean_nat_sub(v_endExclusive_469_, v___x_470_);
v___x_481_ = lean_nat_dec_eq(v___x_479_, v___x_480_);
lean_dec(v___x_480_);
if (v___x_481_ == 0)
{
uint32_t v___x_482_; uint8_t v___y_484_; uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_482_ = lean_string_utf8_get_fast(v_str_467_, v___x_470_);
v___x_489_ = 32;
v___x_490_ = lean_uint32_dec_eq(v___x_482_, v___x_489_);
if (v___x_490_ == 0)
{
uint32_t v___x_491_; uint8_t v___x_492_; 
v___x_491_ = 9;
v___x_492_ = lean_uint32_dec_eq(v___x_482_, v___x_491_);
v___y_484_ = v___x_492_;
goto v___jp_483_;
}
else
{
v___y_484_ = v___x_490_;
goto v___jp_483_;
}
v___jp_483_:
{
if (v___y_484_ == 0)
{
uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 13;
v___x_486_ = lean_uint32_dec_eq(v___x_482_, v___x_485_);
if (v___x_486_ == 0)
{
uint32_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = 10;
v___x_488_ = lean_uint32_dec_eq(v___x_482_, v___x_487_);
v___y_478_ = v___x_488_;
goto v___jp_477_;
}
else
{
v___y_478_ = v___x_486_;
goto v___jp_477_;
}
}
else
{
goto v___jp_471_;
}
}
}
else
{
lean_dec(v___x_470_);
return v_pos_466_;
}
v___jp_471_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_472_ = lean_string_utf8_next_fast(v_str_467_, v___x_470_);
v___x_473_ = lean_nat_sub(v___x_472_, v___x_470_);
lean_dec(v___x_470_);
v___x_474_ = lean_nat_add(v_pos_466_, v___x_473_);
lean_dec(v___x_473_);
v___x_475_ = lean_nat_dec_lt(v_pos_466_, v___x_474_);
if (v___x_475_ == 0)
{
lean_dec(v___x_474_);
return v_pos_466_;
}
else
{
lean_dec(v_pos_466_);
v_pos_466_ = v___x_474_;
goto _start;
}
}
v___jp_477_:
{
if (v___y_478_ == 0)
{
lean_dec(v___x_470_);
return v_pos_466_;
}
else
{
goto v___jp_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object* v_s_493_, lean_object* v_pos_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_493_, v_pos_494_);
lean_dec_ref(v_s_493_);
return v_res_495_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Doc_Inline_empty(lean_box(0));
return v___x_496_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_498_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object* v_a_500_){
_start:
{
if (lean_obj_tag(v_a_500_) == 0)
{
lean_object* v___x_501_; 
v___x_501_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
return v___x_501_;
}
else
{
lean_object* v_head_502_; 
v_head_502_ = lean_ctor_get(v_a_500_, 0);
lean_inc(v_head_502_);
switch(lean_obj_tag(v_head_502_))
{
case 0:
{
lean_object* v_tail_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_550_; 
v_tail_503_ = lean_ctor_get(v_a_500_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_a_500_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v_a_500_, 0);
lean_dec(v_unused_551_);
v___x_505_ = v_a_500_;
v_isShared_506_ = v_isSharedCheck_550_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_tail_503_);
lean_dec(v_a_500_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_550_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v_string_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_549_; 
v_string_507_ = lean_ctor_get(v_head_502_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v_head_502_);
if (v_isSharedCheck_549_ == 0)
{
v___x_509_ = v_head_502_;
v_isShared_510_ = v_isSharedCheck_549_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_string_507_);
lean_dec(v_head_502_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_549_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_string_utf8_byte_size(v_string_507_);
lean_inc_ref(v_string_507_);
v___x_513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_513_, 0, v_string_507_);
lean_ctor_set(v___x_513_, 1, v___x_511_);
lean_ctor_set(v___x_513_, 2, v___x_512_);
v___x_514_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_513_, v___x_511_);
v___x_515_ = lean_nat_sub(v___x_512_, v___x_514_);
v___x_516_ = lean_nat_dec_eq(v___x_515_, v___x_511_);
lean_dec(v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v_s1_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v_s2_520_; lean_object* v___x_522_; 
v_s1_517_ = lean_string_utf8_extract(v_string_507_, v___x_511_, v___x_514_);
lean_dec(v___x_514_);
v___x_518_ = lean_string_length(v_s1_517_);
v___x_519_ = l_String_Slice_Pos_nextn(v___x_513_, v___x_511_, v___x_518_);
lean_dec_ref(v___x_513_);
v_s2_520_ = lean_string_utf8_extract(v_string_507_, v___x_519_, v___x_512_);
lean_dec(v___x_519_);
lean_dec_ref(v_string_507_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v_s2_520_);
v___x_522_ = v___x_509_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_s2_520_);
v___x_522_ = v_reuseFailAlloc_537_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_array_mk(v_tail_503_);
v___x_524_ = lean_array_get_size(v___x_523_);
v___x_525_ = lean_nat_dec_eq(v___x_524_, v___x_511_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_mk_empty_array_with_capacity(v___x_526_);
v___x_528_ = lean_array_push(v___x_527_, v___x_522_);
v___x_529_ = l_Array_append___redArg(v___x_528_, v___x_523_);
lean_dec_ref(v___x_523_);
v___x_530_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 0);
lean_ctor_set(v___x_505_, 1, v___x_530_);
lean_ctor_set(v___x_505_, 0, v_s1_517_);
v___x_532_ = v___x_505_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_s1_517_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
else
{
lean_object* v___x_535_; 
lean_dec_ref(v___x_523_);
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 0);
lean_ctor_set(v___x_505_, 1, v___x_522_);
lean_ctor_set(v___x_505_, 0, v_s1_517_);
v___x_535_ = v___x_505_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_s1_517_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_522_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
else
{
lean_object* v___x_538_; lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_548_; 
lean_dec(v___x_514_);
lean_dec_ref(v___x_513_);
lean_del_object(v___x_509_);
lean_del_object(v___x_505_);
v___x_538_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_503_);
v_fst_539_ = lean_ctor_get(v___x_538_, 0);
v_snd_540_ = lean_ctor_get(v___x_538_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_548_ == 0)
{
v___x_542_ = v___x_538_;
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_snd_540_);
lean_inc(v_fst_539_);
lean_dec(v___x_538_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_string_append(v_string_507_, v_fst_539_);
lean_dec(v_fst_539_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_snd_540_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_552_; lean_object* v_content_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_tail_552_ = lean_ctor_get(v_a_500_, 1);
lean_inc(v_tail_552_);
lean_dec_ref(v_a_500_);
v_content_553_ = lean_ctor_get(v_head_502_, 0);
lean_inc_ref(v_content_553_);
lean_dec_ref(v_head_502_);
v___x_554_ = lean_array_to_list(v_content_553_);
v___x_555_ = l_List_appendTR___redArg(v___x_554_, v_tail_552_);
v_a_500_ = v___x_555_;
goto _start;
}
default: 
{
lean_object* v_tail_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_595_; 
v_tail_557_ = lean_ctor_get(v_a_500_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_a_500_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v_a_500_, 0);
lean_dec(v_unused_596_);
v___x_559_ = v_a_500_;
v_isShared_560_ = v_isSharedCheck_595_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_tail_557_);
lean_dec(v_a_500_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_595_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_562_ = lean_array_mk(v_tail_557_);
if (lean_obj_tag(v_head_502_) == 9)
{
lean_object* v_content_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_content_563_ = lean_ctor_get(v_head_502_, 0);
v___x_564_ = lean_array_get_size(v_content_563_);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_nat_dec_eq(v___x_564_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_567_ = lean_array_get_size(v___x_562_);
v___x_568_ = lean_nat_dec_eq(v___x_567_, v___x_565_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
lean_inc_ref(v_content_563_);
lean_dec_ref(v_head_502_);
v___x_569_ = l_Array_append___redArg(v_content_563_, v___x_562_);
lean_dec_ref(v___x_562_);
v___x_570_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 0);
lean_ctor_set(v___x_559_, 1, v___x_570_);
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_572_ = v___x_559_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
else
{
lean_object* v___x_575_; 
lean_dec_ref(v___x_562_);
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 0);
lean_ctor_set(v___x_559_, 1, v_head_502_);
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_575_ = v___x_559_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_head_502_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_579_; 
lean_dec_ref(v_head_502_);
v___x_577_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_562_);
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 0);
lean_ctor_set(v___x_559_, 1, v___x_577_);
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_579_ = v___x_559_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_581_ = lean_array_get_size(v___x_562_);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_nat_dec_eq(v___x_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = lean_mk_empty_array_with_capacity(v___x_584_);
v___x_586_ = lean_array_push(v___x_585_, v_head_502_);
v___x_587_ = l_Array_append___redArg(v___x_586_, v___x_562_);
lean_dec_ref(v___x_562_);
v___x_588_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 0);
lean_ctor_set(v___x_559_, 1, v___x_588_);
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_590_ = v___x_559_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v___x_593_; 
lean_dec_ref(v___x_562_);
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 0);
lean_ctor_set(v___x_559_, 1, v_head_502_);
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_593_ = v___x_559_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_head_502_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_600_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_box(0);
v___x_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_602_, 0, v_inline_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_604_, lean_object* v_inline_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_607_, lean_object* v_pos_608_){
_start:
{
lean_object* v_str_609_; lean_object* v_startInclusive_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_str_609_ = lean_ctor_get(v_s_607_, 0);
v_startInclusive_610_ = lean_ctor_get(v_s_607_, 1);
v___x_611_ = lean_nat_add(v_startInclusive_610_, v_pos_608_);
v___x_612_ = lean_nat_sub(v___x_611_, v_startInclusive_610_);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_nat_dec_eq(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___y_623_; lean_object* v___x_624_; uint32_t v___x_625_; uint8_t v___y_627_; uint32_t v___x_632_; uint8_t v___x_633_; 
lean_inc(v_startInclusive_610_);
lean_inc_ref(v_str_609_);
v___x_615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_615_, 0, v_str_609_);
lean_ctor_set(v___x_615_, 1, v_startInclusive_610_);
lean_ctor_set(v___x_615_, 2, v___x_611_);
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_sub(v___x_612_, v___x_616_);
lean_dec(v___x_612_);
v___x_618_ = l_String_Slice_posLE(v___x_615_, v___x_617_);
lean_dec_ref(v___x_615_);
v___x_624_ = lean_nat_add(v_startInclusive_610_, v___x_618_);
v___x_625_ = lean_string_utf8_get_fast(v_str_609_, v___x_624_);
lean_dec(v___x_624_);
v___x_632_ = 32;
v___x_633_ = lean_uint32_dec_eq(v___x_625_, v___x_632_);
if (v___x_633_ == 0)
{
uint32_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = 9;
v___x_635_ = lean_uint32_dec_eq(v___x_625_, v___x_634_);
v___y_627_ = v___x_635_;
goto v___jp_626_;
}
else
{
v___y_627_ = v___x_633_;
goto v___jp_626_;
}
v___jp_619_:
{
uint8_t v___x_620_; 
v___x_620_ = lean_nat_dec_lt(v___x_618_, v_pos_608_);
if (v___x_620_ == 0)
{
lean_dec(v___x_618_);
return v_pos_608_;
}
else
{
lean_dec(v_pos_608_);
v_pos_608_ = v___x_618_;
goto _start;
}
}
v___jp_622_:
{
if (v___y_623_ == 0)
{
lean_dec(v___x_618_);
return v_pos_608_;
}
else
{
goto v___jp_619_;
}
}
v___jp_626_:
{
if (v___y_627_ == 0)
{
uint32_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 13;
v___x_629_ = lean_uint32_dec_eq(v___x_625_, v___x_628_);
if (v___x_629_ == 0)
{
uint32_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = 10;
v___x_631_ = lean_uint32_dec_eq(v___x_625_, v___x_630_);
v___y_623_ = v___x_631_;
goto v___jp_622_;
}
else
{
v___y_623_ = v___x_629_;
goto v___jp_622_;
}
}
else
{
goto v___jp_619_;
}
}
}
else
{
lean_dec(v___x_612_);
lean_dec(v___x_611_);
return v_pos_608_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_636_, lean_object* v_pos_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_636_, v_pos_637_);
lean_dec_ref(v_s_636_);
return v_res_638_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_640_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_a_642_){
_start:
{
lean_object* v___y_644_; 
if (lean_obj_tag(v_a_642_) == 0)
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_647_;
}
else
{
lean_object* v_head_648_; 
v_head_648_ = lean_ctor_get(v_a_642_, 0);
lean_inc(v_head_648_);
switch(lean_obj_tag(v_head_648_))
{
case 0:
{
lean_object* v_tail_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_695_; 
v_tail_649_ = lean_ctor_get(v_a_642_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_a_642_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_a_642_, 0);
lean_dec(v_unused_696_);
v___x_651_ = v_a_642_;
v_isShared_652_ = v_isSharedCheck_695_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_tail_649_);
lean_dec(v_a_642_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_695_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v_string_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_694_; 
v_string_653_ = lean_ctor_get(v_head_648_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v_head_648_);
if (v_isSharedCheck_694_ == 0)
{
v___x_655_ = v_head_648_;
v_isShared_656_ = v_isSharedCheck_694_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_string_653_);
lean_dec(v_head_648_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_694_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_string_utf8_byte_size(v_string_653_);
lean_inc_ref(v_string_653_);
v___x_659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_659_, 0, v_string_653_);
lean_ctor_set(v___x_659_, 1, v___x_657_);
lean_ctor_set(v___x_659_, 2, v___x_658_);
v___x_660_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_659_, v___x_657_);
v___x_661_ = lean_nat_sub(v___x_658_, v___x_660_);
lean_dec(v___x_660_);
v___x_662_ = lean_nat_dec_eq(v___x_661_, v___x_657_);
lean_dec(v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v_s1_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v_s2_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_663_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_659_, v___x_658_);
v_s1_664_ = lean_string_utf8_extract(v_string_653_, v___x_663_, v___x_658_);
lean_dec(v___x_663_);
v___x_665_ = lean_string_length(v_s1_664_);
v___x_666_ = l_String_Slice_Pos_prevn(v___x_659_, v___x_658_, v___x_665_);
lean_dec_ref(v___x_659_);
v_s2_667_ = lean_string_utf8_extract(v_string_653_, v___x_657_, v___x_666_);
lean_dec(v___x_666_);
lean_dec_ref(v_string_653_);
v___x_668_ = lean_array_mk(v_tail_649_);
v___x_669_ = l_Array_reverse___redArg(v___x_668_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v_s2_667_);
v___x_671_ = v___x_655_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_s2_667_);
v___x_671_ = v_reuseFailAlloc_682_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = lean_array_get_size(v___x_669_);
v___x_673_ = lean_nat_dec_eq(v___x_672_, v___x_657_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_674_ = lean_array_push(v___x_669_, v___x_671_);
v___x_675_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 0);
lean_ctor_set(v___x_651_, 1, v_s1_664_);
lean_ctor_set(v___x_651_, 0, v___x_675_);
v___x_677_ = v___x_651_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_s1_664_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
else
{
lean_object* v___x_680_; 
lean_dec_ref(v___x_669_);
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 0);
lean_ctor_set(v___x_651_, 1, v_s1_664_);
lean_ctor_set(v___x_651_, 0, v___x_671_);
v___x_680_ = v___x_651_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_s1_664_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v___x_683_; lean_object* v_fst_684_; lean_object* v_snd_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_693_; 
lean_dec_ref(v___x_659_);
lean_del_object(v___x_655_);
lean_del_object(v___x_651_);
v___x_683_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_tail_649_);
v_fst_684_ = lean_ctor_get(v___x_683_, 0);
v_snd_685_ = lean_ctor_get(v___x_683_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_693_ == 0)
{
v___x_687_ = v___x_683_;
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_snd_685_);
lean_inc(v_fst_684_);
lean_dec(v___x_683_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_string_append(v_snd_685_, v_string_653_);
lean_dec_ref(v_string_653_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_fst_684_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_697_; lean_object* v_content_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_tail_697_ = lean_ctor_get(v_a_642_, 1);
lean_inc(v_tail_697_);
lean_dec_ref(v_a_642_);
v_content_698_ = lean_ctor_get(v_head_648_, 0);
lean_inc_ref(v_content_698_);
lean_dec_ref(v_head_648_);
v___x_699_ = l_Array_reverse___redArg(v_content_698_);
v___x_700_ = lean_array_to_list(v___x_699_);
v___x_701_ = l_List_appendTR___redArg(v___x_700_, v_tail_697_);
v_a_642_ = v___x_701_;
goto _start;
}
default: 
{
lean_object* v_tail_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_tail_703_ = lean_ctor_get(v_a_642_, 1);
lean_inc(v_tail_703_);
lean_dec_ref(v_a_642_);
v___x_704_ = lean_array_mk(v_tail_703_);
v___x_705_ = l_Array_reverse___redArg(v___x_704_);
v___x_706_ = lean_array_get_size(v___x_705_);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = lean_nat_dec_eq(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
if (lean_obj_tag(v_head_648_) == 9)
{
lean_object* v_content_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_content_709_ = lean_ctor_get(v_head_648_, 0);
lean_inc_ref(v_content_709_);
lean_dec_ref(v_head_648_);
v___x_710_ = lean_array_get_size(v_content_709_);
v___x_711_ = lean_nat_dec_eq(v___x_710_, v___x_707_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = l_Array_append___redArg(v___x_705_, v_content_709_);
lean_dec_ref(v_content_709_);
v___x_713_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
v___y_644_ = v___x_713_;
goto v___jp_643_;
}
else
{
lean_object* v___x_714_; 
lean_dec_ref(v_content_709_);
v___x_714_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_705_);
v___y_644_ = v___x_714_;
goto v___jp_643_;
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_array_push(v___x_705_, v_head_648_);
v___x_716_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
v___y_644_ = v___x_716_;
goto v___jp_643_;
}
}
else
{
lean_dec_ref(v___x_705_);
v___y_644_ = v_head_648_;
goto v___jp_643_;
}
}
}
}
v___jp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___y_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_a_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_720_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_box(0);
v___x_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_722_, 0, v_inline_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_724_, lean_object* v_inline_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_727_){
_start:
{
lean_object* v___x_728_; lean_object* v_fst_729_; lean_object* v_snd_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_738_; 
v___x_728_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_727_);
v_fst_729_ = lean_ctor_get(v___x_728_, 0);
v_snd_730_ = lean_ctor_get(v___x_728_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_738_ == 0)
{
v___x_732_ = v___x_728_;
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_snd_730_);
lean_inc(v_fst_729_);
lean_dec(v___x_728_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_734_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_730_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___x_734_);
v___x_736_ = v___x_732_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_fst_729_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_739_, lean_object* v_inline_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_740_);
return v___x_741_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19));
v___x_788_ = l_ReaderT_instMonad___redArg(v___x_787_);
return v___x_788_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_797_ = l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0(lean_object* v_inst_799_, lean_object* v___x_800_, lean_object* v_a_801_, lean_object* v_x_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_806_; lean_object* v_snd_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_815_; 
v___x_806_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_799_, v_a_801_, v___y_804_, v___y_805_);
v_snd_807_ = lean_ctor_get(v___x_806_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v___x_806_, 0);
lean_dec(v_unused_816_);
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_snd_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_800_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_811_);
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_snd_807_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__1));
v___x_825_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
lean_ctor_set(v___x_826_, 2, v___x_824_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_828_, lean_object* v_x_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
switch(lean_obj_tag(v_x_829_))
{
case 0:
{
lean_object* v_string_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v_a_830_);
lean_dec_ref(v_inst_828_);
v_string_833_ = lean_ctor_get(v_x_829_, 0);
lean_inc_ref(v_string_833_);
lean_dec_ref(v_x_829_);
v___x_834_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_833_);
lean_dec_ref(v_string_833_);
v___x_835_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_834_, v_a_831_);
lean_dec_ref(v___x_834_);
return v___x_835_;
}
case 1:
{
lean_object* v_content_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_877_; 
v_content_836_ = lean_ctor_get(v_x_829_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_x_829_);
if (v_isSharedCheck_877_ == 0)
{
v___x_838_ = v_x_829_;
v_isShared_839_ = v_isSharedCheck_877_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_content_836_);
lean_dec(v_x_829_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_877_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 9);
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_content_836_);
v___x_841_ = v_reuseFailAlloc_876_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_842_; lean_object* v_snd_843_; lean_object* v_fst_844_; lean_object* v_fst_845_; lean_object* v_snd_846_; uint8_t v_inEmph_848_; uint8_t v_inBold_849_; uint8_t v_inLink_850_; lean_object* v_linePrefix_851_; lean_object* v___y_852_; lean_object* v___x_863_; uint8_t v_inEmph_864_; 
v___x_842_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_841_);
v_snd_843_ = lean_ctor_get(v___x_842_, 1);
lean_inc(v_snd_843_);
v_fst_844_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_fst_844_);
lean_dec_ref(v___x_842_);
v_fst_845_ = lean_ctor_get(v_snd_843_, 0);
lean_inc(v_fst_845_);
v_snd_846_ = lean_ctor_get(v_snd_843_, 1);
lean_inc(v_snd_846_);
lean_dec(v_snd_843_);
v___x_863_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_844_, v_a_831_);
lean_dec(v_fst_844_);
v_inEmph_864_ = lean_ctor_get_uint8(v_a_830_, sizeof(void*)*1);
if (v_inEmph_864_ == 0)
{
lean_object* v_snd_865_; uint8_t v_inBold_866_; uint8_t v_inLink_867_; lean_object* v_linePrefix_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v_snd_871_; 
v_snd_865_ = lean_ctor_get(v___x_863_, 1);
lean_inc(v_snd_865_);
lean_dec_ref(v___x_863_);
v_inBold_866_ = lean_ctor_get_uint8(v_a_830_, sizeof(void*)*1 + 1);
v_inLink_867_ = lean_ctor_get_uint8(v_a_830_, sizeof(void*)*1 + 2);
v_linePrefix_868_ = lean_ctor_get(v_a_830_, 0);
lean_inc_ref(v_linePrefix_868_);
lean_dec_ref(v_a_830_);
v___x_869_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21));
v___x_870_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_869_, v_snd_865_);
v_snd_871_ = lean_ctor_get(v___x_870_, 1);
lean_inc(v_snd_871_);
lean_dec_ref(v___x_870_);
v_inEmph_848_ = v_inEmph_864_;
v_inBold_849_ = v_inBold_866_;
v_inLink_850_ = v_inLink_867_;
v_linePrefix_851_ = v_linePrefix_868_;
v___y_852_ = v_snd_871_;
goto v___jp_847_;
}
else
{
lean_object* v_snd_872_; uint8_t v_inBold_873_; uint8_t v_inLink_874_; lean_object* v_linePrefix_875_; 
v_snd_872_ = lean_ctor_get(v___x_863_, 1);
lean_inc(v_snd_872_);
lean_dec_ref(v___x_863_);
v_inBold_873_ = lean_ctor_get_uint8(v_a_830_, sizeof(void*)*1 + 1);
v_inLink_874_ = lean_ctor_get_uint8(v_a_830_, sizeof(void*)*1 + 2);
v_linePrefix_875_ = lean_ctor_get(v_a_830_, 0);
lean_inc_ref(v_linePrefix_875_);
lean_dec_ref(v_a_830_);
v_inEmph_848_ = v_inEmph_864_;
v_inBold_849_ = v_inBold_873_;
v_inLink_850_ = v_inLink_874_;
v_linePrefix_851_ = v_linePrefix_875_;
v___y_852_ = v_snd_872_;
goto v___jp_847_;
}
v___jp_847_:
{
uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = 1;
v___x_854_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_854_, 0, v_linePrefix_851_);
lean_ctor_set_uint8(v___x_854_, sizeof(void*)*1, v___x_853_);
lean_ctor_set_uint8(v___x_854_, sizeof(void*)*1 + 1, v_inBold_849_);
lean_ctor_set_uint8(v___x_854_, sizeof(void*)*1 + 2, v_inLink_850_);
v___x_855_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_828_, v_fst_845_, v___x_854_, v___y_852_);
if (v_inEmph_848_ == 0)
{
lean_object* v_snd_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_snd_859_; lean_object* v___x_860_; 
v_snd_856_ = lean_ctor_get(v___x_855_, 1);
lean_inc(v_snd_856_);
lean_dec_ref(v___x_855_);
v___x_857_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21));
v___x_858_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_857_, v_snd_856_);
v_snd_859_ = lean_ctor_get(v___x_858_, 1);
lean_inc(v_snd_859_);
lean_dec_ref(v___x_858_);
v___x_860_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_846_, v_snd_859_);
lean_dec(v_snd_846_);
return v___x_860_;
}
else
{
lean_object* v_snd_861_; lean_object* v___x_862_; 
v_snd_861_ = lean_ctor_get(v___x_855_, 1);
lean_inc(v_snd_861_);
lean_dec_ref(v___x_855_);
v___x_862_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_846_, v_snd_861_);
lean_dec(v_snd_846_);
return v___x_862_;
}
}
}
}
}
case 2:
{
lean_object* v_content_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_916_; 
v_content_878_ = lean_ctor_get(v_x_829_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v_x_829_);
if (v_isSharedCheck_916_ == 0)
{
v___x_880_ = v_x_829_;
v_isShared_881_ = v_isSharedCheck_916_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_content_878_);
lean_dec(v_x_829_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_916_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set_tag(v___x_880_, 9);
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_content_878_);
v___x_883_ = v_reuseFailAlloc_915_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v_snd_885_; lean_object* v_fst_886_; lean_object* v_fst_887_; lean_object* v_snd_888_; uint8_t v_inBold_890_; uint8_t v_inLink_891_; lean_object* v_linePrefix_892_; lean_object* v___y_893_; lean_object* v___x_904_; uint8_t v_inBold_905_; 
v___x_884_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_883_);
v_snd_885_ = lean_ctor_get(v___x_884_, 1);
lean_inc(v_snd_885_);
v_fst_886_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_fst_886_);
lean_dec_ref(v___x_884_);
v_fst_887_ = lean_ctor_get(v_snd_885_, 0);
lean_inc(v_fst_887_);
v_snd_888_ = lean_ctor_get(v_snd_885_, 1);
lean_inc(v_snd_888_);
lean_dec(v_snd_885_);
v___x_904_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_886_, v_a_831_);
lean_dec(v_fst_886_);
v_inBold_905_ = lean_ctor_get_uint8(v_a_830_, sizeof(void*)*1 + 1);
if (v_inBold_905_ == 0)
{
lean_object* v_snd_906_; uint8_t v_inLink_907_; lean_object* v_linePrefix_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v_snd_911_; 
v_snd_906_ = lean_ctor_get(v___x_904_, 1);
lean_inc(v_snd_906_);
lean_dec_ref(v___x_904_);
v_inLink_907_ = lean_ctor_get_uint8(v_a_830_, sizeof(void*)*1 + 2);
v_linePrefix_908_ = lean_ctor_get(v_a_830_, 0);
lean_inc_ref(v_linePrefix_908_);
lean_dec_ref(v_a_830_);
v___x_909_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_910_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_909_, v_snd_906_);
v_snd_911_ = lean_ctor_get(v___x_910_, 1);
lean_inc(v_snd_911_);
lean_dec_ref(v___x_910_);
v_inBold_890_ = v_inBold_905_;
v_inLink_891_ = v_inLink_907_;
v_linePrefix_892_ = v_linePrefix_908_;
v___y_893_ = v_snd_911_;
goto v___jp_889_;
}
else
{
lean_object* v_snd_912_; uint8_t v_inLink_913_; lean_object* v_linePrefix_914_; 
v_snd_912_ = lean_ctor_get(v___x_904_, 1);
lean_inc(v_snd_912_);
lean_dec_ref(v___x_904_);
v_inLink_913_ = lean_ctor_get_uint8(v_a_830_, sizeof(void*)*1 + 2);
v_linePrefix_914_ = lean_ctor_get(v_a_830_, 0);
lean_inc_ref(v_linePrefix_914_);
lean_dec_ref(v_a_830_);
v_inBold_890_ = v_inBold_905_;
v_inLink_891_ = v_inLink_913_;
v_linePrefix_892_ = v_linePrefix_914_;
v___y_893_ = v_snd_912_;
goto v___jp_889_;
}
v___jp_889_:
{
uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = 1;
v___x_895_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_895_, 0, v_linePrefix_892_);
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*1, v___x_894_);
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*1 + 1, v_inBold_890_);
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*1 + 2, v_inLink_891_);
v___x_896_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_828_, v_fst_887_, v___x_895_, v___y_893_);
if (v_inBold_890_ == 0)
{
lean_object* v_snd_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_snd_900_; lean_object* v___x_901_; 
v_snd_897_ = lean_ctor_get(v___x_896_, 1);
lean_inc(v_snd_897_);
lean_dec_ref(v___x_896_);
v___x_898_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_899_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_898_, v_snd_897_);
v_snd_900_ = lean_ctor_get(v___x_899_, 1);
lean_inc(v_snd_900_);
lean_dec_ref(v___x_899_);
v___x_901_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_888_, v_snd_900_);
lean_dec(v_snd_888_);
return v___x_901_;
}
else
{
lean_object* v_snd_902_; lean_object* v___x_903_; 
v_snd_902_ = lean_ctor_get(v___x_896_, 1);
lean_inc(v_snd_902_);
lean_dec_ref(v___x_896_);
v___x_903_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_888_, v_snd_902_);
lean_dec(v_snd_888_);
return v___x_903_;
}
}
}
}
}
case 3:
{
lean_object* v_string_917_; lean_object* v___y_919_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_fst_924_; uint8_t v___x_925_; 
lean_dec_ref(v_a_830_);
lean_dec_ref(v_inst_828_);
v_string_917_ = lean_ctor_get(v_x_829_, 0);
lean_inc_ref(v_string_917_);
lean_dec_ref(v_x_829_);
v___x_922_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_923_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v___x_922_, v_a_831_);
v_fst_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_fst_924_);
v___x_925_ = lean_unbox(v_fst_924_);
lean_dec(v_fst_924_);
if (v___x_925_ == 0)
{
lean_object* v_snd_926_; 
v_snd_926_ = lean_ctor_get(v___x_923_, 1);
lean_inc(v_snd_926_);
lean_dec_ref(v___x_923_);
v___y_919_ = v_snd_926_;
goto v___jp_918_;
}
else
{
lean_object* v_snd_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_snd_930_; 
v_snd_927_ = lean_ctor_get(v___x_923_, 1);
lean_inc(v_snd_927_);
lean_dec_ref(v___x_923_);
v___x_928_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23));
v___x_929_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_928_, v_snd_927_);
v_snd_930_ = lean_ctor_get(v___x_929_, 1);
lean_inc(v_snd_930_);
lean_dec_ref(v___x_929_);
v___y_919_ = v_snd_930_;
goto v___jp_918_;
}
v___jp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_917_);
v___x_921_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_920_, v___y_919_);
lean_dec_ref(v___x_920_);
return v___x_921_;
}
}
case 4:
{
uint8_t v_mode_931_; 
lean_dec_ref(v_a_830_);
lean_dec_ref(v_inst_828_);
v_mode_931_ = lean_ctor_get_uint8(v_x_829_, sizeof(void*)*1);
if (v_mode_931_ == 0)
{
lean_object* v_string_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_string_932_ = lean_ctor_get(v_x_829_, 0);
lean_inc_ref(v_string_932_);
lean_dec_ref(v_x_829_);
v___x_933_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24));
v___x_934_ = lean_string_append(v___x_933_, v_string_932_);
lean_dec_ref(v_string_932_);
v___x_935_ = lean_string_append(v___x_934_, v___x_933_);
v___x_936_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_935_, v_a_831_);
lean_dec_ref(v___x_935_);
return v___x_936_;
}
else
{
lean_object* v_string_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_string_937_ = lean_ctor_get(v_x_829_, 0);
lean_inc_ref(v_string_937_);
lean_dec_ref(v_x_829_);
v___x_938_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25));
v___x_939_ = lean_string_append(v___x_938_, v_string_937_);
lean_dec_ref(v_string_937_);
v___x_940_ = lean_string_append(v___x_939_, v___x_938_);
v___x_941_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_940_, v_a_831_);
lean_dec_ref(v___x_940_);
return v___x_941_;
}
}
case 5:
{
lean_object* v_string_942_; lean_object* v_linePrefix_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
lean_dec_ref(v_inst_828_);
v_string_942_ = lean_ctor_get(v_x_829_, 0);
lean_inc_ref(v_string_942_);
lean_dec_ref(v_x_829_);
v_linePrefix_943_ = lean_ctor_get(v_a_830_, 0);
lean_inc_ref(v_linePrefix_943_);
lean_dec_ref(v_a_830_);
v___x_944_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26));
v___x_945_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27));
v___x_946_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_947_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28);
v___x_948_ = lean_string_append(v___x_946_, v_linePrefix_943_);
lean_dec_ref(v_linePrefix_943_);
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = lean_string_utf8_byte_size(v_string_942_);
v___x_951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_951_, 0, v_string_942_);
lean_ctor_set(v___x_951_, 1, v___x_949_);
lean_ctor_set(v___x_951_, 2, v___x_950_);
v___x_952_ = l_String_Slice_replace___redArg(v___x_945_, v___x_944_, v___x_951_, v___x_947_, v___x_948_);
v___x_953_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_952_, v_a_831_);
lean_dec_ref(v___x_952_);
return v___x_953_;
}
case 6:
{
uint8_t v_inLink_954_; 
v_inLink_954_ = lean_ctor_get_uint8(v_a_830_, sizeof(void*)*1 + 2);
if (v_inLink_954_ == 0)
{
lean_object* v_content_955_; lean_object* v_url_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v_snd_959_; lean_object* v___x_960_; lean_object* v___f_961_; size_t v_sz_962_; size_t v___x_963_; lean_object* v___x_12053__overap_964_; lean_object* v___x_965_; lean_object* v_snd_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_snd_969_; lean_object* v___x_970_; lean_object* v_snd_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_content_955_ = lean_ctor_get(v_x_829_, 0);
lean_inc_ref(v_content_955_);
v_url_956_ = lean_ctor_get(v_x_829_, 1);
lean_inc_ref(v_url_956_);
lean_dec_ref(v_x_829_);
v___x_957_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29));
v___x_958_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_957_, v_a_831_);
v_snd_959_ = lean_ctor_get(v___x_958_, 1);
lean_inc(v_snd_959_);
lean_dec_ref(v___x_958_);
v___x_960_ = lean_box(0);
v___f_961_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0), 7, 2);
lean_closure_set(v___f_961_, 0, v_inst_828_);
lean_closure_set(v___f_961_, 1, v___x_960_);
v_sz_962_ = lean_array_size(v_content_955_);
v___x_963_ = ((size_t)0ULL);
v___x_12053__overap_964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_832_, v_content_955_, v___f_961_, v_sz_962_, v___x_963_, v___x_960_);
v___x_965_ = lean_apply_2(v___x_12053__overap_964_, v_a_830_, v_snd_959_);
v_snd_966_ = lean_ctor_get(v___x_965_, 1);
lean_inc(v_snd_966_);
lean_dec_ref(v___x_965_);
v___x_967_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30));
v___x_968_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_967_, v_snd_966_);
v_snd_969_ = lean_ctor_get(v___x_968_, 1);
lean_inc(v_snd_969_);
lean_dec_ref(v___x_968_);
v___x_970_ = l_Lean_Doc_MarkdownM_push___redArg(v_url_956_, v_snd_969_);
lean_dec_ref(v_url_956_);
v_snd_971_ = lean_ctor_get(v___x_970_, 1);
lean_inc(v_snd_971_);
lean_dec_ref(v___x_970_);
v___x_972_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31));
v___x_973_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_972_, v_snd_971_);
return v___x_973_;
}
else
{
lean_object* v_content_974_; lean_object* v___x_975_; lean_object* v___f_976_; size_t v_sz_977_; size_t v___x_978_; lean_object* v___x_12077__overap_979_; lean_object* v___x_980_; lean_object* v_snd_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
v_content_974_ = lean_ctor_get(v_x_829_, 0);
lean_inc_ref(v_content_974_);
lean_dec_ref(v_x_829_);
v___x_975_ = lean_box(0);
v___f_976_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0), 7, 2);
lean_closure_set(v___f_976_, 0, v_inst_828_);
lean_closure_set(v___f_976_, 1, v___x_975_);
v_sz_977_ = lean_array_size(v_content_974_);
v___x_978_ = ((size_t)0ULL);
v___x_12077__overap_979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_832_, v_content_974_, v___f_976_, v_sz_977_, v___x_978_, v___x_975_);
v___x_980_ = lean_apply_2(v___x_12077__overap_979_, v_a_830_, v_a_831_);
v_snd_981_ = lean_ctor_get(v___x_980_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v___x_980_, 0);
lean_dec(v_unused_989_);
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_snd_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_975_);
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_snd_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
case 7:
{
lean_object* v_name_990_; lean_object* v_content_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_snd_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v_a_830_);
v_name_990_ = lean_ctor_get(v_x_829_, 0);
lean_inc_ref(v_name_990_);
v_content_991_ = lean_ctor_get(v_x_829_, 1);
lean_inc_ref(v_content_991_);
lean_dec_ref(v_x_829_);
v___x_992_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32));
v___x_993_ = lean_string_append(v___x_992_, v_name_990_);
v___x_994_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33));
v___x_995_ = lean_string_append(v___x_993_, v___x_994_);
v___x_996_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_995_, v_a_831_);
lean_dec_ref(v___x_995_);
v_snd_997_ = lean_ctor_get(v___x_996_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v___x_996_, 0);
lean_dec(v_unused_1040_);
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1039_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_snd_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1039_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_snd_1002_; lean_object* v___y_1021_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = lean_array_get_size(v_content_991_);
v___x_1025_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34));
v___x_1026_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35);
v___x_1027_ = lean_nat_dec_lt(v___x_1023_, v___x_1024_);
if (v___x_1027_ == 0)
{
lean_dec_ref(v_content_991_);
lean_dec_ref(v_inst_828_);
v_snd_1002_ = v___x_1026_;
goto v___jp_1001_;
}
else
{
lean_object* v___x_1028_; lean_object* v___f_1029_; uint8_t v___x_1030_; 
v___x_1028_ = lean_box(0);
v___f_1029_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1029_, 0, v_inst_828_);
v___x_1030_ = lean_nat_dec_le(v___x_1024_, v___x_1024_);
if (v___x_1030_ == 0)
{
if (v___x_1027_ == 0)
{
lean_dec_ref(v___f_1029_);
lean_dec_ref(v_content_991_);
v_snd_1002_ = v___x_1026_;
goto v___jp_1001_;
}
else
{
size_t v___x_1031_; size_t v___x_1032_; lean_object* v___x_11896__overap_1033_; lean_object* v___x_1034_; 
v___x_1031_ = ((size_t)0ULL);
v___x_1032_ = lean_usize_of_nat(v___x_1024_);
v___x_11896__overap_1033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_832_, v___f_1029_, v_content_991_, v___x_1031_, v___x_1032_, v___x_1028_);
v___x_1034_ = lean_apply_2(v___x_11896__overap_1033_, v___x_1025_, v___x_1026_);
v___y_1021_ = v___x_1034_;
goto v___jp_1020_;
}
}
else
{
size_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_11900__overap_1037_; lean_object* v___x_1038_; 
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = lean_usize_of_nat(v___x_1024_);
v___x_11900__overap_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_832_, v___f_1029_, v_content_991_, v___x_1035_, v___x_1036_, v___x_1028_);
v___x_1038_ = lean_apply_2(v___x_11900__overap_1037_, v___x_1025_, v___x_1026_);
v___y_1021_ = v___x_1038_;
goto v___jp_1020_;
}
}
v___jp_1001_:
{
lean_object* v_priorBlocks_1003_; lean_object* v_currentBlock_1004_; lean_object* v_footnotes_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1019_; 
v_priorBlocks_1003_ = lean_ctor_get(v_snd_997_, 0);
v_currentBlock_1004_ = lean_ctor_get(v_snd_997_, 1);
v_footnotes_1005_ = lean_ctor_get(v_snd_997_, 2);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_snd_997_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1007_ = v_snd_997_;
v_isShared_1008_ = v_isSharedCheck_1019_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_footnotes_1005_);
lean_inc(v_currentBlock_1004_);
lean_inc(v_priorBlocks_1003_);
lean_dec(v_snd_997_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1019_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(v_snd_1002_);
v___x_1010_ = lean_box(0);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 1, v___x_1009_);
lean_ctor_set(v___x_999_, 0, v_name_990_);
v___x_1012_ = v___x_999_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_name_990_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v___x_1009_);
v___x_1012_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_array_push(v_footnotes_1005_, v___x_1012_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 2, v___x_1013_);
v___x_1015_ = v___x_1007_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_priorBlocks_1003_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_currentBlock_1004_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1010_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
return v___x_1016_;
}
}
}
}
v___jp_1020_:
{
lean_object* v_snd_1022_; 
v_snd_1022_ = lean_ctor_get(v___y_1021_, 1);
lean_inc(v_snd_1022_);
lean_dec_ref(v___y_1021_);
v_snd_1002_ = v_snd_1022_;
goto v___jp_1001_;
}
}
}
case 8:
{
lean_object* v_alt_1041_; lean_object* v_url_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref(v_a_830_);
lean_dec_ref(v_inst_828_);
v_alt_1041_ = lean_ctor_get(v_x_829_, 0);
lean_inc_ref(v_alt_1041_);
v_url_1042_ = lean_ctor_get(v_x_829_, 1);
lean_inc_ref(v_url_1042_);
lean_dec_ref(v_x_829_);
v___x_1043_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__36));
v___x_1044_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1041_);
lean_dec_ref(v_alt_1041_);
v___x_1045_ = lean_string_append(v___x_1043_, v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30));
v___x_1047_ = lean_string_append(v___x_1045_, v___x_1046_);
v___x_1048_ = lean_string_append(v___x_1047_, v_url_1042_);
lean_dec_ref(v_url_1042_);
v___x_1049_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31));
v___x_1050_ = lean_string_append(v___x_1048_, v___x_1049_);
v___x_1051_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1050_, v_a_831_);
lean_dec_ref(v___x_1050_);
return v___x_1051_;
}
case 9:
{
lean_object* v_content_1052_; lean_object* v___x_1053_; lean_object* v___f_1054_; size_t v_sz_1055_; size_t v___x_1056_; lean_object* v___x_11991__overap_1057_; lean_object* v___x_1058_; lean_object* v_snd_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
v_content_1052_ = lean_ctor_get(v_x_829_, 0);
lean_inc_ref(v_content_1052_);
lean_dec_ref(v_x_829_);
v___x_1053_ = lean_box(0);
v___f_1054_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0), 7, 2);
lean_closure_set(v___f_1054_, 0, v_inst_828_);
lean_closure_set(v___f_1054_, 1, v___x_1053_);
v_sz_1055_ = lean_array_size(v_content_1052_);
v___x_1056_ = ((size_t)0ULL);
v___x_11991__overap_1057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_832_, v_content_1052_, v___f_1054_, v_sz_1055_, v___x_1056_, v___x_1053_);
v___x_1058_ = lean_apply_2(v___x_11991__overap_1057_, v_a_830_, v_a_831_);
v_snd_1059_ = lean_ctor_get(v___x_1058_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v___x_1058_, 0);
lean_dec(v_unused_1067_);
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_snd_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1053_);
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_snd_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
default: 
{
lean_object* v_container_1068_; lean_object* v_content_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_container_1068_ = lean_ctor_get(v_x_829_, 0);
lean_inc(v_container_1068_);
v_content_1069_ = lean_ctor_get(v_x_829_, 1);
lean_inc_ref(v_content_1069_);
lean_dec_ref(v_x_829_);
lean_inc_ref(v_inst_828_);
v___x_1070_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg), 4, 1);
lean_closure_set(v___x_1070_, 0, v_inst_828_);
v___x_1071_ = lean_apply_5(v_inst_828_, v___x_1070_, v_container_1068_, v_content_1069_, v_a_830_, v_a_831_);
return v___x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2(lean_object* v_inst_1072_, lean_object* v_x_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1072_, v___y_1074_, v___y_1075_, v___y_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1078_, lean_object* v_inst_1079_, lean_object* v_x_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1079_, v_x_1080_, v_a_1081_, v_a_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1084_, lean_object* v_inline_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1084_, v_inline_1085_, v_a_1086_, v_a_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1089_, lean_object* v_inst_1090_, lean_object* v_inline_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1090_, v_inline_1091_, v_a_1092_, v_a_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0(lean_object* v_inst_1095_, lean_object* v_inline_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1095_, v_inline_1096_, v___y_1097_, v___y_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1100_){
_start:
{
lean_object* v___f_1101_; 
v___f_1101_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1101_, 0, v_inst_1100_);
return v___f_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1102_, lean_object* v_inst_1103_){
_start:
{
lean_object* v___f_1104_; 
v___f_1104_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1104_, 0, v_inst_1103_);
return v___f_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(lean_object* v_x_1105_, lean_object* v_x_1106_){
_start:
{
lean_object* v_zero_1107_; uint8_t v_isZero_1108_; 
v_zero_1107_ = lean_unsigned_to_nat(0u);
v_isZero_1108_ = lean_nat_dec_eq(v_x_1105_, v_zero_1107_);
if (v_isZero_1108_ == 1)
{
lean_dec(v_x_1105_);
return v_x_1106_;
}
else
{
uint32_t v___x_1109_; lean_object* v_one_1110_; lean_object* v_n_1111_; lean_object* v___x_1112_; 
v___x_1109_ = 32;
v_one_1110_ = lean_unsigned_to_nat(1u);
v_n_1111_ = lean_nat_sub(v_x_1105_, v_one_1110_);
lean_dec(v_x_1105_);
v___x_1112_ = lean_string_push(v_x_1106_, v___x_1109_);
v_x_1105_ = v_n_1111_;
v_x_1106_ = v___x_1112_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(lean_object* v_str_1114_, lean_object* v_indent_1115_, lean_object* v_b_1116_){
_start:
{
lean_object* v_snd_1117_; lean_object* v_snd_1118_; lean_object* v_fst_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1181_; 
v_snd_1117_ = lean_ctor_get(v_b_1116_, 1);
lean_inc(v_snd_1117_);
v_snd_1118_ = lean_ctor_get(v_snd_1117_, 1);
lean_inc(v_snd_1118_);
v_fst_1119_ = lean_ctor_get(v_b_1116_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_b_1116_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v_b_1116_, 1);
lean_dec(v_unused_1182_);
v___x_1121_ = v_b_1116_;
v_isShared_1122_ = v_isSharedCheck_1181_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_fst_1119_);
lean_dec(v_b_1116_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1181_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v_fst_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1179_; 
v_fst_1123_ = lean_ctor_get(v_snd_1117_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_snd_1117_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; 
v_unused_1180_ = lean_ctor_get(v_snd_1117_, 1);
lean_dec(v_unused_1180_);
v___x_1125_ = v_snd_1117_;
v_isShared_1126_ = v_isSharedCheck_1179_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_fst_1123_);
lean_dec(v_snd_1117_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1179_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_fst_1127_; lean_object* v_snd_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1178_; 
v_fst_1127_ = lean_ctor_get(v_snd_1118_, 0);
v_snd_1128_ = lean_ctor_get(v_snd_1118_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_snd_1118_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1130_ = v_snd_1118_;
v_isShared_1131_ = v_isSharedCheck_1178_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_snd_1128_);
lean_inc(v_fst_1127_);
lean_dec(v_snd_1118_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1178_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_string_utf8_byte_size(v_str_1114_);
v___x_1133_ = lean_nat_dec_eq(v_fst_1127_, v___x_1132_);
if (v___x_1133_ == 0)
{
uint32_t v_c_1134_; lean_object* v_iter_1135_; lean_object* v_longest_1137_; lean_object* v_current_1138_; uint32_t v___x_1163_; uint8_t v___x_1164_; 
v_c_1134_ = lean_string_utf8_get_fast(v_str_1114_, v_fst_1127_);
v_iter_1135_ = lean_string_utf8_next_fast(v_str_1114_, v_fst_1127_);
lean_dec(v_fst_1127_);
v___x_1163_ = 96;
v___x_1164_ = lean_uint32_dec_eq(v_c_1134_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v_current_1165_; uint8_t v___x_1166_; 
v_current_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = lean_nat_dec_le(v_fst_1119_, v_fst_1123_);
if (v___x_1166_ == 0)
{
lean_dec(v_fst_1123_);
v_longest_1137_ = v_fst_1119_;
v_current_1138_ = v_current_1165_;
goto v___jp_1136_;
}
else
{
lean_dec(v_fst_1119_);
v_longest_1137_ = v_fst_1123_;
v_current_1138_ = v_current_1165_;
goto v___jp_1136_;
}
}
else
{
lean_object* v___x_1167_; lean_object* v_current_1168_; 
v___x_1167_ = lean_unsigned_to_nat(1u);
v_current_1168_ = lean_nat_add(v_fst_1123_, v___x_1167_);
lean_dec(v_fst_1123_);
v_longest_1137_ = v_fst_1119_;
v_current_1138_ = v_current_1168_;
goto v___jp_1136_;
}
v___jp_1136_:
{
lean_object* v_out_1139_; uint32_t v___x_1140_; uint8_t v___x_1141_; 
v_out_1139_ = lean_string_push(v_snd_1128_, v_c_1134_);
v___x_1140_ = 10;
v___x_1141_ = lean_uint32_dec_eq(v_c_1134_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1143_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 1, v_out_1139_);
lean_ctor_set(v___x_1130_, 0, v_iter_1135_);
v___x_1143_ = v___x_1130_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_iter_1135_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_out_1139_);
v___x_1143_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v___x_1143_);
lean_ctor_set(v___x_1125_, 0, v_current_1138_);
v___x_1145_ = v___x_1125_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_current_1138_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v___x_1145_);
lean_ctor_set(v___x_1121_, 0, v_longest_1137_);
v___x_1147_ = v___x_1121_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_longest_1137_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
v_b_1116_ = v___x_1147_;
goto _start;
}
}
}
}
else
{
lean_object* v_out_1152_; lean_object* v___x_1154_; 
lean_inc(v_indent_1115_);
v_out_1152_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(v_indent_1115_, v_out_1139_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 1, v_out_1152_);
lean_ctor_set(v___x_1130_, 0, v_iter_1135_);
v___x_1154_ = v___x_1130_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_iter_1135_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_out_1152_);
v___x_1154_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v___x_1154_);
lean_ctor_set(v___x_1125_, 0, v_current_1138_);
v___x_1156_ = v___x_1125_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_current_1138_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1158_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v___x_1156_);
lean_ctor_set(v___x_1121_, 0, v_longest_1137_);
v___x_1158_ = v___x_1121_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_longest_1137_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
v_b_1116_ = v___x_1158_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_1170_; 
lean_dec(v_indent_1115_);
if (v_isShared_1131_ == 0)
{
v___x_1170_ = v___x_1130_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_fst_1127_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_snd_1128_);
v___x_1170_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v___x_1170_);
v___x_1172_ = v___x_1125_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_fst_1123_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1174_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v___x_1172_);
v___x_1174_ = v___x_1121_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_fst_1119_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1___boxed(lean_object* v_str_1183_, lean_object* v_indent_1184_, lean_object* v_b_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(v_str_1183_, v_indent_1184_, v_b_1185_);
lean_dec_ref(v_str_1183_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(lean_object* v_indent_1196_, lean_object* v_str_1197_){
_start:
{
lean_object* v_current_1198_; lean_object* v_out_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_snd_1202_; lean_object* v_snd_1203_; lean_object* v_fst_1204_; lean_object* v_fst_1205_; lean_object* v_snd_1206_; lean_object* v___x_1207_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1220_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_current_1198_ = lean_unsigned_to_nat(0u);
v_out_1199_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_1200_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__2));
lean_inc(v_indent_1196_);
v___x_1201_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(v_str_1197_, v_indent_1196_, v___x_1200_);
v_snd_1202_ = lean_ctor_get(v___x_1201_, 1);
lean_inc(v_snd_1202_);
v_snd_1203_ = lean_ctor_get(v_snd_1202_, 1);
lean_inc(v_snd_1203_);
v_fst_1204_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_fst_1204_);
lean_dec_ref(v___x_1201_);
v_fst_1205_ = lean_ctor_get(v_snd_1202_, 0);
lean_inc(v_fst_1205_);
lean_dec(v_snd_1202_);
v_snd_1206_ = lean_ctor_get(v_snd_1203_, 1);
lean_inc(v_snd_1206_);
lean_dec(v_snd_1203_);
v___x_1207_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1226_ = lean_string_utf8_byte_size(v_snd_1206_);
v___x_1227_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2);
v___x_1228_ = lean_nat_dec_le(v___x_1227_, v___x_1226_);
if (v___x_1228_ == 0)
{
goto v___jp_1223_;
}
else
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_nat_sub(v___x_1226_, v___x_1227_);
v___x_1230_ = lean_string_memcmp(v_snd_1206_, v___x_1207_, v___x_1229_, v_current_1198_, v___x_1227_);
lean_dec(v___x_1229_);
if (v___x_1230_ == 0)
{
goto v___jp_1223_;
}
else
{
v___y_1220_ = v_snd_1206_;
goto v___jp_1219_;
}
}
v___jp_1208_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_nat_add(v___y_1211_, v___x_1212_);
lean_dec(v___y_1211_);
v___x_1214_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__1(v___x_1213_, v___y_1210_);
lean_inc_ref(v___x_1214_);
v___x_1215_ = lean_string_append(v___x_1214_, v___x_1207_);
v___x_1216_ = lean_string_append(v___x_1215_, v___y_1209_);
lean_dec_ref(v___y_1209_);
v___x_1217_ = lean_string_append(v___x_1216_, v___x_1214_);
lean_dec_ref(v___x_1214_);
v___x_1218_ = lean_string_append(v___x_1217_, v___x_1207_);
return v___x_1218_;
}
v___jp_1219_:
{
lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(v_indent_1196_, v_out_1199_);
v___x_1222_ = lean_nat_dec_le(v_fst_1204_, v_fst_1205_);
if (v___x_1222_ == 0)
{
lean_dec(v_fst_1205_);
v___y_1209_ = v___y_1220_;
v___y_1210_ = v___x_1221_;
v___y_1211_ = v_fst_1204_;
goto v___jp_1208_;
}
else
{
lean_dec(v_fst_1204_);
v___y_1209_ = v___y_1220_;
v___y_1210_ = v___x_1221_;
v___y_1211_ = v_fst_1205_;
goto v___jp_1208_;
}
}
v___jp_1223_:
{
uint32_t v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = 10;
v___x_1225_ = lean_string_push(v_snd_1206_, v___x_1224_);
v___y_1220_ = v___x_1225_;
goto v___jp_1219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___boxed(lean_object* v_indent_1231_, lean_object* v_str_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v_indent_1231_, v_str_1232_);
lean_dec_ref(v_str_1232_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v___x_1235_, lean_object* v___f_1236_, lean_object* v___x_1237_, lean_object* v_a_1238_, lean_object* v_x_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v_inEmph_1243_; uint8_t v_inBold_1244_; uint8_t v_inLink_1245_; lean_object* v_linePrefix_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1273_; 
v_inEmph_1243_ = lean_ctor_get_uint8(v___y_1241_, sizeof(void*)*1);
v_inBold_1244_ = lean_ctor_get_uint8(v___y_1241_, sizeof(void*)*1 + 1);
v_inLink_1245_ = lean_ctor_get_uint8(v___y_1241_, sizeof(void*)*1 + 2);
v_linePrefix_1246_ = lean_ctor_get(v___y_1241_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___y_1241_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1248_ = v___y_1241_;
v_isShared_1249_ = v_isSharedCheck_1273_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_linePrefix_1246_);
lean_dec(v___y_1241_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1273_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_snd_1253_; size_t v_sz_1254_; size_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1250_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
lean_inc_ref(v_linePrefix_1246_);
v___x_1251_ = lean_string_append(v_linePrefix_1246_, v___x_1250_);
v___x_1252_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1251_, v___y_1242_);
lean_dec_ref(v___x_1251_);
v_snd_1253_ = lean_ctor_get(v___x_1252_, 1);
lean_inc(v_snd_1253_);
lean_dec_ref(v___x_1252_);
v_sz_1254_ = lean_array_size(v_a_1238_);
v___x_1255_ = ((size_t)0ULL);
v___x_1256_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1257_ = lean_string_append(v_linePrefix_1246_, v___x_1256_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1257_);
v___x_1259_ = v___x_1248_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1272_, sizeof(void*)*1, v_inEmph_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1272_, sizeof(void*)*1 + 1, v_inBold_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1272_, sizeof(void*)*1 + 2, v_inLink_1245_);
v___x_1259_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_13714__overap_1260_; lean_object* v___x_1261_; lean_object* v_snd_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1270_; 
v___x_13714__overap_1260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1235_, v_a_1238_, v___f_1236_, v_sz_1254_, v___x_1255_, v___x_1237_);
v___x_1261_ = lean_apply_2(v___x_13714__overap_1260_, v___x_1259_, v_snd_1253_);
v_snd_1262_ = lean_ctor_get(v___x_1261_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; 
v_unused_1271_ = lean_ctor_get(v___x_1261_, 0);
lean_dec(v_unused_1271_);
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_snd_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1237_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1266_);
v___x_1268_ = v___x_1264_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_snd_1262_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v___x_1277_, lean_object* v___x_1278_, lean_object* v_a_1279_, lean_object* v_x_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
uint8_t v_inEmph_1284_; uint8_t v_inBold_1285_; uint8_t v_inLink_1286_; lean_object* v_linePrefix_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1319_; 
v_inEmph_1284_ = lean_ctor_get_uint8(v___y_1282_, sizeof(void*)*1);
v_inBold_1285_ = lean_ctor_get_uint8(v___y_1282_, sizeof(void*)*1 + 1);
v_inLink_1286_ = lean_ctor_get_uint8(v___y_1282_, sizeof(void*)*1 + 2);
v_linePrefix_1287_ = lean_ctor_get(v___y_1282_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___y_1282_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1289_ = v___y_1282_;
v_isShared_1290_ = v_isSharedCheck_1319_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_linePrefix_1287_);
lean_dec(v___y_1282_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1319_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v_snd_1296_; lean_object* v___x_1297_; lean_object* v___f_1298_; size_t v_sz_1299_; size_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
lean_inc(v___y_1281_);
v___x_1291_ = l_Nat_reprFast(v___y_1281_);
v___x_1292_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0));
v___x_1293_ = lean_string_append(v___x_1291_, v___x_1292_);
lean_inc_ref(v_linePrefix_1287_);
v___x_1294_ = lean_string_append(v_linePrefix_1287_, v___x_1293_);
lean_dec_ref(v___x_1293_);
v___x_1295_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1294_, v___y_1283_);
lean_dec_ref(v___x_1294_);
v_snd_1296_ = lean_ctor_get(v___x_1295_, 1);
lean_inc(v_snd_1296_);
lean_dec_ref(v___x_1295_);
v___x_1297_ = lean_box(0);
v___f_1298_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1), 8, 3);
lean_closure_set(v___f_1298_, 0, v_inst_1275_);
lean_closure_set(v___f_1298_, 1, v_inst_1276_);
lean_closure_set(v___f_1298_, 2, v___x_1297_);
v_sz_1299_ = lean_array_size(v_a_1279_);
v___x_1300_ = ((size_t)0ULL);
v___x_1301_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1302_ = lean_string_append(v_linePrefix_1287_, v___x_1301_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1302_);
v___x_1304_ = v___x_1289_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*1, v_inEmph_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*1 + 1, v_inBold_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*1 + 2, v_inLink_1286_);
v___x_1304_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_13752__overap_1305_; lean_object* v___x_1306_; lean_object* v_snd_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1316_; 
v___x_13752__overap_1305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1277_, v_a_1279_, v___f_1298_, v_sz_1299_, v___x_1300_, v___x_1297_);
v___x_1306_ = lean_apply_2(v___x_13752__overap_1305_, v___x_1304_, v_snd_1296_);
v_snd_1307_ = lean_ctor_get(v___x_1306_, 1);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v___x_1306_, 0);
lean_dec(v_unused_1317_);
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1316_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_snd_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1316_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1311_ = lean_nat_add(v___y_1281_, v___x_1278_);
lean_dec(v___y_1281_);
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1312_);
v___x_1314_ = v___x_1309_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_snd_1307_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v___x_1322_, lean_object* v___x_1323_, lean_object* v_a_1324_, lean_object* v_x_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1320_, v_inst_1321_, v___x_1322_, v___x_1323_, v_a_1324_, v_x_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___x_1323_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v___x_1335_, lean_object* v_a_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint8_t v_inEmph_1341_; uint8_t v_inBold_1342_; uint8_t v_inLink_1343_; lean_object* v_linePrefix_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1382_; 
v_inEmph_1341_ = lean_ctor_get_uint8(v___y_1339_, sizeof(void*)*1);
v_inBold_1342_ = lean_ctor_get_uint8(v___y_1339_, sizeof(void*)*1 + 1);
v_inLink_1343_ = lean_ctor_get_uint8(v___y_1339_, sizeof(void*)*1 + 2);
v_linePrefix_1344_ = lean_ctor_get(v___y_1339_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___y_1339_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1346_ = v___y_1339_;
v_isShared_1347_ = v_isSharedCheck_1382_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_linePrefix_1344_);
lean_dec(v___y_1339_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1382_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v_snd_1351_; lean_object* v_term_1352_; lean_object* v_desc_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1348_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
lean_inc_ref(v_linePrefix_1344_);
v___x_1349_ = lean_string_append(v_linePrefix_1344_, v___x_1348_);
v___x_1350_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1349_, v___y_1340_);
lean_dec_ref(v___x_1349_);
v_snd_1351_ = lean_ctor_get(v___x_1350_, 1);
lean_inc(v_snd_1351_);
lean_dec_ref(v___x_1350_);
v_term_1352_ = lean_ctor_get(v_a_1336_, 0);
v_desc_1353_ = lean_ctor_get(v_a_1336_, 1);
lean_inc_ref(v_term_1352_);
v___x_1354_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_term_1352_);
v___x_1355_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1356_ = lean_string_append(v_linePrefix_1344_, v___x_1355_);
lean_inc_ref(v___x_1356_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1356_);
v___x_1358_ = v___x_1346_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1356_);
lean_ctor_set_uint8(v_reuseFailAlloc_1381_, sizeof(void*)*1, v_inEmph_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1381_, sizeof(void*)*1 + 1, v_inBold_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1381_, sizeof(void*)*1 + 2, v_inLink_1343_);
v___x_1358_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; lean_object* v_snd_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_snd_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_snd_1366_; lean_object* v___x_1367_; lean_object* v_snd_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v_snd_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1379_; 
lean_inc_ref(v___x_1358_);
lean_inc_ref(v_inst_1333_);
v___x_1359_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1333_, v___x_1354_, v___x_1358_, v_snd_1351_);
v_snd_1360_ = lean_ctor_get(v___x_1359_, 1);
lean_inc(v_snd_1360_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1));
lean_inc_ref(v___x_1358_);
lean_inc_ref(v_inst_1333_);
v___x_1362_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1333_, v___x_1361_, v___x_1358_, v_snd_1360_);
v_snd_1363_ = lean_ctor_get(v___x_1362_, 1);
lean_inc(v_snd_1363_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1365_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1364_, v_snd_1363_);
v_snd_1366_ = lean_ctor_get(v___x_1365_, 1);
lean_inc(v_snd_1366_);
lean_dec_ref(v___x_1365_);
v___x_1367_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1356_, v_snd_1366_);
lean_dec_ref(v___x_1356_);
v_snd_1368_ = lean_ctor_get(v___x_1367_, 1);
lean_inc(v_snd_1368_);
lean_dec_ref(v___x_1367_);
lean_inc_ref(v_desc_1353_);
v___x_1369_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1369_, 0, v_desc_1353_);
v___x_1370_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1333_, v_inst_1334_, v___x_1369_, v___x_1358_, v_snd_1368_);
v_snd_1371_ = lean_ctor_get(v___x_1370_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v___x_1370_, 0);
lean_dec(v_unused_1380_);
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snd_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1335_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1375_);
v___x_1377_ = v___x_1373_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_snd_1371_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1383_, lean_object* v_inst_1384_, lean_object* v___x_1385_, lean_object* v_a_1386_, lean_object* v_x_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1383_, v_inst_1384_, v___x_1385_, v_a_1386_, v_x_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec_ref(v_a_1386_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_x_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
switch(lean_obj_tag(v_x_1395_))
{
case 0:
{
lean_object* v_contents_1399_; lean_object* v___x_1400_; lean_object* v___f_1401_; size_t v_sz_1402_; size_t v___x_1403_; lean_object* v___x_12963__overap_1404_; lean_object* v___x_1405_; lean_object* v_snd_1406_; lean_object* v___x_1407_; 
lean_dec_ref(v_inst_1394_);
v_contents_1399_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_contents_1399_);
lean_dec_ref(v_x_1395_);
v___x_1400_ = lean_box(0);
v___f_1401_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0), 7, 2);
lean_closure_set(v___f_1401_, 0, v_inst_1393_);
lean_closure_set(v___f_1401_, 1, v___x_1400_);
v_sz_1402_ = lean_array_size(v_contents_1399_);
v___x_1403_ = ((size_t)0ULL);
v___x_12963__overap_1404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1398_, v_contents_1399_, v___f_1401_, v_sz_1402_, v___x_1403_, v___x_1400_);
v___x_1405_ = lean_apply_2(v___x_12963__overap_1404_, v_a_1396_, v_a_1397_);
v_snd_1406_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_snd_1406_);
lean_dec_ref(v___x_1405_);
v___x_1407_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1406_);
return v___x_1407_;
}
case 1:
{
lean_object* v_content_1408_; lean_object* v___y_1410_; lean_object* v___y_1411_; uint8_t v___y_1419_; lean_object* v_currentBlock_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
lean_dec_ref(v_inst_1394_);
lean_dec_ref(v_inst_1393_);
v_content_1408_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_content_1408_);
lean_dec_ref(v_x_1395_);
v_currentBlock_1423_ = lean_ctor_get(v_a_1397_, 1);
v___x_1424_ = lean_string_utf8_byte_size(v_currentBlock_1423_);
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = lean_nat_dec_eq(v___x_1424_, v___x_1425_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1427_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1428_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2);
v___x_1429_ = lean_nat_dec_le(v___x_1428_, v___x_1424_);
if (v___x_1429_ == 0)
{
v___y_1419_ = v___x_1426_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = lean_nat_sub(v___x_1424_, v___x_1428_);
v___x_1431_ = lean_string_memcmp(v_currentBlock_1423_, v___x_1427_, v___x_1430_, v___x_1425_, v___x_1428_);
lean_dec(v___x_1430_);
v___y_1419_ = v___x_1431_;
goto v___jp_1418_;
}
}
else
{
v___y_1419_ = v___x_1426_;
goto v___jp_1418_;
}
v___jp_1409_:
{
lean_object* v_linePrefix_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v_snd_1416_; lean_object* v___x_1417_; 
v_linePrefix_1412_ = lean_ctor_get(v___y_1410_, 0);
lean_inc_ref(v_linePrefix_1412_);
lean_dec_ref(v___y_1410_);
v___x_1413_ = lean_string_length(v_linePrefix_1412_);
lean_dec_ref(v_linePrefix_1412_);
v___x_1414_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v___x_1413_, v_content_1408_);
lean_dec_ref(v_content_1408_);
v___x_1415_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1414_, v___y_1411_);
lean_dec_ref(v___x_1414_);
v_snd_1416_ = lean_ctor_get(v___x_1415_, 1);
lean_inc(v_snd_1416_);
lean_dec_ref(v___x_1415_);
v___x_1417_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1416_);
return v___x_1417_;
}
v___jp_1418_:
{
if (v___y_1419_ == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v_snd_1422_; 
v___x_1420_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1421_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1420_, v_a_1397_);
v_snd_1422_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_snd_1422_);
lean_dec_ref(v___x_1421_);
v___y_1410_ = v_a_1396_;
v___y_1411_ = v_snd_1422_;
goto v___jp_1409_;
}
else
{
v___y_1410_ = v_a_1396_;
v___y_1411_ = v_a_1397_;
goto v___jp_1409_;
}
}
}
case 2:
{
lean_object* v_items_1432_; lean_object* v___x_1433_; lean_object* v___f_1434_; lean_object* v___f_1435_; size_t v_sz_1436_; size_t v___x_1437_; lean_object* v___x_13191__overap_1438_; lean_object* v___x_1439_; lean_object* v_snd_1440_; lean_object* v___x_1441_; 
v_items_1432_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_items_1432_);
lean_dec_ref(v_x_1395_);
v___x_1433_ = lean_box(0);
v___f_1434_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1), 8, 3);
lean_closure_set(v___f_1434_, 0, v_inst_1393_);
lean_closure_set(v___f_1434_, 1, v_inst_1394_);
lean_closure_set(v___f_1434_, 2, v___x_1433_);
v___f_1435_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0), 8, 3);
lean_closure_set(v___f_1435_, 0, v___x_1398_);
lean_closure_set(v___f_1435_, 1, v___f_1434_);
lean_closure_set(v___f_1435_, 2, v___x_1433_);
v_sz_1436_ = lean_array_size(v_items_1432_);
v___x_1437_ = ((size_t)0ULL);
v___x_13191__overap_1438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1398_, v_items_1432_, v___f_1435_, v_sz_1436_, v___x_1437_, v___x_1433_);
v___x_1439_ = lean_apply_2(v___x_13191__overap_1438_, v_a_1396_, v_a_1397_);
v_snd_1440_ = lean_ctor_get(v___x_1439_, 1);
lean_inc(v_snd_1440_);
lean_dec_ref(v___x_1439_);
v___x_1441_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1440_);
return v___x_1441_;
}
case 3:
{
lean_object* v_start_1442_; lean_object* v_items_1443_; lean_object* v___x_1444_; lean_object* v___f_1445_; lean_object* v___y_1447_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v_start_1442_ = lean_ctor_get(v_x_1395_, 0);
lean_inc(v_start_1442_);
v_items_1443_ = lean_ctor_get(v_x_1395_, 1);
lean_inc_ref(v_items_1443_);
lean_dec_ref(v_x_1395_);
v___x_1444_ = lean_unsigned_to_nat(1u);
v___f_1445_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 9, 4);
lean_closure_set(v___f_1445_, 0, v_inst_1393_);
lean_closure_set(v___f_1445_, 1, v_inst_1394_);
lean_closure_set(v___f_1445_, 2, v___x_1398_);
lean_closure_set(v___f_1445_, 3, v___x_1444_);
v___x_1454_ = l_Int_toNat(v_start_1442_);
lean_dec(v_start_1442_);
v___x_1455_ = lean_nat_dec_le(v___x_1444_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_dec(v___x_1454_);
v___y_1447_ = v___x_1444_;
goto v___jp_1446_;
}
else
{
v___y_1447_ = v___x_1454_;
goto v___jp_1446_;
}
v___jp_1446_:
{
size_t v_sz_1448_; size_t v___x_1449_; lean_object* v___x_13285__overap_1450_; lean_object* v___x_1451_; lean_object* v_snd_1452_; lean_object* v___x_1453_; 
v_sz_1448_ = lean_array_size(v_items_1443_);
v___x_1449_ = ((size_t)0ULL);
v___x_13285__overap_1450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1398_, v_items_1443_, v___f_1445_, v_sz_1448_, v___x_1449_, v___y_1447_);
v___x_1451_ = lean_apply_2(v___x_13285__overap_1450_, v_a_1396_, v_a_1397_);
v_snd_1452_ = lean_ctor_get(v___x_1451_, 1);
lean_inc(v_snd_1452_);
lean_dec_ref(v___x_1451_);
v___x_1453_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1452_);
return v___x_1453_;
}
}
case 4:
{
lean_object* v_items_1456_; lean_object* v___x_1457_; lean_object* v___f_1458_; size_t v_sz_1459_; size_t v___x_1460_; lean_object* v___x_13388__overap_1461_; lean_object* v___x_1462_; lean_object* v_snd_1463_; lean_object* v___x_1464_; 
v_items_1456_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_items_1456_);
lean_dec_ref(v_x_1395_);
v___x_1457_ = lean_box(0);
v___f_1458_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 8, 3);
lean_closure_set(v___f_1458_, 0, v_inst_1393_);
lean_closure_set(v___f_1458_, 1, v_inst_1394_);
lean_closure_set(v___f_1458_, 2, v___x_1457_);
v_sz_1459_ = lean_array_size(v_items_1456_);
v___x_1460_ = ((size_t)0ULL);
v___x_13388__overap_1461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1398_, v_items_1456_, v___f_1458_, v_sz_1459_, v___x_1460_, v___x_1457_);
v___x_1462_ = lean_apply_2(v___x_13388__overap_1461_, v_a_1396_, v_a_1397_);
v_snd_1463_ = lean_ctor_get(v___x_1462_, 1);
lean_inc(v_snd_1463_);
lean_dec_ref(v___x_1462_);
v___x_1464_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1463_);
return v___x_1464_;
}
case 5:
{
lean_object* v_items_1465_; uint8_t v_inEmph_1466_; uint8_t v_inBold_1467_; uint8_t v_inLink_1468_; lean_object* v_linePrefix_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1486_; 
v_items_1465_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_items_1465_);
lean_dec_ref(v_x_1395_);
v_inEmph_1466_ = lean_ctor_get_uint8(v_a_1396_, sizeof(void*)*1);
v_inBold_1467_ = lean_ctor_get_uint8(v_a_1396_, sizeof(void*)*1 + 1);
v_inLink_1468_ = lean_ctor_get_uint8(v_a_1396_, sizeof(void*)*1 + 2);
v_linePrefix_1469_ = lean_ctor_get(v_a_1396_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_a_1396_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1471_ = v_a_1396_;
v_isShared_1472_ = v_isSharedCheck_1486_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_linePrefix_1469_);
lean_dec(v_a_1396_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1486_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___f_1474_; size_t v_sz_1475_; size_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1473_ = lean_box(0);
v___f_1474_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1), 8, 3);
lean_closure_set(v___f_1474_, 0, v_inst_1393_);
lean_closure_set(v___f_1474_, 1, v_inst_1394_);
lean_closure_set(v___f_1474_, 2, v___x_1473_);
v_sz_1475_ = lean_array_size(v_items_1465_);
v___x_1476_ = ((size_t)0ULL);
v___x_1477_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_1478_ = lean_string_append(v_linePrefix_1469_, v___x_1477_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1478_);
v___x_1480_ = v___x_1471_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1478_);
lean_ctor_set_uint8(v_reuseFailAlloc_1485_, sizeof(void*)*1, v_inEmph_1466_);
lean_ctor_set_uint8(v_reuseFailAlloc_1485_, sizeof(void*)*1 + 1, v_inBold_1467_);
lean_ctor_set_uint8(v_reuseFailAlloc_1485_, sizeof(void*)*1 + 2, v_inLink_1468_);
v___x_1480_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_13494__overap_1481_; lean_object* v___x_1482_; lean_object* v_snd_1483_; lean_object* v___x_1484_; 
v___x_13494__overap_1481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1398_, v_items_1465_, v___f_1474_, v_sz_1475_, v___x_1476_, v___x_1473_);
v___x_1482_ = lean_apply_2(v___x_13494__overap_1481_, v___x_1480_, v_a_1397_);
v_snd_1483_ = lean_ctor_get(v___x_1482_, 1);
lean_inc(v_snd_1483_);
lean_dec_ref(v___x_1482_);
v___x_1484_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1483_);
return v___x_1484_;
}
}
}
case 6:
{
lean_object* v_content_1487_; lean_object* v___x_1488_; lean_object* v___f_1489_; size_t v_sz_1490_; size_t v___x_1491_; lean_object* v___x_13530__overap_1492_; lean_object* v___x_1493_; lean_object* v_snd_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
v_content_1487_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_content_1487_);
lean_dec_ref(v_x_1395_);
v___x_1488_ = lean_box(0);
v___f_1489_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1), 8, 3);
lean_closure_set(v___f_1489_, 0, v_inst_1393_);
lean_closure_set(v___f_1489_, 1, v_inst_1394_);
lean_closure_set(v___f_1489_, 2, v___x_1488_);
v_sz_1490_ = lean_array_size(v_content_1487_);
v___x_1491_ = ((size_t)0ULL);
v___x_13530__overap_1492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1398_, v_content_1487_, v___f_1489_, v_sz_1490_, v___x_1491_, v___x_1488_);
v___x_1493_ = lean_apply_2(v___x_13530__overap_1492_, v_a_1396_, v_a_1397_);
v_snd_1494_ = lean_ctor_get(v___x_1493_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v___x_1493_, 0);
lean_dec(v_unused_1502_);
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snd_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1488_);
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_snd_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
default: 
{
lean_object* v_container_1503_; lean_object* v_content_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_container_1503_ = lean_ctor_get(v_x_1395_, 0);
lean_inc(v_container_1503_);
v_content_1504_ = lean_ctor_get(v_x_1395_, 1);
lean_inc_ref(v_content_1504_);
lean_dec_ref(v_x_1395_);
lean_inc_ref(v_inst_1393_);
v___x_1505_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown), 5, 2);
lean_closure_set(v___x_1505_, 0, lean_box(0));
lean_closure_set(v___x_1505_, 1, v_inst_1393_);
lean_inc_ref(v_inst_1394_);
v___x_1506_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg), 5, 2);
lean_closure_set(v___x_1506_, 0, v_inst_1393_);
lean_closure_set(v___x_1506_, 1, v_inst_1394_);
v___x_1507_ = lean_apply_6(v_inst_1394_, v___x_1505_, v___x_1506_, v_container_1503_, v_content_1504_, v_a_1396_, v_a_1397_);
return v___x_1507_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v___x_1510_, lean_object* v_a_1511_, lean_object* v_x_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v_snd_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1525_; 
v___x_1516_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1508_, v_inst_1509_, v_a_1511_, v___y_1514_, v___y_1515_);
v_snd_1517_ = lean_ctor_get(v___x_1516_, 1);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; 
v_unused_1526_ = lean_ctor_get(v___x_1516_, 0);
lean_dec(v_unused_1526_);
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_snd_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1510_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1521_);
v___x_1523_ = v___x_1519_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_snd_1517_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1527_, lean_object* v_b_1528_, lean_object* v_inst_1529_, lean_object* v_inst_1530_, lean_object* v_x_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1529_, v_inst_1530_, v_x_1531_, v_a_1532_, v_a_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1535_, lean_object* v_inst_1536_, lean_object* v_block_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1535_, v_inst_1536_, v_block_1537_, v_a_1538_, v_a_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1541_, lean_object* v_b_1542_, lean_object* v_inst_1543_, lean_object* v_inst_1544_, lean_object* v_block_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1543_, v_inst_1544_, v_block_1545_, v_a_1546_, v_a_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_1549_, lean_object* v_inst_1550_, lean_object* v_block_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1549_, v_inst_1550_, v_block_1551_, v___y_1552_, v___y_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1555_, lean_object* v_inst_1556_){
_start:
{
lean_object* v___f_1557_; 
v___f_1557_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1557_, 0, v_inst_1555_);
lean_closure_set(v___f_1557_, 1, v_inst_1556_);
return v___f_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1558_, lean_object* v_b_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_){
_start:
{
lean_object* v___f_1562_; 
v___f_1562_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1562_, 0, v_inst_1560_);
lean_closure_set(v___f_1562_, 1, v_inst_1561_);
return v___f_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0(uint32_t v___x_1563_, lean_object* v_s_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_string_push(v_s_1564_, v___x_1563_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0___boxed(lean_object* v___x_1566_, lean_object* v_s_1567_){
_start:
{
uint32_t v___x_4130__boxed_1568_; lean_object* v_res_1569_; 
v___x_4130__boxed_1568_ = lean_unbox_uint32(v___x_1566_);
lean_dec(v___x_1566_);
v_res_1569_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0(v___x_4130__boxed_1568_, v_s_1567_);
return v_res_1569_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = 35;
v___x_1571_ = lean_box_uint32(v___x_1570_);
return v___x_1571_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___f_1573_; 
v___x_1572_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1573_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1573_, 0, v___x_1572_);
return v___f_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v___x_1576_, lean_object* v___x_1577_, lean_object* v_a_1578_, lean_object* v_x_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3(v_inst_1574_, v_inst_1575_, v___x_1576_, v___x_1577_, v_a_1578_, v_x_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___x_1576_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_level_1586_, lean_object* v_part_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___f_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v_snd_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v_snd_1600_; lean_object* v_title_1601_; lean_object* v_content_1602_; lean_object* v_subParts_1603_; lean_object* v___x_1604_; lean_object* v___f_1605_; size_t v_sz_1606_; size_t v___x_1607_; lean_object* v___x_3968__overap_1608_; lean_object* v___x_1609_; lean_object* v_snd_1610_; lean_object* v___x_1611_; lean_object* v_snd_1612_; lean_object* v___f_1613_; size_t v_sz_1614_; lean_object* v___x_3986__overap_1615_; lean_object* v___x_1616_; lean_object* v_snd_1617_; lean_object* v___x_1618_; lean_object* v_snd_1619_; lean_object* v___f_1620_; size_t v_sz_1621_; lean_object* v___x_4004__overap_1622_; lean_object* v___x_1623_; lean_object* v_snd_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
v___x_1590_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
v___x_1591_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___f_1592_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0);
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_add(v_level_1586_, v___x_1593_);
lean_inc(v___x_1594_);
v___x_1595_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1592_, v___x_1594_, v___x_1591_);
v___x_1596_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1595_, v_a_1589_);
lean_dec(v___x_1595_);
v_snd_1597_ = lean_ctor_get(v___x_1596_, 1);
lean_inc(v_snd_1597_);
lean_dec_ref(v___x_1596_);
v___x_1598_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_1599_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1598_, v_snd_1597_);
v_snd_1600_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_snd_1600_);
lean_dec_ref(v___x_1599_);
v_title_1601_ = lean_ctor_get(v_part_1587_, 0);
lean_inc_ref(v_title_1601_);
v_content_1602_ = lean_ctor_get(v_part_1587_, 3);
lean_inc_ref(v_content_1602_);
v_subParts_1603_ = lean_ctor_get(v_part_1587_, 4);
lean_inc_ref(v_subParts_1603_);
lean_dec_ref(v_part_1587_);
v___x_1604_ = lean_box(0);
lean_inc_ref(v_inst_1584_);
v___f_1605_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0), 7, 2);
lean_closure_set(v___f_1605_, 0, v_inst_1584_);
lean_closure_set(v___f_1605_, 1, v___x_1604_);
v_sz_1606_ = lean_array_size(v_title_1601_);
v___x_1607_ = ((size_t)0ULL);
v___x_3968__overap_1608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1590_, v_title_1601_, v___f_1605_, v_sz_1606_, v___x_1607_, v___x_1604_);
lean_inc_ref(v_a_1588_);
v___x_1609_ = lean_apply_2(v___x_3968__overap_1608_, v_a_1588_, v_snd_1600_);
v_snd_1610_ = lean_ctor_get(v___x_1609_, 1);
lean_inc(v_snd_1610_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1610_);
v_snd_1612_ = lean_ctor_get(v___x_1611_, 1);
lean_inc(v_snd_1612_);
lean_dec_ref(v___x_1611_);
lean_inc_ref(v_inst_1585_);
lean_inc_ref(v_inst_1584_);
v___f_1613_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1), 8, 3);
lean_closure_set(v___f_1613_, 0, v_inst_1584_);
lean_closure_set(v___f_1613_, 1, v_inst_1585_);
lean_closure_set(v___f_1613_, 2, v___x_1604_);
v_sz_1614_ = lean_array_size(v_content_1602_);
v___x_3986__overap_1615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1590_, v_content_1602_, v___f_1613_, v_sz_1614_, v___x_1607_, v___x_1604_);
lean_inc_ref(v_a_1588_);
v___x_1616_ = lean_apply_2(v___x_3986__overap_1615_, v_a_1588_, v_snd_1612_);
v_snd_1617_ = lean_ctor_get(v___x_1616_, 1);
lean_inc(v_snd_1617_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1617_);
v_snd_1619_ = lean_ctor_get(v___x_1618_, 1);
lean_inc(v_snd_1619_);
lean_dec_ref(v___x_1618_);
v___f_1620_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3___boxed), 9, 4);
lean_closure_set(v___f_1620_, 0, v_inst_1584_);
lean_closure_set(v___f_1620_, 1, v_inst_1585_);
lean_closure_set(v___f_1620_, 2, v___x_1594_);
lean_closure_set(v___f_1620_, 3, v___x_1604_);
v_sz_1621_ = lean_array_size(v_subParts_1603_);
v___x_4004__overap_1622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1590_, v_subParts_1603_, v___f_1620_, v_sz_1621_, v___x_1607_, v___x_1604_);
v___x_1623_ = lean_apply_2(v___x_4004__overap_1622_, v_a_1588_, v_snd_1619_);
v_snd_1624_ = lean_ctor_get(v___x_1623_, 1);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; 
v_unused_1632_ = lean_ctor_get(v___x_1623_, 0);
lean_dec(v_unused_1632_);
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_snd_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1604_);
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_snd_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3(lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v___x_1635_, lean_object* v___x_1636_, lean_object* v_a_1637_, lean_object* v_x_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v___x_1642_; lean_object* v_snd_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1651_; 
v___x_1642_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1633_, v_inst_1634_, v___x_1635_, v_a_1637_, v___y_1640_, v___y_1641_);
v_snd_1643_ = lean_ctor_get(v___x_1642_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; 
v_unused_1652_ = lean_ctor_get(v___x_1642_, 0);
lean_dec(v_unused_1652_);
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_snd_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1636_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1647_);
v___x_1649_ = v___x_1645_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_snd_1643_);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_level_1655_, lean_object* v_part_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1653_, v_inst_1654_, v_level_1655_, v_part_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_level_1655_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown(lean_object* v_i_1660_, lean_object* v_b_1661_, lean_object* v_p_1662_, lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_level_1665_, lean_object* v_part_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1663_, v_inst_1664_, v_level_1665_, v_part_1666_, v_a_1667_, v_a_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___boxed(lean_object* v_i_1670_, lean_object* v_b_1671_, lean_object* v_p_1672_, lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_level_1675_, lean_object* v_part_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown(v_i_1670_, v_b_1671_, v_p_1672_, v_inst_1673_, v_inst_1674_, v_level_1675_, v_part_1676_, v_a_1677_, v_a_1678_);
lean_dec(v_level_1675_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1680_, lean_object* v_inst_1681_, lean_object* v_part_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = lean_unsigned_to_nat(0u);
v___x_1686_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1680_, v_inst_1681_, v___x_1685_, v_part_1682_, v_a_1683_, v_a_1684_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1687_, lean_object* v_b_1688_, lean_object* v_p_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_part_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1690_, v_inst_1691_, v_part_1692_, v_a_1693_, v_a_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_1696_, lean_object* v_inst_1697_, lean_object* v_part_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1696_, v_inst_1697_, v_part_1698_, v___y_1699_, v___y_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1702_, lean_object* v_inst_1703_){
_start:
{
lean_object* v___f_1704_; 
v___f_1704_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1704_, 0, v_inst_1702_);
lean_closure_set(v___f_1704_, 1, v_inst_1703_);
return v___f_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1705_, lean_object* v_b_1706_, lean_object* v_p_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_){
_start:
{
lean_object* v___f_1710_; 
v___f_1710_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1710_, 0, v_inst_1708_);
lean_closure_set(v___f_1710_, 1, v_inst_1709_);
return v___f_1710_;
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
