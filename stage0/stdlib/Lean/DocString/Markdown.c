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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_Inline_empty(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_465_, lean_object* v_curr_466_){
_start:
{
lean_object* v_str_467_; lean_object* v_startInclusive_468_; lean_object* v_endExclusive_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___y_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_str_467_ = lean_ctor_get(v_s_465_, 0);
v_startInclusive_468_ = lean_ctor_get(v_s_465_, 1);
v_endExclusive_469_ = lean_ctor_get(v_s_465_, 2);
v___x_470_ = lean_nat_add(v_startInclusive_468_, v_curr_466_);
lean_inc(v_endExclusive_469_);
lean_inc(v___x_470_);
lean_inc_ref(v_str_467_);
v___x_471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_471_, 0, v_str_467_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
lean_ctor_set(v___x_471_, 2, v_endExclusive_469_);
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_nat_sub(v_endExclusive_469_, v___x_470_);
v___x_482_ = lean_nat_dec_eq(v___x_480_, v___x_481_);
lean_dec(v___x_481_);
if (v___x_482_ == 0)
{
uint32_t v___x_483_; uint8_t v___y_485_; uint32_t v___x_490_; uint8_t v___x_491_; 
v___x_483_ = lean_string_utf8_get_fast(v_str_467_, v___x_470_);
v___x_490_ = 32;
v___x_491_ = lean_uint32_dec_eq(v___x_483_, v___x_490_);
if (v___x_491_ == 0)
{
uint32_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = 9;
v___x_493_ = lean_uint32_dec_eq(v___x_483_, v___x_492_);
v___y_485_ = v___x_493_;
goto v___jp_484_;
}
else
{
v___y_485_ = v___x_491_;
goto v___jp_484_;
}
v___jp_484_:
{
if (v___y_485_ == 0)
{
uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = 13;
v___x_487_ = lean_uint32_dec_eq(v___x_483_, v___x_486_);
if (v___x_487_ == 0)
{
uint32_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 10;
v___x_489_ = lean_uint32_dec_eq(v___x_483_, v___x_488_);
v___y_479_ = v___x_489_;
goto v___jp_478_;
}
else
{
v___y_479_ = v___x_487_;
goto v___jp_478_;
}
}
else
{
goto v___jp_472_;
}
}
}
else
{
lean_dec(v___x_470_);
lean_dec(v_curr_466_);
return v___x_471_;
}
v___jp_472_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_473_ = lean_string_utf8_next_fast(v_str_467_, v___x_470_);
v___x_474_ = lean_nat_sub(v___x_473_, v___x_470_);
lean_dec(v___x_470_);
v___x_475_ = lean_nat_add(v_curr_466_, v___x_474_);
lean_dec(v___x_474_);
v___x_476_ = lean_nat_dec_lt(v_curr_466_, v___x_475_);
lean_dec(v_curr_466_);
if (v___x_476_ == 0)
{
lean_dec(v___x_475_);
return v___x_471_;
}
else
{
lean_dec_ref(v___x_471_);
v_curr_466_ = v___x_475_;
goto _start;
}
}
v___jp_478_:
{
if (v___y_479_ == 0)
{
lean_dec(v___x_470_);
lean_dec(v_curr_466_);
return v___x_471_;
}
else
{
goto v___jp_472_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object* v_s_494_, lean_object* v_curr_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_494_, v_curr_495_);
lean_dec_ref(v_s_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__1(lean_object* v_s_497_, lean_object* v_curr_498_){
_start:
{
lean_object* v_str_499_; lean_object* v_startInclusive_500_; lean_object* v_endExclusive_501_; lean_object* v___x_502_; uint8_t v___y_520_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_str_499_ = lean_ctor_get(v_s_497_, 0);
v_startInclusive_500_ = lean_ctor_get(v_s_497_, 1);
v_endExclusive_501_ = lean_ctor_get(v_s_497_, 2);
v___x_502_ = lean_nat_add(v_startInclusive_500_, v_curr_498_);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_nat_sub(v_endExclusive_501_, v___x_502_);
v___x_533_ = lean_nat_dec_eq(v___x_531_, v___x_532_);
lean_dec(v___x_532_);
if (v___x_533_ == 0)
{
uint32_t v___x_534_; uint8_t v___y_536_; uint32_t v___x_541_; uint8_t v___x_542_; 
v___x_534_ = lean_string_utf8_get_fast(v_str_499_, v___x_502_);
v___x_541_ = 32;
v___x_542_ = lean_uint32_dec_eq(v___x_534_, v___x_541_);
if (v___x_542_ == 0)
{
uint32_t v___x_543_; uint8_t v___x_544_; 
v___x_543_ = 9;
v___x_544_ = lean_uint32_dec_eq(v___x_534_, v___x_543_);
v___y_536_ = v___x_544_;
goto v___jp_535_;
}
else
{
v___y_536_ = v___x_542_;
goto v___jp_535_;
}
v___jp_535_:
{
if (v___y_536_ == 0)
{
uint32_t v___x_537_; uint8_t v___x_538_; 
v___x_537_ = 13;
v___x_538_ = lean_uint32_dec_eq(v___x_534_, v___x_537_);
if (v___x_538_ == 0)
{
uint32_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = 10;
v___x_540_ = lean_uint32_dec_eq(v___x_534_, v___x_539_);
v___y_520_ = v___x_540_;
goto v___jp_519_;
}
else
{
v___y_520_ = v___x_538_;
goto v___jp_519_;
}
}
else
{
goto v___jp_503_;
}
}
}
else
{
lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_inc(v_startInclusive_500_);
lean_inc_ref(v_str_499_);
lean_dec(v_curr_498_);
v_isSharedCheck_551_ = !lean_is_exclusive(v_s_497_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; lean_object* v_unused_553_; lean_object* v_unused_554_; 
v_unused_552_ = lean_ctor_get(v_s_497_, 2);
lean_dec(v_unused_552_);
v_unused_553_ = lean_ctor_get(v_s_497_, 1);
lean_dec(v_unused_553_);
v_unused_554_ = lean_ctor_get(v_s_497_, 0);
lean_dec(v_unused_554_);
v___x_546_ = v_s_497_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_dec(v_s_497_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 2, v___x_502_);
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_str_499_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_startInclusive_500_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v___x_502_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
v___jp_503_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_504_ = lean_string_utf8_next_fast(v_str_499_, v___x_502_);
v___x_505_ = lean_nat_sub(v___x_504_, v___x_502_);
v___x_506_ = lean_nat_add(v_curr_498_, v___x_505_);
lean_dec(v___x_505_);
v___x_507_ = lean_nat_dec_lt(v_curr_498_, v___x_506_);
lean_dec(v_curr_498_);
if (v___x_507_ == 0)
{
lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_inc(v_startInclusive_500_);
lean_inc_ref(v_str_499_);
lean_dec(v___x_506_);
v_isSharedCheck_514_ = !lean_is_exclusive(v_s_497_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; lean_object* v_unused_516_; lean_object* v_unused_517_; 
v_unused_515_ = lean_ctor_get(v_s_497_, 2);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_s_497_, 1);
lean_dec(v_unused_516_);
v_unused_517_ = lean_ctor_get(v_s_497_, 0);
lean_dec(v_unused_517_);
v___x_509_ = v_s_497_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_dec(v_s_497_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 2, v___x_502_);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_str_499_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_startInclusive_500_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v___x_502_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_dec(v___x_502_);
v_curr_498_ = v___x_506_;
goto _start;
}
}
v___jp_519_:
{
if (v___y_520_ == 0)
{
lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_inc(v_startInclusive_500_);
lean_inc_ref(v_str_499_);
lean_dec(v_curr_498_);
v_isSharedCheck_527_ = !lean_is_exclusive(v_s_497_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; lean_object* v_unused_529_; lean_object* v_unused_530_; 
v_unused_528_ = lean_ctor_get(v_s_497_, 2);
lean_dec(v_unused_528_);
v_unused_529_ = lean_ctor_get(v_s_497_, 1);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_s_497_, 0);
lean_dec(v_unused_530_);
v___x_522_ = v_s_497_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_dec(v_s_497_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 2, v___x_502_);
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_str_499_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_startInclusive_500_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v___x_502_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
goto v___jp_503_;
}
}
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Doc_Inline_empty(lean_box(0));
return v___x_555_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_557_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___x_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object* v_a_559_){
_start:
{
if (lean_obj_tag(v_a_559_) == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
return v___x_560_;
}
else
{
lean_object* v_head_561_; 
v_head_561_ = lean_ctor_get(v_a_559_, 0);
lean_inc(v_head_561_);
switch(lean_obj_tag(v_head_561_))
{
case 0:
{
lean_object* v_tail_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_615_; 
v_tail_562_ = lean_ctor_get(v_a_559_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_a_559_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_a_559_, 0);
lean_dec(v_unused_616_);
v___x_564_ = v_a_559_;
v_isShared_565_ = v_isSharedCheck_615_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_tail_562_);
lean_dec(v_a_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_615_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_string_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_614_; 
v_string_566_ = lean_ctor_get(v_head_561_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_head_561_);
if (v_isSharedCheck_614_ == 0)
{
v___x_568_ = v_head_561_;
v_isShared_569_ = v_isSharedCheck_614_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_string_566_);
lean_dec(v_head_561_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_614_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v_startInclusive_574_; lean_object* v_endExclusive_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_string_utf8_byte_size(v_string_566_);
lean_inc_ref(v_string_566_);
v___x_572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_572_, 0, v_string_566_);
lean_ctor_set(v___x_572_, 1, v___x_570_);
lean_ctor_set(v___x_572_, 2, v___x_571_);
v___x_573_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_572_, v___x_570_);
v_startInclusive_574_ = lean_ctor_get(v___x_573_, 1);
lean_inc(v_startInclusive_574_);
v_endExclusive_575_ = lean_ctor_get(v___x_573_, 2);
lean_inc(v_endExclusive_575_);
lean_dec_ref(v___x_573_);
v___x_576_ = lean_nat_sub(v_endExclusive_575_, v_startInclusive_574_);
lean_dec(v_startInclusive_574_);
lean_dec(v_endExclusive_575_);
v___x_577_ = lean_nat_dec_eq(v___x_576_, v___x_570_);
lean_dec(v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v_str_579_; lean_object* v_startInclusive_580_; lean_object* v_endExclusive_581_; lean_object* v_s1_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_s2_585_; lean_object* v___x_587_; 
lean_inc_ref(v___x_572_);
v___x_578_ = l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__1(v___x_572_, v___x_570_);
v_str_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc_ref(v_str_579_);
v_startInclusive_580_ = lean_ctor_get(v___x_578_, 1);
lean_inc(v_startInclusive_580_);
v_endExclusive_581_ = lean_ctor_get(v___x_578_, 2);
lean_inc(v_endExclusive_581_);
lean_dec_ref(v___x_578_);
v_s1_582_ = lean_string_utf8_extract(v_str_579_, v_startInclusive_580_, v_endExclusive_581_);
lean_dec(v_endExclusive_581_);
lean_dec(v_startInclusive_580_);
lean_dec_ref(v_str_579_);
v___x_583_ = lean_string_length(v_s1_582_);
v___x_584_ = l_String_Slice_Pos_nextn(v___x_572_, v___x_570_, v___x_583_);
lean_dec_ref(v___x_572_);
v_s2_585_ = lean_string_utf8_extract(v_string_566_, v___x_584_, v___x_571_);
lean_dec(v___x_584_);
lean_dec_ref(v_string_566_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v_s2_585_);
v___x_587_ = v___x_568_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_s2_585_);
v___x_587_ = v_reuseFailAlloc_602_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_array_mk(v_tail_562_);
v___x_589_ = lean_array_get_size(v___x_588_);
v___x_590_ = lean_nat_dec_eq(v___x_589_, v___x_570_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_mk_empty_array_with_capacity(v___x_591_);
v___x_593_ = lean_array_push(v___x_592_, v___x_587_);
v___x_594_ = l_Array_append___redArg(v___x_593_, v___x_588_);
lean_dec_ref(v___x_588_);
v___x_595_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 0);
lean_ctor_set(v___x_564_, 1, v___x_595_);
lean_ctor_set(v___x_564_, 0, v_s1_582_);
v___x_597_ = v___x_564_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_s1_582_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
else
{
lean_object* v___x_600_; 
lean_dec_ref(v___x_588_);
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 0);
lean_ctor_set(v___x_564_, 1, v___x_587_);
lean_ctor_set(v___x_564_, 0, v_s1_582_);
v___x_600_ = v___x_564_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_s1_582_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___x_587_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v___x_603_; lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v___x_572_);
lean_del_object(v___x_568_);
lean_del_object(v___x_564_);
v___x_603_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_562_);
v_fst_604_ = lean_ctor_get(v___x_603_, 0);
v_snd_605_ = lean_ctor_get(v___x_603_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_613_ == 0)
{
v___x_607_ = v___x_603_;
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_snd_605_);
lean_inc(v_fst_604_);
lean_dec(v___x_603_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_string_append(v_string_566_, v_fst_604_);
lean_dec(v_fst_604_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_snd_605_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_617_; lean_object* v_content_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_tail_617_ = lean_ctor_get(v_a_559_, 1);
lean_inc(v_tail_617_);
lean_dec_ref(v_a_559_);
v_content_618_ = lean_ctor_get(v_head_561_, 0);
lean_inc_ref(v_content_618_);
lean_dec_ref(v_head_561_);
v___x_619_ = lean_array_to_list(v_content_618_);
v___x_620_ = l_List_appendTR___redArg(v___x_619_, v_tail_617_);
v_a_559_ = v___x_620_;
goto _start;
}
default: 
{
lean_object* v_tail_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_660_; 
v_tail_622_ = lean_ctor_get(v_a_559_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v_a_559_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v_a_559_, 0);
lean_dec(v_unused_661_);
v___x_624_ = v_a_559_;
v_isShared_625_ = v_isSharedCheck_660_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_tail_622_);
lean_dec(v_a_559_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_660_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_627_ = lean_array_mk(v_tail_622_);
if (lean_obj_tag(v_head_561_) == 9)
{
lean_object* v_content_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_content_628_ = lean_ctor_get(v_head_561_, 0);
v___x_629_ = lean_array_get_size(v_content_628_);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_nat_dec_eq(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = lean_array_get_size(v___x_627_);
v___x_633_ = lean_nat_dec_eq(v___x_632_, v___x_630_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
lean_inc_ref(v_content_628_);
lean_dec_ref(v_head_561_);
v___x_634_ = l_Array_append___redArg(v_content_628_, v___x_627_);
lean_dec_ref(v___x_627_);
v___x_635_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 0);
lean_ctor_set(v___x_624_, 1, v___x_635_);
lean_ctor_set(v___x_624_, 0, v___x_626_);
v___x_637_ = v___x_624_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
else
{
lean_object* v___x_640_; 
lean_dec_ref(v___x_627_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 0);
lean_ctor_set(v___x_624_, 1, v_head_561_);
lean_ctor_set(v___x_624_, 0, v___x_626_);
v___x_640_ = v___x_624_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_head_561_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_644_; 
lean_dec_ref(v_head_561_);
v___x_642_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_627_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 0);
lean_ctor_set(v___x_624_, 1, v___x_642_);
lean_ctor_set(v___x_624_, 0, v___x_626_);
v___x_644_ = v___x_624_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_646_ = lean_array_get_size(v___x_627_);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_nat_dec_eq(v___x_646_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_mk_empty_array_with_capacity(v___x_649_);
v___x_651_ = lean_array_push(v___x_650_, v_head_561_);
v___x_652_ = l_Array_append___redArg(v___x_651_, v___x_627_);
lean_dec_ref(v___x_627_);
v___x_653_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 0);
lean_ctor_set(v___x_624_, 1, v___x_653_);
lean_ctor_set(v___x_624_, 0, v___x_626_);
v___x_655_ = v___x_624_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
else
{
lean_object* v___x_658_; 
lean_dec_ref(v___x_627_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 0);
lean_ctor_set(v___x_624_, 1, v_head_561_);
lean_ctor_set(v___x_624_, 0, v___x_626_);
v___x_658_ = v___x_624_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_head_561_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_box(0);
v___x_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_667_, 0, v_inline_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_669_, lean_object* v_inline_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_672_, lean_object* v_curr_673_){
_start:
{
lean_object* v_str_674_; lean_object* v_startInclusive_675_; lean_object* v_endExclusive_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_str_674_ = lean_ctor_get(v_s_672_, 0);
v_startInclusive_675_ = lean_ctor_get(v_s_672_, 1);
v_endExclusive_676_ = lean_ctor_get(v_s_672_, 2);
v___x_677_ = lean_nat_add(v_startInclusive_675_, v_curr_673_);
v___x_678_ = lean_nat_sub(v___x_677_, v_startInclusive_675_);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_nat_dec_eq(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___y_699_; lean_object* v___x_710_; uint32_t v___x_711_; uint8_t v___y_713_; uint32_t v___x_718_; uint8_t v___x_719_; 
lean_inc(v___x_677_);
lean_inc(v_startInclusive_675_);
lean_inc_ref(v_str_674_);
v___x_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_681_, 0, v_str_674_);
lean_ctor_set(v___x_681_, 1, v_startInclusive_675_);
lean_ctor_set(v___x_681_, 2, v___x_677_);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_sub(v___x_678_, v___x_682_);
lean_dec(v___x_678_);
v___x_684_ = l_String_Slice_posLE(v___x_681_, v___x_683_);
lean_dec_ref(v___x_681_);
v___x_710_ = lean_nat_add(v_startInclusive_675_, v___x_684_);
v___x_711_ = lean_string_utf8_get_fast(v_str_674_, v___x_710_);
lean_dec(v___x_710_);
v___x_718_ = 32;
v___x_719_ = lean_uint32_dec_eq(v___x_711_, v___x_718_);
if (v___x_719_ == 0)
{
uint32_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = 9;
v___x_721_ = lean_uint32_dec_eq(v___x_711_, v___x_720_);
v___y_713_ = v___x_721_;
goto v___jp_712_;
}
else
{
v___y_713_ = v___x_719_;
goto v___jp_712_;
}
v___jp_685_:
{
uint8_t v___x_686_; 
v___x_686_ = lean_nat_dec_lt(v___x_684_, v_curr_673_);
lean_dec(v_curr_673_);
if (v___x_686_ == 0)
{
lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_inc(v_endExclusive_676_);
lean_inc_ref(v_str_674_);
lean_dec(v___x_684_);
v_isSharedCheck_693_ = !lean_is_exclusive(v_s_672_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; lean_object* v_unused_695_; lean_object* v_unused_696_; 
v_unused_694_ = lean_ctor_get(v_s_672_, 2);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_s_672_, 1);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_s_672_, 0);
lean_dec(v_unused_696_);
v___x_688_ = v_s_672_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_dec(v_s_672_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_677_);
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_str_674_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_endExclusive_676_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_dec(v___x_677_);
v_curr_673_ = v___x_684_;
goto _start;
}
}
v___jp_698_:
{
if (v___y_699_ == 0)
{
lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_inc(v_endExclusive_676_);
lean_inc_ref(v_str_674_);
lean_dec(v___x_684_);
lean_dec(v_curr_673_);
v_isSharedCheck_706_ = !lean_is_exclusive(v_s_672_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; 
v_unused_707_ = lean_ctor_get(v_s_672_, 2);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_s_672_, 1);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_s_672_, 0);
lean_dec(v_unused_709_);
v___x_701_ = v_s_672_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_dec(v_s_672_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_677_);
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_str_674_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_endExclusive_676_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
goto v___jp_685_;
}
}
v___jp_712_:
{
if (v___y_713_ == 0)
{
uint32_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = 13;
v___x_715_ = lean_uint32_dec_eq(v___x_711_, v___x_714_);
if (v___x_715_ == 0)
{
uint32_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = 10;
v___x_717_ = lean_uint32_dec_eq(v___x_711_, v___x_716_);
v___y_699_ = v___x_717_;
goto v___jp_698_;
}
else
{
v___y_699_ = v___x_715_;
goto v___jp_698_;
}
}
else
{
goto v___jp_685_;
}
}
}
else
{
lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_inc(v_endExclusive_676_);
lean_inc_ref(v_str_674_);
lean_dec(v___x_678_);
lean_dec(v_curr_673_);
v_isSharedCheck_728_ = !lean_is_exclusive(v_s_672_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; lean_object* v_unused_730_; lean_object* v_unused_731_; 
v_unused_729_ = lean_ctor_get(v_s_672_, 2);
lean_dec(v_unused_729_);
v_unused_730_ = lean_ctor_get(v_s_672_, 1);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_s_672_, 0);
lean_dec(v_unused_731_);
v___x_723_ = v_s_672_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_dec(v_s_672_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_677_);
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_str_674_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_endExclusive_676_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_733_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_732_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_a_735_){
_start:
{
lean_object* v___y_737_; 
if (lean_obj_tag(v_a_735_) == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_740_;
}
else
{
lean_object* v_head_741_; 
v_head_741_ = lean_ctor_get(v_a_735_, 0);
lean_inc(v_head_741_);
switch(lean_obj_tag(v_head_741_))
{
case 0:
{
lean_object* v_tail_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_793_; 
v_tail_742_ = lean_ctor_get(v_a_735_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_a_735_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_a_735_, 0);
lean_dec(v_unused_794_);
v___x_744_ = v_a_735_;
v_isShared_745_ = v_isSharedCheck_793_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_tail_742_);
lean_dec(v_a_735_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_793_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_string_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_792_; 
v_string_746_ = lean_ctor_get(v_head_741_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v_head_741_);
if (v_isSharedCheck_792_ == 0)
{
v___x_748_ = v_head_741_;
v_isShared_749_ = v_isSharedCheck_792_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_string_746_);
lean_dec(v_head_741_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_792_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_startInclusive_754_; lean_object* v_endExclusive_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = lean_string_utf8_byte_size(v_string_746_);
lean_inc_ref(v_string_746_);
v___x_752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_752_, 0, v_string_746_);
lean_ctor_set(v___x_752_, 1, v___x_750_);
lean_ctor_set(v___x_752_, 2, v___x_751_);
v___x_753_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_752_, v___x_750_);
v_startInclusive_754_ = lean_ctor_get(v___x_753_, 1);
lean_inc(v_startInclusive_754_);
v_endExclusive_755_ = lean_ctor_get(v___x_753_, 2);
lean_inc(v_endExclusive_755_);
lean_dec_ref(v___x_753_);
v___x_756_ = lean_nat_sub(v_endExclusive_755_, v_startInclusive_754_);
lean_dec(v_startInclusive_754_);
lean_dec(v_endExclusive_755_);
v___x_757_ = lean_nat_dec_eq(v___x_756_, v___x_750_);
lean_dec(v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v_str_759_; lean_object* v_startInclusive_760_; lean_object* v_endExclusive_761_; lean_object* v_s1_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v_s2_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
lean_inc_ref(v___x_752_);
v___x_758_ = l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_752_, v___x_751_);
v_str_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc_ref(v_str_759_);
v_startInclusive_760_ = lean_ctor_get(v___x_758_, 1);
lean_inc(v_startInclusive_760_);
v_endExclusive_761_ = lean_ctor_get(v___x_758_, 2);
lean_inc(v_endExclusive_761_);
lean_dec_ref(v___x_758_);
v_s1_762_ = lean_string_utf8_extract(v_str_759_, v_startInclusive_760_, v_endExclusive_761_);
lean_dec(v_endExclusive_761_);
lean_dec(v_startInclusive_760_);
lean_dec_ref(v_str_759_);
v___x_763_ = lean_string_length(v_s1_762_);
v___x_764_ = l_String_Slice_Pos_prevn(v___x_752_, v___x_751_, v___x_763_);
lean_dec_ref(v___x_752_);
v_s2_765_ = lean_string_utf8_extract(v_string_746_, v___x_750_, v___x_764_);
lean_dec(v___x_764_);
lean_dec_ref(v_string_746_);
v___x_766_ = lean_array_mk(v_tail_742_);
v___x_767_ = l_Array_reverse___redArg(v___x_766_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v_s2_765_);
v___x_769_ = v___x_748_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_s2_765_);
v___x_769_ = v_reuseFailAlloc_780_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = lean_array_get_size(v___x_767_);
v___x_771_ = lean_nat_dec_eq(v___x_770_, v___x_750_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_772_ = lean_array_push(v___x_767_, v___x_769_);
v___x_773_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 0);
lean_ctor_set(v___x_744_, 1, v_s1_762_);
lean_ctor_set(v___x_744_, 0, v___x_773_);
v___x_775_ = v___x_744_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_s1_762_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
else
{
lean_object* v___x_778_; 
lean_dec_ref(v___x_767_);
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 0);
lean_ctor_set(v___x_744_, 1, v_s1_762_);
lean_ctor_set(v___x_744_, 0, v___x_769_);
v___x_778_ = v___x_744_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_s1_762_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v___x_781_; lean_object* v_fst_782_; lean_object* v_snd_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v___x_752_);
lean_del_object(v___x_748_);
lean_del_object(v___x_744_);
v___x_781_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_tail_742_);
v_fst_782_ = lean_ctor_get(v___x_781_, 0);
v_snd_783_ = lean_ctor_get(v___x_781_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_791_ == 0)
{
v___x_785_ = v___x_781_;
v_isShared_786_ = v_isSharedCheck_791_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_snd_783_);
lean_inc(v_fst_782_);
lean_dec(v___x_781_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_791_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_string_append(v_snd_783_, v_string_746_);
lean_dec_ref(v_string_746_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v___x_787_);
v___x_789_ = v___x_785_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_fst_782_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_795_; lean_object* v_content_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_tail_795_ = lean_ctor_get(v_a_735_, 1);
lean_inc(v_tail_795_);
lean_dec_ref(v_a_735_);
v_content_796_ = lean_ctor_get(v_head_741_, 0);
lean_inc_ref(v_content_796_);
lean_dec_ref(v_head_741_);
v___x_797_ = l_Array_reverse___redArg(v_content_796_);
v___x_798_ = lean_array_to_list(v___x_797_);
v___x_799_ = l_List_appendTR___redArg(v___x_798_, v_tail_795_);
v_a_735_ = v___x_799_;
goto _start;
}
default: 
{
lean_object* v_tail_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_tail_801_ = lean_ctor_get(v_a_735_, 1);
lean_inc(v_tail_801_);
lean_dec_ref(v_a_735_);
v___x_802_ = lean_array_mk(v_tail_801_);
v___x_803_ = l_Array_reverse___redArg(v___x_802_);
v___x_804_ = lean_array_get_size(v___x_803_);
v___x_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = lean_nat_dec_eq(v___x_804_, v___x_805_);
if (v___x_806_ == 0)
{
if (lean_obj_tag(v_head_741_) == 9)
{
lean_object* v_content_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_content_807_ = lean_ctor_get(v_head_741_, 0);
lean_inc_ref(v_content_807_);
lean_dec_ref(v_head_741_);
v___x_808_ = lean_array_get_size(v_content_807_);
v___x_809_ = lean_nat_dec_eq(v___x_808_, v___x_805_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = l_Array_append___redArg(v___x_803_, v_content_807_);
lean_dec_ref(v_content_807_);
v___x_811_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___y_737_ = v___x_811_;
goto v___jp_736_;
}
else
{
lean_object* v___x_812_; 
lean_dec_ref(v_content_807_);
v___x_812_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_803_);
v___y_737_ = v___x_812_;
goto v___jp_736_;
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_array_push(v___x_803_, v_head_741_);
v___x_814_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___y_737_ = v___x_814_;
goto v___jp_736_;
}
}
else
{
lean_dec_ref(v___x_803_);
v___y_737_ = v_head_741_;
goto v___jp_736_;
}
}
}
}
v___jp_736_:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___y_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_815_, lean_object* v_a_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_a_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_box(0);
v___x_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_820_, 0, v_inline_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_822_, lean_object* v_inline_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_825_){
_start:
{
lean_object* v___x_826_; lean_object* v_fst_827_; lean_object* v_snd_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_836_; 
v___x_826_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_825_);
v_fst_827_ = lean_ctor_get(v___x_826_, 0);
v_snd_828_ = lean_ctor_get(v___x_826_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_836_ == 0)
{
v___x_830_ = v___x_826_;
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_snd_828_);
lean_inc(v_fst_827_);
lean_dec(v___x_826_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_828_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v___x_832_);
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_fst_827_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_837_, lean_object* v_inline_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_838_);
return v___x_839_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19));
v___x_886_ = l_ReaderT_instMonad___redArg(v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_895_ = l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0(lean_object* v_inst_897_, lean_object* v___x_898_, lean_object* v_a_899_, lean_object* v_x_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_904_; lean_object* v_snd_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_913_; 
v___x_904_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_897_, v_a_899_, v___y_902_, v___y_903_);
v_snd_905_ = lean_ctor_get(v___x_904_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v___x_904_, 0);
lean_dec(v_unused_914_);
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_913_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_snd_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_913_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_898_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_909_);
v___x_911_ = v___x_907_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_snd_905_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__1));
v___x_923_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
lean_ctor_set(v___x_924_, 2, v___x_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_926_, lean_object* v_x_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
switch(lean_obj_tag(v_x_927_))
{
case 0:
{
lean_object* v_string_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref(v_a_928_);
lean_dec_ref(v_inst_926_);
v_string_931_ = lean_ctor_get(v_x_927_, 0);
lean_inc_ref(v_string_931_);
lean_dec_ref(v_x_927_);
v___x_932_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_931_);
lean_dec_ref(v_string_931_);
v___x_933_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_932_, v_a_929_);
lean_dec_ref(v___x_932_);
return v___x_933_;
}
case 1:
{
lean_object* v_content_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_975_; 
v_content_934_ = lean_ctor_get(v_x_927_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v_x_927_);
if (v_isSharedCheck_975_ == 0)
{
v___x_936_ = v_x_927_;
v_isShared_937_ = v_isSharedCheck_975_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_content_934_);
lean_dec(v_x_927_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_975_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set_tag(v___x_936_, 9);
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_content_934_);
v___x_939_ = v_reuseFailAlloc_974_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; lean_object* v_snd_941_; lean_object* v_fst_942_; lean_object* v_fst_943_; lean_object* v_snd_944_; uint8_t v_inEmph_946_; uint8_t v_inBold_947_; uint8_t v_inLink_948_; lean_object* v_linePrefix_949_; lean_object* v___y_950_; lean_object* v___x_961_; uint8_t v_inEmph_962_; 
v___x_940_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_939_);
v_snd_941_ = lean_ctor_get(v___x_940_, 1);
lean_inc(v_snd_941_);
v_fst_942_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_fst_942_);
lean_dec_ref(v___x_940_);
v_fst_943_ = lean_ctor_get(v_snd_941_, 0);
lean_inc(v_fst_943_);
v_snd_944_ = lean_ctor_get(v_snd_941_, 1);
lean_inc(v_snd_944_);
lean_dec(v_snd_941_);
v___x_961_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_942_, v_a_929_);
lean_dec(v_fst_942_);
v_inEmph_962_ = lean_ctor_get_uint8(v_a_928_, sizeof(void*)*1);
if (v_inEmph_962_ == 0)
{
lean_object* v_snd_963_; uint8_t v_inBold_964_; uint8_t v_inLink_965_; lean_object* v_linePrefix_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_snd_969_; 
v_snd_963_ = lean_ctor_get(v___x_961_, 1);
lean_inc(v_snd_963_);
lean_dec_ref(v___x_961_);
v_inBold_964_ = lean_ctor_get_uint8(v_a_928_, sizeof(void*)*1 + 1);
v_inLink_965_ = lean_ctor_get_uint8(v_a_928_, sizeof(void*)*1 + 2);
v_linePrefix_966_ = lean_ctor_get(v_a_928_, 0);
lean_inc_ref(v_linePrefix_966_);
lean_dec_ref(v_a_928_);
v___x_967_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21));
v___x_968_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_967_, v_snd_963_);
v_snd_969_ = lean_ctor_get(v___x_968_, 1);
lean_inc(v_snd_969_);
lean_dec_ref(v___x_968_);
v_inEmph_946_ = v_inEmph_962_;
v_inBold_947_ = v_inBold_964_;
v_inLink_948_ = v_inLink_965_;
v_linePrefix_949_ = v_linePrefix_966_;
v___y_950_ = v_snd_969_;
goto v___jp_945_;
}
else
{
lean_object* v_snd_970_; uint8_t v_inBold_971_; uint8_t v_inLink_972_; lean_object* v_linePrefix_973_; 
v_snd_970_ = lean_ctor_get(v___x_961_, 1);
lean_inc(v_snd_970_);
lean_dec_ref(v___x_961_);
v_inBold_971_ = lean_ctor_get_uint8(v_a_928_, sizeof(void*)*1 + 1);
v_inLink_972_ = lean_ctor_get_uint8(v_a_928_, sizeof(void*)*1 + 2);
v_linePrefix_973_ = lean_ctor_get(v_a_928_, 0);
lean_inc_ref(v_linePrefix_973_);
lean_dec_ref(v_a_928_);
v_inEmph_946_ = v_inEmph_962_;
v_inBold_947_ = v_inBold_971_;
v_inLink_948_ = v_inLink_972_;
v_linePrefix_949_ = v_linePrefix_973_;
v___y_950_ = v_snd_970_;
goto v___jp_945_;
}
v___jp_945_:
{
uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = 1;
v___x_952_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_952_, 0, v_linePrefix_949_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*1, v___x_951_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*1 + 1, v_inBold_947_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*1 + 2, v_inLink_948_);
v___x_953_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_926_, v_fst_943_, v___x_952_, v___y_950_);
if (v_inEmph_946_ == 0)
{
lean_object* v_snd_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v_snd_957_; lean_object* v___x_958_; 
v_snd_954_ = lean_ctor_get(v___x_953_, 1);
lean_inc(v_snd_954_);
lean_dec_ref(v___x_953_);
v___x_955_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21));
v___x_956_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_955_, v_snd_954_);
v_snd_957_ = lean_ctor_get(v___x_956_, 1);
lean_inc(v_snd_957_);
lean_dec_ref(v___x_956_);
v___x_958_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_944_, v_snd_957_);
lean_dec(v_snd_944_);
return v___x_958_;
}
else
{
lean_object* v_snd_959_; lean_object* v___x_960_; 
v_snd_959_ = lean_ctor_get(v___x_953_, 1);
lean_inc(v_snd_959_);
lean_dec_ref(v___x_953_);
v___x_960_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_944_, v_snd_959_);
lean_dec(v_snd_944_);
return v___x_960_;
}
}
}
}
}
case 2:
{
lean_object* v_content_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1014_; 
v_content_976_ = lean_ctor_get(v_x_927_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_x_927_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_978_ = v_x_927_;
v_isShared_979_ = v_isSharedCheck_1014_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_content_976_);
lean_dec(v_x_927_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1014_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set_tag(v___x_978_, 9);
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_content_976_);
v___x_981_ = v_reuseFailAlloc_1013_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; lean_object* v_snd_983_; lean_object* v_fst_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; uint8_t v_inBold_988_; uint8_t v_inLink_989_; lean_object* v_linePrefix_990_; lean_object* v___y_991_; lean_object* v___x_1002_; uint8_t v_inBold_1003_; 
v___x_982_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_981_);
v_snd_983_ = lean_ctor_get(v___x_982_, 1);
lean_inc(v_snd_983_);
v_fst_984_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_fst_984_);
lean_dec_ref(v___x_982_);
v_fst_985_ = lean_ctor_get(v_snd_983_, 0);
lean_inc(v_fst_985_);
v_snd_986_ = lean_ctor_get(v_snd_983_, 1);
lean_inc(v_snd_986_);
lean_dec(v_snd_983_);
v___x_1002_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_984_, v_a_929_);
lean_dec(v_fst_984_);
v_inBold_1003_ = lean_ctor_get_uint8(v_a_928_, sizeof(void*)*1 + 1);
if (v_inBold_1003_ == 0)
{
lean_object* v_snd_1004_; uint8_t v_inLink_1005_; lean_object* v_linePrefix_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_snd_1009_; 
v_snd_1004_ = lean_ctor_get(v___x_1002_, 1);
lean_inc(v_snd_1004_);
lean_dec_ref(v___x_1002_);
v_inLink_1005_ = lean_ctor_get_uint8(v_a_928_, sizeof(void*)*1 + 2);
v_linePrefix_1006_ = lean_ctor_get(v_a_928_, 0);
lean_inc_ref(v_linePrefix_1006_);
lean_dec_ref(v_a_928_);
v___x_1007_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_1008_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1007_, v_snd_1004_);
v_snd_1009_ = lean_ctor_get(v___x_1008_, 1);
lean_inc(v_snd_1009_);
lean_dec_ref(v___x_1008_);
v_inBold_988_ = v_inBold_1003_;
v_inLink_989_ = v_inLink_1005_;
v_linePrefix_990_ = v_linePrefix_1006_;
v___y_991_ = v_snd_1009_;
goto v___jp_987_;
}
else
{
lean_object* v_snd_1010_; uint8_t v_inLink_1011_; lean_object* v_linePrefix_1012_; 
v_snd_1010_ = lean_ctor_get(v___x_1002_, 1);
lean_inc(v_snd_1010_);
lean_dec_ref(v___x_1002_);
v_inLink_1011_ = lean_ctor_get_uint8(v_a_928_, sizeof(void*)*1 + 2);
v_linePrefix_1012_ = lean_ctor_get(v_a_928_, 0);
lean_inc_ref(v_linePrefix_1012_);
lean_dec_ref(v_a_928_);
v_inBold_988_ = v_inBold_1003_;
v_inLink_989_ = v_inLink_1011_;
v_linePrefix_990_ = v_linePrefix_1012_;
v___y_991_ = v_snd_1010_;
goto v___jp_987_;
}
v___jp_987_:
{
uint8_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = 1;
v___x_993_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_993_, 0, v_linePrefix_990_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*1, v___x_992_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*1 + 1, v_inBold_988_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*1 + 2, v_inLink_989_);
v___x_994_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_926_, v_fst_985_, v___x_993_, v___y_991_);
if (v_inBold_988_ == 0)
{
lean_object* v_snd_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_snd_998_; lean_object* v___x_999_; 
v_snd_995_ = lean_ctor_get(v___x_994_, 1);
lean_inc(v_snd_995_);
lean_dec_ref(v___x_994_);
v___x_996_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_997_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_996_, v_snd_995_);
v_snd_998_ = lean_ctor_get(v___x_997_, 1);
lean_inc(v_snd_998_);
lean_dec_ref(v___x_997_);
v___x_999_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_986_, v_snd_998_);
lean_dec(v_snd_986_);
return v___x_999_;
}
else
{
lean_object* v_snd_1000_; lean_object* v___x_1001_; 
v_snd_1000_ = lean_ctor_get(v___x_994_, 1);
lean_inc(v_snd_1000_);
lean_dec_ref(v___x_994_);
v___x_1001_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_986_, v_snd_1000_);
lean_dec(v_snd_986_);
return v___x_1001_;
}
}
}
}
}
case 3:
{
lean_object* v_string_1015_; lean_object* v___y_1017_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_fst_1022_; uint8_t v___x_1023_; 
lean_dec_ref(v_a_928_);
lean_dec_ref(v_inst_926_);
v_string_1015_ = lean_ctor_get(v_x_927_, 0);
lean_inc_ref(v_string_1015_);
lean_dec_ref(v_x_927_);
v___x_1020_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__1));
v___x_1021_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v___x_1020_, v_a_929_);
v_fst_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_fst_1022_);
v___x_1023_ = lean_unbox(v_fst_1022_);
lean_dec(v_fst_1022_);
if (v___x_1023_ == 0)
{
lean_object* v_snd_1024_; 
v_snd_1024_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_snd_1024_);
lean_dec_ref(v___x_1021_);
v___y_1017_ = v_snd_1024_;
goto v___jp_1016_;
}
else
{
lean_object* v_snd_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v_snd_1028_; 
v_snd_1025_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_snd_1025_);
lean_dec_ref(v___x_1021_);
v___x_1026_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23));
v___x_1027_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1026_, v_snd_1025_);
v_snd_1028_ = lean_ctor_get(v___x_1027_, 1);
lean_inc(v_snd_1028_);
lean_dec_ref(v___x_1027_);
v___y_1017_ = v_snd_1028_;
goto v___jp_1016_;
}
v___jp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1015_);
v___x_1019_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1018_, v___y_1017_);
lean_dec_ref(v___x_1018_);
return v___x_1019_;
}
}
case 4:
{
uint8_t v_mode_1029_; 
lean_dec_ref(v_a_928_);
lean_dec_ref(v_inst_926_);
v_mode_1029_ = lean_ctor_get_uint8(v_x_927_, sizeof(void*)*1);
if (v_mode_1029_ == 0)
{
lean_object* v_string_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_string_1030_ = lean_ctor_get(v_x_927_, 0);
lean_inc_ref(v_string_1030_);
lean_dec_ref(v_x_927_);
v___x_1031_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24));
v___x_1032_ = lean_string_append(v___x_1031_, v_string_1030_);
lean_dec_ref(v_string_1030_);
v___x_1033_ = lean_string_append(v___x_1032_, v___x_1031_);
v___x_1034_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1033_, v_a_929_);
lean_dec_ref(v___x_1033_);
return v___x_1034_;
}
else
{
lean_object* v_string_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_string_1035_ = lean_ctor_get(v_x_927_, 0);
lean_inc_ref(v_string_1035_);
lean_dec_ref(v_x_927_);
v___x_1036_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25));
v___x_1037_ = lean_string_append(v___x_1036_, v_string_1035_);
lean_dec_ref(v_string_1035_);
v___x_1038_ = lean_string_append(v___x_1037_, v___x_1036_);
v___x_1039_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1038_, v_a_929_);
lean_dec_ref(v___x_1038_);
return v___x_1039_;
}
}
case 5:
{
lean_object* v_string_1040_; lean_object* v_linePrefix_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref(v_inst_926_);
v_string_1040_ = lean_ctor_get(v_x_927_, 0);
lean_inc_ref(v_string_1040_);
lean_dec_ref(v_x_927_);
v_linePrefix_1041_ = lean_ctor_get(v_a_928_, 0);
lean_inc_ref(v_linePrefix_1041_);
lean_dec_ref(v_a_928_);
v___x_1042_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26));
v___x_1043_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27));
v___x_1044_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1045_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28);
v___x_1046_ = lean_string_append(v___x_1044_, v_linePrefix_1041_);
lean_dec_ref(v_linePrefix_1041_);
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = lean_string_utf8_byte_size(v_string_1040_);
v___x_1049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1049_, 0, v_string_1040_);
lean_ctor_set(v___x_1049_, 1, v___x_1047_);
lean_ctor_set(v___x_1049_, 2, v___x_1048_);
v___x_1050_ = l_String_Slice_replace___redArg(v___x_1043_, v___x_1042_, v___x_1049_, v___x_1045_, v___x_1046_);
v___x_1051_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1050_, v_a_929_);
lean_dec_ref(v___x_1050_);
return v___x_1051_;
}
case 6:
{
uint8_t v_inLink_1052_; 
v_inLink_1052_ = lean_ctor_get_uint8(v_a_928_, sizeof(void*)*1 + 2);
if (v_inLink_1052_ == 0)
{
lean_object* v_content_1053_; lean_object* v_url_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v_snd_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; size_t v_sz_1060_; size_t v___x_1061_; lean_object* v___x_12053__overap_1062_; lean_object* v___x_1063_; lean_object* v_snd_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v_snd_1067_; lean_object* v___x_1068_; lean_object* v_snd_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_content_1053_ = lean_ctor_get(v_x_927_, 0);
lean_inc_ref(v_content_1053_);
v_url_1054_ = lean_ctor_get(v_x_927_, 1);
lean_inc_ref(v_url_1054_);
lean_dec_ref(v_x_927_);
v___x_1055_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29));
v___x_1056_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1055_, v_a_929_);
v_snd_1057_ = lean_ctor_get(v___x_1056_, 1);
lean_inc(v_snd_1057_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = lean_box(0);
v___f_1059_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0), 7, 2);
lean_closure_set(v___f_1059_, 0, v_inst_926_);
lean_closure_set(v___f_1059_, 1, v___x_1058_);
v_sz_1060_ = lean_array_size(v_content_1053_);
v___x_1061_ = ((size_t)0ULL);
v___x_12053__overap_1062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_930_, v_content_1053_, v___f_1059_, v_sz_1060_, v___x_1061_, v___x_1058_);
v___x_1063_ = lean_apply_2(v___x_12053__overap_1062_, v_a_928_, v_snd_1057_);
v_snd_1064_ = lean_ctor_get(v___x_1063_, 1);
lean_inc(v_snd_1064_);
lean_dec_ref(v___x_1063_);
v___x_1065_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30));
v___x_1066_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1065_, v_snd_1064_);
v_snd_1067_ = lean_ctor_get(v___x_1066_, 1);
lean_inc(v_snd_1067_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = l_Lean_Doc_MarkdownM_push___redArg(v_url_1054_, v_snd_1067_);
lean_dec_ref(v_url_1054_);
v_snd_1069_ = lean_ctor_get(v___x_1068_, 1);
lean_inc(v_snd_1069_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31));
v___x_1071_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1070_, v_snd_1069_);
return v___x_1071_;
}
else
{
lean_object* v_content_1072_; lean_object* v___x_1073_; lean_object* v___f_1074_; size_t v_sz_1075_; size_t v___x_1076_; lean_object* v___x_12077__overap_1077_; lean_object* v___x_1078_; lean_object* v_snd_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_content_1072_ = lean_ctor_get(v_x_927_, 0);
lean_inc_ref(v_content_1072_);
lean_dec_ref(v_x_927_);
v___x_1073_ = lean_box(0);
v___f_1074_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0), 7, 2);
lean_closure_set(v___f_1074_, 0, v_inst_926_);
lean_closure_set(v___f_1074_, 1, v___x_1073_);
v_sz_1075_ = lean_array_size(v_content_1072_);
v___x_1076_ = ((size_t)0ULL);
v___x_12077__overap_1077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_930_, v_content_1072_, v___f_1074_, v_sz_1075_, v___x_1076_, v___x_1073_);
v___x_1078_ = lean_apply_2(v___x_12077__overap_1077_, v_a_928_, v_a_929_);
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
}
case 7:
{
lean_object* v_name_1088_; lean_object* v_content_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_snd_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v_a_928_);
v_name_1088_ = lean_ctor_get(v_x_927_, 0);
lean_inc_ref(v_name_1088_);
v_content_1089_ = lean_ctor_get(v_x_927_, 1);
lean_inc_ref(v_content_1089_);
lean_dec_ref(v_x_927_);
v___x_1090_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32));
v___x_1091_ = lean_string_append(v___x_1090_, v_name_1088_);
v___x_1092_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33));
v___x_1093_ = lean_string_append(v___x_1091_, v___x_1092_);
v___x_1094_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1093_, v_a_929_);
lean_dec_ref(v___x_1093_);
v_snd_1095_ = lean_ctor_get(v___x_1094_, 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v___x_1094_, 0);
lean_dec(v_unused_1138_);
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1137_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_snd_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1137_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v_snd_1100_; lean_object* v___y_1119_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = lean_array_get_size(v_content_1089_);
v___x_1123_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34));
v___x_1124_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__35);
v___x_1125_ = lean_nat_dec_lt(v___x_1121_, v___x_1122_);
if (v___x_1125_ == 0)
{
lean_dec_ref(v_content_1089_);
lean_dec_ref(v_inst_926_);
v_snd_1100_ = v___x_1124_;
goto v___jp_1099_;
}
else
{
lean_object* v___x_1126_; lean_object* v___f_1127_; uint8_t v___x_1128_; 
v___x_1126_ = lean_box(0);
v___f_1127_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1127_, 0, v_inst_926_);
v___x_1128_ = lean_nat_dec_le(v___x_1122_, v___x_1122_);
if (v___x_1128_ == 0)
{
if (v___x_1125_ == 0)
{
lean_dec_ref(v___f_1127_);
lean_dec_ref(v_content_1089_);
v_snd_1100_ = v___x_1124_;
goto v___jp_1099_;
}
else
{
size_t v___x_1129_; size_t v___x_1130_; lean_object* v___x_11896__overap_1131_; lean_object* v___x_1132_; 
v___x_1129_ = ((size_t)0ULL);
v___x_1130_ = lean_usize_of_nat(v___x_1122_);
v___x_11896__overap_1131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_930_, v___f_1127_, v_content_1089_, v___x_1129_, v___x_1130_, v___x_1126_);
v___x_1132_ = lean_apply_2(v___x_11896__overap_1131_, v___x_1123_, v___x_1124_);
v___y_1119_ = v___x_1132_;
goto v___jp_1118_;
}
}
else
{
size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_11900__overap_1135_; lean_object* v___x_1136_; 
v___x_1133_ = ((size_t)0ULL);
v___x_1134_ = lean_usize_of_nat(v___x_1122_);
v___x_11900__overap_1135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_930_, v___f_1127_, v_content_1089_, v___x_1133_, v___x_1134_, v___x_1126_);
v___x_1136_ = lean_apply_2(v___x_11900__overap_1135_, v___x_1123_, v___x_1124_);
v___y_1119_ = v___x_1136_;
goto v___jp_1118_;
}
}
v___jp_1099_:
{
lean_object* v_priorBlocks_1101_; lean_object* v_currentBlock_1102_; lean_object* v_footnotes_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1117_; 
v_priorBlocks_1101_ = lean_ctor_get(v_snd_1095_, 0);
v_currentBlock_1102_ = lean_ctor_get(v_snd_1095_, 1);
v_footnotes_1103_ = lean_ctor_get(v_snd_1095_, 2);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_snd_1095_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1105_ = v_snd_1095_;
v_isShared_1106_ = v_isSharedCheck_1117_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_footnotes_1103_);
lean_inc(v_currentBlock_1102_);
lean_inc(v_priorBlocks_1101_);
lean_dec(v_snd_1095_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1117_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1107_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(v_snd_1100_);
v___x_1108_ = lean_box(0);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 1, v___x_1107_);
lean_ctor_set(v___x_1097_, 0, v_name_1088_);
v___x_1110_ = v___x_1097_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_name_1088_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1107_);
v___x_1110_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = lean_array_push(v_footnotes_1103_, v___x_1110_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 2, v___x_1111_);
v___x_1113_ = v___x_1105_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_priorBlocks_1101_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_currentBlock_1102_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1108_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
return v___x_1114_;
}
}
}
}
v___jp_1118_:
{
lean_object* v_snd_1120_; 
v_snd_1120_ = lean_ctor_get(v___y_1119_, 1);
lean_inc(v_snd_1120_);
lean_dec_ref(v___y_1119_);
v_snd_1100_ = v_snd_1120_;
goto v___jp_1099_;
}
}
}
case 8:
{
lean_object* v_alt_1139_; lean_object* v_url_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec_ref(v_a_928_);
lean_dec_ref(v_inst_926_);
v_alt_1139_ = lean_ctor_get(v_x_927_, 0);
lean_inc_ref(v_alt_1139_);
v_url_1140_ = lean_ctor_get(v_x_927_, 1);
lean_inc_ref(v_url_1140_);
lean_dec_ref(v_x_927_);
v___x_1141_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__36));
v___x_1142_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1139_);
lean_dec_ref(v_alt_1139_);
v___x_1143_ = lean_string_append(v___x_1141_, v___x_1142_);
lean_dec_ref(v___x_1142_);
v___x_1144_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30));
v___x_1145_ = lean_string_append(v___x_1143_, v___x_1144_);
v___x_1146_ = lean_string_append(v___x_1145_, v_url_1140_);
lean_dec_ref(v_url_1140_);
v___x_1147_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31));
v___x_1148_ = lean_string_append(v___x_1146_, v___x_1147_);
v___x_1149_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1148_, v_a_929_);
lean_dec_ref(v___x_1148_);
return v___x_1149_;
}
case 9:
{
lean_object* v_content_1150_; lean_object* v___x_1151_; lean_object* v___f_1152_; size_t v_sz_1153_; size_t v___x_1154_; lean_object* v___x_11991__overap_1155_; lean_object* v___x_1156_; lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_content_1150_ = lean_ctor_get(v_x_927_, 0);
lean_inc_ref(v_content_1150_);
lean_dec_ref(v_x_927_);
v___x_1151_ = lean_box(0);
v___f_1152_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0), 7, 2);
lean_closure_set(v___f_1152_, 0, v_inst_926_);
lean_closure_set(v___f_1152_, 1, v___x_1151_);
v_sz_1153_ = lean_array_size(v_content_1150_);
v___x_1154_ = ((size_t)0ULL);
v___x_11991__overap_1155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_930_, v_content_1150_, v___f_1152_, v_sz_1153_, v___x_1154_, v___x_1151_);
v___x_1156_ = lean_apply_2(v___x_11991__overap_1155_, v_a_928_, v_a_929_);
v_snd_1157_ = lean_ctor_get(v___x_1156_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v___x_1156_, 0);
lean_dec(v_unused_1165_);
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1151_);
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_snd_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
default: 
{
lean_object* v_container_1166_; lean_object* v_content_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v_container_1166_ = lean_ctor_get(v_x_927_, 0);
lean_inc(v_container_1166_);
v_content_1167_ = lean_ctor_get(v_x_927_, 1);
lean_inc_ref(v_content_1167_);
lean_dec_ref(v_x_927_);
lean_inc_ref(v_inst_926_);
v___x_1168_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg), 4, 1);
lean_closure_set(v___x_1168_, 0, v_inst_926_);
v___x_1169_ = lean_apply_5(v_inst_926_, v___x_1168_, v_container_1166_, v_content_1167_, v_a_928_, v_a_929_);
return v___x_1169_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__2(lean_object* v_inst_1170_, lean_object* v_x_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1170_, v___y_1172_, v___y_1173_, v___y_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1176_, lean_object* v_inst_1177_, lean_object* v_x_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1177_, v_x_1178_, v_a_1179_, v_a_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1182_, lean_object* v_inline_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1182_, v_inline_1183_, v_a_1184_, v_a_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1187_, lean_object* v_inst_1188_, lean_object* v_inline_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1188_, v_inline_1189_, v_a_1190_, v_a_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0(lean_object* v_inst_1193_, lean_object* v_inline_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1193_, v_inline_1194_, v___y_1195_, v___y_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1198_){
_start:
{
lean_object* v___f_1199_; 
v___f_1199_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1199_, 0, v_inst_1198_);
return v___f_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1200_, lean_object* v_inst_1201_){
_start:
{
lean_object* v___f_1202_; 
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1202_, 0, v_inst_1201_);
return v___f_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(lean_object* v_x_1203_, lean_object* v_x_1204_){
_start:
{
lean_object* v_zero_1205_; uint8_t v_isZero_1206_; 
v_zero_1205_ = lean_unsigned_to_nat(0u);
v_isZero_1206_ = lean_nat_dec_eq(v_x_1203_, v_zero_1205_);
if (v_isZero_1206_ == 1)
{
lean_dec(v_x_1203_);
return v_x_1204_;
}
else
{
uint32_t v___x_1207_; lean_object* v_one_1208_; lean_object* v_n_1209_; lean_object* v___x_1210_; 
v___x_1207_ = 32;
v_one_1208_ = lean_unsigned_to_nat(1u);
v_n_1209_ = lean_nat_sub(v_x_1203_, v_one_1208_);
lean_dec(v_x_1203_);
v___x_1210_ = lean_string_push(v_x_1204_, v___x_1207_);
v_x_1203_ = v_n_1209_;
v_x_1204_ = v___x_1210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(lean_object* v_str_1212_, lean_object* v_indent_1213_, lean_object* v_b_1214_){
_start:
{
lean_object* v_snd_1215_; lean_object* v_snd_1216_; lean_object* v_fst_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1279_; 
v_snd_1215_ = lean_ctor_get(v_b_1214_, 1);
lean_inc(v_snd_1215_);
v_snd_1216_ = lean_ctor_get(v_snd_1215_, 1);
lean_inc(v_snd_1216_);
v_fst_1217_ = lean_ctor_get(v_b_1214_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_b_1214_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v_b_1214_, 1);
lean_dec(v_unused_1280_);
v___x_1219_ = v_b_1214_;
v_isShared_1220_ = v_isSharedCheck_1279_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_fst_1217_);
lean_dec(v_b_1214_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1279_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_fst_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1277_; 
v_fst_1221_ = lean_ctor_get(v_snd_1215_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_snd_1215_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v_snd_1215_, 1);
lean_dec(v_unused_1278_);
v___x_1223_ = v_snd_1215_;
v_isShared_1224_ = v_isSharedCheck_1277_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_fst_1221_);
lean_dec(v_snd_1215_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1277_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_fst_1225_; lean_object* v_snd_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1276_; 
v_fst_1225_ = lean_ctor_get(v_snd_1216_, 0);
v_snd_1226_ = lean_ctor_get(v_snd_1216_, 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_snd_1216_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1228_ = v_snd_1216_;
v_isShared_1229_ = v_isSharedCheck_1276_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_snd_1226_);
lean_inc(v_fst_1225_);
lean_dec(v_snd_1216_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1276_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = lean_string_utf8_byte_size(v_str_1212_);
v___x_1231_ = lean_nat_dec_eq(v_fst_1225_, v___x_1230_);
if (v___x_1231_ == 0)
{
uint32_t v_c_1232_; lean_object* v_iter_1233_; lean_object* v_longest_1235_; lean_object* v_current_1236_; uint32_t v___x_1261_; uint8_t v___x_1262_; 
v_c_1232_ = lean_string_utf8_get_fast(v_str_1212_, v_fst_1225_);
v_iter_1233_ = lean_string_utf8_next_fast(v_str_1212_, v_fst_1225_);
lean_dec(v_fst_1225_);
v___x_1261_ = 96;
v___x_1262_ = lean_uint32_dec_eq(v_c_1232_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v_current_1263_; uint8_t v___x_1264_; 
v_current_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = lean_nat_dec_le(v_fst_1217_, v_fst_1221_);
if (v___x_1264_ == 0)
{
lean_dec(v_fst_1221_);
v_longest_1235_ = v_fst_1217_;
v_current_1236_ = v_current_1263_;
goto v___jp_1234_;
}
else
{
lean_dec(v_fst_1217_);
v_longest_1235_ = v_fst_1221_;
v_current_1236_ = v_current_1263_;
goto v___jp_1234_;
}
}
else
{
lean_object* v___x_1265_; lean_object* v_current_1266_; 
v___x_1265_ = lean_unsigned_to_nat(1u);
v_current_1266_ = lean_nat_add(v_fst_1221_, v___x_1265_);
lean_dec(v_fst_1221_);
v_longest_1235_ = v_fst_1217_;
v_current_1236_ = v_current_1266_;
goto v___jp_1234_;
}
v___jp_1234_:
{
lean_object* v_out_1237_; uint32_t v___x_1238_; uint8_t v___x_1239_; 
v_out_1237_ = lean_string_push(v_snd_1226_, v_c_1232_);
v___x_1238_ = 10;
v___x_1239_ = lean_uint32_dec_eq(v_c_1232_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1241_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v_out_1237_);
lean_ctor_set(v___x_1228_, 0, v_iter_1233_);
v___x_1241_ = v___x_1228_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_iter_1233_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_out_1237_);
v___x_1241_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1243_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1241_);
lean_ctor_set(v___x_1223_, 0, v_current_1236_);
v___x_1243_ = v___x_1223_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_current_1236_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1245_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v___x_1243_);
lean_ctor_set(v___x_1219_, 0, v_longest_1235_);
v___x_1245_ = v___x_1219_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_longest_1235_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
v_b_1214_ = v___x_1245_;
goto _start;
}
}
}
}
else
{
lean_object* v_out_1250_; lean_object* v___x_1252_; 
lean_inc(v_indent_1213_);
v_out_1250_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(v_indent_1213_, v_out_1237_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v_out_1250_);
lean_ctor_set(v___x_1228_, 0, v_iter_1233_);
v___x_1252_ = v___x_1228_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_iter_1233_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_out_1250_);
v___x_1252_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1254_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1252_);
lean_ctor_set(v___x_1223_, 0, v_current_1236_);
v___x_1254_ = v___x_1223_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_current_1236_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1256_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v___x_1254_);
lean_ctor_set(v___x_1219_, 0, v_longest_1235_);
v___x_1256_ = v___x_1219_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_longest_1235_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
v_b_1214_ = v___x_1256_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_1268_; 
lean_dec(v_indent_1213_);
if (v_isShared_1229_ == 0)
{
v___x_1268_ = v___x_1228_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_fst_1225_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_snd_1226_);
v___x_1268_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1270_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1268_);
v___x_1270_ = v___x_1223_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_fst_1221_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1272_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v___x_1270_);
v___x_1272_ = v___x_1219_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_fst_1217_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1___boxed(lean_object* v_str_1281_, lean_object* v_indent_1282_, lean_object* v_b_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(v_str_1281_, v_indent_1282_, v_b_1283_);
lean_dec_ref(v_str_1281_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(lean_object* v_indent_1294_, lean_object* v_str_1295_){
_start:
{
lean_object* v_current_1296_; lean_object* v_out_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_snd_1300_; lean_object* v_snd_1301_; lean_object* v_fst_1302_; lean_object* v_fst_1303_; lean_object* v_snd_1304_; lean_object* v___x_1305_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1318_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_current_1296_ = lean_unsigned_to_nat(0u);
v_out_1297_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___x_1298_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___closed__2));
lean_inc(v_indent_1294_);
v___x_1299_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__1(v_str_1295_, v_indent_1294_, v___x_1298_);
v_snd_1300_ = lean_ctor_get(v___x_1299_, 1);
lean_inc(v_snd_1300_);
v_snd_1301_ = lean_ctor_get(v_snd_1300_, 1);
lean_inc(v_snd_1301_);
v_fst_1302_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_fst_1302_);
lean_dec_ref(v___x_1299_);
v_fst_1303_ = lean_ctor_get(v_snd_1300_, 0);
lean_inc(v_fst_1303_);
lean_dec(v_snd_1300_);
v_snd_1304_ = lean_ctor_get(v_snd_1301_, 1);
lean_inc(v_snd_1304_);
lean_dec(v_snd_1301_);
v___x_1305_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1324_ = lean_string_utf8_byte_size(v_snd_1304_);
v___x_1325_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2);
v___x_1326_ = lean_nat_dec_le(v___x_1325_, v___x_1324_);
if (v___x_1326_ == 0)
{
goto v___jp_1321_;
}
else
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = lean_nat_sub(v___x_1324_, v___x_1325_);
v___x_1328_ = lean_string_memcmp(v_snd_1304_, v___x_1305_, v___x_1327_, v_current_1296_, v___x_1325_);
lean_dec(v___x_1327_);
if (v___x_1328_ == 0)
{
goto v___jp_1321_;
}
else
{
v___y_1318_ = v_snd_1304_;
goto v___jp_1317_;
}
}
v___jp_1306_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1311_ = lean_nat_add(v___y_1309_, v___x_1310_);
lean_dec(v___y_1309_);
v___x_1312_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode_spec__1(v___x_1311_, v___y_1308_);
lean_inc_ref(v___x_1312_);
v___x_1313_ = lean_string_append(v___x_1312_, v___x_1305_);
v___x_1314_ = lean_string_append(v___x_1313_, v___y_1307_);
lean_dec_ref(v___y_1307_);
v___x_1315_ = lean_string_append(v___x_1314_, v___x_1312_);
lean_dec_ref(v___x_1312_);
v___x_1316_ = lean_string_append(v___x_1315_, v___x_1305_);
return v___x_1316_;
}
v___jp_1317_:
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock_spec__0(v_indent_1294_, v_out_1297_);
v___x_1320_ = lean_nat_dec_le(v_fst_1302_, v_fst_1303_);
if (v___x_1320_ == 0)
{
lean_dec(v_fst_1303_);
v___y_1307_ = v___y_1318_;
v___y_1308_ = v___x_1319_;
v___y_1309_ = v_fst_1302_;
goto v___jp_1306_;
}
else
{
lean_dec(v_fst_1302_);
v___y_1307_ = v___y_1318_;
v___y_1308_ = v___x_1319_;
v___y_1309_ = v_fst_1303_;
goto v___jp_1306_;
}
}
v___jp_1321_:
{
uint32_t v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = 10;
v___x_1323_ = lean_string_push(v_snd_1304_, v___x_1322_);
v___y_1318_ = v___x_1323_;
goto v___jp_1317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock___boxed(lean_object* v_indent_1329_, lean_object* v_str_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v_indent_1329_, v_str_1330_);
lean_dec_ref(v_str_1330_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v___x_1333_, lean_object* v___f_1334_, lean_object* v___x_1335_, lean_object* v_a_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint8_t v_inEmph_1341_; uint8_t v_inBold_1342_; uint8_t v_inLink_1343_; lean_object* v_linePrefix_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1371_; 
v_inEmph_1341_ = lean_ctor_get_uint8(v___y_1339_, sizeof(void*)*1);
v_inBold_1342_ = lean_ctor_get_uint8(v___y_1339_, sizeof(void*)*1 + 1);
v_inLink_1343_ = lean_ctor_get_uint8(v___y_1339_, sizeof(void*)*1 + 2);
v_linePrefix_1344_ = lean_ctor_get(v___y_1339_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___y_1339_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1346_ = v___y_1339_;
v_isShared_1347_ = v_isSharedCheck_1371_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_linePrefix_1344_);
lean_dec(v___y_1339_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1371_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v_snd_1351_; size_t v_sz_1352_; size_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1348_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
lean_inc_ref(v_linePrefix_1344_);
v___x_1349_ = lean_string_append(v_linePrefix_1344_, v___x_1348_);
v___x_1350_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1349_, v___y_1340_);
lean_dec_ref(v___x_1349_);
v_snd_1351_ = lean_ctor_get(v___x_1350_, 1);
lean_inc(v_snd_1351_);
lean_dec_ref(v___x_1350_);
v_sz_1352_ = lean_array_size(v_a_1336_);
v___x_1353_ = ((size_t)0ULL);
v___x_1354_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1355_ = lean_string_append(v_linePrefix_1344_, v___x_1354_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1355_);
v___x_1357_ = v___x_1346_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*1, v_inEmph_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*1 + 1, v_inBold_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*1 + 2, v_inLink_1343_);
v___x_1357_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_13714__overap_1358_; lean_object* v___x_1359_; lean_object* v_snd_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1368_; 
v___x_13714__overap_1358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1333_, v_a_1336_, v___f_1334_, v_sz_1352_, v___x_1353_, v___x_1335_);
v___x_1359_ = lean_apply_2(v___x_13714__overap_1358_, v___x_1357_, v_snd_1351_);
v_snd_1360_ = lean_ctor_get(v___x_1359_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; 
v_unused_1369_ = lean_ctor_get(v___x_1359_, 0);
lean_dec(v_unused_1369_);
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_snd_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1335_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1364_);
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_snd_1360_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1373_, lean_object* v_inst_1374_, lean_object* v___x_1375_, lean_object* v___x_1376_, lean_object* v_a_1377_, lean_object* v_x_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
uint8_t v_inEmph_1382_; uint8_t v_inBold_1383_; uint8_t v_inLink_1384_; lean_object* v_linePrefix_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1417_; 
v_inEmph_1382_ = lean_ctor_get_uint8(v___y_1380_, sizeof(void*)*1);
v_inBold_1383_ = lean_ctor_get_uint8(v___y_1380_, sizeof(void*)*1 + 1);
v_inLink_1384_ = lean_ctor_get_uint8(v___y_1380_, sizeof(void*)*1 + 2);
v_linePrefix_1385_ = lean_ctor_get(v___y_1380_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___y_1380_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1387_ = v___y_1380_;
v_isShared_1388_ = v_isSharedCheck_1417_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_linePrefix_1385_);
lean_dec(v___y_1380_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1417_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_snd_1394_; lean_object* v___x_1395_; lean_object* v___f_1396_; size_t v_sz_1397_; size_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
lean_inc(v___y_1379_);
v___x_1389_ = l_Nat_reprFast(v___y_1379_);
v___x_1390_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0));
v___x_1391_ = lean_string_append(v___x_1389_, v___x_1390_);
lean_inc_ref(v_linePrefix_1385_);
v___x_1392_ = lean_string_append(v_linePrefix_1385_, v___x_1391_);
lean_dec_ref(v___x_1391_);
v___x_1393_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1392_, v___y_1381_);
lean_dec_ref(v___x_1392_);
v_snd_1394_ = lean_ctor_get(v___x_1393_, 1);
lean_inc(v_snd_1394_);
lean_dec_ref(v___x_1393_);
v___x_1395_ = lean_box(0);
v___f_1396_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1), 8, 3);
lean_closure_set(v___f_1396_, 0, v_inst_1373_);
lean_closure_set(v___f_1396_, 1, v_inst_1374_);
lean_closure_set(v___f_1396_, 2, v___x_1395_);
v_sz_1397_ = lean_array_size(v_a_1377_);
v___x_1398_ = ((size_t)0ULL);
v___x_1399_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1400_ = lean_string_append(v_linePrefix_1385_, v___x_1399_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1400_);
v___x_1402_ = v___x_1387_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1400_);
lean_ctor_set_uint8(v_reuseFailAlloc_1416_, sizeof(void*)*1, v_inEmph_1382_);
lean_ctor_set_uint8(v_reuseFailAlloc_1416_, sizeof(void*)*1 + 1, v_inBold_1383_);
lean_ctor_set_uint8(v_reuseFailAlloc_1416_, sizeof(void*)*1 + 2, v_inLink_1384_);
v___x_1402_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_13752__overap_1403_; lean_object* v___x_1404_; lean_object* v_snd_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1414_; 
v___x_13752__overap_1403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1375_, v_a_1377_, v___f_1396_, v_sz_1397_, v___x_1398_, v___x_1395_);
v___x_1404_ = lean_apply_2(v___x_13752__overap_1403_, v___x_1402_, v_snd_1394_);
v_snd_1405_ = lean_ctor_get(v___x_1404_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v___x_1404_, 0);
lean_dec(v_unused_1415_);
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1414_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_snd_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1414_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1409_ = lean_nat_add(v___y_1379_, v___x_1376_);
lean_dec(v___y_1379_);
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1410_);
v___x_1412_ = v___x_1407_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_snd_1405_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v___x_1420_, lean_object* v___x_1421_, lean_object* v_a_1422_, lean_object* v_x_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1418_, v_inst_1419_, v___x_1420_, v___x_1421_, v_a_1422_, v_x_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___x_1421_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v___x_1433_, lean_object* v_a_1434_, lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
uint8_t v_inEmph_1439_; uint8_t v_inBold_1440_; uint8_t v_inLink_1441_; lean_object* v_linePrefix_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1480_; 
v_inEmph_1439_ = lean_ctor_get_uint8(v___y_1437_, sizeof(void*)*1);
v_inBold_1440_ = lean_ctor_get_uint8(v___y_1437_, sizeof(void*)*1 + 1);
v_inLink_1441_ = lean_ctor_get_uint8(v___y_1437_, sizeof(void*)*1 + 2);
v_linePrefix_1442_ = lean_ctor_get(v___y_1437_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___y_1437_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1444_ = v___y_1437_;
v_isShared_1445_ = v_isSharedCheck_1480_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_linePrefix_1442_);
lean_dec(v___y_1437_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1480_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v_snd_1449_; lean_object* v_term_1450_; lean_object* v_desc_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1446_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
lean_inc_ref(v_linePrefix_1442_);
v___x_1447_ = lean_string_append(v_linePrefix_1442_, v___x_1446_);
v___x_1448_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1447_, v___y_1438_);
lean_dec_ref(v___x_1447_);
v_snd_1449_ = lean_ctor_get(v___x_1448_, 1);
lean_inc(v_snd_1449_);
lean_dec_ref(v___x_1448_);
v_term_1450_ = lean_ctor_get(v_a_1434_, 0);
v_desc_1451_ = lean_ctor_get(v_a_1434_, 1);
lean_inc_ref(v_term_1450_);
v___x_1452_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1452_, 0, v_term_1450_);
v___x_1453_ = ((lean_object*)(l_Lean_Doc_MarkdownM_indent___redArg___closed__0));
v___x_1454_ = lean_string_append(v_linePrefix_1442_, v___x_1453_);
lean_inc_ref(v___x_1454_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1454_);
v___x_1456_ = v___x_1444_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*1, v_inEmph_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*1 + 1, v_inBold_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*1 + 2, v_inLink_1441_);
v___x_1456_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; lean_object* v_snd_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v_snd_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_snd_1464_; lean_object* v___x_1465_; lean_object* v_snd_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v_snd_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1477_; 
lean_inc_ref(v___x_1456_);
lean_inc_ref(v_inst_1431_);
v___x_1457_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1431_, v___x_1452_, v___x_1456_, v_snd_1449_);
v_snd_1458_ = lean_ctor_get(v___x_1457_, 1);
lean_inc(v_snd_1458_);
lean_dec_ref(v___x_1457_);
v___x_1459_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1));
lean_inc_ref(v___x_1456_);
lean_inc_ref(v_inst_1431_);
v___x_1460_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1431_, v___x_1459_, v___x_1456_, v_snd_1458_);
v_snd_1461_ = lean_ctor_get(v___x_1460_, 1);
lean_inc(v_snd_1461_);
lean_dec_ref(v___x_1460_);
v___x_1462_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1463_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1462_, v_snd_1461_);
v_snd_1464_ = lean_ctor_get(v___x_1463_, 1);
lean_inc(v_snd_1464_);
lean_dec_ref(v___x_1463_);
v___x_1465_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1454_, v_snd_1464_);
lean_dec_ref(v___x_1454_);
v_snd_1466_ = lean_ctor_get(v___x_1465_, 1);
lean_inc(v_snd_1466_);
lean_dec_ref(v___x_1465_);
lean_inc_ref(v_desc_1451_);
v___x_1467_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1467_, 0, v_desc_1451_);
v___x_1468_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1431_, v_inst_1432_, v___x_1467_, v___x_1456_, v_snd_1466_);
v_snd_1469_ = lean_ctor_get(v___x_1468_, 1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v___x_1468_, 0);
lean_dec(v_unused_1478_);
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_snd_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1433_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1473_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_snd_1469_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v___x_1483_, lean_object* v_a_1484_, lean_object* v_x_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1481_, v_inst_1482_, v___x_1483_, v_a_1484_, v_x_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec_ref(v_a_1484_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1491_, lean_object* v_inst_1492_, lean_object* v_x_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
switch(lean_obj_tag(v_x_1493_))
{
case 0:
{
lean_object* v_contents_1497_; lean_object* v___x_1498_; lean_object* v___f_1499_; size_t v_sz_1500_; size_t v___x_1501_; lean_object* v___x_12963__overap_1502_; lean_object* v___x_1503_; lean_object* v_snd_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v_inst_1492_);
v_contents_1497_ = lean_ctor_get(v_x_1493_, 0);
lean_inc_ref(v_contents_1497_);
lean_dec_ref(v_x_1493_);
v___x_1498_ = lean_box(0);
v___f_1499_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0), 7, 2);
lean_closure_set(v___f_1499_, 0, v_inst_1491_);
lean_closure_set(v___f_1499_, 1, v___x_1498_);
v_sz_1500_ = lean_array_size(v_contents_1497_);
v___x_1501_ = ((size_t)0ULL);
v___x_12963__overap_1502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1496_, v_contents_1497_, v___f_1499_, v_sz_1500_, v___x_1501_, v___x_1498_);
v___x_1503_ = lean_apply_2(v___x_12963__overap_1502_, v_a_1494_, v_a_1495_);
v_snd_1504_ = lean_ctor_get(v___x_1503_, 1);
lean_inc(v_snd_1504_);
lean_dec_ref(v___x_1503_);
v___x_1505_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1504_);
return v___x_1505_;
}
case 1:
{
lean_object* v_content_1506_; lean_object* v___y_1508_; lean_object* v___y_1509_; uint8_t v___y_1517_; lean_object* v_currentBlock_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
lean_dec_ref(v_inst_1492_);
lean_dec_ref(v_inst_1491_);
v_content_1506_ = lean_ctor_get(v_x_1493_, 0);
lean_inc_ref(v_content_1506_);
lean_dec_ref(v_x_1493_);
v_currentBlock_1521_ = lean_ctor_get(v_a_1495_, 1);
v___x_1522_ = lean_string_utf8_byte_size(v_currentBlock_1521_);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = lean_nat_dec_eq(v___x_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1525_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1526_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__2);
v___x_1527_ = lean_nat_dec_le(v___x_1526_, v___x_1522_);
if (v___x_1527_ == 0)
{
v___y_1517_ = v___x_1524_;
goto v___jp_1516_;
}
else
{
lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1528_ = lean_nat_sub(v___x_1522_, v___x_1526_);
v___x_1529_ = lean_string_memcmp(v_currentBlock_1521_, v___x_1525_, v___x_1528_, v___x_1523_, v___x_1526_);
lean_dec(v___x_1528_);
v___y_1517_ = v___x_1529_;
goto v___jp_1516_;
}
}
else
{
v___y_1517_ = v___x_1524_;
goto v___jp_1516_;
}
v___jp_1507_:
{
lean_object* v_linePrefix_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v_snd_1514_; lean_object* v___x_1515_; 
v_linePrefix_1510_ = lean_ctor_get(v___y_1508_, 0);
lean_inc_ref(v_linePrefix_1510_);
lean_dec_ref(v___y_1508_);
v___x_1511_ = lean_string_length(v_linePrefix_1510_);
lean_dec_ref(v_linePrefix_1510_);
v___x_1512_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v___x_1511_, v_content_1506_);
lean_dec_ref(v_content_1506_);
v___x_1513_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1512_, v___y_1509_);
lean_dec_ref(v___x_1512_);
v_snd_1514_ = lean_ctor_get(v___x_1513_, 1);
lean_inc(v_snd_1514_);
lean_dec_ref(v___x_1513_);
v___x_1515_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1514_);
return v___x_1515_;
}
v___jp_1516_:
{
if (v___y_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v_snd_1520_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_combineBlocks___closed__1));
v___x_1519_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1518_, v_a_1495_);
v_snd_1520_ = lean_ctor_get(v___x_1519_, 1);
lean_inc(v_snd_1520_);
lean_dec_ref(v___x_1519_);
v___y_1508_ = v_a_1494_;
v___y_1509_ = v_snd_1520_;
goto v___jp_1507_;
}
else
{
v___y_1508_ = v_a_1494_;
v___y_1509_ = v_a_1495_;
goto v___jp_1507_;
}
}
}
case 2:
{
lean_object* v_items_1530_; lean_object* v___x_1531_; lean_object* v___f_1532_; lean_object* v___f_1533_; size_t v_sz_1534_; size_t v___x_1535_; lean_object* v___x_13191__overap_1536_; lean_object* v___x_1537_; lean_object* v_snd_1538_; lean_object* v___x_1539_; 
v_items_1530_ = lean_ctor_get(v_x_1493_, 0);
lean_inc_ref(v_items_1530_);
lean_dec_ref(v_x_1493_);
v___x_1531_ = lean_box(0);
v___f_1532_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1), 8, 3);
lean_closure_set(v___f_1532_, 0, v_inst_1491_);
lean_closure_set(v___f_1532_, 1, v_inst_1492_);
lean_closure_set(v___f_1532_, 2, v___x_1531_);
v___f_1533_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0), 8, 3);
lean_closure_set(v___f_1533_, 0, v___x_1496_);
lean_closure_set(v___f_1533_, 1, v___f_1532_);
lean_closure_set(v___f_1533_, 2, v___x_1531_);
v_sz_1534_ = lean_array_size(v_items_1530_);
v___x_1535_ = ((size_t)0ULL);
v___x_13191__overap_1536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1496_, v_items_1530_, v___f_1533_, v_sz_1534_, v___x_1535_, v___x_1531_);
v___x_1537_ = lean_apply_2(v___x_13191__overap_1536_, v_a_1494_, v_a_1495_);
v_snd_1538_ = lean_ctor_get(v___x_1537_, 1);
lean_inc(v_snd_1538_);
lean_dec_ref(v___x_1537_);
v___x_1539_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1538_);
return v___x_1539_;
}
case 3:
{
lean_object* v_start_1540_; lean_object* v_items_1541_; lean_object* v___x_1542_; lean_object* v___f_1543_; lean_object* v___y_1545_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v_start_1540_ = lean_ctor_get(v_x_1493_, 0);
lean_inc(v_start_1540_);
v_items_1541_ = lean_ctor_get(v_x_1493_, 1);
lean_inc_ref(v_items_1541_);
lean_dec_ref(v_x_1493_);
v___x_1542_ = lean_unsigned_to_nat(1u);
v___f_1543_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 9, 4);
lean_closure_set(v___f_1543_, 0, v_inst_1491_);
lean_closure_set(v___f_1543_, 1, v_inst_1492_);
lean_closure_set(v___f_1543_, 2, v___x_1496_);
lean_closure_set(v___f_1543_, 3, v___x_1542_);
v___x_1552_ = l_Int_toNat(v_start_1540_);
lean_dec(v_start_1540_);
v___x_1553_ = lean_nat_dec_le(v___x_1542_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_dec(v___x_1552_);
v___y_1545_ = v___x_1542_;
goto v___jp_1544_;
}
else
{
v___y_1545_ = v___x_1552_;
goto v___jp_1544_;
}
v___jp_1544_:
{
size_t v_sz_1546_; size_t v___x_1547_; lean_object* v___x_13285__overap_1548_; lean_object* v___x_1549_; lean_object* v_snd_1550_; lean_object* v___x_1551_; 
v_sz_1546_ = lean_array_size(v_items_1541_);
v___x_1547_ = ((size_t)0ULL);
v___x_13285__overap_1548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1496_, v_items_1541_, v___f_1543_, v_sz_1546_, v___x_1547_, v___y_1545_);
v___x_1549_ = lean_apply_2(v___x_13285__overap_1548_, v_a_1494_, v_a_1495_);
v_snd_1550_ = lean_ctor_get(v___x_1549_, 1);
lean_inc(v_snd_1550_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1550_);
return v___x_1551_;
}
}
case 4:
{
lean_object* v_items_1554_; lean_object* v___x_1555_; lean_object* v___f_1556_; size_t v_sz_1557_; size_t v___x_1558_; lean_object* v___x_13388__overap_1559_; lean_object* v___x_1560_; lean_object* v_snd_1561_; lean_object* v___x_1562_; 
v_items_1554_ = lean_ctor_get(v_x_1493_, 0);
lean_inc_ref(v_items_1554_);
lean_dec_ref(v_x_1493_);
v___x_1555_ = lean_box(0);
v___f_1556_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 8, 3);
lean_closure_set(v___f_1556_, 0, v_inst_1491_);
lean_closure_set(v___f_1556_, 1, v_inst_1492_);
lean_closure_set(v___f_1556_, 2, v___x_1555_);
v_sz_1557_ = lean_array_size(v_items_1554_);
v___x_1558_ = ((size_t)0ULL);
v___x_13388__overap_1559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1496_, v_items_1554_, v___f_1556_, v_sz_1557_, v___x_1558_, v___x_1555_);
v___x_1560_ = lean_apply_2(v___x_13388__overap_1559_, v_a_1494_, v_a_1495_);
v_snd_1561_ = lean_ctor_get(v___x_1560_, 1);
lean_inc(v_snd_1561_);
lean_dec_ref(v___x_1560_);
v___x_1562_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1561_);
return v___x_1562_;
}
case 5:
{
lean_object* v_items_1563_; uint8_t v_inEmph_1564_; uint8_t v_inBold_1565_; uint8_t v_inLink_1566_; lean_object* v_linePrefix_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1584_; 
v_items_1563_ = lean_ctor_get(v_x_1493_, 0);
lean_inc_ref(v_items_1563_);
lean_dec_ref(v_x_1493_);
v_inEmph_1564_ = lean_ctor_get_uint8(v_a_1494_, sizeof(void*)*1);
v_inBold_1565_ = lean_ctor_get_uint8(v_a_1494_, sizeof(void*)*1 + 1);
v_inLink_1566_ = lean_ctor_get_uint8(v_a_1494_, sizeof(void*)*1 + 2);
v_linePrefix_1567_ = lean_ctor_get(v_a_1494_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_a_1494_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1569_ = v_a_1494_;
v_isShared_1570_ = v_isSharedCheck_1584_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_linePrefix_1567_);
lean_dec(v_a_1494_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1584_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___f_1572_; size_t v_sz_1573_; size_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1571_ = lean_box(0);
v___f_1572_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1), 8, 3);
lean_closure_set(v___f_1572_, 0, v_inst_1491_);
lean_closure_set(v___f_1572_, 1, v_inst_1492_);
lean_closure_set(v___f_1572_, 2, v___x_1571_);
v_sz_1573_ = lean_array_size(v_items_1563_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_1576_ = lean_string_append(v_linePrefix_1567_, v___x_1575_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1576_);
v___x_1578_ = v___x_1569_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*1, v_inEmph_1564_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*1 + 1, v_inBold_1565_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*1 + 2, v_inLink_1566_);
v___x_1578_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_13494__overap_1579_; lean_object* v___x_1580_; lean_object* v_snd_1581_; lean_object* v___x_1582_; 
v___x_13494__overap_1579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1496_, v_items_1563_, v___f_1572_, v_sz_1573_, v___x_1574_, v___x_1571_);
v___x_1580_ = lean_apply_2(v___x_13494__overap_1579_, v___x_1578_, v_a_1495_);
v_snd_1581_ = lean_ctor_get(v___x_1580_, 1);
lean_inc(v_snd_1581_);
lean_dec_ref(v___x_1580_);
v___x_1582_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1581_);
return v___x_1582_;
}
}
}
case 6:
{
lean_object* v_content_1585_; lean_object* v___x_1586_; lean_object* v___f_1587_; size_t v_sz_1588_; size_t v___x_1589_; lean_object* v___x_13530__overap_1590_; lean_object* v___x_1591_; lean_object* v_snd_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
v_content_1585_ = lean_ctor_get(v_x_1493_, 0);
lean_inc_ref(v_content_1585_);
lean_dec_ref(v_x_1493_);
v___x_1586_ = lean_box(0);
v___f_1587_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1), 8, 3);
lean_closure_set(v___f_1587_, 0, v_inst_1491_);
lean_closure_set(v___f_1587_, 1, v_inst_1492_);
lean_closure_set(v___f_1587_, 2, v___x_1586_);
v_sz_1588_ = lean_array_size(v_content_1585_);
v___x_1589_ = ((size_t)0ULL);
v___x_13530__overap_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1496_, v_content_1585_, v___f_1587_, v_sz_1588_, v___x_1589_, v___x_1586_);
v___x_1591_ = lean_apply_2(v___x_13530__overap_1590_, v_a_1494_, v_a_1495_);
v_snd_1592_ = lean_ctor_get(v___x_1591_, 1);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; 
v_unused_1600_ = lean_ctor_get(v___x_1591_, 0);
lean_dec(v_unused_1600_);
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_snd_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1586_);
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_snd_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
default: 
{
lean_object* v_container_1601_; lean_object* v_content_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_container_1601_ = lean_ctor_get(v_x_1493_, 0);
lean_inc(v_container_1601_);
v_content_1602_ = lean_ctor_get(v_x_1493_, 1);
lean_inc_ref(v_content_1602_);
lean_dec_ref(v_x_1493_);
lean_inc_ref(v_inst_1491_);
v___x_1603_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown), 5, 2);
lean_closure_set(v___x_1603_, 0, lean_box(0));
lean_closure_set(v___x_1603_, 1, v_inst_1491_);
lean_inc_ref(v_inst_1492_);
v___x_1604_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg), 5, 2);
lean_closure_set(v___x_1604_, 0, v_inst_1491_);
lean_closure_set(v___x_1604_, 1, v_inst_1492_);
v___x_1605_ = lean_apply_6(v_inst_1492_, v___x_1603_, v___x_1604_, v_container_1601_, v_content_1602_, v_a_1494_, v_a_1495_);
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v___x_1608_, lean_object* v_a_1609_, lean_object* v_x_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___x_1614_; lean_object* v_snd_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1623_; 
v___x_1614_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1606_, v_inst_1607_, v_a_1609_, v___y_1612_, v___y_1613_);
v_snd_1615_ = lean_ctor_get(v___x_1614_, 1);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v___x_1614_, 0);
lean_dec(v_unused_1624_);
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_snd_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1608_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1619_);
v___x_1621_ = v___x_1617_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_snd_1615_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1625_, lean_object* v_b_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_x_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1627_, v_inst_1628_, v_x_1629_, v_a_1630_, v_a_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_block_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1633_, v_inst_1634_, v_block_1635_, v_a_1636_, v_a_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1639_, lean_object* v_b_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_block_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1641_, v_inst_1642_, v_block_1643_, v_a_1644_, v_a_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_1647_, lean_object* v_inst_1648_, lean_object* v_block_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1647_, v_inst_1648_, v_block_1649_, v___y_1650_, v___y_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1653_, lean_object* v_inst_1654_){
_start:
{
lean_object* v___f_1655_; 
v___f_1655_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1655_, 0, v_inst_1653_);
lean_closure_set(v___f_1655_, 1, v_inst_1654_);
return v___f_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1656_, lean_object* v_b_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_){
_start:
{
lean_object* v___f_1660_; 
v___f_1660_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1660_, 0, v_inst_1658_);
lean_closure_set(v___f_1660_, 1, v_inst_1659_);
return v___f_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0(uint32_t v___x_1661_, lean_object* v_s_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_string_push(v_s_1662_, v___x_1661_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0___boxed(lean_object* v___x_1664_, lean_object* v_s_1665_){
_start:
{
uint32_t v___x_4130__boxed_1666_; lean_object* v_res_1667_; 
v___x_4130__boxed_1666_ = lean_unbox_uint32(v___x_1664_);
lean_dec(v___x_1664_);
v_res_1667_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0(v___x_4130__boxed_1666_, v_s_1665_);
return v_res_1667_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = 35;
v___x_1669_ = lean_box_uint32(v___x_1668_);
return v___x_1669_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___f_1671_; 
v___x_1670_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1671_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1671_, 0, v___x_1670_);
return v___f_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v___x_1674_, lean_object* v___x_1675_, lean_object* v_a_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3(v_inst_1672_, v_inst_1673_, v___x_1674_, v___x_1675_, v_a_1676_, v_x_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___x_1674_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_level_1684_, lean_object* v_part_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v_snd_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v_snd_1698_; lean_object* v_title_1699_; lean_object* v_content_1700_; lean_object* v_subParts_1701_; lean_object* v___x_1702_; lean_object* v___f_1703_; size_t v_sz_1704_; size_t v___x_1705_; lean_object* v___x_3968__overap_1706_; lean_object* v___x_1707_; lean_object* v_snd_1708_; lean_object* v___x_1709_; lean_object* v_snd_1710_; lean_object* v___f_1711_; size_t v_sz_1712_; lean_object* v___x_3986__overap_1713_; lean_object* v___x_1714_; lean_object* v_snd_1715_; lean_object* v___x_1716_; lean_object* v_snd_1717_; lean_object* v___f_1718_; size_t v_sz_1719_; lean_object* v___x_4004__overap_1720_; lean_object* v___x_1721_; lean_object* v_snd_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v___x_1688_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20);
v___x_1689_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_endBlock___closed__0));
v___f_1690_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___closed__0);
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = lean_nat_add(v_level_1684_, v___x_1691_);
lean_inc(v___x_1692_);
v___x_1693_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1690_, v___x_1692_, v___x_1689_);
v___x_1694_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1693_, v_a_1687_);
lean_dec(v___x_1693_);
v_snd_1695_ = lean_ctor_get(v___x_1694_, 1);
lean_inc(v_snd_1695_);
lean_dec_ref(v___x_1694_);
v___x_1696_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_1697_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1696_, v_snd_1695_);
v_snd_1698_ = lean_ctor_get(v___x_1697_, 1);
lean_inc(v_snd_1698_);
lean_dec_ref(v___x_1697_);
v_title_1699_ = lean_ctor_get(v_part_1685_, 0);
lean_inc_ref(v_title_1699_);
v_content_1700_ = lean_ctor_get(v_part_1685_, 3);
lean_inc_ref(v_content_1700_);
v_subParts_1701_ = lean_ctor_get(v_part_1685_, 4);
lean_inc_ref(v_subParts_1701_);
lean_dec_ref(v_part_1685_);
v___x_1702_ = lean_box(0);
lean_inc_ref(v_inst_1682_);
v___f_1703_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___lam__0), 7, 2);
lean_closure_set(v___f_1703_, 0, v_inst_1682_);
lean_closure_set(v___f_1703_, 1, v___x_1702_);
v_sz_1704_ = lean_array_size(v_title_1699_);
v___x_1705_ = ((size_t)0ULL);
v___x_3968__overap_1706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1688_, v_title_1699_, v___f_1703_, v_sz_1704_, v___x_1705_, v___x_1702_);
lean_inc_ref(v_a_1686_);
v___x_1707_ = lean_apply_2(v___x_3968__overap_1706_, v_a_1686_, v_snd_1698_);
v_snd_1708_ = lean_ctor_get(v___x_1707_, 1);
lean_inc(v_snd_1708_);
lean_dec_ref(v___x_1707_);
v___x_1709_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1708_);
v_snd_1710_ = lean_ctor_get(v___x_1709_, 1);
lean_inc(v_snd_1710_);
lean_dec_ref(v___x_1709_);
lean_inc_ref(v_inst_1683_);
lean_inc_ref(v_inst_1682_);
v___f_1711_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1), 8, 3);
lean_closure_set(v___f_1711_, 0, v_inst_1682_);
lean_closure_set(v___f_1711_, 1, v_inst_1683_);
lean_closure_set(v___f_1711_, 2, v___x_1702_);
v_sz_1712_ = lean_array_size(v_content_1700_);
v___x_3986__overap_1713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1688_, v_content_1700_, v___f_1711_, v_sz_1712_, v___x_1705_, v___x_1702_);
lean_inc_ref(v_a_1686_);
v___x_1714_ = lean_apply_2(v___x_3986__overap_1713_, v_a_1686_, v_snd_1710_);
v_snd_1715_ = lean_ctor_get(v___x_1714_, 1);
lean_inc(v_snd_1715_);
lean_dec_ref(v___x_1714_);
v___x_1716_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_1715_);
v_snd_1717_ = lean_ctor_get(v___x_1716_, 1);
lean_inc(v_snd_1717_);
lean_dec_ref(v___x_1716_);
v___f_1718_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3___boxed), 9, 4);
lean_closure_set(v___f_1718_, 0, v_inst_1682_);
lean_closure_set(v___f_1718_, 1, v_inst_1683_);
lean_closure_set(v___f_1718_, 2, v___x_1692_);
lean_closure_set(v___f_1718_, 3, v___x_1702_);
v_sz_1719_ = lean_array_size(v_subParts_1701_);
v___x_4004__overap_1720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1688_, v_subParts_1701_, v___f_1718_, v_sz_1719_, v___x_1705_, v___x_1702_);
v___x_1721_ = lean_apply_2(v___x_4004__overap_1720_, v_a_1686_, v_snd_1717_);
v_snd_1722_ = lean_ctor_get(v___x_1721_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v___x_1721_, 0);
lean_dec(v_unused_1730_);
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_snd_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1702_);
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_snd_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___lam__3(lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v___x_1733_, lean_object* v___x_1734_, lean_object* v_a_1735_, lean_object* v_x_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___x_1740_; lean_object* v_snd_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1749_; 
v___x_1740_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1731_, v_inst_1732_, v___x_1733_, v_a_1735_, v___y_1738_, v___y_1739_);
v_snd_1741_ = lean_ctor_get(v___x_1740_, 1);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v___x_1740_, 0);
lean_dec(v_unused_1750_);
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1749_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_snd_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1749_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1734_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1745_);
v___x_1747_ = v___x_1743_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_snd_1741_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1751_, lean_object* v_inst_1752_, lean_object* v_level_1753_, lean_object* v_part_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1751_, v_inst_1752_, v_level_1753_, v_part_1754_, v_a_1755_, v_a_1756_);
lean_dec(v_level_1753_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown(lean_object* v_i_1758_, lean_object* v_b_1759_, lean_object* v_p_1760_, lean_object* v_inst_1761_, lean_object* v_inst_1762_, lean_object* v_level_1763_, lean_object* v_part_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1761_, v_inst_1762_, v_level_1763_, v_part_1764_, v_a_1765_, v_a_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___boxed(lean_object* v_i_1768_, lean_object* v_b_1769_, lean_object* v_p_1770_, lean_object* v_inst_1771_, lean_object* v_inst_1772_, lean_object* v_level_1773_, lean_object* v_part_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown(v_i_1768_, v_b_1769_, v_p_1770_, v_inst_1771_, v_inst_1772_, v_level_1773_, v_part_1774_, v_a_1775_, v_a_1776_);
lean_dec(v_level_1773_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_part_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___redArg(v_inst_1778_, v_inst_1779_, v___x_1783_, v_part_1780_, v_a_1781_, v_a_1782_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1785_, lean_object* v_b_1786_, lean_object* v_p_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v_part_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1788_, v_inst_1789_, v_part_1790_, v_a_1791_, v_a_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_part_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1794_, v_inst_1795_, v_part_1796_, v___y_1797_, v___y_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1800_, lean_object* v_inst_1801_){
_start:
{
lean_object* v___f_1802_; 
v___f_1802_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1802_, 0, v_inst_1800_);
lean_closure_set(v___f_1802_, 1, v_inst_1801_);
return v___f_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1803_, lean_object* v_b_1804_, lean_object* v_p_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_){
_start:
{
lean_object* v___f_1808_; 
v___f_1808_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1808_, 0, v_inst_1806_);
lean_closure_set(v___f_1808_, 1, v_inst_1807_);
return v___f_1808_;
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
