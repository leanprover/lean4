// Lean compiler output
// Module: Lean.DocString.Markdown
// Imports: public import Lean.DocString.Types public import Init.Data.String.TakeDrop public import Init.Data.String.Search public import Init.Data.String.Length import Init.Data.ToString.Macro import Init.While
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Doc_Inline_empty(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static const lean_ctor_object l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0 = (const lean_object*)&l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default = (const lean_object*)&l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_MarkdownM_instInhabitedInlineCtx = (const lean_object*)&l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[^"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]:"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_Doc_MarkdownM_run_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_MarkdownM_run_x27___closed__0 = (const lean_object*)&l_Lean_Doc_MarkdownM_run_x27___closed__0_value;
static const lean_string_object l_Lean_Doc_MarkdownM_run_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Doc_MarkdownM_run_x27___closed__1 = (const lean_object*)&l_Lean_Doc_MarkdownM_run_x27___closed__1_value;
static const lean_string_object l_Lean_Doc_MarkdownM_run_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l_Lean_Doc_MarkdownM_run_x27___closed__2 = (const lean_object*)&l_Lean_Doc_MarkdownM_run_x27___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run_x27(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_prefixLines(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_prefixListLines(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_prefixListLines___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Doc_joinBlocks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_joinBlocks___closed__0 = (const lean_object*)&l_Lean_Doc_joinBlocks___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "​"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instMarkdownInlineEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instMarkdownInlineEmpty___closed__0 = (const lean_object*)&l_Lean_Doc_instMarkdownInlineEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instMarkdownInlineEmpty = (const lean_object*)&l_Lean_Doc_instMarkdownInlineEmpty___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instMarkdownBlockEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instMarkdownBlockEmpty___closed__0 = (const lean_object*)&l_Lean_Doc_instMarkdownBlockEmpty___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(lean_object*, uint32_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "*_`<[]{}()#"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3;
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0;
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "> -+. \t"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(lean_object*);
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
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "**"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]("};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_partMarkdown___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_partMarkdown___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0(lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
if (lean_obj_tag(v_a_7_) == 0)
{
lean_object* v___x_9_; 
v___x_9_ = l_List_reverse___redArg(v_a_8_);
return v___x_9_;
}
else
{
lean_object* v_head_10_; lean_object* v_tail_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_26_; 
v_head_10_ = lean_ctor_get(v_a_7_, 0);
v_tail_11_ = lean_ctor_get(v_a_7_, 1);
v_isSharedCheck_26_ = !lean_is_exclusive(v_a_7_);
if (v_isSharedCheck_26_ == 0)
{
v___x_13_ = v_a_7_;
v_isShared_14_ = v_isSharedCheck_26_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_tail_11_);
lean_inc(v_head_10_);
lean_dec(v_a_7_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_26_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v_fst_15_; lean_object* v_snd_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_23_; 
v_fst_15_ = lean_ctor_get(v_head_10_, 0);
lean_inc(v_fst_15_);
v_snd_16_ = lean_ctor_get(v_head_10_, 1);
lean_inc(v_snd_16_);
lean_dec(v_head_10_);
v___x_17_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_18_ = lean_string_append(v___x_17_, v_fst_15_);
lean_dec(v_fst_15_);
v___x_19_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__1));
v___x_20_ = lean_string_append(v___x_18_, v___x_19_);
v___x_21_ = lean_string_append(v___x_20_, v_snd_16_);
lean_dec(v_snd_16_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v_a_8_);
lean_ctor_set(v___x_13_, 0, v___x_21_);
v___x_23_ = v___x_13_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_21_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_a_8_);
v___x_23_ = v_reuseFailAlloc_25_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
v_a_7_ = v_tail_11_;
v_a_8_ = v___x_23_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run_x27(lean_object* v_act_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v_fst_35_; lean_object* v_snd_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v_main_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__0));
v___x_34_ = lean_apply_1(v_act_31_, v___x_33_);
v_fst_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_fst_35_);
v_snd_36_ = lean_ctor_get(v___x_34_, 1);
lean_inc(v_snd_36_);
lean_dec_ref(v___x_34_);
v___x_37_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_38_ = lean_array_to_list(v_fst_35_);
v_main_39_ = l_String_intercalate(v___x_37_, v___x_38_);
v___x_40_ = lean_array_get_size(v_snd_36_);
v___x_41_ = lean_nat_dec_eq(v___x_40_, v___x_32_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_foots_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_42_ = lean_array_to_list(v_snd_36_);
v___x_43_ = lean_box(0);
v_foots_44_ = l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0(v___x_42_, v___x_43_);
v___x_45_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__2));
v___x_46_ = lean_string_append(v_main_39_, v___x_45_);
v___x_47_ = l_String_intercalate(v___x_45_, v_foots_44_);
v___x_48_ = lean_string_append(v___x_46_, v___x_47_);
lean_dec_ref(v___x_47_);
return v___x_48_;
}
else
{
lean_dec(v_snd_36_);
return v_main_39_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(lean_object* v_s_49_, lean_object* v_pos_50_){
_start:
{
lean_object* v_str_51_; lean_object* v_startInclusive_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v_str_51_ = lean_ctor_get(v_s_49_, 0);
v_startInclusive_52_ = lean_ctor_get(v_s_49_, 1);
v___x_53_ = lean_nat_add(v_startInclusive_52_, v_pos_50_);
v___x_54_ = lean_nat_sub(v___x_53_, v_startInclusive_52_);
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_nat_dec_eq(v___x_54_, v___x_55_);
if (v___x_56_ == 0)
{
uint32_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; uint32_t v___x_63_; uint8_t v___x_64_; 
v___x_57_ = 32;
lean_inc(v_startInclusive_52_);
lean_inc_ref(v_str_51_);
v___x_58_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_58_, 0, v_str_51_);
lean_ctor_set(v___x_58_, 1, v_startInclusive_52_);
lean_ctor_set(v___x_58_, 2, v___x_53_);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_sub(v___x_54_, v___x_59_);
lean_dec(v___x_54_);
v___x_61_ = l_String_Slice_posLE(v___x_58_, v___x_60_);
lean_dec_ref_known(v___x_58_, 3);
v___x_62_ = lean_nat_add(v_startInclusive_52_, v___x_61_);
v___x_63_ = lean_string_utf8_get_fast(v_str_51_, v___x_62_);
lean_dec(v___x_62_);
v___x_64_ = lean_uint32_dec_eq(v___x_63_, v___x_57_);
if (v___x_64_ == 0)
{
lean_dec(v___x_61_);
return v_pos_50_;
}
else
{
uint8_t v___x_65_; 
v___x_65_ = lean_nat_dec_lt(v___x_61_, v_pos_50_);
if (v___x_65_ == 0)
{
lean_dec(v___x_61_);
return v_pos_50_;
}
else
{
lean_dec(v_pos_50_);
v_pos_50_ = v___x_61_;
goto _start;
}
}
}
else
{
lean_dec(v___x_54_);
lean_dec(v___x_53_);
return v_pos_50_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0___boxed(lean_object* v_s_67_, lean_object* v_pos_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(v_s_67_, v_pos_68_);
lean_dec_ref(v_s_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(lean_object* v_s_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_string_utf8_byte_size(v_s_70_);
lean_inc_ref(v_s_70_);
v___x_73_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_73_, 0, v_s_70_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_72_);
v___x_74_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(v___x_73_, v___x_72_);
lean_dec_ref_known(v___x_73_, 3);
v___x_75_ = lean_string_utf8_extract(v_s_70_, v___x_71_, v___x_74_);
lean_dec(v___x_74_);
lean_dec_ref(v_s_70_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(lean_object* v_p_76_, lean_object* v_pTrim_77_, size_t v_sz_78_, size_t v_i_79_, lean_object* v_bs_80_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = lean_usize_dec_lt(v_i_79_, v_sz_78_);
if (v___x_81_ == 0)
{
lean_dec_ref(v_pTrim_77_);
lean_dec_ref(v_p_76_);
return v_bs_80_;
}
else
{
lean_object* v_v_82_; lean_object* v___x_83_; lean_object* v_bs_x27_84_; lean_object* v___y_86_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_v_82_ = lean_array_uget(v_bs_80_, v_i_79_);
v___x_83_ = lean_unsigned_to_nat(0u);
v_bs_x27_84_ = lean_array_uset(v_bs_80_, v_i_79_, v___x_83_);
v___x_91_ = lean_string_utf8_byte_size(v_v_82_);
v___x_92_ = lean_nat_dec_eq(v___x_91_, v___x_83_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_inc_ref(v_p_76_);
v___x_93_ = lean_string_append(v_p_76_, v_v_82_);
lean_dec(v_v_82_);
v___y_86_ = v___x_93_;
goto v___jp_85_;
}
else
{
lean_dec(v_v_82_);
lean_inc_ref(v_pTrim_77_);
v___y_86_ = v_pTrim_77_;
goto v___jp_85_;
}
v___jp_85_:
{
size_t v___x_87_; size_t v___x_88_; lean_object* v___x_89_; 
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_add(v_i_79_, v___x_87_);
v___x_89_ = lean_array_uset(v_bs_x27_84_, v_i_79_, v___y_86_);
v_i_79_ = v___x_88_;
v_bs_80_ = v___x_89_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0___boxed(lean_object* v_p_94_, lean_object* v_pTrim_95_, lean_object* v_sz_96_, lean_object* v_i_97_, lean_object* v_bs_98_){
_start:
{
size_t v_sz_boxed_99_; size_t v_i_boxed_100_; lean_object* v_res_101_; 
v_sz_boxed_99_ = lean_unbox_usize(v_sz_96_);
lean_dec(v_sz_96_);
v_i_boxed_100_ = lean_unbox_usize(v_i_97_);
lean_dec(v_i_97_);
v_res_101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(v_p_94_, v_pTrim_95_, v_sz_boxed_99_, v_i_boxed_100_, v_bs_98_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_prefixLines(lean_object* v_p_102_, lean_object* v_lines_103_){
_start:
{
lean_object* v_pTrim_104_; size_t v_sz_105_; size_t v___x_106_; lean_object* v___x_107_; 
lean_inc_ref(v_p_102_);
v_pTrim_104_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_p_102_);
v_sz_105_ = lean_array_size(v_lines_103_);
v___x_106_ = ((size_t)0ULL);
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(v_p_102_, v_pTrim_104_, v_sz_105_, v___x_106_, v_lines_103_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(lean_object* v_rest_108_, lean_object* v_restTrim_109_, lean_object* v_head_110_, lean_object* v_headTrim_111_, lean_object* v_as_112_, lean_object* v_i_113_, lean_object* v_j_114_, lean_object* v_bs_115_){
_start:
{
lean_object* v_zero_116_; uint8_t v_isZero_117_; 
v_zero_116_ = lean_unsigned_to_nat(0u);
v_isZero_117_ = lean_nat_dec_eq(v_i_113_, v_zero_116_);
if (v_isZero_117_ == 1)
{
lean_dec(v_j_114_);
lean_dec(v_i_113_);
lean_dec_ref(v_headTrim_111_);
lean_dec_ref(v_head_110_);
lean_dec_ref(v_restTrim_109_);
lean_dec_ref(v_rest_108_);
return v_bs_115_;
}
else
{
lean_object* v_one_118_; lean_object* v_n_119_; lean_object* v___y_121_; lean_object* v___x_125_; lean_object* v_fst_127_; lean_object* v_snd_128_; uint8_t v___x_132_; 
v_one_118_ = lean_unsigned_to_nat(1u);
v_n_119_ = lean_nat_sub(v_i_113_, v_one_118_);
lean_dec(v_i_113_);
v___x_125_ = lean_array_fget_borrowed(v_as_112_, v_j_114_);
v___x_132_ = lean_nat_dec_eq(v_j_114_, v_zero_116_);
if (v___x_132_ == 0)
{
lean_inc_ref(v_restTrim_109_);
lean_inc_ref(v_rest_108_);
v_fst_127_ = v_rest_108_;
v_snd_128_ = v_restTrim_109_;
goto v___jp_126_;
}
else
{
lean_inc_ref(v_headTrim_111_);
lean_inc_ref(v_head_110_);
v_fst_127_ = v_head_110_;
v_snd_128_ = v_headTrim_111_;
goto v___jp_126_;
}
v___jp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_nat_add(v_j_114_, v_one_118_);
lean_dec(v_j_114_);
v___x_123_ = lean_array_push(v_bs_115_, v___y_121_);
v_i_113_ = v_n_119_;
v_j_114_ = v___x_122_;
v_bs_115_ = v___x_123_;
goto _start;
}
v___jp_126_:
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_string_utf8_byte_size(v___x_125_);
v___x_130_ = lean_nat_dec_eq(v___x_129_, v_zero_116_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
lean_dec_ref(v_snd_128_);
v___x_131_ = lean_string_append(v_fst_127_, v___x_125_);
v___y_121_ = v___x_131_;
goto v___jp_120_;
}
else
{
lean_dec_ref(v_fst_127_);
v___y_121_ = v_snd_128_;
goto v___jp_120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg___boxed(lean_object* v_rest_133_, lean_object* v_restTrim_134_, lean_object* v_head_135_, lean_object* v_headTrim_136_, lean_object* v_as_137_, lean_object* v_i_138_, lean_object* v_j_139_, lean_object* v_bs_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_133_, v_restTrim_134_, v_head_135_, v_headTrim_136_, v_as_137_, v_i_138_, v_j_139_, v_bs_140_);
lean_dec_ref(v_as_137_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_prefixListLines(lean_object* v_head_142_, lean_object* v_rest_143_, lean_object* v_lines_144_){
_start:
{
lean_object* v_headTrim_145_; lean_object* v_restTrim_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_inc_ref(v_head_142_);
v_headTrim_145_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_head_142_);
lean_inc_ref(v_rest_143_);
v_restTrim_146_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_rest_143_);
v___x_147_ = lean_array_get_size(v_lines_144_);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_mk_empty_array_with_capacity(v___x_147_);
v___x_150_ = l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_143_, v_restTrim_146_, v_head_142_, v_headTrim_145_, v_lines_144_, v___x_147_, v___x_148_, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_prefixListLines___boxed(lean_object* v_head_151_, lean_object* v_rest_152_, lean_object* v_lines_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Doc_prefixListLines(v_head_151_, v_rest_152_, v_lines_153_);
lean_dec_ref(v_lines_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0(lean_object* v_rest_155_, lean_object* v_restTrim_156_, lean_object* v_head_157_, lean_object* v_headTrim_158_, lean_object* v_as_159_, lean_object* v_i_160_, lean_object* v_j_161_, lean_object* v_inv_162_, lean_object* v_bs_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_155_, v_restTrim_156_, v_head_157_, v_headTrim_158_, v_as_159_, v_i_160_, v_j_161_, v_bs_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___boxed(lean_object* v_rest_165_, lean_object* v_restTrim_166_, lean_object* v_head_167_, lean_object* v_headTrim_168_, lean_object* v_as_169_, lean_object* v_i_170_, lean_object* v_j_171_, lean_object* v_inv_172_, lean_object* v_bs_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0(v_rest_165_, v_restTrim_166_, v_head_167_, v_headTrim_168_, v_as_169_, v_i_170_, v_j_171_, v_inv_172_, v_bs_173_);
lean_dec_ref(v_as_169_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(lean_object* v_as_176_, size_t v_i_177_, size_t v_stop_178_, lean_object* v_b_179_){
_start:
{
lean_object* v___y_181_; uint8_t v___x_185_; 
v___x_185_ = lean_usize_dec_eq(v_i_177_, v_stop_178_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_186_ = lean_array_uget_borrowed(v_as_176_, v_i_177_);
v___x_187_ = lean_array_get_size(v___x_186_);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_nat_dec_eq(v___x_187_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = lean_array_get_size(v_b_179_);
v___x_191_ = lean_nat_dec_eq(v___x_190_, v___x_188_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_193_ = lean_array_push(v_b_179_, v___x_192_);
v___x_194_ = l_Array_append___redArg(v___x_193_, v___x_186_);
v___y_181_ = v___x_194_;
goto v___jp_180_;
}
else
{
lean_dec_ref(v_b_179_);
lean_inc(v___x_186_);
v___y_181_ = v___x_186_;
goto v___jp_180_;
}
}
else
{
v___y_181_ = v_b_179_;
goto v___jp_180_;
}
}
else
{
return v_b_179_;
}
v___jp_180_:
{
size_t v___x_182_; size_t v___x_183_; 
v___x_182_ = ((size_t)1ULL);
v___x_183_ = lean_usize_add(v_i_177_, v___x_182_);
v_i_177_ = v___x_183_;
v_b_179_ = v___y_181_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___boxed(lean_object* v_as_195_, lean_object* v_i_196_, lean_object* v_stop_197_, lean_object* v_b_198_){
_start:
{
size_t v_i_boxed_199_; size_t v_stop_boxed_200_; lean_object* v_res_201_; 
v_i_boxed_199_ = lean_unbox_usize(v_i_196_);
lean_dec(v_i_196_);
v_stop_boxed_200_ = lean_unbox_usize(v_stop_197_);
lean_dec(v_stop_197_);
v_res_201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_as_195_, v_i_boxed_199_, v_stop_boxed_200_, v_b_198_);
lean_dec_ref(v_as_195_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks(lean_object* v_blocks_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_207_ = lean_array_get_size(v_blocks_204_);
v___x_208_ = lean_nat_dec_lt(v___x_205_, v___x_207_);
if (v___x_208_ == 0)
{
return v___x_206_;
}
else
{
uint8_t v___x_209_; 
v___x_209_ = lean_nat_dec_le(v___x_207_, v___x_207_);
if (v___x_209_ == 0)
{
if (v___x_208_ == 0)
{
return v___x_206_;
}
else
{
size_t v___x_210_; size_t v___x_211_; lean_object* v___x_212_; 
v___x_210_ = ((size_t)0ULL);
v___x_211_ = lean_usize_of_nat(v___x_207_);
v___x_212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_204_, v___x_210_, v___x_211_, v___x_206_);
return v___x_212_;
}
}
else
{
size_t v___x_213_; size_t v___x_214_; lean_object* v___x_215_; 
v___x_213_ = ((size_t)0ULL);
v___x_214_ = lean_usize_of_nat(v___x_207_);
v___x_215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_204_, v___x_213_, v___x_214_, v___x_206_);
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks___boxed(lean_object* v_blocks_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Doc_joinBlocks(v_blocks_216_);
lean_dec_ref(v_blocks_216_);
return v_res_217_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_220_ = lean_string_utf8_byte_size(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(lean_object* v_l_222_, lean_object* v_r_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_224_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_225_ = lean_string_utf8_byte_size(v_l_222_);
v___x_226_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1);
v___x_227_ = lean_nat_dec_le(v___x_226_, v___x_225_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
v___x_228_ = lean_string_append(v_l_222_, v_r_223_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_nat_sub(v___x_225_, v___x_226_);
v___x_231_ = lean_string_memcmp(v_l_222_, v___x_224_, v___x_230_, v___x_229_, v___x_226_);
lean_dec(v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
v___x_232_ = lean_string_append(v_l_222_, v_r_223_);
return v___x_232_;
}
else
{
lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_233_ = lean_string_utf8_byte_size(v_r_223_);
v___x_234_ = lean_nat_dec_le(v___x_226_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
v___x_235_ = lean_string_append(v_l_222_, v_r_223_);
return v___x_235_;
}
else
{
uint8_t v___x_236_; 
v___x_236_ = lean_string_memcmp(v_r_223_, v___x_224_, v___x_229_, v___x_229_, v___x_226_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
v___x_237_ = lean_string_append(v_l_222_, v_r_223_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2));
v___x_239_ = lean_string_append(v_l_222_, v___x_238_);
v___x_240_ = lean_string_append(v___x_239_, v_r_223_);
return v___x_240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___boxed(lean_object* v_l_241_, lean_object* v_r_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v_l_241_, v_r_242_);
lean_dec_ref(v_r_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(lean_object* v_as_244_, size_t v_i_245_, size_t v_stop_246_, lean_object* v_b_247_){
_start:
{
lean_object* v___y_249_; uint8_t v___x_253_; 
v___x_253_ = lean_usize_dec_eq(v_i_245_, v_stop_246_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_254_ = lean_array_uget_borrowed(v_as_244_, v_i_245_);
v___x_255_ = lean_array_get_size(v___x_254_);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_nat_dec_eq(v___x_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_array_get_size(v_b_247_);
v___x_259_ = lean_nat_dec_eq(v___x_258_, v___x_256_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v_lastIdx_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_glued_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_260_ = lean_unsigned_to_nat(1u);
v_lastIdx_261_ = lean_nat_sub(v___x_258_, v___x_260_);
v___x_262_ = lean_array_fget_borrowed(v_b_247_, v_lastIdx_261_);
v___x_263_ = lean_array_fget_borrowed(v___x_254_, v___x_256_);
lean_inc(v___x_262_);
v_glued_264_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v___x_262_, v___x_263_);
v___x_265_ = lean_array_fset(v_b_247_, v_lastIdx_261_, v_glued_264_);
lean_dec(v_lastIdx_261_);
v___x_266_ = l_Array_extract___redArg(v___x_254_, v___x_260_, v___x_255_);
v___x_267_ = l_Array_append___redArg(v___x_265_, v___x_266_);
lean_dec_ref(v___x_266_);
v___y_249_ = v___x_267_;
goto v___jp_248_;
}
else
{
lean_dec_ref(v_b_247_);
lean_inc(v___x_254_);
v___y_249_ = v___x_254_;
goto v___jp_248_;
}
}
else
{
v___y_249_ = v_b_247_;
goto v___jp_248_;
}
}
else
{
return v_b_247_;
}
v___jp_248_:
{
size_t v___x_250_; size_t v___x_251_; 
v___x_250_ = ((size_t)1ULL);
v___x_251_ = lean_usize_add(v_i_245_, v___x_250_);
v_i_245_ = v___x_251_;
v_b_247_ = v___y_249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0___boxed(lean_object* v_as_268_, lean_object* v_i_269_, lean_object* v_stop_270_, lean_object* v_b_271_){
_start:
{
size_t v_i_boxed_272_; size_t v_stop_boxed_273_; lean_object* v_res_274_; 
v_i_boxed_272_ = lean_unbox_usize(v_i_269_);
lean_dec(v_i_269_);
v_stop_boxed_273_ = lean_unbox_usize(v_stop_270_);
lean_dec(v_stop_270_);
v_res_274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_as_268_, v_i_boxed_272_, v_stop_boxed_273_, v_b_271_);
lean_dec_ref(v_as_268_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines(lean_object* v_parts_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_278_ = lean_array_get_size(v_parts_275_);
v___x_279_ = lean_nat_dec_lt(v___x_276_, v___x_278_);
if (v___x_279_ == 0)
{
return v___x_277_;
}
else
{
uint8_t v___x_280_; 
v___x_280_ = lean_nat_dec_le(v___x_278_, v___x_278_);
if (v___x_280_ == 0)
{
if (v___x_279_ == 0)
{
return v___x_277_;
}
else
{
size_t v___x_281_; size_t v___x_282_; lean_object* v___x_283_; 
v___x_281_ = ((size_t)0ULL);
v___x_282_ = lean_usize_of_nat(v___x_278_);
v___x_283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_275_, v___x_281_, v___x_282_, v___x_277_);
return v___x_283_;
}
}
else
{
size_t v___x_284_; size_t v___x_285_; lean_object* v___x_286_; 
v___x_284_ = ((size_t)0ULL);
v___x_285_ = lean_usize_of_nat(v___x_278_);
v___x_286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_275_, v___x_284_, v___x_285_, v___x_277_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines___boxed(lean_object* v_parts_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Doc_joinInlines(v_parts_287_);
lean_dec_ref(v_parts_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object* v_a_289_, uint8_t v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
uint8_t v_a_13__boxed_297_; lean_object* v_res_298_; 
v_a_13__boxed_297_ = lean_unbox(v_a_294_);
v_res_298_ = l_Lean_Doc_instMarkdownInlineEmpty___lam__0(v_a_293_, v_a_13__boxed_297_, v_a_295_, v_a_296_);
lean_dec_ref(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec_ref(v_a_293_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0(lean_object* v_a_301_, lean_object* v_a_302_, uint8_t v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed(lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
uint8_t v_a_17__boxed_311_; lean_object* v_res_312_; 
v_a_17__boxed_311_ = lean_unbox(v_a_308_);
v_res_312_ = l_Lean_Doc_instMarkdownBlockEmpty___lam__0(v_a_306_, v_a_307_, v_a_17__boxed_311_, v_a_309_, v_a_310_);
lean_dec_ref(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec_ref(v_a_307_);
lean_dec_ref(v_a_306_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object* v_i_314_){
_start:
{
lean_object* v___f_315_; 
v___f_315_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___closed__0));
return v___f_315_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
if (lean_obj_tag(v_x_317_) == 0)
{
uint8_t v___x_318_; 
v___x_318_ = 1;
return v___x_318_;
}
else
{
uint8_t v___x_319_; 
v___x_319_ = 0;
return v___x_319_;
}
}
else
{
if (lean_obj_tag(v_x_317_) == 0)
{
uint8_t v___x_320_; 
v___x_320_ = 0;
return v___x_320_;
}
else
{
lean_object* v_val_321_; lean_object* v_val_322_; uint32_t v___x_323_; uint32_t v___x_324_; uint8_t v___x_325_; 
v_val_321_ = lean_ctor_get(v_x_316_, 0);
v_val_322_ = lean_ctor_get(v_x_317_, 0);
v___x_323_ = lean_unbox_uint32(v_val_321_);
v___x_324_ = lean_unbox_uint32(v_val_322_);
v___x_325_ = lean_uint32_dec_eq(v___x_323_, v___x_324_);
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1___boxed(lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
uint8_t v_res_328_; lean_object* v_r_329_; 
v_res_328_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_x_326_, v_x_327_);
lean_dec(v_x_327_);
lean_dec(v_x_326_);
v_r_329_ = lean_box(v_res_328_);
return v_r_329_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(lean_object* v_s_330_, uint32_t v_c_331_, lean_object* v_a_332_, uint8_t v_b_333_){
_start:
{
lean_object* v_str_334_; lean_object* v_startInclusive_335_; lean_object* v_endExclusive_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_str_334_ = lean_ctor_get(v_s_330_, 0);
v_startInclusive_335_ = lean_ctor_get(v_s_330_, 1);
v_endExclusive_336_ = lean_ctor_get(v_s_330_, 2);
v___x_337_ = lean_nat_sub(v_endExclusive_336_, v_startInclusive_335_);
v___x_338_ = lean_nat_dec_eq(v_a_332_, v___x_337_);
lean_dec(v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; uint32_t v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_nat_add(v_startInclusive_335_, v_a_332_);
lean_dec(v_a_332_);
v___x_340_ = lean_string_utf8_get_fast(v_str_334_, v___x_339_);
v___x_341_ = lean_uint32_dec_eq(v___x_340_, v_c_331_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_string_utf8_next_fast(v_str_334_, v___x_339_);
lean_dec(v___x_339_);
v___x_343_ = lean_nat_sub(v___x_342_, v_startInclusive_335_);
v_a_332_ = v___x_343_;
v_b_333_ = v___x_341_;
goto _start;
}
else
{
lean_dec(v___x_339_);
return v___x_341_;
}
}
else
{
lean_dec(v_a_332_);
return v_b_333_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg___boxed(lean_object* v_s_345_, lean_object* v_c_346_, lean_object* v_a_347_, lean_object* v_b_348_){
_start:
{
uint32_t v_c_boxed_349_; uint8_t v_b_boxed_350_; uint8_t v_res_351_; lean_object* v_r_352_; 
v_c_boxed_349_ = lean_unbox_uint32(v_c_346_);
lean_dec(v_c_346_);
v_b_boxed_350_ = lean_unbox(v_b_348_);
v_res_351_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_345_, v_c_boxed_349_, v_a_347_, v_b_boxed_350_);
lean_dec_ref(v_s_345_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(uint32_t v_c_353_, lean_object* v_s_354_){
_start:
{
lean_object* v_searcher_355_; uint8_t v___x_356_; uint8_t v___x_357_; 
v_searcher_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = 0;
v___x_357_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_354_, v_c_353_, v_searcher_355_, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0___boxed(lean_object* v_c_358_, lean_object* v_s_359_){
_start:
{
uint32_t v_c_boxed_360_; uint8_t v_res_361_; lean_object* v_r_362_; 
v_c_boxed_360_ = lean_unbox_uint32(v_c_358_);
lean_dec(v_c_358_);
v_res_361_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_boxed_360_, v_s_359_);
lean_dec_ref(v_s_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0));
v___x_365_ = lean_string_utf8_byte_size(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_366_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1);
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0));
v___x_369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
lean_ctor_set(v___x_369_, 2, v___x_366_);
return v___x_369_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_370_; lean_object* v___x_371_; 
v___x_370_ = 91;
v___x_371_ = lean_box_uint32(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1;
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(uint32_t v_c_374_, lean_object* v_next_x3f_375_){
_start:
{
uint32_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 33;
v___x_377_ = lean_uint32_dec_eq(v_c_374_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2);
v___x_379_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_374_, v___x_378_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3);
v___x_381_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_375_, v___x_380_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___boxed(lean_object* v_c_382_, lean_object* v_next_x3f_383_){
_start:
{
uint32_t v_c_boxed_384_; uint8_t v_res_385_; lean_object* v_r_386_; 
v_c_boxed_384_ = lean_unbox_uint32(v_c_382_);
lean_dec(v_c_382_);
v_res_385_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_boxed_384_, v_next_x3f_383_);
lean_dec(v_next_x3f_383_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(lean_object* v_s_387_, uint32_t v_c_388_, lean_object* v_inst_389_, lean_object* v_R_390_, lean_object* v_a_391_, uint8_t v_b_392_, lean_object* v_c_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_387_, v_c_388_, v_a_391_, v_b_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___boxed(lean_object* v_s_395_, lean_object* v_c_396_, lean_object* v_inst_397_, lean_object* v_R_398_, lean_object* v_a_399_, lean_object* v_b_400_, lean_object* v_c_401_){
_start:
{
uint32_t v_c_boxed_402_; uint8_t v_b_boxed_403_; uint8_t v_res_404_; lean_object* v_r_405_; 
v_c_boxed_402_ = lean_unbox_uint32(v_c_396_);
lean_dec(v_c_396_);
v_b_boxed_403_ = lean_unbox(v_b_400_);
v_res_404_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(v_s_395_, v_c_boxed_402_, v_inst_397_, v_R_398_, v_a_399_, v_b_boxed_403_, v_c_401_);
lean_dec_ref(v_s_395_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_406_; lean_object* v___x_407_; 
v___x_406_ = 32;
v___x_407_ = lean_box_uint32(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(lean_object* v_prev_x3f_410_, uint32_t v_c_411_, lean_object* v_next_x3f_412_){
_start:
{
uint8_t v___y_414_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0);
v___x_432_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_412_, v___x_431_);
if (v___x_432_ == 0)
{
if (lean_obj_tag(v_next_x3f_412_) == 0)
{
uint8_t v___x_433_; 
v___x_433_ = 1;
v___y_414_ = v___x_433_;
goto v___jp_413_;
}
else
{
v___y_414_ = v___x_432_;
goto v___jp_413_;
}
}
else
{
v___y_414_ = v___x_432_;
goto v___jp_413_;
}
v___jp_413_:
{
uint32_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 62;
v___x_416_ = lean_uint32_dec_eq(v_c_411_, v___x_415_);
if (v___x_416_ == 0)
{
uint32_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 45;
v___x_418_ = lean_uint32_dec_eq(v_c_411_, v___x_417_);
if (v___x_418_ == 0)
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 43;
v___x_420_ = lean_uint32_dec_eq(v_c_411_, v___x_419_);
if (v___x_420_ == 0)
{
uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 46;
v___x_422_ = lean_uint32_dec_eq(v_c_411_, v___x_421_);
if (v___x_422_ == 0)
{
uint8_t v___x_423_; 
v___x_423_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_411_, v_next_x3f_412_);
return v___x_423_;
}
else
{
if (lean_obj_tag(v_prev_x3f_410_) == 0)
{
return v___x_420_;
}
else
{
lean_object* v_val_424_; uint32_t v___x_425_; uint32_t v___x_426_; uint8_t v___x_427_; 
v_val_424_ = lean_ctor_get(v_prev_x3f_410_, 0);
v___x_425_ = 48;
v___x_426_ = lean_unbox_uint32(v_val_424_);
v___x_427_ = lean_uint32_dec_le(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
if (v___x_427_ == 0)
{
return v___x_427_;
}
else
{
return v___y_414_;
}
}
else
{
uint32_t v___x_428_; uint32_t v___x_429_; uint8_t v___x_430_; 
v___x_428_ = 57;
v___x_429_ = lean_unbox_uint32(v_val_424_);
v___x_430_ = lean_uint32_dec_le(v___x_429_, v___x_428_);
if (v___x_430_ == 0)
{
return v___x_430_;
}
else
{
return v___y_414_;
}
}
}
}
}
else
{
return v___y_414_;
}
}
else
{
return v___y_414_;
}
}
else
{
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___boxed(lean_object* v_prev_x3f_434_, lean_object* v_c_435_, lean_object* v_next_x3f_436_){
_start:
{
uint32_t v_c_boxed_437_; uint8_t v_res_438_; lean_object* v_r_439_; 
v_c_boxed_437_ = lean_unbox_uint32(v_c_435_);
lean_dec(v_c_435_);
v_res_438_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_prev_x3f_434_, v_c_boxed_437_, v_next_x3f_436_);
lean_dec(v_next_x3f_436_);
lean_dec(v_prev_x3f_434_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0));
v___x_442_ = lean_string_utf8_byte_size(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_443_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0));
v___x_446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
lean_ctor_set(v___x_446_, 2, v___x_443_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(uint32_t v___x_447_, lean_object* v___x_448_, lean_object* v_____r_449_, lean_object* v_s_x27_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___y_459_; uint32_t v___x_465_; uint8_t v___x_466_; 
v___x_451_ = lean_string_push(v_s_x27_450_, v___x_447_);
v___x_452_ = lean_box_uint32(v___x_447_);
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
v___x_465_ = 48;
v___x_466_ = lean_uint32_dec_le(v___x_465_, v___x_447_);
if (v___x_466_ == 0)
{
v___y_459_ = v___x_466_;
goto v___jp_458_;
}
else
{
uint32_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = 57;
v___x_468_ = lean_uint32_dec_le(v___x_447_, v___x_467_);
v___y_459_ = v___x_468_;
goto v___jp_458_;
}
v___jp_454_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_448_);
lean_ctor_set(v___x_455_, 1, v___x_453_);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_451_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
v___jp_458_:
{
if (v___y_459_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2);
v___x_461_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v___x_447_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_448_);
lean_ctor_set(v___x_462_, 1, v___x_453_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_451_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
else
{
goto v___jp_454_;
}
}
else
{
goto v___jp_454_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed(lean_object* v___x_469_, lean_object* v___x_470_, lean_object* v_____r_471_, lean_object* v_s_x27_472_){
_start:
{
uint32_t v___x_1753__boxed_473_; lean_object* v_res_474_; 
v___x_1753__boxed_473_ = lean_unbox_uint32(v___x_469_);
lean_dec(v___x_469_);
v_res_474_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_1753__boxed_473_, v___x_470_, v_____r_471_, v_s_x27_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(lean_object* v_s_475_, lean_object* v_a_476_){
_start:
{
lean_object* v___y_478_; lean_object* v_snd_482_; lean_object* v_fst_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_517_; 
v_snd_482_ = lean_ctor_get(v_a_476_, 1);
v_fst_483_ = lean_ctor_get(v_a_476_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_a_476_);
if (v_isSharedCheck_517_ == 0)
{
v___x_485_ = v_a_476_;
v_isShared_486_ = v_isSharedCheck_517_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_snd_482_);
lean_inc(v_fst_483_);
lean_dec(v_a_476_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_517_;
goto v_resetjp_484_;
}
v___jp_477_:
{
if (lean_obj_tag(v___y_478_) == 0)
{
lean_object* v_a_479_; 
v_a_479_ = lean_ctor_get(v___y_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___y_478_, 1);
return v_a_479_;
}
else
{
lean_object* v_a_480_; 
v_a_480_ = lean_ctor_get(v___y_478_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___y_478_, 1);
v_a_476_ = v_a_480_;
goto _start;
}
}
v_resetjp_484_:
{
lean_object* v_fst_487_; lean_object* v_snd_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_516_; 
v_fst_487_ = lean_ctor_get(v_snd_482_, 0);
v_snd_488_ = lean_ctor_get(v_snd_482_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_snd_482_);
if (v_isSharedCheck_516_ == 0)
{
v___x_490_ = v_snd_482_;
v_isShared_491_ = v_isSharedCheck_516_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_snd_488_);
lean_inc(v_fst_487_);
lean_dec(v_snd_482_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_516_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_string_utf8_byte_size(v_s_475_);
v___x_493_ = lean_nat_dec_eq(v_fst_487_, v___x_492_);
if (v___x_493_ == 0)
{
uint32_t v___x_494_; lean_object* v___x_495_; lean_object* v___y_497_; uint8_t v___x_505_; 
lean_del_object(v___x_490_);
lean_del_object(v___x_485_);
v___x_494_ = lean_string_utf8_get_fast(v_s_475_, v_fst_487_);
v___x_495_ = lean_string_utf8_next_fast(v_s_475_, v_fst_487_);
lean_dec(v_fst_487_);
v___x_505_ = lean_nat_dec_eq(v___x_495_, v___x_492_);
if (v___x_505_ == 0)
{
uint32_t v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_string_utf8_get_fast(v_s_475_, v___x_495_);
v___x_507_ = lean_box_uint32(v___x_506_);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
v___y_497_ = v___x_508_;
goto v___jp_496_;
}
else
{
lean_object* v_prev_x3f_509_; 
v_prev_x3f_509_ = lean_box(0);
v___y_497_ = v_prev_x3f_509_;
goto v___jp_496_;
}
v___jp_496_:
{
uint8_t v___x_498_; 
v___x_498_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_snd_488_, v___x_494_, v___y_497_);
lean_dec(v___y_497_);
lean_dec(v_snd_488_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_box(0);
v___x_500_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_494_, v___x_495_, v___x_499_, v_fst_483_);
v___y_478_ = v___x_500_;
goto v___jp_477_;
}
else
{
uint32_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_501_ = 92;
v___x_502_ = lean_string_push(v_fst_483_, v___x_501_);
v___x_503_ = lean_box(0);
v___x_504_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_494_, v___x_495_, v___x_503_, v___x_502_);
v___y_478_ = v___x_504_;
goto v___jp_477_;
}
}
}
else
{
lean_object* v___x_511_; 
if (v_isShared_491_ == 0)
{
v___x_511_ = v___x_490_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_fst_487_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_snd_488_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_511_);
v___x_513_ = v___x_485_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_fst_483_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___boxed(lean_object* v_s_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_518_, v_a_519_);
lean_dec_ref(v_s_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(uint32_t v___x_521_, lean_object* v___x_522_, lean_object* v_____r_523_, lean_object* v_s_x27_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_string_push(v_s_x27_524_, v___x_521_);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v___x_522_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0___boxed(lean_object* v___x_528_, lean_object* v___x_529_, lean_object* v_____r_530_, lean_object* v_s_x27_531_){
_start:
{
uint32_t v___x_1877__boxed_532_; lean_object* v_res_533_; 
v___x_1877__boxed_532_ = lean_unbox_uint32(v___x_528_);
lean_dec(v___x_528_);
v_res_533_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_1877__boxed_532_, v___x_529_, v_____r_530_, v_s_x27_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(lean_object* v_s_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___y_537_; lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_567_; 
v_fst_541_ = lean_ctor_get(v_a_535_, 0);
v_snd_542_ = lean_ctor_get(v_a_535_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_a_535_);
if (v_isSharedCheck_567_ == 0)
{
v___x_544_ = v_a_535_;
v_isShared_545_ = v_isSharedCheck_567_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_snd_542_);
lean_inc(v_fst_541_);
lean_dec(v_a_535_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_567_;
goto v_resetjp_543_;
}
v___jp_536_:
{
if (lean_obj_tag(v___y_537_) == 0)
{
lean_object* v_a_538_; 
v_a_538_ = lean_ctor_get(v___y_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___y_537_, 1);
return v_a_538_;
}
else
{
lean_object* v_a_539_; 
v_a_539_ = lean_ctor_get(v___y_537_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___y_537_, 1);
v_a_535_ = v_a_539_;
goto _start;
}
}
v_resetjp_543_:
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_string_utf8_byte_size(v_s_534_);
v___x_547_ = lean_nat_dec_eq(v_snd_542_, v___x_546_);
if (v___x_547_ == 0)
{
uint32_t v___x_548_; lean_object* v___x_549_; lean_object* v___y_551_; uint8_t v___x_559_; 
lean_del_object(v___x_544_);
v___x_548_ = lean_string_utf8_get_fast(v_s_534_, v_snd_542_);
v___x_549_ = lean_string_utf8_next_fast(v_s_534_, v_snd_542_);
lean_dec(v_snd_542_);
v___x_559_ = lean_nat_dec_eq(v___x_549_, v___x_546_);
if (v___x_559_ == 0)
{
uint32_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_string_utf8_get_fast(v_s_534_, v___x_549_);
v___x_561_ = lean_box_uint32(v___x_560_);
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
v___y_551_ = v___x_562_;
goto v___jp_550_;
}
else
{
lean_object* v_prev_x3f_563_; 
v_prev_x3f_563_ = lean_box(0);
v___y_551_ = v_prev_x3f_563_;
goto v___jp_550_;
}
v___jp_550_:
{
uint8_t v___x_552_; 
v___x_552_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v___x_548_, v___y_551_);
lean_dec(v___y_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_box(0);
v___x_554_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_548_, v___x_549_, v___x_553_, v_fst_541_);
v___y_537_ = v___x_554_;
goto v___jp_536_;
}
else
{
uint32_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_555_ = 92;
v___x_556_ = lean_string_push(v_fst_541_, v___x_555_);
v___x_557_ = lean_box(0);
v___x_558_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_548_, v___x_549_, v___x_557_, v___x_556_);
v___y_537_ = v___x_558_;
goto v___jp_536_;
}
}
}
else
{
lean_object* v___x_565_; 
if (v_isShared_545_ == 0)
{
v___x_565_ = v___x_544_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_fst_541_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_snd_542_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___boxed(lean_object* v_s_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_568_, v_a_569_);
lean_dec_ref(v_s_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object* v_s_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_snd_580_; lean_object* v_fst_581_; lean_object* v_fst_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_591_; 
v___x_578_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1));
v___x_579_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_577_, v___x_578_);
v_snd_580_ = lean_ctor_get(v___x_579_, 1);
lean_inc(v_snd_580_);
v_fst_581_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_fst_581_);
lean_dec_ref(v___x_579_);
v_fst_582_ = lean_ctor_get(v_snd_580_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_snd_580_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v_snd_580_, 1);
lean_dec(v_unused_592_);
v___x_584_ = v_snd_580_;
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_fst_582_);
lean_dec(v_snd_580_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 1, v_fst_582_);
lean_ctor_set(v___x_584_, 0, v_fst_581_);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_fst_581_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_fst_582_);
v___x_587_ = v_reuseFailAlloc_590_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; lean_object* v_fst_589_; 
v___x_588_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_577_, v___x_587_);
v_fst_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_fst_589_);
lean_dec_ref(v___x_588_);
return v_fst_589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object* v_s_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_593_);
lean_dec_ref(v_s_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object* v_s_595_, lean_object* v_inst_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_595_, v_a_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object* v_s_599_, lean_object* v_inst_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_599_, v_inst_600_, v_a_601_);
lean_dec_ref(v_s_599_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(lean_object* v_s_603_, lean_object* v_inst_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_603_, v_a_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___boxed(lean_object* v_s_607_, lean_object* v_inst_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(v_s_607_, v_inst_608_, v_a_609_);
lean_dec_ref(v_s_607_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v_str_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_snd_613_; lean_object* v_fst_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_656_; 
v_snd_613_ = lean_ctor_get(v_a_612_, 1);
v_fst_614_ = lean_ctor_get(v_a_612_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v_a_612_);
if (v_isSharedCheck_656_ == 0)
{
v___x_616_ = v_a_612_;
v_isShared_617_ = v_isSharedCheck_656_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_snd_613_);
lean_inc(v_fst_614_);
lean_dec(v_a_612_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_656_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v_fst_618_; lean_object* v_snd_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_655_; 
v_fst_618_ = lean_ctor_get(v_snd_613_, 0);
v_snd_619_ = lean_ctor_get(v_snd_613_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_snd_613_);
if (v_isSharedCheck_655_ == 0)
{
v___x_621_ = v_snd_613_;
v_isShared_622_ = v_isSharedCheck_655_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_snd_619_);
lean_inc(v_fst_618_);
lean_dec(v_snd_613_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_655_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = lean_string_utf8_byte_size(v_str_611_);
v___x_624_ = lean_nat_dec_eq(v_snd_619_, v___x_623_);
if (v___x_624_ == 0)
{
uint32_t v___x_625_; lean_object* v___x_626_; uint32_t v___x_627_; uint8_t v___x_628_; 
v___x_625_ = lean_string_utf8_get_fast(v_str_611_, v_snd_619_);
v___x_626_ = lean_string_utf8_next_fast(v_str_611_, v_snd_619_);
lean_dec(v_snd_619_);
v___x_627_ = 96;
v___x_628_ = lean_uint32_dec_eq(v___x_625_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v_longest_629_; lean_object* v___y_631_; uint8_t v___x_639_; 
v_longest_629_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_nat_dec_le(v_fst_614_, v_fst_618_);
if (v___x_639_ == 0)
{
lean_dec(v_fst_618_);
v___y_631_ = v_fst_614_;
goto v___jp_630_;
}
else
{
lean_dec(v_fst_614_);
v___y_631_ = v_fst_618_;
goto v___jp_630_;
}
v___jp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_626_);
lean_ctor_set(v___x_621_, 0, v_longest_629_);
v___x_633_ = v___x_621_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_longest_629_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_626_);
v___x_633_ = v_reuseFailAlloc_638_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v___x_633_);
lean_ctor_set(v___x_616_, 0, v___y_631_);
v___x_635_ = v___x_616_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___y_631_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_633_);
v___x_635_ = v_reuseFailAlloc_637_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
v_a_612_ = v___x_635_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = lean_nat_add(v_fst_618_, v___x_640_);
lean_dec(v_fst_618_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_626_);
lean_ctor_set(v___x_621_, 0, v___x_641_);
v___x_643_ = v___x_621_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_626_);
v___x_643_ = v_reuseFailAlloc_648_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v___x_643_);
v___x_645_ = v___x_616_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_fst_614_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_647_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
v_a_612_ = v___x_645_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_650_; 
if (v_isShared_622_ == 0)
{
v___x_650_ = v___x_621_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_fst_618_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_snd_619_);
v___x_650_ = v_reuseFailAlloc_654_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_652_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v___x_650_);
v___x_652_ = v___x_616_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fst_614_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v_str_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_657_, v_a_658_);
lean_dec_ref(v_str_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(lean_object* v_str_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_snd_668_; lean_object* v_fst_669_; lean_object* v_fst_670_; uint8_t v___x_671_; 
v___x_666_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1));
v___x_667_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_665_, v___x_666_);
v_snd_668_ = lean_ctor_get(v___x_667_, 1);
lean_inc(v_snd_668_);
v_fst_669_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_fst_669_);
lean_dec_ref(v___x_667_);
v_fst_670_ = lean_ctor_get(v_snd_668_, 0);
lean_inc(v_fst_670_);
lean_dec(v_snd_668_);
v___x_671_ = lean_nat_dec_le(v_fst_669_, v_fst_670_);
if (v___x_671_ == 0)
{
lean_dec(v_fst_670_);
return v_fst_669_;
}
else
{
lean_dec(v_fst_669_);
return v_fst_670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___boxed(lean_object* v_str_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_672_);
lean_dec_ref(v_str_672_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(lean_object* v_str_674_, lean_object* v_inst_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_674_, v_a_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v_str_678_, lean_object* v_inst_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(v_str_678_, v_inst_679_, v_a_680_);
lean_dec_ref(v_str_678_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
lean_object* v_zero_684_; uint8_t v_isZero_685_; 
v_zero_684_ = lean_unsigned_to_nat(0u);
v_isZero_685_ = lean_nat_dec_eq(v_x_682_, v_zero_684_);
if (v_isZero_685_ == 1)
{
lean_dec(v_x_682_);
return v_x_683_;
}
else
{
uint32_t v___x_686_; lean_object* v_one_687_; lean_object* v_n_688_; lean_object* v___x_689_; 
v___x_686_ = 96;
v_one_687_ = lean_unsigned_to_nat(1u);
v_n_688_ = lean_nat_sub(v_x_682_, v_one_687_);
lean_dec(v_x_682_);
v___x_689_ = lean_string_push(v_x_683_, v___x_686_);
v_x_682_ = v_n_688_;
v_x_683_ = v___x_689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(lean_object* v_atLeast_691_, lean_object* v_str_692_){
_start:
{
lean_object* v___x_693_; lean_object* v___y_695_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_699_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_692_);
v___x_700_ = lean_nat_dec_le(v_atLeast_691_, v___x_699_);
if (v___x_700_ == 0)
{
lean_dec(v___x_699_);
v___y_695_ = v_atLeast_691_;
goto v___jp_694_;
}
else
{
lean_dec(v_atLeast_691_);
v___y_695_ = v___x_699_;
goto v___jp_694_;
}
v___jp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = lean_nat_add(v___y_695_, v___x_696_);
lean_dec(v___y_695_);
v___x_698_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(v___x_697_, v___x_693_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor___boxed(lean_object* v_atLeast_701_, lean_object* v_str_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v_atLeast_701_, v_str_702_);
lean_dec_ref(v_str_702_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object* v_str_705_){
_start:
{
lean_object* v___x_706_; lean_object* v_backticks_707_; lean_object* v___y_709_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_706_ = lean_unsigned_to_nat(0u);
v_backticks_707_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_706_, v_str_705_);
v___x_723_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_724_ = lean_string_utf8_byte_size(v_str_705_);
v___x_725_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1);
v___x_726_ = lean_nat_dec_le(v___x_725_, v___x_724_);
if (v___x_726_ == 0)
{
goto v___jp_716_;
}
else
{
uint8_t v___x_727_; 
v___x_727_ = lean_string_memcmp(v_str_705_, v___x_723_, v___x_706_, v___x_706_, v___x_725_);
if (v___x_727_ == 0)
{
goto v___jp_716_;
}
else
{
goto v___jp_712_;
}
}
v___jp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_inc_ref(v_backticks_707_);
v___x_710_ = lean_string_append(v_backticks_707_, v___y_709_);
lean_dec_ref(v___y_709_);
v___x_711_ = lean_string_append(v___x_710_, v_backticks_707_);
lean_dec_ref(v_backticks_707_);
return v___x_711_;
}
v___jp_712_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_714_ = lean_string_append(v___x_713_, v_str_705_);
lean_dec_ref(v_str_705_);
v___x_715_ = lean_string_append(v___x_714_, v___x_713_);
v___y_709_ = v___x_715_;
goto v___jp_708_;
}
v___jp_716_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_717_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_718_ = lean_string_utf8_byte_size(v_str_705_);
v___x_719_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1);
v___x_720_ = lean_nat_dec_le(v___x_719_, v___x_718_);
if (v___x_720_ == 0)
{
v___y_709_ = v_str_705_;
goto v___jp_708_;
}
else
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_nat_sub(v___x_718_, v___x_719_);
v___x_722_ = lean_string_memcmp(v_str_705_, v___x_717_, v___x_721_, v___x_706_, v___x_719_);
lean_dec(v___x_721_);
if (v___x_722_ == 0)
{
v___y_709_ = v_str_705_;
goto v___jp_708_;
}
else
{
goto v___jp_712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(lean_object* v_s_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0));
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___boxed(lean_object* v_s_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v_s_732_);
lean_dec_ref(v_s_732_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(lean_object* v_str_734_, lean_object* v___x_735_, lean_object* v___x_736_, lean_object* v_a_737_, lean_object* v_b_738_){
_start:
{
lean_object* v_it_740_; lean_object* v_startInclusive_741_; lean_object* v_endExclusive_742_; 
if (lean_obj_tag(v_a_737_) == 0)
{
lean_object* v_currPos_746_; lean_object* v_searcher_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_773_; 
v_currPos_746_ = lean_ctor_get(v_a_737_, 0);
v_searcher_747_ = lean_ctor_get(v_a_737_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_737_);
if (v_isSharedCheck_773_ == 0)
{
v___x_749_ = v_a_737_;
v_isShared_750_ = v_isSharedCheck_773_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_searcher_747_);
lean_inc(v_currPos_746_);
lean_dec(v_a_737_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_773_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_startInclusive_751_; lean_object* v_endExclusive_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v_startInclusive_751_ = lean_ctor_get(v___x_735_, 1);
v_endExclusive_752_ = lean_ctor_get(v___x_735_, 2);
v___x_753_ = lean_nat_sub(v_endExclusive_752_, v_startInclusive_751_);
v___x_754_ = lean_nat_dec_eq(v_searcher_747_, v___x_753_);
lean_dec(v___x_753_);
if (v___x_754_ == 0)
{
uint32_t v___x_755_; uint32_t v___x_756_; uint8_t v___x_757_; 
v___x_755_ = 10;
v___x_756_ = lean_string_utf8_get_fast(v_str_734_, v_searcher_747_);
v___x_757_ = lean_uint32_dec_eq(v___x_756_, v___x_755_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = lean_string_utf8_next_fast(v_str_734_, v_searcher_747_);
lean_dec(v_searcher_747_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_758_);
v___x_760_ = v___x_749_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_currPos_746_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_758_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
v_a_737_ = v___x_760_;
goto _start;
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_slice_766_; lean_object* v_nextIt_768_; 
v___x_763_ = lean_string_utf8_next_fast(v_str_734_, v_searcher_747_);
v___x_764_ = lean_nat_sub(v___x_763_, v_searcher_747_);
v___x_765_ = lean_nat_add(v_searcher_747_, v___x_764_);
lean_dec(v___x_764_);
v_slice_766_ = l_String_Slice_subslice_x21(v___x_735_, v_currPos_746_, v_searcher_747_);
lean_inc(v___x_765_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_765_);
lean_ctor_set(v___x_749_, 0, v___x_765_);
v_nextIt_768_ = v___x_749_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_765_);
v_nextIt_768_ = v_reuseFailAlloc_771_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v_startInclusive_769_; lean_object* v_endExclusive_770_; 
v_startInclusive_769_ = lean_ctor_get(v_slice_766_, 0);
lean_inc(v_startInclusive_769_);
v_endExclusive_770_ = lean_ctor_get(v_slice_766_, 1);
lean_inc(v_endExclusive_770_);
lean_dec_ref(v_slice_766_);
v_it_740_ = v_nextIt_768_;
v_startInclusive_741_ = v_startInclusive_769_;
v_endExclusive_742_ = v_endExclusive_770_;
goto v___jp_739_;
}
}
}
else
{
lean_object* v___x_772_; 
lean_del_object(v___x_749_);
lean_dec(v_searcher_747_);
v___x_772_ = lean_box(1);
lean_inc(v___x_736_);
v_it_740_ = v___x_772_;
v_startInclusive_741_ = v_currPos_746_;
v_endExclusive_742_ = v___x_736_;
goto v___jp_739_;
}
}
}
else
{
lean_dec(v___x_736_);
return v_b_738_;
}
v___jp_739_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_string_utf8_extract(v_str_734_, v_startInclusive_741_, v_endExclusive_742_);
lean_dec(v_endExclusive_742_);
lean_dec(v_startInclusive_741_);
v___x_744_ = lean_array_push(v_b_738_, v___x_743_);
v_a_737_ = v_it_740_;
v_b_738_ = v___x_744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg___boxed(lean_object* v_str_774_, lean_object* v___x_775_, lean_object* v___x_776_, lean_object* v_a_777_, lean_object* v_b_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_774_, v___x_775_, v___x_776_, v_a_777_, v_b_778_);
lean_dec_ref(v___x_775_);
lean_dec_ref(v_str_774_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(lean_object* v_str_780_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_string_utf8_byte_size(v_str_780_);
lean_inc_ref(v_str_780_);
v___x_783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_783_, 0, v_str_780_);
lean_ctor_set(v___x_783_, 1, v___x_781_);
lean_ctor_set(v___x_783_, 2, v___x_782_);
v___x_784_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v___x_783_);
v___x_785_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_786_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_780_, v___x_783_, v___x_782_, v___x_784_, v___x_785_);
lean_dec_ref_known(v___x_783_, 3);
lean_dec_ref(v_str_780_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(lean_object* v_str_787_, lean_object* v___x_788_, lean_object* v___x_789_, lean_object* v_inst_790_, lean_object* v_R_791_, lean_object* v_a_792_, lean_object* v_b_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_787_, v___x_788_, v___x_789_, v_a_792_, v_b_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___boxed(lean_object* v_str_795_, lean_object* v___x_796_, lean_object* v___x_797_, lean_object* v_inst_798_, lean_object* v_R_799_, lean_object* v_a_800_, lean_object* v_b_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(v_str_795_, v___x_796_, v___x_797_, v_inst_798_, v_R_799_, v_a_800_, v_b_801_);
lean_dec_ref(v___x_796_);
lean_dec_ref(v_str_795_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(lean_object* v_str_803_){
_start:
{
lean_object* v___x_804_; lean_object* v_fence_805_; lean_object* v___y_807_; lean_object* v_body_813_; uint8_t v___y_815_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_804_ = lean_unsigned_to_nat(2u);
v_fence_805_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_804_, v_str_803_);
v_body_813_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(v_str_803_);
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_array_get_size(v_body_813_);
v___x_819_ = lean_nat_dec_lt(v___x_817_, v___x_818_);
if (v___x_819_ == 0)
{
v___y_815_ = v___x_819_;
goto v___jp_814_;
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_nat_sub(v___x_818_, v___x_821_);
v___x_823_ = lean_array_get(v___x_820_, v_body_813_, v___x_822_);
lean_dec(v___x_822_);
v___x_824_ = lean_string_utf8_byte_size(v___x_823_);
lean_dec(v___x_823_);
v___x_825_ = lean_nat_dec_eq(v___x_824_, v___x_817_);
v___y_815_ = v___x_825_;
goto v___jp_814_;
}
v___jp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = lean_mk_empty_array_with_capacity(v___x_808_);
v___x_810_ = lean_array_push(v___x_809_, v_fence_805_);
lean_inc_ref(v___x_810_);
v___x_811_ = l_Array_append___redArg(v___x_810_, v___y_807_);
lean_dec_ref(v___y_807_);
v___x_812_ = l_Array_append___redArg(v___x_811_, v___x_810_);
lean_dec_ref(v___x_810_);
return v___x_812_;
}
v___jp_814_:
{
if (v___y_815_ == 0)
{
v___y_807_ = v_body_813_;
goto v___jp_806_;
}
else
{
lean_object* v___x_816_; 
v___x_816_ = lean_array_pop(v_body_813_);
v___y_807_ = v___x_816_;
goto v___jp_806_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_826_, lean_object* v_pos_827_){
_start:
{
lean_object* v_str_828_; lean_object* v_startInclusive_829_; lean_object* v_endExclusive_830_; lean_object* v___x_831_; uint8_t v___y_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_str_828_ = lean_ctor_get(v_s_826_, 0);
v_startInclusive_829_ = lean_ctor_get(v_s_826_, 1);
v_endExclusive_830_ = lean_ctor_get(v_s_826_, 2);
v___x_831_ = lean_nat_add(v_startInclusive_829_, v_pos_827_);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_nat_sub(v_endExclusive_830_, v___x_831_);
v___x_842_ = lean_nat_dec_eq(v___x_840_, v___x_841_);
lean_dec(v___x_841_);
if (v___x_842_ == 0)
{
uint32_t v___x_843_; uint8_t v___y_845_; uint32_t v___x_850_; uint8_t v___x_851_; 
v___x_843_ = lean_string_utf8_get_fast(v_str_828_, v___x_831_);
v___x_850_ = 32;
v___x_851_ = lean_uint32_dec_eq(v___x_843_, v___x_850_);
if (v___x_851_ == 0)
{
uint32_t v___x_852_; uint8_t v___x_853_; 
v___x_852_ = 9;
v___x_853_ = lean_uint32_dec_eq(v___x_843_, v___x_852_);
v___y_845_ = v___x_853_;
goto v___jp_844_;
}
else
{
v___y_845_ = v___x_851_;
goto v___jp_844_;
}
v___jp_844_:
{
if (v___y_845_ == 0)
{
uint32_t v___x_846_; uint8_t v___x_847_; 
v___x_846_ = 13;
v___x_847_ = lean_uint32_dec_eq(v___x_843_, v___x_846_);
if (v___x_847_ == 0)
{
uint32_t v___x_848_; uint8_t v___x_849_; 
v___x_848_ = 10;
v___x_849_ = lean_uint32_dec_eq(v___x_843_, v___x_848_);
v___y_839_ = v___x_849_;
goto v___jp_838_;
}
else
{
v___y_839_ = v___x_847_;
goto v___jp_838_;
}
}
else
{
goto v___jp_832_;
}
}
}
else
{
lean_dec(v___x_831_);
return v_pos_827_;
}
v___jp_832_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_833_ = lean_string_utf8_next_fast(v_str_828_, v___x_831_);
v___x_834_ = lean_nat_sub(v___x_833_, v___x_831_);
lean_dec(v___x_831_);
v___x_835_ = lean_nat_add(v_pos_827_, v___x_834_);
lean_dec(v___x_834_);
v___x_836_ = lean_nat_dec_lt(v_pos_827_, v___x_835_);
if (v___x_836_ == 0)
{
lean_dec(v___x_835_);
return v_pos_827_;
}
else
{
lean_dec(v_pos_827_);
v_pos_827_ = v___x_835_;
goto _start;
}
}
v___jp_838_:
{
if (v___y_839_ == 0)
{
lean_dec(v___x_831_);
return v_pos_827_;
}
else
{
goto v___jp_832_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object* v_s_854_, lean_object* v_pos_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_854_, v_pos_855_);
lean_dec_ref(v_s_854_);
return v_res_856_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Doc_Inline_empty(lean_box(0));
return v___x_857_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object* v_a_861_){
_start:
{
if (lean_obj_tag(v_a_861_) == 0)
{
lean_object* v___x_862_; 
v___x_862_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
return v___x_862_;
}
else
{
lean_object* v_head_863_; 
v_head_863_ = lean_ctor_get(v_a_861_, 0);
lean_inc(v_head_863_);
switch(lean_obj_tag(v_head_863_))
{
case 0:
{
lean_object* v_tail_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_908_; 
v_tail_864_ = lean_ctor_get(v_a_861_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_a_861_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v_a_861_, 0);
lean_dec(v_unused_909_);
v___x_866_ = v_a_861_;
v_isShared_867_ = v_isSharedCheck_908_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_tail_864_);
lean_dec(v_a_861_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_908_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_string_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_907_; 
v_string_868_ = lean_ctor_get(v_head_863_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v_head_863_);
if (v_isSharedCheck_907_ == 0)
{
v___x_870_ = v_head_863_;
v_isShared_871_ = v_isSharedCheck_907_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_string_868_);
lean_dec(v_head_863_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_907_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_872_ = lean_unsigned_to_nat(0u);
v___x_873_ = lean_string_utf8_byte_size(v_string_868_);
lean_inc_ref(v_string_868_);
v___x_874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_874_, 0, v_string_868_);
lean_ctor_set(v___x_874_, 1, v___x_872_);
lean_ctor_set(v___x_874_, 2, v___x_873_);
v___x_875_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_874_, v___x_872_);
lean_dec_ref_known(v___x_874_, 3);
v___x_876_ = lean_nat_dec_eq(v___x_875_, v___x_873_);
if (v___x_876_ == 0)
{
lean_object* v_s1_877_; lean_object* v_s2_878_; lean_object* v___x_880_; 
v_s1_877_ = lean_string_utf8_extract(v_string_868_, v___x_872_, v___x_875_);
v_s2_878_ = lean_string_utf8_extract(v_string_868_, v___x_875_, v___x_873_);
lean_dec(v___x_875_);
lean_dec_ref(v_string_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v_s2_878_);
v___x_880_ = v___x_870_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_s2_878_);
v___x_880_ = v_reuseFailAlloc_895_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_881_ = lean_array_mk(v_tail_864_);
v___x_882_ = lean_array_get_size(v___x_881_);
v___x_883_ = lean_nat_dec_eq(v___x_882_, v___x_872_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_mk_empty_array_with_capacity(v___x_884_);
v___x_886_ = lean_array_push(v___x_885_, v___x_880_);
v___x_887_ = l_Array_append___redArg(v___x_886_, v___x_881_);
lean_dec_ref(v___x_881_);
v___x_888_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 0);
lean_ctor_set(v___x_866_, 1, v___x_888_);
lean_ctor_set(v___x_866_, 0, v_s1_877_);
v___x_890_ = v___x_866_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_s1_877_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
else
{
lean_object* v___x_893_; 
lean_dec_ref(v___x_881_);
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 0);
lean_ctor_set(v___x_866_, 1, v___x_880_);
lean_ctor_set(v___x_866_, 0, v_s1_877_);
v___x_893_ = v___x_866_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_s1_877_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_880_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v___x_896_; lean_object* v_fst_897_; lean_object* v_snd_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_906_; 
lean_dec(v___x_875_);
lean_del_object(v___x_870_);
lean_del_object(v___x_866_);
v___x_896_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_864_);
v_fst_897_ = lean_ctor_get(v___x_896_, 0);
v_snd_898_ = lean_ctor_get(v___x_896_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_906_ == 0)
{
v___x_900_ = v___x_896_;
v_isShared_901_ = v_isSharedCheck_906_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_snd_898_);
lean_inc(v_fst_897_);
lean_dec(v___x_896_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_906_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_902_ = lean_string_append(v_string_868_, v_fst_897_);
lean_dec(v_fst_897_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_902_);
v___x_904_ = v___x_900_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_snd_898_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_910_; lean_object* v_content_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_tail_910_ = lean_ctor_get(v_a_861_, 1);
lean_inc(v_tail_910_);
lean_dec_ref_known(v_a_861_, 2);
v_content_911_ = lean_ctor_get(v_head_863_, 0);
lean_inc_ref(v_content_911_);
lean_dec_ref_known(v_head_863_, 1);
v___x_912_ = lean_array_to_list(v_content_911_);
v___x_913_ = l_List_appendTR___redArg(v___x_912_, v_tail_910_);
v_a_861_ = v___x_913_;
goto _start;
}
default: 
{
lean_object* v_tail_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_953_; 
v_tail_915_ = lean_ctor_get(v_a_861_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_a_861_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v_a_861_, 0);
lean_dec(v_unused_954_);
v___x_917_ = v_a_861_;
v_isShared_918_ = v_isSharedCheck_953_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_tail_915_);
lean_dec(v_a_861_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_953_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_920_ = lean_array_mk(v_tail_915_);
if (lean_obj_tag(v_head_863_) == 9)
{
lean_object* v_content_921_; lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v_content_921_ = lean_ctor_get(v_head_863_, 0);
v___x_922_ = lean_array_get_size(v_content_921_);
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = lean_nat_dec_eq(v___x_922_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_925_ = lean_array_get_size(v___x_920_);
v___x_926_ = lean_nat_dec_eq(v___x_925_, v___x_923_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
lean_inc_ref(v_content_921_);
lean_dec_ref_known(v_head_863_, 1);
v___x_927_ = l_Array_append___redArg(v_content_921_, v___x_920_);
lean_dec_ref(v___x_920_);
v___x_928_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 0);
lean_ctor_set(v___x_917_, 1, v___x_928_);
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_930_ = v___x_917_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
else
{
lean_object* v___x_933_; 
lean_dec_ref(v___x_920_);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 0);
lean_ctor_set(v___x_917_, 1, v_head_863_);
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_933_ = v___x_917_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_head_863_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_937_; 
lean_dec_ref_known(v_head_863_, 1);
v___x_935_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_920_);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 0);
lean_ctor_set(v___x_917_, 1, v___x_935_);
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_937_ = v___x_917_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_939_ = lean_array_get_size(v___x_920_);
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_nat_dec_eq(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_mk_empty_array_with_capacity(v___x_942_);
v___x_944_ = lean_array_push(v___x_943_, v_head_863_);
v___x_945_ = l_Array_append___redArg(v___x_944_, v___x_920_);
lean_dec_ref(v___x_920_);
v___x_946_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 0);
lean_ctor_set(v___x_917_, 1, v___x_946_);
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_948_ = v___x_917_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
else
{
lean_object* v___x_951_; 
lean_dec_ref(v___x_920_);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 0);
lean_ctor_set(v___x_917_, 1, v_head_863_);
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_951_ = v___x_917_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_head_863_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_958_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = lean_box(0);
v___x_960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_960_, 0, v_inline_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_962_, lean_object* v_inline_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_965_, lean_object* v_pos_966_){
_start:
{
lean_object* v_str_967_; lean_object* v_startInclusive_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v_str_967_ = lean_ctor_get(v_s_965_, 0);
v_startInclusive_968_ = lean_ctor_get(v_s_965_, 1);
v___x_969_ = lean_nat_add(v_startInclusive_968_, v_pos_966_);
v___x_970_ = lean_nat_sub(v___x_969_, v_startInclusive_968_);
v___x_971_ = lean_unsigned_to_nat(0u);
v___x_972_ = lean_nat_dec_eq(v___x_970_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___y_981_; lean_object* v___x_982_; uint32_t v___x_983_; uint8_t v___y_985_; uint32_t v___x_990_; uint8_t v___x_991_; 
lean_inc(v_startInclusive_968_);
lean_inc_ref(v_str_967_);
v___x_973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_973_, 0, v_str_967_);
lean_ctor_set(v___x_973_, 1, v_startInclusive_968_);
lean_ctor_set(v___x_973_, 2, v___x_969_);
v___x_974_ = lean_unsigned_to_nat(1u);
v___x_975_ = lean_nat_sub(v___x_970_, v___x_974_);
lean_dec(v___x_970_);
v___x_976_ = l_String_Slice_posLE(v___x_973_, v___x_975_);
lean_dec_ref_known(v___x_973_, 3);
v___x_982_ = lean_nat_add(v_startInclusive_968_, v___x_976_);
v___x_983_ = lean_string_utf8_get_fast(v_str_967_, v___x_982_);
lean_dec(v___x_982_);
v___x_990_ = 32;
v___x_991_ = lean_uint32_dec_eq(v___x_983_, v___x_990_);
if (v___x_991_ == 0)
{
uint32_t v___x_992_; uint8_t v___x_993_; 
v___x_992_ = 9;
v___x_993_ = lean_uint32_dec_eq(v___x_983_, v___x_992_);
v___y_985_ = v___x_993_;
goto v___jp_984_;
}
else
{
v___y_985_ = v___x_991_;
goto v___jp_984_;
}
v___jp_977_:
{
uint8_t v___x_978_; 
v___x_978_ = lean_nat_dec_lt(v___x_976_, v_pos_966_);
if (v___x_978_ == 0)
{
lean_dec(v___x_976_);
return v_pos_966_;
}
else
{
lean_dec(v_pos_966_);
v_pos_966_ = v___x_976_;
goto _start;
}
}
v___jp_980_:
{
if (v___y_981_ == 0)
{
lean_dec(v___x_976_);
return v_pos_966_;
}
else
{
goto v___jp_977_;
}
}
v___jp_984_:
{
if (v___y_985_ == 0)
{
uint32_t v___x_986_; uint8_t v___x_987_; 
v___x_986_ = 13;
v___x_987_ = lean_uint32_dec_eq(v___x_983_, v___x_986_);
if (v___x_987_ == 0)
{
uint32_t v___x_988_; uint8_t v___x_989_; 
v___x_988_ = 10;
v___x_989_ = lean_uint32_dec_eq(v___x_983_, v___x_988_);
v___y_981_ = v___x_989_;
goto v___jp_980_;
}
else
{
v___y_981_ = v___x_987_;
goto v___jp_980_;
}
}
else
{
goto v___jp_977_;
}
}
}
else
{
lean_dec(v___x_970_);
lean_dec(v___x_969_);
return v_pos_966_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_994_, lean_object* v_pos_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_994_, v_pos_995_);
lean_dec_ref(v_s_994_);
return v_res_996_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_998_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_xs_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1001_ = lean_array_get_size(v_xs_1000_);
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_nat_dec_eq(v___x_1001_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_unsigned_to_nat(1u);
v___x_1005_ = lean_nat_sub(v___x_1001_, v___x_1004_);
v___x_1006_ = lean_array_fget(v_xs_1000_, v___x_1005_);
lean_dec(v___x_1005_);
switch(lean_obj_tag(v___x_1006_))
{
case 0:
{
lean_object* v_string_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1037_; 
v_string_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1037_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_string_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1037_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1011_ = lean_string_utf8_byte_size(v_string_1007_);
lean_inc_ref(v_string_1007_);
v___x_1012_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1012_, 0, v_string_1007_);
lean_ctor_set(v___x_1012_, 1, v___x_1002_);
lean_ctor_set(v___x_1012_, 2, v___x_1011_);
v___x_1013_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_1012_, v___x_1002_);
v___x_1014_ = lean_nat_dec_eq(v___x_1013_, v___x_1011_);
lean_dec(v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1015_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_1012_, v___x_1011_);
lean_dec_ref_known(v___x_1012_, 3);
v___x_1016_ = lean_array_pop(v_xs_1000_);
v___x_1017_ = lean_string_utf8_extract(v_string_1007_, v___x_1002_, v___x_1015_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1017_);
v___x_1019_ = v___x_1009_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1020_ = lean_array_push(v___x_1016_, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
v___x_1022_ = lean_string_utf8_extract(v_string_1007_, v___x_1015_, v___x_1011_);
lean_dec(v___x_1015_);
lean_dec_ref(v_string_1007_);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
return v___x_1023_;
}
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref_known(v___x_1012_, 3);
lean_del_object(v___x_1009_);
v___x_1025_ = lean_array_pop(v_xs_1000_);
v___x_1026_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1025_);
v_fst_1027_ = lean_ctor_get(v___x_1026_, 0);
v_snd_1028_ = lean_ctor_get(v___x_1026_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1030_ = v___x_1026_;
v_isShared_1031_ = v_isSharedCheck_1036_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_snd_1028_);
lean_inc(v_fst_1027_);
lean_dec(v___x_1026_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1036_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = lean_string_append(v_snd_1028_, v_string_1007_);
lean_dec_ref(v_string_1007_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___x_1032_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_fst_1027_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_1032_);
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
}
case 9:
{
lean_object* v_content_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_content_1038_ = lean_ctor_get(v___x_1006_, 0);
lean_inc_ref(v_content_1038_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1039_ = lean_array_pop(v_xs_1000_);
v___x_1040_ = l_Array_append___redArg(v___x_1039_, v_content_1038_);
lean_dec_ref(v_content_1038_);
v_xs_1000_ = v___x_1040_;
goto _start;
}
default: 
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec(v___x_1006_);
v___x_1042_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1042_, 0, v_xs_1000_);
v___x_1043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
return v___x_1044_;
}
}
}
else
{
lean_object* v___x_1045_; 
lean_dec_ref(v_xs_1000_);
v___x_1045_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_1046_, lean_object* v_xs_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_xs_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_1049_){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1050_ = lean_unsigned_to_nat(1u);
v___x_1051_ = lean_mk_empty_array_with_capacity(v___x_1050_);
v___x_1052_ = lean_array_push(v___x_1051_, v_inline_1049_);
v___x_1053_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_1054_, lean_object* v_inline_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_1057_){
_start:
{
lean_object* v___x_1058_; lean_object* v_fst_1059_; lean_object* v_snd_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1068_; 
v___x_1058_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1057_);
v_fst_1059_ = lean_ctor_get(v___x_1058_, 0);
v_snd_1060_ = lean_ctor_get(v___x_1058_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1062_ = v___x_1058_;
v_isShared_1063_ = v_isSharedCheck_1068_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_snd_1060_);
lean_inc(v_fst_1059_);
lean_dec(v___x_1058_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1068_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_1060_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 1, v___x_1064_);
v___x_1066_ = v___x_1062_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_fst_1059_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_1069_, lean_object* v_inline_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29));
v___x_1144_ = lean_unsigned_to_nat(3u);
v___x_1145_ = lean_mk_empty_array_with_capacity(v___x_1144_);
v___x_1146_ = lean_array_push(v___x_1145_, v___x_1143_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_pieces_1154_; lean_object* v___y_1155_; lean_object* v_pieces_1159_; lean_object* v___y_1160_; lean_object* v___x_1163_; 
v___x_1163_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19));
switch(lean_obj_tag(v_x_1151_))
{
case 0:
{
lean_object* v_string_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec_ref(v_x_1150_);
lean_dec_ref(v_inst_1149_);
v_string_1164_ = lean_ctor_get(v_x_1151_, 0);
lean_inc_ref(v_string_1164_);
lean_dec_ref_known(v_x_1151_, 1);
v___x_1165_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1164_);
lean_dec_ref(v_string_1164_);
v___x_1166_ = lean_unsigned_to_nat(1u);
v___x_1167_ = lean_mk_empty_array_with_capacity(v___x_1166_);
v___x_1168_ = lean_array_push(v___x_1167_, v___x_1165_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v_a_1152_);
return v___x_1169_;
}
case 1:
{
lean_object* v_content_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1224_; 
v_content_1170_ = lean_ctor_get(v_x_1151_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_x_1151_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1172_ = v_x_1151_;
v_isShared_1173_ = v_isSharedCheck_1224_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_content_1170_);
lean_dec(v_x_1151_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1224_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set_tag(v___x_1172_, 9);
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_content_1170_);
v___x_1175_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v_snd_1177_; lean_object* v_fst_1178_; lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v_pieces_1182_; lean_object* v___y_1183_; uint8_t v_inEmph_1191_; uint8_t v_inBold_1192_; uint8_t v_inLink_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1222_; 
v___x_1176_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1175_);
v_snd_1177_ = lean_ctor_get(v___x_1176_, 1);
lean_inc(v_snd_1177_);
v_fst_1178_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_fst_1178_);
lean_dec_ref(v___x_1176_);
v_fst_1179_ = lean_ctor_get(v_snd_1177_, 0);
lean_inc(v_fst_1179_);
v_snd_1180_ = lean_ctor_get(v_snd_1177_, 1);
lean_inc(v_snd_1180_);
lean_dec(v_snd_1177_);
v_inEmph_1191_ = lean_ctor_get_uint8(v_x_1150_, 0);
v_inBold_1192_ = lean_ctor_get_uint8(v_x_1150_, 1);
v_inLink_1193_ = lean_ctor_get_uint8(v_x_1150_, 2);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1195_ = v_x_1150_;
v_isShared_1196_ = v_isSharedCheck_1222_;
goto v_resetjp_1194_;
}
else
{
lean_dec(v_x_1150_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1222_;
goto v_resetjp_1194_;
}
v___jp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1184_ = lean_string_utf8_byte_size(v_snd_1180_);
v___x_1185_ = lean_unsigned_to_nat(0u);
v___x_1186_ = lean_nat_dec_eq(v___x_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_mk_empty_array_with_capacity(v___x_1187_);
v___x_1189_ = lean_array_push(v___x_1188_, v_snd_1180_);
v___x_1190_ = lean_array_push(v_pieces_1182_, v___x_1189_);
v_pieces_1159_ = v___x_1190_;
v___y_1160_ = v___y_1183_;
goto v___jp_1158_;
}
else
{
lean_dec(v_snd_1180_);
v_pieces_1159_ = v_pieces_1182_;
v___y_1160_ = v___y_1183_;
goto v___jp_1158_;
}
}
v_resetjp_1194_:
{
uint8_t v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = 1;
if (v_isShared_1196_ == 0)
{
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1221_, 1, v_inBold_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1221_, 2, v_inLink_1193_);
v___x_1199_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v_fst_1201_; lean_object* v_snd_1202_; lean_object* v_pieces_1204_; lean_object* v___y_1205_; lean_object* v_pieces_1210_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
lean_ctor_set_uint8(v___x_1199_, 0, v___x_1197_);
v___x_1200_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1149_, v___x_1199_, v_fst_1179_, v_a_1152_);
v_fst_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_fst_1201_);
v_snd_1202_ = lean_ctor_get(v___x_1200_, 1);
lean_inc(v_snd_1202_);
lean_dec_ref(v___x_1200_);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_1215_ = lean_string_utf8_byte_size(v_fst_1178_);
v___x_1216_ = lean_nat_dec_eq(v___x_1215_, v___x_1213_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1217_ = lean_unsigned_to_nat(1u);
v___x_1218_ = lean_mk_empty_array_with_capacity(v___x_1217_);
v___x_1219_ = lean_array_push(v___x_1218_, v_fst_1178_);
v___x_1220_ = lean_array_push(v___x_1214_, v___x_1219_);
v_pieces_1210_ = v___x_1220_;
goto v___jp_1209_;
}
else
{
lean_dec(v_fst_1178_);
v_pieces_1210_ = v___x_1214_;
goto v___jp_1209_;
}
v___jp_1203_:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_array_push(v_pieces_1204_, v_fst_1201_);
if (v_inEmph_1191_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21));
v___x_1208_ = lean_array_push(v___x_1206_, v___x_1207_);
v_pieces_1182_ = v___x_1208_;
v___y_1183_ = v___y_1205_;
goto v___jp_1181_;
}
else
{
v_pieces_1182_ = v___x_1206_;
v___y_1183_ = v___y_1205_;
goto v___jp_1181_;
}
}
v___jp_1209_:
{
if (v_inEmph_1191_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21));
v___x_1212_ = lean_array_push(v_pieces_1210_, v___x_1211_);
v_pieces_1204_ = v___x_1212_;
v___y_1205_ = v_snd_1202_;
goto v___jp_1203_;
}
else
{
v_pieces_1204_ = v_pieces_1210_;
v___y_1205_ = v_snd_1202_;
goto v___jp_1203_;
}
}
}
}
}
}
}
case 2:
{
lean_object* v_content_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1279_; 
v_content_1225_ = lean_ctor_get(v_x_1151_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_x_1151_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1227_ = v_x_1151_;
v_isShared_1228_ = v_isSharedCheck_1279_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_content_1225_);
lean_dec(v_x_1151_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1279_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set_tag(v___x_1227_, 9);
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_content_1225_);
v___x_1230_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v_snd_1232_; lean_object* v_fst_1233_; lean_object* v_fst_1234_; lean_object* v_snd_1235_; lean_object* v_pieces_1237_; lean_object* v___y_1238_; uint8_t v_inEmph_1246_; uint8_t v_inBold_1247_; uint8_t v_inLink_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1277_; 
v___x_1231_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1230_);
v_snd_1232_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_snd_1232_);
v_fst_1233_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_fst_1233_);
lean_dec_ref(v___x_1231_);
v_fst_1234_ = lean_ctor_get(v_snd_1232_, 0);
lean_inc(v_fst_1234_);
v_snd_1235_ = lean_ctor_get(v_snd_1232_, 1);
lean_inc(v_snd_1235_);
lean_dec(v_snd_1232_);
v_inEmph_1246_ = lean_ctor_get_uint8(v_x_1150_, 0);
v_inBold_1247_ = lean_ctor_get_uint8(v_x_1150_, 1);
v_inLink_1248_ = lean_ctor_get_uint8(v_x_1150_, 2);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1250_ = v_x_1150_;
v_isShared_1251_ = v_isSharedCheck_1277_;
goto v_resetjp_1249_;
}
else
{
lean_dec(v_x_1150_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1277_;
goto v_resetjp_1249_;
}
v___jp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1239_ = lean_string_utf8_byte_size(v_snd_1235_);
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = lean_nat_dec_eq(v___x_1239_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = lean_mk_empty_array_with_capacity(v___x_1242_);
v___x_1244_ = lean_array_push(v___x_1243_, v_snd_1235_);
v___x_1245_ = lean_array_push(v_pieces_1237_, v___x_1244_);
v_pieces_1154_ = v___x_1245_;
v___y_1155_ = v___y_1238_;
goto v___jp_1153_;
}
else
{
lean_dec(v_snd_1235_);
v_pieces_1154_ = v_pieces_1237_;
v___y_1155_ = v___y_1238_;
goto v___jp_1153_;
}
}
v_resetjp_1249_:
{
uint8_t v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = 1;
if (v_isShared_1251_ == 0)
{
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, 0, v_inEmph_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, 2, v_inLink_1248_);
v___x_1254_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; lean_object* v_fst_1256_; lean_object* v_snd_1257_; lean_object* v_pieces_1259_; lean_object* v___y_1260_; lean_object* v_pieces_1265_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
lean_ctor_set_uint8(v___x_1254_, 1, v___x_1252_);
v___x_1255_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1149_, v___x_1254_, v_fst_1234_, v_a_1152_);
v_fst_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_fst_1256_);
v_snd_1257_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_snd_1257_);
lean_dec_ref(v___x_1255_);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_1270_ = lean_string_utf8_byte_size(v_fst_1233_);
v___x_1271_ = lean_nat_dec_eq(v___x_1270_, v___x_1268_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_mk_empty_array_with_capacity(v___x_1272_);
v___x_1274_ = lean_array_push(v___x_1273_, v_fst_1233_);
v___x_1275_ = lean_array_push(v___x_1269_, v___x_1274_);
v_pieces_1265_ = v___x_1275_;
goto v___jp_1264_;
}
else
{
lean_dec(v_fst_1233_);
v_pieces_1265_ = v___x_1269_;
goto v___jp_1264_;
}
v___jp_1258_:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_array_push(v_pieces_1259_, v_fst_1256_);
if (v_inBold_1247_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24));
v___x_1263_ = lean_array_push(v___x_1261_, v___x_1262_);
v_pieces_1237_ = v___x_1263_;
v___y_1238_ = v___y_1260_;
goto v___jp_1236_;
}
else
{
v_pieces_1237_ = v___x_1261_;
v___y_1238_ = v___y_1260_;
goto v___jp_1236_;
}
}
v___jp_1264_:
{
if (v_inBold_1247_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24));
v___x_1267_ = lean_array_push(v_pieces_1265_, v___x_1266_);
v_pieces_1259_ = v___x_1267_;
v___y_1260_ = v_snd_1257_;
goto v___jp_1258_;
}
else
{
v_pieces_1259_ = v_pieces_1265_;
v___y_1260_ = v_snd_1257_;
goto v___jp_1258_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_string_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec_ref(v_x_1150_);
lean_dec_ref(v_inst_1149_);
v_string_1280_ = lean_ctor_get(v_x_1151_, 0);
lean_inc_ref(v_string_1280_);
lean_dec_ref_known(v_x_1151_, 1);
v___x_1281_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1280_);
v___x_1282_ = lean_unsigned_to_nat(1u);
v___x_1283_ = lean_mk_empty_array_with_capacity(v___x_1282_);
v___x_1284_ = lean_array_push(v___x_1283_, v___x_1281_);
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v_a_1152_);
return v___x_1285_;
}
case 4:
{
uint8_t v_mode_1286_; 
lean_dec_ref(v_x_1150_);
lean_dec_ref(v_inst_1149_);
v_mode_1286_ = lean_ctor_get_uint8(v_x_1151_, sizeof(void*)*1);
if (v_mode_1286_ == 0)
{
lean_object* v_string_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_string_1287_ = lean_ctor_get(v_x_1151_, 0);
lean_inc_ref(v_string_1287_);
lean_dec_ref_known(v_x_1151_, 1);
v___x_1288_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25));
v___x_1289_ = lean_string_append(v___x_1288_, v_string_1287_);
lean_dec_ref(v_string_1287_);
v___x_1290_ = lean_string_append(v___x_1289_, v___x_1288_);
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_mk_empty_array_with_capacity(v___x_1291_);
v___x_1293_ = lean_array_push(v___x_1292_, v___x_1290_);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v_a_1152_);
return v___x_1294_;
}
else
{
lean_object* v_string_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v_string_1295_ = lean_ctor_get(v_x_1151_, 0);
lean_inc_ref(v_string_1295_);
lean_dec_ref_known(v_x_1151_, 1);
v___x_1296_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26));
v___x_1297_ = lean_string_append(v___x_1296_, v_string_1295_);
lean_dec_ref(v_string_1295_);
v___x_1298_ = lean_string_append(v___x_1297_, v___x_1296_);
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = lean_mk_empty_array_with_capacity(v___x_1299_);
v___x_1301_ = lean_array_push(v___x_1300_, v___x_1298_);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v_a_1152_);
return v___x_1302_;
}
}
case 5:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec_ref_known(v_x_1151_, 1);
lean_dec_ref(v_x_1150_);
lean_dec_ref(v_inst_1149_);
v___x_1303_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27));
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v_a_1152_);
return v___x_1304_;
}
case 6:
{
uint8_t v_inLink_1305_; 
v_inLink_1305_ = lean_ctor_get_uint8(v_x_1150_, 2);
if (v_inLink_1305_ == 0)
{
lean_object* v_content_1306_; lean_object* v_url_1307_; uint8_t v_inEmph_1308_; uint8_t v_inBold_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1339_; 
v_content_1306_ = lean_ctor_get(v_x_1151_, 0);
lean_inc_ref(v_content_1306_);
v_url_1307_ = lean_ctor_get(v_x_1151_, 1);
lean_inc_ref(v_url_1307_);
lean_dec_ref_known(v_x_1151_, 2);
v_inEmph_1308_ = lean_ctor_get_uint8(v_x_1150_, 0);
v_inBold_1309_ = lean_ctor_get_uint8(v_x_1150_, 1);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1311_ = v_x_1150_;
v_isShared_1312_ = v_isSharedCheck_1339_;
goto v_resetjp_1310_;
}
else
{
lean_dec(v_x_1150_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1339_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
uint8_t v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = 1;
if (v_isShared_1312_ == 0)
{
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, 0, v_inEmph_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, 1, v_inBold_1309_);
v___x_1315_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_fst_1318_; lean_object* v_snd_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1337_; 
lean_ctor_set_uint8(v___x_1315_, 2, v___x_1313_);
v___x_1316_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_content_1306_);
v___x_1317_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1149_, v___x_1315_, v___x_1316_, v_a_1152_);
v_fst_1318_ = lean_ctor_get(v___x_1317_, 0);
v_snd_1319_ = lean_ctor_get(v___x_1317_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1321_ = v___x_1317_;
v_isShared_1322_ = v_isSharedCheck_1337_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_snd_1319_);
lean_inc(v_fst_1318_);
lean_dec(v___x_1317_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1337_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = lean_mk_empty_array_with_capacity(v___x_1323_);
v___x_1325_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30));
v___x_1326_ = lean_string_append(v___x_1325_, v_url_1307_);
lean_dec_ref(v_url_1307_);
v___x_1327_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31));
v___x_1328_ = lean_string_append(v___x_1326_, v___x_1327_);
v___x_1329_ = lean_array_push(v___x_1324_, v___x_1328_);
v___x_1330_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32);
v___x_1331_ = lean_array_push(v___x_1330_, v_fst_1318_);
v___x_1332_ = lean_array_push(v___x_1331_, v___x_1329_);
v___x_1333_ = l_Lean_Doc_joinInlines(v___x_1332_);
lean_dec_ref(v___x_1332_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1333_);
v___x_1335_ = v___x_1321_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_snd_1319_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
else
{
lean_object* v_content_1340_; lean_object* v___x_1341_; size_t v_sz_1342_; size_t v___x_1343_; lean_object* v___x_5248__overap_1344_; lean_object* v___x_1345_; lean_object* v_fst_1346_; lean_object* v_snd_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1355_; 
v_content_1340_ = lean_ctor_get(v_x_1151_, 0);
lean_inc_ref(v_content_1340_);
lean_dec_ref_known(v_x_1151_, 2);
v___x_1341_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg), 4, 2);
lean_closure_set(v___x_1341_, 0, v_inst_1149_);
lean_closure_set(v___x_1341_, 1, v_x_1150_);
v_sz_1342_ = lean_array_size(v_content_1340_);
v___x_1343_ = ((size_t)0ULL);
v___x_5248__overap_1344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1163_, v___x_1341_, v_sz_1342_, v___x_1343_, v_content_1340_);
v___x_1345_ = lean_apply_1(v___x_5248__overap_1344_, v_a_1152_);
v_fst_1346_ = lean_ctor_get(v___x_1345_, 0);
v_snd_1347_ = lean_ctor_get(v___x_1345_, 1);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1349_ = v___x_1345_;
v_isShared_1350_ = v_isSharedCheck_1355_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_snd_1347_);
lean_inc(v_fst_1346_);
lean_dec(v___x_1345_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1355_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = l_Lean_Doc_joinInlines(v_fst_1346_);
lean_dec(v_fst_1346_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1351_);
v___x_1353_ = v___x_1349_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_snd_1347_);
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
case 7:
{
lean_object* v_name_1356_; lean_object* v_content_1357_; lean_object* v___x_1358_; size_t v_sz_1359_; size_t v___x_1360_; lean_object* v___x_5251__overap_1361_; lean_object* v___x_1362_; lean_object* v_fst_1363_; lean_object* v_snd_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1384_; 
v_name_1356_ = lean_ctor_get(v_x_1151_, 0);
lean_inc_ref(v_name_1356_);
v_content_1357_ = lean_ctor_get(v_x_1151_, 1);
lean_inc_ref(v_content_1357_);
lean_dec_ref_known(v_x_1151_, 2);
v___x_1358_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg), 4, 2);
lean_closure_set(v___x_1358_, 0, v_inst_1149_);
lean_closure_set(v___x_1358_, 1, v_x_1150_);
v_sz_1359_ = lean_array_size(v_content_1357_);
v___x_1360_ = ((size_t)0ULL);
v___x_5251__overap_1361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1163_, v___x_1358_, v_sz_1359_, v___x_1360_, v_content_1357_);
v___x_1362_ = lean_apply_1(v___x_5251__overap_1361_, v_a_1152_);
v_fst_1363_ = lean_ctor_get(v___x_1362_, 0);
v_snd_1364_ = lean_ctor_get(v___x_1362_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1366_ = v___x_1362_;
v_isShared_1367_ = v_isSharedCheck_1384_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_snd_1364_);
lean_inc(v_fst_1363_);
lean_dec(v___x_1362_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1384_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1368_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_1369_ = l_Lean_Doc_joinInlines(v_fst_1363_);
lean_dec(v_fst_1363_);
v___x_1370_ = lean_array_to_list(v___x_1369_);
v___x_1371_ = l_String_intercalate(v___x_1368_, v___x_1370_);
lean_inc_ref(v_name_1356_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v___x_1371_);
lean_ctor_set(v___x_1366_, 0, v_name_1356_);
v___x_1373_ = v___x_1366_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_name_1356_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1374_ = lean_array_push(v_snd_1364_, v___x_1373_);
v___x_1375_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_1376_ = lean_string_append(v___x_1375_, v_name_1356_);
lean_dec_ref(v_name_1356_);
v___x_1377_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33));
v___x_1378_ = lean_string_append(v___x_1376_, v___x_1377_);
v___x_1379_ = lean_unsigned_to_nat(1u);
v___x_1380_ = lean_mk_empty_array_with_capacity(v___x_1379_);
v___x_1381_ = lean_array_push(v___x_1380_, v___x_1378_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v___x_1374_);
return v___x_1382_;
}
}
}
case 8:
{
lean_object* v_alt_1385_; lean_object* v_url_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec_ref(v_x_1150_);
lean_dec_ref(v_inst_1149_);
v_alt_1385_ = lean_ctor_get(v_x_1151_, 0);
lean_inc_ref(v_alt_1385_);
v_url_1386_ = lean_ctor_get(v_x_1151_, 1);
lean_inc_ref(v_url_1386_);
lean_dec_ref_known(v_x_1151_, 2);
v___x_1387_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34));
v___x_1388_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1385_);
lean_dec_ref(v_alt_1385_);
v___x_1389_ = lean_string_append(v___x_1387_, v___x_1388_);
lean_dec_ref(v___x_1388_);
v___x_1390_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30));
v___x_1391_ = lean_string_append(v___x_1389_, v___x_1390_);
v___x_1392_ = lean_string_append(v___x_1391_, v_url_1386_);
lean_dec_ref(v_url_1386_);
v___x_1393_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31));
v___x_1394_ = lean_string_append(v___x_1392_, v___x_1393_);
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = lean_mk_empty_array_with_capacity(v___x_1395_);
v___x_1397_ = lean_array_push(v___x_1396_, v___x_1394_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v_a_1152_);
return v___x_1398_;
}
case 9:
{
lean_object* v_content_1399_; lean_object* v___x_1400_; size_t v_sz_1401_; size_t v___x_1402_; lean_object* v___x_5254__overap_1403_; lean_object* v___x_1404_; lean_object* v_fst_1405_; lean_object* v_snd_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1414_; 
v_content_1399_ = lean_ctor_get(v_x_1151_, 0);
lean_inc_ref(v_content_1399_);
lean_dec_ref_known(v_x_1151_, 1);
v___x_1400_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg), 4, 2);
lean_closure_set(v___x_1400_, 0, v_inst_1149_);
lean_closure_set(v___x_1400_, 1, v_x_1150_);
v_sz_1401_ = lean_array_size(v_content_1399_);
v___x_1402_ = ((size_t)0ULL);
v___x_5254__overap_1403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1163_, v___x_1400_, v_sz_1401_, v___x_1402_, v_content_1399_);
v___x_1404_ = lean_apply_1(v___x_5254__overap_1403_, v_a_1152_);
v_fst_1405_ = lean_ctor_get(v___x_1404_, 0);
v_snd_1406_ = lean_ctor_get(v___x_1404_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1408_ = v___x_1404_;
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_snd_1406_);
lean_inc(v_fst_1405_);
lean_dec(v___x_1404_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = l_Lean_Doc_joinInlines(v_fst_1405_);
lean_dec(v_fst_1405_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1410_);
v___x_1412_ = v___x_1408_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_snd_1406_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
default: 
{
lean_object* v_container_1415_; lean_object* v_content_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_container_1415_ = lean_ctor_get(v_x_1151_, 0);
lean_inc(v_container_1415_);
v_content_1416_ = lean_ctor_get(v_x_1151_, 1);
lean_inc_ref(v_content_1416_);
lean_dec_ref_known(v_x_1151_, 2);
lean_inc_ref(v_inst_1149_);
v___x_1417_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg), 4, 2);
lean_closure_set(v___x_1417_, 0, v_inst_1149_);
lean_closure_set(v___x_1417_, 1, v_x_1150_);
v___x_1418_ = lean_apply_4(v_inst_1149_, v___x_1417_, v_container_1415_, v_content_1416_, v_a_1152_);
return v___x_1418_;
}
}
v___jp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = l_Lean_Doc_joinInlines(v_pieces_1154_);
lean_dec_ref(v_pieces_1154_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___y_1155_);
return v___x_1157_;
}
v___jp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = l_Lean_Doc_joinInlines(v_pieces_1159_);
lean_dec_ref(v_pieces_1159_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v___y_1160_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1419_, lean_object* v_inst_1420_, lean_object* v_x_1421_, lean_object* v_x_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1420_, v_x_1421_, v_x_1422_, v_a_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1429_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1425_, v___x_1428_, v_a_1426_, v_a_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1430_, lean_object* v_inst_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1435_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1431_, v___x_1434_, v_a_1432_, v_a_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1), 4, 2);
lean_closure_set(v___x_1437_, 0, lean_box(0));
lean_closure_set(v___x_1437_, 1, v_inst_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1438_, lean_object* v_inst_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1), 4, 2);
lean_closure_set(v___x_1440_, 0, lean_box(0));
lean_closure_set(v___x_1440_, 1, v_inst_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(uint32_t v___x_1441_, lean_object* v_s_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_string_push(v_s_1442_, v___x_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object* v___x_1444_, lean_object* v_s_1445_){
_start:
{
uint32_t v___x_3198__boxed_1446_; lean_object* v_res_1447_; 
v___x_3198__boxed_1446_ = lean_unbox_uint32(v___x_1444_);
lean_dec(v___x_1444_);
v_res_1447_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v___x_3198__boxed_1446_, v_s_1445_);
return v_res_1447_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___f_1452_; 
v___x_1451_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___f_1452_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1452_, 0, v___x_1451_);
return v___f_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v___x_1455_, lean_object* v___x_1456_, lean_object* v_a_1457_, lean_object* v_x_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___x_1461_; size_t v_sz_1462_; size_t v___x_1463_; lean_object* v___x_3142__overap_1464_; lean_object* v___x_1465_; lean_object* v_fst_1466_; lean_object* v_snd_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1495_; 
v___x_1461_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg), 4, 2);
lean_closure_set(v___x_1461_, 0, v_inst_1453_);
lean_closure_set(v___x_1461_, 1, v_inst_1454_);
v_sz_1462_ = lean_array_size(v_a_1457_);
v___x_1463_ = ((size_t)0ULL);
v___x_3142__overap_1464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1455_, v___x_1461_, v_sz_1462_, v___x_1463_, v_a_1457_);
v___x_1465_ = lean_apply_1(v___x_3142__overap_1464_, v___y_1460_);
v_fst_1466_ = lean_ctor_get(v___x_1465_, 0);
v_snd_1467_ = lean_ctor_get(v___x_1465_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1469_ = v___x_1465_;
v_isShared_1470_ = v_isSharedCheck_1495_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_snd_1467_);
lean_inc(v_fst_1466_);
lean_dec(v___x_1465_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1495_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_fst_1471_; lean_object* v_snd_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1494_; 
v_fst_1471_ = lean_ctor_get(v___y_1459_, 0);
v_snd_1472_ = lean_ctor_get(v___y_1459_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___y_1459_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1474_ = v___y_1459_;
v_isShared_1475_ = v_isSharedCheck_1494_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_snd_1472_);
lean_inc(v_fst_1471_);
lean_dec(v___y_1459_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1494_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
lean_inc(v_snd_1472_);
v___x_1476_ = l_Nat_reprFast(v_snd_1472_);
v___x_1477_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_1478_ = lean_string_append(v___x_1476_, v___x_1477_);
v___x_1479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_1480_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1);
v___x_1481_ = lean_string_utf8_byte_size(v___x_1478_);
v___x_1482_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1480_, v___x_1481_, v___x_1479_);
v___x_1483_ = l_Lean_Doc_joinBlocks(v_fst_1466_);
lean_dec(v_fst_1466_);
v___x_1484_ = l_Lean_Doc_prefixListLines(v___x_1478_, v___x_1482_, v___x_1483_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = lean_array_push(v_fst_1471_, v___x_1484_);
v___x_1486_ = lean_nat_add(v_snd_1472_, v___x_1456_);
lean_dec(v_snd_1472_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v___x_1486_);
lean_ctor_set(v___x_1474_, 0, v___x_1485_);
v___x_1488_ = v___x_1474_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1489_);
v___x_1491_ = v___x_1469_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_snd_1467_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1496_, lean_object* v_inst_1497_, lean_object* v___x_1498_, lean_object* v___x_1499_, lean_object* v_a_1500_, lean_object* v_x_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1496_, v_inst_1497_, v___x_1498_, v___x_1499_, v_a_1500_, v_x_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___x_1499_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v___x_1512_, lean_object* v_item_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1515_; lean_object* v_term_1516_; lean_object* v_desc_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v_fst_1520_; lean_object* v_snd_1521_; lean_object* v___x_1522_; size_t v_sz_1523_; size_t v___x_1524_; lean_object* v___x_3172__overap_1525_; lean_object* v___x_1526_; lean_object* v_fst_1527_; lean_object* v_snd_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1555_; 
v___x_1515_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_1516_ = lean_ctor_get(v_item_1513_, 0);
lean_inc_ref(v_term_1516_);
v_desc_1517_ = lean_ctor_get(v_item_1513_, 1);
lean_inc_ref_n(v_desc_1517_, 2);
lean_dec_ref(v_item_1513_);
v___x_1518_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1518_, 0, v_term_1516_);
lean_inc_ref(v_inst_1510_);
v___x_1519_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1510_, v___x_1515_, v___x_1518_, v___y_1514_);
v_fst_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_fst_1520_);
v_snd_1521_ = lean_ctor_get(v___x_1519_, 1);
lean_inc(v_snd_1521_);
lean_dec_ref(v___x_1519_);
v___x_1522_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg), 4, 2);
lean_closure_set(v___x_1522_, 0, v_inst_1510_);
lean_closure_set(v___x_1522_, 1, v_inst_1511_);
v_sz_1523_ = lean_array_size(v_desc_1517_);
v___x_1524_ = ((size_t)0ULL);
v___x_3172__overap_1525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1512_, v___x_1522_, v_sz_1523_, v___x_1524_, v_desc_1517_);
v___x_1526_ = lean_apply_1(v___x_3172__overap_1525_, v_snd_1521_);
v_fst_1527_ = lean_ctor_get(v___x_1526_, 0);
v_snd_1528_ = lean_ctor_get(v___x_1526_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1530_ = v___x_1526_;
v_isShared_1531_ = v_isSharedCheck_1555_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_snd_1528_);
lean_inc(v_fst_1527_);
lean_dec(v___x_1526_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1555_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___y_1533_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1540_ = lean_unsigned_to_nat(1u);
v___x_1541_ = lean_mk_empty_array_with_capacity(v___x_1540_);
v___x_1542_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_1543_ = lean_unsigned_to_nat(2u);
v___x_1544_ = lean_mk_empty_array_with_capacity(v___x_1543_);
v___x_1545_ = lean_array_push(v___x_1544_, v_fst_1520_);
v___x_1546_ = lean_array_push(v___x_1545_, v___x_1542_);
v___x_1547_ = l_Lean_Doc_joinInlines(v___x_1546_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = lean_array_get_size(v_desc_1517_);
lean_dec_ref(v_desc_1517_);
v___x_1549_ = lean_nat_dec_le(v___x_1548_, v___x_1540_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = lean_array_push(v___x_1541_, v___x_1547_);
v___x_1551_ = l_Array_append___redArg(v___x_1550_, v_fst_1527_);
lean_dec(v_fst_1527_);
v___x_1552_ = l_Lean_Doc_joinBlocks(v___x_1551_);
lean_dec_ref(v___x_1551_);
v___y_1533_ = v___x_1552_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec_ref(v___x_1541_);
v___x_1553_ = l_Lean_Doc_joinBlocks(v_fst_1527_);
lean_dec(v_fst_1527_);
v___x_1554_ = l_Array_append___redArg(v___x_1547_, v___x_1553_);
lean_dec_ref(v___x_1553_);
v___y_1533_ = v___x_1554_;
goto v___jp_1532_;
}
v___jp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1534_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1535_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1536_ = l_Lean_Doc_prefixListLines(v___x_1534_, v___x_1535_, v___y_1533_);
lean_dec_ref(v___y_1533_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1536_);
v___x_1538_ = v___x_1530_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_snd_1528_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_x_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19));
switch(lean_obj_tag(v_x_1559_))
{
case 0:
{
lean_object* v_contents_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v_inst_1558_);
v_contents_1562_ = lean_ctor_get(v_x_1559_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_x_1559_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1564_ = v_x_1559_;
v_isShared_1565_ = v_isSharedCheck_1571_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_contents_1562_);
lean_dec(v_x_1559_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1571_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1566_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_1565_ == 0)
{
lean_ctor_set_tag(v___x_1564_, 9);
v___x_1568_ = v___x_1564_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_contents_1562_);
v___x_1568_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1569_; 
v___x_1569_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1557_, v___x_1566_, v___x_1568_, v_a_1560_);
return v___x_1569_;
}
}
}
case 1:
{
lean_object* v_content_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec_ref(v_inst_1558_);
lean_dec_ref(v_inst_1557_);
v_content_1572_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_content_1572_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1573_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_1572_);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v_a_1560_);
return v___x_1574_;
}
case 2:
{
lean_object* v_items_1575_; lean_object* v___f_1576_; size_t v_sz_1577_; size_t v___x_1578_; lean_object* v___x_3079__overap_1579_; lean_object* v___x_1580_; lean_object* v_fst_1581_; lean_object* v_snd_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1590_; 
v_items_1575_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_items_1575_);
lean_dec_ref_known(v_x_1559_, 1);
v___f_1576_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1576_, 0, v_inst_1557_);
lean_closure_set(v___f_1576_, 1, v_inst_1558_);
lean_closure_set(v___f_1576_, 2, v___x_1561_);
v_sz_1577_ = lean_array_size(v_items_1575_);
v___x_1578_ = ((size_t)0ULL);
v___x_3079__overap_1579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1561_, v___f_1576_, v_sz_1577_, v___x_1578_, v_items_1575_);
v___x_1580_ = lean_apply_1(v___x_3079__overap_1579_, v_a_1560_);
v_fst_1581_ = lean_ctor_get(v___x_1580_, 0);
v_snd_1582_ = lean_ctor_get(v___x_1580_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1584_ = v___x_1580_;
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_snd_1582_);
lean_inc(v_fst_1581_);
lean_dec(v___x_1580_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = l_Lean_Doc_joinBlocks(v_fst_1581_);
lean_dec(v_fst_1581_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1586_);
v___x_1588_ = v___x_1584_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_snd_1582_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
case 3:
{
lean_object* v_start_1591_; lean_object* v_items_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1622_; 
v_start_1591_ = lean_ctor_get(v_x_1559_, 0);
v_items_1592_ = lean_ctor_get(v_x_1559_, 1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_x_1559_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1594_ = v_x_1559_;
v_isShared_1595_ = v_isSharedCheck_1622_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_items_1592_);
lean_inc(v_start_1591_);
lean_dec(v_x_1559_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1622_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_out_1596_; lean_object* v___x_1597_; lean_object* v___f_1598_; lean_object* v___y_1600_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v_out_1596_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22));
v___x_1597_ = lean_unsigned_to_nat(1u);
v___f_1598_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 8, 4);
lean_closure_set(v___f_1598_, 0, v_inst_1557_);
lean_closure_set(v___f_1598_, 1, v_inst_1558_);
lean_closure_set(v___f_1598_, 2, v___x_1561_);
lean_closure_set(v___f_1598_, 3, v___x_1597_);
v___x_1620_ = l_Int_toNat(v_start_1591_);
lean_dec(v_start_1591_);
v___x_1621_ = lean_nat_dec_le(v___x_1597_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_dec(v___x_1620_);
v___y_1600_ = v___x_1597_;
goto v___jp_1599_;
}
else
{
v___y_1600_ = v___x_1620_;
goto v___jp_1599_;
}
v___jp_1599_:
{
lean_object* v___x_1602_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set_tag(v___x_1594_, 0);
lean_ctor_set(v___x_1594_, 1, v___y_1600_);
lean_ctor_set(v___x_1594_, 0, v_out_1596_);
v___x_1602_ = v___x_1594_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_out_1596_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v___y_1600_);
v___x_1602_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
size_t v_sz_1603_; size_t v___x_1604_; lean_object* v___x_2973__overap_1605_; lean_object* v___x_1606_; lean_object* v_fst_1607_; lean_object* v_snd_1608_; lean_object* v_fst_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1617_; 
v_sz_1603_ = lean_array_size(v_items_1592_);
v___x_1604_ = ((size_t)0ULL);
v___x_2973__overap_1605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1561_, v_items_1592_, v___f_1598_, v_sz_1603_, v___x_1604_, v___x_1602_);
v___x_1606_ = lean_apply_1(v___x_2973__overap_1605_, v_a_1560_);
v_fst_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_fst_1607_);
v_snd_1608_ = lean_ctor_get(v___x_1606_, 1);
lean_inc(v_snd_1608_);
lean_dec_ref(v___x_1606_);
v_fst_1609_ = lean_ctor_get(v_fst_1607_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_fst_1607_);
if (v_isSharedCheck_1617_ == 0)
{
lean_object* v_unused_1618_; 
v_unused_1618_ = lean_ctor_get(v_fst_1607_, 1);
lean_dec(v_unused_1618_);
v___x_1611_ = v_fst_1607_;
v_isShared_1612_ = v_isSharedCheck_1617_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_fst_1609_);
lean_dec(v_fst_1607_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1617_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1613_ = l_Lean_Doc_joinBlocks(v_fst_1609_);
lean_dec(v_fst_1609_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 1, v_snd_1608_);
lean_ctor_set(v___x_1611_, 0, v___x_1613_);
v___x_1615_ = v___x_1611_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_snd_1608_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
}
case 4:
{
lean_object* v_items_1623_; lean_object* v___f_1624_; size_t v_sz_1625_; size_t v___x_1626_; lean_object* v___x_3085__overap_1627_; lean_object* v___x_1628_; lean_object* v_fst_1629_; lean_object* v_snd_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1638_; 
v_items_1623_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_items_1623_);
lean_dec_ref_known(v_x_1559_, 1);
v___f_1624_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3), 5, 3);
lean_closure_set(v___f_1624_, 0, v_inst_1557_);
lean_closure_set(v___f_1624_, 1, v_inst_1558_);
lean_closure_set(v___f_1624_, 2, v___x_1561_);
v_sz_1625_ = lean_array_size(v_items_1623_);
v___x_1626_ = ((size_t)0ULL);
v___x_3085__overap_1627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1561_, v___f_1624_, v_sz_1625_, v___x_1626_, v_items_1623_);
v___x_1628_ = lean_apply_1(v___x_3085__overap_1627_, v_a_1560_);
v_fst_1629_ = lean_ctor_get(v___x_1628_, 0);
v_snd_1630_ = lean_ctor_get(v___x_1628_, 1);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1632_ = v___x_1628_;
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_snd_1630_);
lean_inc(v_fst_1629_);
lean_dec(v___x_1628_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = l_Lean_Doc_joinBlocks(v_fst_1629_);
lean_dec(v_fst_1629_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1634_);
v___x_1636_ = v___x_1632_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_snd_1630_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
case 5:
{
lean_object* v_items_1639_; lean_object* v___x_1640_; size_t v_sz_1641_; size_t v___x_1642_; lean_object* v___x_3088__overap_1643_; lean_object* v___x_1644_; lean_object* v_fst_1645_; lean_object* v_snd_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1656_; 
v_items_1639_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_items_1639_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1640_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg), 4, 2);
lean_closure_set(v___x_1640_, 0, v_inst_1557_);
lean_closure_set(v___x_1640_, 1, v_inst_1558_);
v_sz_1641_ = lean_array_size(v_items_1639_);
v___x_1642_ = ((size_t)0ULL);
v___x_3088__overap_1643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1561_, v___x_1640_, v_sz_1641_, v___x_1642_, v_items_1639_);
v___x_1644_ = lean_apply_1(v___x_3088__overap_1643_, v_a_1560_);
v_fst_1645_ = lean_ctor_get(v___x_1644_, 0);
v_snd_1646_ = lean_ctor_get(v___x_1644_, 1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1648_ = v___x_1644_;
v_isShared_1649_ = v_isSharedCheck_1656_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_snd_1646_);
lean_inc(v_fst_1645_);
lean_dec(v___x_1644_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1656_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1650_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_1651_ = l_Lean_Doc_joinBlocks(v_fst_1645_);
lean_dec(v_fst_1645_);
v___x_1652_ = l_Lean_Doc_prefixLines(v___x_1650_, v___x_1651_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1652_);
v___x_1654_ = v___x_1648_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_snd_1646_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
case 6:
{
lean_object* v_content_1657_; lean_object* v___x_1658_; size_t v_sz_1659_; size_t v___x_1660_; lean_object* v___x_3091__overap_1661_; lean_object* v___x_1662_; lean_object* v_fst_1663_; lean_object* v_snd_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1672_; 
v_content_1657_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_content_1657_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1658_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg), 4, 2);
lean_closure_set(v___x_1658_, 0, v_inst_1557_);
lean_closure_set(v___x_1658_, 1, v_inst_1558_);
v_sz_1659_ = lean_array_size(v_content_1657_);
v___x_1660_ = ((size_t)0ULL);
v___x_3091__overap_1661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1561_, v___x_1658_, v_sz_1659_, v___x_1660_, v_content_1657_);
v___x_1662_ = lean_apply_1(v___x_3091__overap_1661_, v_a_1560_);
v_fst_1663_ = lean_ctor_get(v___x_1662_, 0);
v_snd_1664_ = lean_ctor_get(v___x_1662_, 1);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1666_ = v___x_1662_;
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_snd_1664_);
lean_inc(v_fst_1663_);
lean_dec(v___x_1662_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = l_Lean_Doc_joinBlocks(v_fst_1663_);
lean_dec(v_fst_1663_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1668_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_snd_1664_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
default: 
{
lean_object* v_container_1673_; lean_object* v_content_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_container_1673_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_container_1673_);
v_content_1674_ = lean_ctor_get(v_x_1559_, 1);
lean_inc_ref(v_content_1674_);
lean_dec_ref_known(v_x_1559_, 2);
v___x_1675_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc_ref(v_inst_1557_);
v___x_1676_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown), 5, 3);
lean_closure_set(v___x_1676_, 0, lean_box(0));
lean_closure_set(v___x_1676_, 1, v_inst_1557_);
lean_closure_set(v___x_1676_, 2, v___x_1675_);
lean_inc_ref(v_inst_1558_);
v___x_1677_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg), 4, 2);
lean_closure_set(v___x_1677_, 0, v_inst_1557_);
lean_closure_set(v___x_1677_, 1, v_inst_1558_);
v___x_1678_ = lean_apply_5(v_inst_1558_, v___x_1676_, v___x_1677_, v_container_1673_, v_content_1674_, v_a_1560_);
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v_inst_1679_, lean_object* v_inst_1680_, lean_object* v___x_1681_, lean_object* v_item_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1684_; size_t v_sz_1685_; size_t v___x_1686_; lean_object* v___x_3123__overap_1687_; lean_object* v___x_1688_; lean_object* v_fst_1689_; lean_object* v_snd_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1701_; 
v___x_1684_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg), 4, 2);
lean_closure_set(v___x_1684_, 0, v_inst_1679_);
lean_closure_set(v___x_1684_, 1, v_inst_1680_);
v_sz_1685_ = lean_array_size(v_item_1682_);
v___x_1686_ = ((size_t)0ULL);
v___x_3123__overap_1687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1681_, v___x_1684_, v_sz_1685_, v___x_1686_, v_item_1682_);
v___x_1688_ = lean_apply_1(v___x_3123__overap_1687_, v___y_1683_);
v_fst_1689_ = lean_ctor_get(v___x_1688_, 0);
v_snd_1690_ = lean_ctor_get(v___x_1688_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1692_ = v___x_1688_;
v_isShared_1693_ = v_isSharedCheck_1701_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_snd_1690_);
lean_inc(v_fst_1689_);
lean_dec(v___x_1688_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1701_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1694_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1695_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1696_ = l_Lean_Doc_joinBlocks(v_fst_1689_);
lean_dec(v_fst_1689_);
v___x_1697_ = l_Lean_Doc_prefixListLines(v___x_1694_, v___x_1695_, v___x_1696_);
lean_dec_ref(v___x_1696_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1697_);
v___x_1699_ = v___x_1692_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_snd_1690_);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1702_, lean_object* v_b_1703_, lean_object* v_inst_1704_, lean_object* v_inst_1705_, lean_object* v_x_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1704_, v_inst_1705_, v_x_1706_, v_a_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1709_, v_inst_1710_, v_a_1711_, v_a_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1714_, lean_object* v_b_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1716_, v_inst_1717_, v_a_1718_, v_a_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1721_, lean_object* v_inst_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1), 6, 4);
lean_closure_set(v___x_1723_, 0, lean_box(0));
lean_closure_set(v___x_1723_, 1, lean_box(0));
lean_closure_set(v___x_1723_, 2, v_inst_1721_);
lean_closure_set(v___x_1723_, 3, v_inst_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1724_, lean_object* v_b_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1), 6, 4);
lean_closure_set(v___x_1728_, 0, lean_box(0));
lean_closure_set(v___x_1728_, 1, lean_box(0));
lean_closure_set(v___x_1728_, 2, v_inst_1726_);
lean_closure_set(v___x_1728_, 3, v_inst_1727_);
return v___x_1728_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = 35;
v___x_1730_ = lean_box_uint32(v___x_1729_);
return v___x_1730_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___f_1732_; 
v___x_1731_ = l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1732_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1732_, 0, v___x_1731_);
return v___f_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_level_1735_, lean_object* v_part_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Doc_partMarkdown___redArg(v_inst_1733_, v_inst_1734_, v_level_1735_, v_part_1736_, v_a_1737_);
lean_dec(v_level_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg(lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_level_1741_, lean_object* v_part_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1744_; lean_object* v_title_1745_; lean_object* v_content_1746_; lean_object* v_subParts_1747_; lean_object* v___x_1748_; size_t v_sz_1749_; size_t v___x_1750_; lean_object* v___x_613__overap_1751_; lean_object* v___x_1752_; lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v___x_1755_; size_t v_sz_1756_; lean_object* v___x_616__overap_1757_; lean_object* v___x_1758_; lean_object* v_fst_1759_; lean_object* v_snd_1760_; lean_object* v___x_1761_; lean_object* v___f_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; size_t v_sz_1767_; lean_object* v___x_619__overap_1768_; lean_object* v___x_1769_; lean_object* v_fst_1770_; lean_object* v_snd_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1789_; 
v___x_1744_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19));
v_title_1745_ = lean_ctor_get(v_part_1742_, 0);
lean_inc_ref(v_title_1745_);
v_content_1746_ = lean_ctor_get(v_part_1742_, 3);
lean_inc_ref(v_content_1746_);
v_subParts_1747_ = lean_ctor_get(v_part_1742_, 4);
lean_inc_ref(v_subParts_1747_);
lean_dec_ref(v_part_1742_);
lean_inc_ref_n(v_inst_1739_, 2);
v___x_1748_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1), 4, 2);
lean_closure_set(v___x_1748_, 0, lean_box(0));
lean_closure_set(v___x_1748_, 1, v_inst_1739_);
v_sz_1749_ = lean_array_size(v_title_1745_);
v___x_1750_ = ((size_t)0ULL);
v___x_613__overap_1751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1744_, v___x_1748_, v_sz_1749_, v___x_1750_, v_title_1745_);
v___x_1752_ = lean_apply_1(v___x_613__overap_1751_, v_a_1743_);
v_fst_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_fst_1753_);
v_snd_1754_ = lean_ctor_get(v___x_1752_, 1);
lean_inc(v_snd_1754_);
lean_dec_ref(v___x_1752_);
lean_inc_ref(v_inst_1740_);
v___x_1755_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1), 6, 4);
lean_closure_set(v___x_1755_, 0, lean_box(0));
lean_closure_set(v___x_1755_, 1, lean_box(0));
lean_closure_set(v___x_1755_, 2, v_inst_1739_);
lean_closure_set(v___x_1755_, 3, v_inst_1740_);
v_sz_1756_ = lean_array_size(v_content_1746_);
v___x_616__overap_1757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1744_, v___x_1755_, v_sz_1756_, v___x_1750_, v_content_1746_);
v___x_1758_ = lean_apply_1(v___x_616__overap_1757_, v_snd_1754_);
v_fst_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_fst_1759_);
v_snd_1760_ = lean_ctor_get(v___x_1758_, 1);
lean_inc(v_snd_1760_);
lean_dec_ref(v___x_1758_);
v___x_1761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_1762_ = lean_obj_once(&l_Lean_Doc_partMarkdown___redArg___closed__0, &l_Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_partMarkdown___redArg___closed__0);
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = lean_nat_add(v_level_1741_, v___x_1763_);
lean_inc(v___x_1764_);
v___x_1765_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1762_, v___x_1764_, v___x_1761_);
v___x_1766_ = lean_alloc_closure((void*)(l_Lean_Doc_partMarkdown___redArg___boxed), 5, 3);
lean_closure_set(v___x_1766_, 0, v_inst_1739_);
lean_closure_set(v___x_1766_, 1, v_inst_1740_);
lean_closure_set(v___x_1766_, 2, v___x_1764_);
v_sz_1767_ = lean_array_size(v_subParts_1747_);
v___x_619__overap_1768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1744_, v___x_1766_, v_sz_1767_, v___x_1750_, v_subParts_1747_);
v___x_1769_ = lean_apply_1(v___x_619__overap_1768_, v_snd_1760_);
v_fst_1770_ = lean_ctor_get(v___x_1769_, 0);
v_snd_1771_ = lean_ctor_get(v___x_1769_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1773_ = v___x_1769_;
v_isShared_1774_ = v_isSharedCheck_1789_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_snd_1771_);
lean_inc(v_fst_1770_);
lean_dec(v___x_1769_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1789_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1775_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_1776_ = lean_string_append(v___x_1765_, v___x_1775_);
v___x_1777_ = lean_mk_empty_array_with_capacity(v___x_1763_);
lean_inc_ref_n(v___x_1777_, 2);
v___x_1778_ = lean_array_push(v___x_1777_, v___x_1776_);
v___x_1779_ = lean_array_push(v___x_1777_, v___x_1778_);
v___x_1780_ = l_Array_append___redArg(v___x_1779_, v_fst_1753_);
lean_dec(v_fst_1753_);
v___x_1781_ = l_Lean_Doc_joinInlines(v___x_1780_);
lean_dec_ref(v___x_1780_);
v___x_1782_ = lean_array_push(v___x_1777_, v___x_1781_);
v___x_1783_ = l_Array_append___redArg(v___x_1782_, v_fst_1759_);
lean_dec(v_fst_1759_);
v___x_1784_ = l_Array_append___redArg(v___x_1783_, v_fst_1770_);
lean_dec(v_fst_1770_);
v___x_1785_ = l_Lean_Doc_joinBlocks(v___x_1784_);
lean_dec_ref(v___x_1784_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1785_);
v___x_1787_ = v___x_1773_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_snd_1771_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown(lean_object* v_i_1790_, lean_object* v_b_1791_, lean_object* v_p_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_level_1795_, lean_object* v_part_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_Doc_partMarkdown___redArg(v_inst_1793_, v_inst_1794_, v_level_1795_, v_part_1796_, v_a_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___boxed(lean_object* v_i_1799_, lean_object* v_b_1800_, lean_object* v_p_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_level_1804_, lean_object* v_part_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_Doc_partMarkdown(v_i_1799_, v_b_1800_, v_p_1801_, v_inst_1802_, v_inst_1803_, v_level_1804_, v_part_1805_, v_a_1806_);
lean_dec(v_level_1804_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_1808_, lean_object* v_inst_1809_, lean_object* v_part_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = l_Lean_Doc_partMarkdown___redArg(v_inst_1808_, v_inst_1809_, v___x_1812_, v_part_1810_, v___y_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1814_, lean_object* v_inst_1815_){
_start:
{
lean_object* v___f_1816_; 
v___f_1816_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1816_, 0, v_inst_1814_);
lean_closure_set(v___f_1816_, 1, v_inst_1815_);
return v___f_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1817_, lean_object* v_b_1818_, lean_object* v_p_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_){
_start:
{
lean_object* v___f_1822_; 
v___f_1822_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1822_, 0, v_inst_1820_);
lean_closure_set(v___f_1822_, 1, v_inst_1821_);
return v___f_1822_;
}
}
lean_object* runtime_initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
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
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1 = _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1);
l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1 = _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1);
l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1 = _init_l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1);
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
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
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
res = initialize_Init_Data_String_Length(builtin);
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
