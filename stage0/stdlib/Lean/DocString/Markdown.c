// Lean compiler output
// Module: Lean.DocString.Markdown
// Imports: public import Lean.DocString.Types public import Lean.DocString.Extension public import Lean.CoreM public import Init.Data.String.TakeDrop public import Init.Data.String.Search public import Init.Data.String.Length import Init.Data.ToString.Macro import Init.While
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Doc_Inline_empty(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findInternalDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_prefixLines(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_prefixListLines(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Doc_joinBlocks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_joinBlocks___closed__0 = (const lean_object*)&l_Lean_Doc_joinBlocks___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "​"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instMarkdownInlineEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instMarkdownInlineEmpty___closed__0 = (const lean_object*)&l_Lean_Doc_instMarkdownInlineEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instMarkdownInlineEmpty = (const lean_object*)&l_Lean_Doc_instMarkdownInlineEmpty___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instMarkdownBlockEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
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
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "**"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]("};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_partMarkdown___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_partMarkdown___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Doc_instInhabitedMdRendererState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instInhabitedMdRendererState_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedMdRendererState_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedMdRendererState_default = (const lean_object*)&l_Lean_Doc_instInhabitedMdRendererState_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedMdRendererState = (const lean_object*)&l_Lean_Doc_instInhabitedMdRendererState_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "docInlineMdExt"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 166, 70, 241, 45, 192, 139, 120)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__8_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__8_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__8_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__9_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Doc_instInhabitedMdRendererState_default___closed__0_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__9_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__9_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__10_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__9_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__8_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__10_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__10_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__10_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_docInlineMdExt;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "docBlockMdExt"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(110, 223, 229, 192, 185, 199, 58, 226)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__9_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__8_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_docBlockMdExt;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mdRendererHeartbeats;
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instMarkdownInlineElabInline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instMarkdownInlineElabInline___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instMarkdownInlineElabInline___closed__0 = (const lean_object*)&l_Lean_Doc_instMarkdownInlineElabInline___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline;
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___closed__0 = (const lean_object*)&l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Doc_instToMarkdownVersoDocString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instToMarkdownVersoDocString___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString;
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Doc_instToMarkdownSnippet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instToMarkdownSnippet___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__0;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__1;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__2;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__3;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__4;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__5;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__6;
static const lean_string_object l_Lean_Doc_runMarkdown___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__7 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Doc_runMarkdown___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__8 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Doc_runMarkdown___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__9 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Doc_runMarkdown___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__10 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__11;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__12;
static const lean_array_object l_Lean_Doc_runMarkdown___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__13 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__13_value;
static const lean_string_object l_Lean_Doc_runMarkdown___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "<docstring>"};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__14 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__14_value;
static const lean_string_object l_Lean_Doc_runMarkdown___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__15 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__15_value;
static const lean_string_object l_Lean_Doc_runMarkdown___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__16 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__16_value;
static const lean_string_object l_Lean_Doc_runMarkdown___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__17 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(lean_object* v_name_1_, lean_object* v_body_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_5_ = lean_st_ref_take(v_a_3_);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v_name_1_);
lean_ctor_set(v___x_6_, 1, v_body_2_);
v___x_7_ = lean_array_push(v___x_5_, v___x_6_);
v___x_8_ = lean_st_ref_put(v_a_3_, v___x_7_);
v___x_9_ = lean_box(0);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg___boxed(lean_object* v_name_11_, lean_object* v_body_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_11_, v_body_12_, v_a_13_);
lean_dec(v_a_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote(lean_object* v_name_16_, lean_object* v_body_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_16_, v_body_17_, v_a_18_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___boxed(lean_object* v_name_23_, lean_object* v_body_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote(v_name_23_, v_body_24_, v_a_25_, v_a_26_, v_a_27_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0(lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
if (lean_obj_tag(v_a_36_) == 0)
{
lean_object* v___x_38_; 
v___x_38_ = l_List_reverse___redArg(v_a_37_);
return v___x_38_;
}
else
{
lean_object* v_head_39_; lean_object* v_tail_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_55_; 
v_head_39_ = lean_ctor_get(v_a_36_, 0);
v_tail_40_ = lean_ctor_get(v_a_36_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v_a_36_);
if (v_isSharedCheck_55_ == 0)
{
v___x_42_ = v_a_36_;
v_isShared_43_ = v_isSharedCheck_55_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_tail_40_);
lean_inc(v_head_39_);
lean_dec(v_a_36_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_55_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v_fst_44_; lean_object* v_snd_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
v_fst_44_ = lean_ctor_get(v_head_39_, 0);
lean_inc(v_fst_44_);
v_snd_45_ = lean_ctor_get(v_head_39_, 1);
lean_inc(v_snd_45_);
lean_dec(v_head_39_);
v___x_46_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_47_ = lean_string_append(v___x_46_, v_fst_44_);
lean_dec(v_fst_44_);
v___x_48_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__1));
v___x_49_ = lean_string_append(v___x_47_, v___x_48_);
v___x_50_ = lean_string_append(v___x_49_, v_snd_45_);
lean_dec(v_snd_45_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v_a_37_);
lean_ctor_set(v___x_42_, 0, v___x_50_);
v___x_52_ = v___x_42_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_a_37_);
v___x_52_ = v_reuseFailAlloc_54_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
v_a_36_ = v_tail_40_;
v_a_37_ = v___x_52_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run_x27(lean_object* v_act_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__0));
v___x_66_ = lean_st_mk_ref(v___x_65_);
lean_inc(v_a_62_);
lean_inc_ref(v_a_61_);
lean_inc(v___x_66_);
v___x_67_ = lean_apply_4(v_act_60_, v___x_66_, v_a_61_, v_a_62_, lean_box(0));
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_91_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_91_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_91_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_91_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_72_ = lean_st_ref_get(v___x_66_);
lean_dec(v___x_66_);
v___x_73_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_74_ = lean_array_to_list(v_a_68_);
v___x_75_ = l_String_intercalate(v___x_73_, v___x_74_);
v___x_76_ = lean_array_get_size(v___x_72_);
v___x_77_ = lean_nat_dec_eq(v___x_76_, v___x_64_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_78_ = lean_array_to_list(v___x_72_);
v___x_79_ = lean_box(0);
v___x_80_ = l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0(v___x_78_, v___x_79_);
v___x_81_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__2));
v___x_82_ = lean_string_append(v___x_75_, v___x_81_);
v___x_83_ = l_String_intercalate(v___x_81_, v___x_80_);
v___x_84_ = lean_string_append(v___x_82_, v___x_83_);
lean_dec_ref(v___x_83_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_84_);
v___x_86_ = v___x_70_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
else
{
lean_object* v___x_89_; 
lean_dec(v___x_72_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_75_);
v___x_89_ = v___x_70_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_75_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec(v___x_66_);
v_a_92_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_67_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_67_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run_x27___boxed(lean_object* v_act_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Doc_MarkdownM_run_x27(v_act_100_, v_a_101_, v_a_102_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(lean_object* v_s_105_, lean_object* v_pos_106_){
_start:
{
lean_object* v_str_107_; lean_object* v_startInclusive_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v_decide_112_; 
v_str_107_ = lean_ctor_get(v_s_105_, 0);
v_startInclusive_108_ = lean_ctor_get(v_s_105_, 1);
v___x_109_ = lean_nat_add(v_startInclusive_108_, v_pos_106_);
v___x_110_ = lean_nat_sub(v___x_109_, v_startInclusive_108_);
v___x_111_ = lean_unsigned_to_nat(0u);
v_decide_112_ = lean_nat_dec_eq(v___x_110_, v___x_111_);
if (v_decide_112_ == 0)
{
uint32_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint32_t v___x_119_; uint8_t v___x_120_; 
v___x_113_ = 32;
lean_inc(v_startInclusive_108_);
lean_inc_ref(v_str_107_);
v___x_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_114_, 0, v_str_107_);
lean_ctor_set(v___x_114_, 1, v_startInclusive_108_);
lean_ctor_set(v___x_114_, 2, v___x_109_);
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_sub(v___x_110_, v___x_115_);
lean_dec(v___x_110_);
v___x_117_ = l_String_Slice_posLE(v___x_114_, v___x_116_);
lean_dec_ref_known(v___x_114_, 3);
v___x_118_ = lean_nat_add(v_startInclusive_108_, v___x_117_);
v___x_119_ = lean_string_utf8_get_fast(v_str_107_, v___x_118_);
lean_dec(v___x_118_);
v___x_120_ = lean_uint32_dec_eq(v___x_119_, v___x_113_);
if (v___x_120_ == 0)
{
lean_dec(v___x_117_);
return v_pos_106_;
}
else
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_nat_add(v___x_117_, v___x_115_);
v___x_122_ = lean_nat_dec_le(v___x_121_, v_pos_106_);
lean_dec(v___x_121_);
if (v___x_122_ == 0)
{
lean_dec(v___x_117_);
return v_pos_106_;
}
else
{
lean_dec(v_pos_106_);
v_pos_106_ = v___x_117_;
goto _start;
}
}
}
else
{
lean_dec(v___x_110_);
lean_dec(v___x_109_);
return v_pos_106_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0___boxed(lean_object* v_s_124_, lean_object* v_pos_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(v_s_124_, v_pos_125_);
lean_dec_ref(v_s_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(lean_object* v_s_127_){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_string_utf8_byte_size(v_s_127_);
lean_inc_ref(v_s_127_);
v___x_130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_130_, 0, v_s_127_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
lean_ctor_set(v___x_130_, 2, v___x_129_);
v___x_131_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(v___x_130_, v___x_129_);
lean_dec_ref_known(v___x_130_, 3);
v___x_132_ = lean_string_utf8_extract_fast(v_s_127_, v___x_128_, v___x_131_);
lean_dec(v___x_131_);
lean_dec_ref(v_s_127_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(lean_object* v_p_133_, lean_object* v_pTrim_134_, size_t v_sz_135_, size_t v_i_136_, lean_object* v_bs_137_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = lean_usize_dec_lt(v_i_136_, v_sz_135_);
if (v___x_138_ == 0)
{
lean_dec_ref(v_pTrim_134_);
lean_dec_ref(v_p_133_);
return v_bs_137_;
}
else
{
lean_object* v_v_139_; lean_object* v___x_140_; lean_object* v_bs_x27_141_; lean_object* v___y_143_; lean_object* v___x_148_; uint8_t v___x_149_; 
v_v_139_ = lean_array_uget(v_bs_137_, v_i_136_);
v___x_140_ = lean_unsigned_to_nat(0u);
v_bs_x27_141_ = lean_array_uset(v_bs_137_, v_i_136_, v___x_140_);
v___x_148_ = lean_string_utf8_byte_size(v_v_139_);
v___x_149_ = lean_nat_dec_eq(v___x_148_, v___x_140_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
lean_inc_ref(v_p_133_);
v___x_150_ = lean_string_append(v_p_133_, v_v_139_);
lean_dec(v_v_139_);
v___y_143_ = v___x_150_;
goto v___jp_142_;
}
else
{
lean_dec(v_v_139_);
lean_inc_ref(v_pTrim_134_);
v___y_143_ = v_pTrim_134_;
goto v___jp_142_;
}
v___jp_142_:
{
size_t v___x_144_; size_t v___x_145_; lean_object* v___x_146_; 
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_add(v_i_136_, v___x_144_);
v___x_146_ = lean_array_uset(v_bs_x27_141_, v_i_136_, v___y_143_);
v_i_136_ = v___x_145_;
v_bs_137_ = v___x_146_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0___boxed(lean_object* v_p_151_, lean_object* v_pTrim_152_, lean_object* v_sz_153_, lean_object* v_i_154_, lean_object* v_bs_155_){
_start:
{
size_t v_sz_boxed_156_; size_t v_i_boxed_157_; lean_object* v_res_158_; 
v_sz_boxed_156_ = lean_unbox_usize(v_sz_153_);
lean_dec(v_sz_153_);
v_i_boxed_157_ = lean_unbox_usize(v_i_154_);
lean_dec(v_i_154_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(v_p_151_, v_pTrim_152_, v_sz_boxed_156_, v_i_boxed_157_, v_bs_155_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_prefixLines(lean_object* v_p_159_, lean_object* v_lines_160_){
_start:
{
lean_object* v_pTrim_161_; size_t v_sz_162_; size_t v___x_163_; lean_object* v___x_164_; 
lean_inc_ref(v_p_159_);
v_pTrim_161_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_p_159_);
v_sz_162_ = lean_array_size(v_lines_160_);
v___x_163_ = ((size_t)0ULL);
v___x_164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(v_p_159_, v_pTrim_161_, v_sz_162_, v___x_163_, v_lines_160_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(lean_object* v_rest_165_, lean_object* v_restTrim_166_, lean_object* v_head_167_, lean_object* v_headTrim_168_, size_t v_sz_169_, size_t v_i_170_, lean_object* v_bs_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = lean_usize_dec_lt(v_i_170_, v_sz_169_);
if (v___x_172_ == 0)
{
lean_dec_ref(v_headTrim_168_);
lean_dec_ref(v_head_167_);
lean_dec_ref(v_restTrim_166_);
lean_dec_ref(v_rest_165_);
return v_bs_171_;
}
else
{
lean_object* v_v_173_; lean_object* v___x_174_; lean_object* v_bs_x27_175_; lean_object* v___y_177_; lean_object* v_fst_183_; lean_object* v_snd_184_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_v_173_ = lean_array_uget(v_bs_171_, v_i_170_);
v___x_174_ = lean_unsigned_to_nat(0u);
v_bs_x27_175_ = lean_array_uset(v_bs_171_, v_i_170_, v___x_174_);
v___x_188_ = lean_usize_to_nat(v_i_170_);
v___x_189_ = lean_nat_dec_eq(v___x_188_, v___x_174_);
lean_dec(v___x_188_);
if (v___x_189_ == 0)
{
lean_inc_ref(v_restTrim_166_);
lean_inc_ref(v_rest_165_);
v_fst_183_ = v_rest_165_;
v_snd_184_ = v_restTrim_166_;
goto v___jp_182_;
}
else
{
lean_inc_ref(v_headTrim_168_);
lean_inc_ref(v_head_167_);
v_fst_183_ = v_head_167_;
v_snd_184_ = v_headTrim_168_;
goto v___jp_182_;
}
v___jp_176_:
{
size_t v___x_178_; size_t v___x_179_; lean_object* v___x_180_; 
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_i_170_, v___x_178_);
v___x_180_ = lean_array_uset(v_bs_x27_175_, v_i_170_, v___y_177_);
v_i_170_ = v___x_179_;
v_bs_171_ = v___x_180_;
goto _start;
}
v___jp_182_:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = lean_string_utf8_byte_size(v_v_173_);
v___x_186_ = lean_nat_dec_eq(v___x_185_, v___x_174_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_dec_ref(v_snd_184_);
v___x_187_ = lean_string_append(v_fst_183_, v_v_173_);
lean_dec(v_v_173_);
v___y_177_ = v___x_187_;
goto v___jp_176_;
}
else
{
lean_dec_ref(v_fst_183_);
lean_dec(v_v_173_);
v___y_177_ = v_snd_184_;
goto v___jp_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg___boxed(lean_object* v_rest_190_, lean_object* v_restTrim_191_, lean_object* v_head_192_, lean_object* v_headTrim_193_, lean_object* v_sz_194_, lean_object* v_i_195_, lean_object* v_bs_196_){
_start:
{
size_t v_sz_boxed_197_; size_t v_i_boxed_198_; lean_object* v_res_199_; 
v_sz_boxed_197_ = lean_unbox_usize(v_sz_194_);
lean_dec(v_sz_194_);
v_i_boxed_198_ = lean_unbox_usize(v_i_195_);
lean_dec(v_i_195_);
v_res_199_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_190_, v_restTrim_191_, v_head_192_, v_headTrim_193_, v_sz_boxed_197_, v_i_boxed_198_, v_bs_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_prefixListLines(lean_object* v_head_200_, lean_object* v_rest_201_, lean_object* v_lines_202_){
_start:
{
lean_object* v_headTrim_203_; lean_object* v_restTrim_204_; size_t v_sz_205_; size_t v___x_206_; lean_object* v___x_207_; 
lean_inc_ref(v_head_200_);
v_headTrim_203_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_head_200_);
lean_inc_ref(v_rest_201_);
v_restTrim_204_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_rest_201_);
v_sz_205_ = lean_array_size(v_lines_202_);
v___x_206_ = ((size_t)0ULL);
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_201_, v_restTrim_204_, v_head_200_, v_headTrim_203_, v_sz_205_, v___x_206_, v_lines_202_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0(lean_object* v_rest_208_, lean_object* v_restTrim_209_, lean_object* v_head_210_, lean_object* v_headTrim_211_, lean_object* v_as_212_, size_t v_sz_213_, size_t v_i_214_, lean_object* v_bs_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_208_, v_restTrim_209_, v_head_210_, v_headTrim_211_, v_sz_213_, v_i_214_, v_bs_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___boxed(lean_object* v_rest_217_, lean_object* v_restTrim_218_, lean_object* v_head_219_, lean_object* v_headTrim_220_, lean_object* v_as_221_, lean_object* v_sz_222_, lean_object* v_i_223_, lean_object* v_bs_224_){
_start:
{
size_t v_sz_boxed_225_; size_t v_i_boxed_226_; lean_object* v_res_227_; 
v_sz_boxed_225_ = lean_unbox_usize(v_sz_222_);
lean_dec(v_sz_222_);
v_i_boxed_226_ = lean_unbox_usize(v_i_223_);
lean_dec(v_i_223_);
v_res_227_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0(v_rest_217_, v_restTrim_218_, v_head_219_, v_headTrim_220_, v_as_221_, v_sz_boxed_225_, v_i_boxed_226_, v_bs_224_);
lean_dec_ref(v_as_221_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(lean_object* v_as_229_, size_t v_i_230_, size_t v_stop_231_, lean_object* v_b_232_){
_start:
{
lean_object* v___y_234_; uint8_t v___x_238_; 
v___x_238_ = lean_usize_dec_eq(v_i_230_, v_stop_231_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_239_ = lean_array_uget_borrowed(v_as_229_, v_i_230_);
v___x_240_ = lean_array_get_size(v___x_239_);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_nat_dec_eq(v___x_240_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_array_get_size(v_b_232_);
v___x_244_ = lean_nat_dec_eq(v___x_243_, v___x_241_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_246_ = lean_array_push(v_b_232_, v___x_245_);
v___x_247_ = l_Array_append___redArg(v___x_246_, v___x_239_);
v___y_234_ = v___x_247_;
goto v___jp_233_;
}
else
{
lean_dec_ref(v_b_232_);
lean_inc(v___x_239_);
v___y_234_ = v___x_239_;
goto v___jp_233_;
}
}
else
{
v___y_234_ = v_b_232_;
goto v___jp_233_;
}
}
else
{
return v_b_232_;
}
v___jp_233_:
{
size_t v___x_235_; size_t v___x_236_; 
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_add(v_i_230_, v___x_235_);
v_i_230_ = v___x_236_;
v_b_232_ = v___y_234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___boxed(lean_object* v_as_248_, lean_object* v_i_249_, lean_object* v_stop_250_, lean_object* v_b_251_){
_start:
{
size_t v_i_boxed_252_; size_t v_stop_boxed_253_; lean_object* v_res_254_; 
v_i_boxed_252_ = lean_unbox_usize(v_i_249_);
lean_dec(v_i_249_);
v_stop_boxed_253_ = lean_unbox_usize(v_stop_250_);
lean_dec(v_stop_250_);
v_res_254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_as_248_, v_i_boxed_252_, v_stop_boxed_253_, v_b_251_);
lean_dec_ref(v_as_248_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks(lean_object* v_blocks_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_260_ = lean_array_get_size(v_blocks_257_);
v___x_261_ = lean_nat_dec_lt(v___x_258_, v___x_260_);
if (v___x_261_ == 0)
{
return v___x_259_;
}
else
{
uint8_t v___x_262_; 
v___x_262_ = lean_nat_dec_le(v___x_260_, v___x_260_);
if (v___x_262_ == 0)
{
if (v___x_261_ == 0)
{
return v___x_259_;
}
else
{
size_t v___x_263_; size_t v___x_264_; lean_object* v___x_265_; 
v___x_263_ = ((size_t)0ULL);
v___x_264_ = lean_usize_of_nat(v___x_260_);
v___x_265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_257_, v___x_263_, v___x_264_, v___x_259_);
return v___x_265_;
}
}
else
{
size_t v___x_266_; size_t v___x_267_; lean_object* v___x_268_; 
v___x_266_ = ((size_t)0ULL);
v___x_267_ = lean_usize_of_nat(v___x_260_);
v___x_268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_257_, v___x_266_, v___x_267_, v___x_259_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks___boxed(lean_object* v_blocks_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Doc_joinBlocks(v_blocks_269_);
lean_dec_ref(v_blocks_269_);
return v_res_270_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1));
v___x_274_ = lean_string_utf8_byte_size(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(lean_object* v_l_275_, lean_object* v_r_276_){
_start:
{
uint8_t v___y_278_; uint8_t v___y_279_; lean_object* v___x_285_; uint8_t v___y_287_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_285_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1));
v___x_293_ = lean_string_utf8_byte_size(v_l_275_);
v___x_294_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2);
v___x_295_ = lean_nat_dec_le(v___x_294_, v___x_293_);
if (v___x_295_ == 0)
{
v___y_287_ = v___x_295_;
goto v___jp_286_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_nat_sub(v___x_293_, v___x_294_);
v___x_298_ = lean_string_memcmp(v_l_275_, v___x_285_, v___x_297_, v___x_296_, v___x_294_);
lean_dec(v___x_297_);
v___y_287_ = v___x_298_;
goto v___jp_286_;
}
v___jp_277_:
{
if (v___y_278_ == 0)
{
lean_object* v___x_280_; 
v___x_280_ = lean_string_append(v_l_275_, v_r_276_);
return v___x_280_;
}
else
{
if (v___y_279_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_string_append(v_l_275_, v_r_276_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_283_ = lean_string_append(v_l_275_, v___x_282_);
v___x_284_ = lean_string_append(v___x_283_, v_r_276_);
return v___x_284_;
}
}
}
v___jp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_string_utf8_byte_size(v_r_276_);
v___x_289_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2);
v___x_290_ = lean_nat_dec_le(v___x_289_, v___x_288_);
if (v___x_290_ == 0)
{
v___y_278_ = v___y_287_;
v___y_279_ = v___x_290_;
goto v___jp_277_;
}
else
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_string_memcmp(v_r_276_, v___x_285_, v___x_291_, v___x_291_, v___x_289_);
v___y_278_ = v___y_287_;
v___y_279_ = v___x_292_;
goto v___jp_277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___boxed(lean_object* v_l_299_, lean_object* v_r_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v_l_299_, v_r_300_);
lean_dec_ref(v_r_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(lean_object* v_as_302_, size_t v_i_303_, size_t v_stop_304_, lean_object* v_b_305_){
_start:
{
lean_object* v___y_307_; uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_eq(v_i_303_, v_stop_304_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_312_ = lean_array_uget_borrowed(v_as_302_, v_i_303_);
v___x_313_ = lean_array_get_size(v___x_312_);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_nat_dec_eq(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = lean_array_get_size(v_b_305_);
v___x_317_ = lean_nat_dec_eq(v___x_316_, v___x_314_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v_lastIdx_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_glued_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v_lastIdx_319_ = lean_nat_sub(v___x_316_, v___x_318_);
v___x_320_ = lean_array_fget_borrowed(v_b_305_, v_lastIdx_319_);
v___x_321_ = lean_array_fget_borrowed(v___x_312_, v___x_314_);
lean_inc(v___x_320_);
v_glued_322_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v___x_320_, v___x_321_);
v___x_323_ = lean_array_fset(v_b_305_, v_lastIdx_319_, v_glued_322_);
lean_dec(v_lastIdx_319_);
v___x_324_ = l_Array_extract___redArg(v___x_312_, v___x_318_, v___x_313_);
v___x_325_ = l_Array_append___redArg(v___x_323_, v___x_324_);
lean_dec_ref(v___x_324_);
v___y_307_ = v___x_325_;
goto v___jp_306_;
}
else
{
lean_dec_ref(v_b_305_);
lean_inc(v___x_312_);
v___y_307_ = v___x_312_;
goto v___jp_306_;
}
}
else
{
v___y_307_ = v_b_305_;
goto v___jp_306_;
}
}
else
{
return v_b_305_;
}
v___jp_306_:
{
size_t v___x_308_; size_t v___x_309_; 
v___x_308_ = ((size_t)1ULL);
v___x_309_ = lean_usize_add(v_i_303_, v___x_308_);
v_i_303_ = v___x_309_;
v_b_305_ = v___y_307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0___boxed(lean_object* v_as_326_, lean_object* v_i_327_, lean_object* v_stop_328_, lean_object* v_b_329_){
_start:
{
size_t v_i_boxed_330_; size_t v_stop_boxed_331_; lean_object* v_res_332_; 
v_i_boxed_330_ = lean_unbox_usize(v_i_327_);
lean_dec(v_i_327_);
v_stop_boxed_331_ = lean_unbox_usize(v_stop_328_);
lean_dec(v_stop_328_);
v_res_332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_as_326_, v_i_boxed_330_, v_stop_boxed_331_, v_b_329_);
lean_dec_ref(v_as_326_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines(lean_object* v_parts_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_336_ = lean_array_get_size(v_parts_333_);
v___x_337_ = lean_nat_dec_lt(v___x_334_, v___x_336_);
if (v___x_337_ == 0)
{
return v___x_335_;
}
else
{
uint8_t v___x_338_; 
v___x_338_ = lean_nat_dec_le(v___x_336_, v___x_336_);
if (v___x_338_ == 0)
{
if (v___x_337_ == 0)
{
return v___x_335_;
}
else
{
size_t v___x_339_; size_t v___x_340_; lean_object* v___x_341_; 
v___x_339_ = ((size_t)0ULL);
v___x_340_ = lean_usize_of_nat(v___x_336_);
v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_333_, v___x_339_, v___x_340_, v___x_335_);
return v___x_341_;
}
}
else
{
size_t v___x_342_; size_t v___x_343_; lean_object* v___x_344_; 
v___x_342_ = ((size_t)0ULL);
v___x_343_ = lean_usize_of_nat(v___x_336_);
v___x_344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_333_, v___x_342_, v___x_343_, v___x_335_);
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines___boxed(lean_object* v_parts_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Doc_joinInlines(v_parts_345_);
lean_dec_ref(v_parts_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object* v_a_347_, uint8_t v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
uint8_t v_a_19__boxed_361_; lean_object* v_res_362_; 
v_a_19__boxed_361_ = lean_unbox(v_a_355_);
v_res_362_ = l_Lean_Doc_instMarkdownInlineEmpty___lam__0(v_a_354_, v_a_19__boxed_361_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec_ref(v_a_354_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0(lean_object* v_a_365_, lean_object* v_a_366_, uint8_t v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed(lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
uint8_t v_a_23__boxed_381_; lean_object* v_res_382_; 
v_a_23__boxed_381_ = lean_unbox(v_a_375_);
v_res_382_ = l_Lean_Doc_instMarkdownBlockEmpty___lam__0(v_a_373_, v_a_374_, v_a_23__boxed_381_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec_ref(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object* v_i_384_){
_start:
{
lean_object* v___f_385_; 
v___f_385_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___closed__0));
return v___f_385_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
if (lean_obj_tag(v_x_387_) == 0)
{
uint8_t v___x_388_; 
v___x_388_ = 1;
return v___x_388_;
}
else
{
uint8_t v___x_389_; 
v___x_389_ = 0;
return v___x_389_;
}
}
else
{
if (lean_obj_tag(v_x_387_) == 0)
{
uint8_t v___x_390_; 
v___x_390_ = 0;
return v___x_390_;
}
else
{
lean_object* v_val_391_; lean_object* v_val_392_; uint32_t v___x_393_; uint32_t v___x_394_; uint8_t v___x_395_; 
v_val_391_ = lean_ctor_get(v_x_386_, 0);
v_val_392_ = lean_ctor_get(v_x_387_, 0);
v___x_393_ = lean_unbox_uint32(v_val_391_);
v___x_394_ = lean_unbox_uint32(v_val_392_);
v___x_395_ = lean_uint32_dec_eq(v___x_393_, v___x_394_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1___boxed(lean_object* v_x_396_, lean_object* v_x_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_x_396_, v_x_397_);
lean_dec(v_x_397_);
lean_dec(v_x_396_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(lean_object* v_s_400_, uint32_t v_c_401_, lean_object* v_a_402_, uint8_t v_b_403_){
_start:
{
lean_object* v_str_404_; lean_object* v_startInclusive_405_; lean_object* v_endExclusive_406_; lean_object* v___x_407_; uint8_t v_decide_408_; 
v_str_404_ = lean_ctor_get(v_s_400_, 0);
v_startInclusive_405_ = lean_ctor_get(v_s_400_, 1);
v_endExclusive_406_ = lean_ctor_get(v_s_400_, 2);
v___x_407_ = lean_nat_sub(v_endExclusive_406_, v_startInclusive_405_);
v_decide_408_ = lean_nat_dec_eq(v_a_402_, v___x_407_);
lean_dec(v___x_407_);
if (v_decide_408_ == 0)
{
lean_object* v___x_409_; uint32_t v___x_410_; uint8_t v___x_411_; 
v___x_409_ = lean_nat_add(v_startInclusive_405_, v_a_402_);
lean_dec(v_a_402_);
v___x_410_ = lean_string_utf8_get_fast(v_str_404_, v___x_409_);
v___x_411_ = lean_uint32_dec_eq(v___x_410_, v_c_401_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_string_utf8_next_fast(v_str_404_, v___x_409_);
lean_dec(v___x_409_);
v___x_413_ = lean_nat_sub(v___x_412_, v_startInclusive_405_);
v_a_402_ = v___x_413_;
v_b_403_ = v___x_411_;
goto _start;
}
else
{
lean_dec(v___x_409_);
return v___x_411_;
}
}
else
{
lean_dec(v_a_402_);
return v_b_403_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg___boxed(lean_object* v_s_415_, lean_object* v_c_416_, lean_object* v_a_417_, lean_object* v_b_418_){
_start:
{
uint32_t v_c_boxed_419_; uint8_t v_b_boxed_420_; uint8_t v_res_421_; lean_object* v_r_422_; 
v_c_boxed_419_ = lean_unbox_uint32(v_c_416_);
lean_dec(v_c_416_);
v_b_boxed_420_ = lean_unbox(v_b_418_);
v_res_421_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_415_, v_c_boxed_419_, v_a_417_, v_b_boxed_420_);
lean_dec_ref(v_s_415_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(uint32_t v_c_423_, lean_object* v_s_424_){
_start:
{
lean_object* v_searcher_425_; uint8_t v___x_426_; uint8_t v___x_427_; 
v_searcher_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = 0;
v___x_427_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_424_, v_c_423_, v_searcher_425_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0___boxed(lean_object* v_c_428_, lean_object* v_s_429_){
_start:
{
uint32_t v_c_boxed_430_; uint8_t v_res_431_; lean_object* v_r_432_; 
v_c_boxed_430_ = lean_unbox_uint32(v_c_428_);
lean_dec(v_c_428_);
v_res_431_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_boxed_430_, v_s_429_);
lean_dec_ref(v_s_429_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0));
v___x_435_ = lean_string_utf8_byte_size(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0));
v___x_439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v___x_437_);
lean_ctor_set(v___x_439_, 2, v___x_436_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_440_; lean_object* v___x_441_; 
v___x_440_ = 91;
v___x_441_ = lean_box_uint32(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1;
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(uint32_t v_c_444_, lean_object* v_next_x3f_445_){
_start:
{
uint32_t v___x_446_; uint8_t v___x_447_; 
v___x_446_ = 33;
v___x_447_ = lean_uint32_dec_eq(v_c_444_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2);
v___x_449_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_444_, v___x_448_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3);
v___x_451_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_445_, v___x_450_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___boxed(lean_object* v_c_452_, lean_object* v_next_x3f_453_){
_start:
{
uint32_t v_c_boxed_454_; uint8_t v_res_455_; lean_object* v_r_456_; 
v_c_boxed_454_ = lean_unbox_uint32(v_c_452_);
lean_dec(v_c_452_);
v_res_455_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_boxed_454_, v_next_x3f_453_);
lean_dec(v_next_x3f_453_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(lean_object* v_s_457_, uint32_t v_c_458_, lean_object* v_inst_459_, lean_object* v_R_460_, lean_object* v_a_461_, uint8_t v_b_462_, lean_object* v_c_463_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_457_, v_c_458_, v_a_461_, v_b_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___boxed(lean_object* v_s_465_, lean_object* v_c_466_, lean_object* v_inst_467_, lean_object* v_R_468_, lean_object* v_a_469_, lean_object* v_b_470_, lean_object* v_c_471_){
_start:
{
uint32_t v_c_boxed_472_; uint8_t v_b_boxed_473_; uint8_t v_res_474_; lean_object* v_r_475_; 
v_c_boxed_472_ = lean_unbox_uint32(v_c_466_);
lean_dec(v_c_466_);
v_b_boxed_473_ = lean_unbox(v_b_470_);
v_res_474_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(v_s_465_, v_c_boxed_472_, v_inst_467_, v_R_468_, v_a_469_, v_b_boxed_473_, v_c_471_);
lean_dec_ref(v_s_465_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_476_; lean_object* v___x_477_; 
v___x_476_ = 32;
v___x_477_ = lean_box_uint32(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(lean_object* v_prev_x3f_480_, uint32_t v_c_481_, lean_object* v_next_x3f_482_){
_start:
{
uint8_t v___y_484_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0);
v___x_502_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_482_, v___x_501_);
if (v___x_502_ == 0)
{
if (lean_obj_tag(v_next_x3f_482_) == 0)
{
uint8_t v___x_503_; 
v___x_503_ = 1;
v___y_484_ = v___x_503_;
goto v___jp_483_;
}
else
{
v___y_484_ = v___x_502_;
goto v___jp_483_;
}
}
else
{
v___y_484_ = v___x_502_;
goto v___jp_483_;
}
v___jp_483_:
{
uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 62;
v___x_486_ = lean_uint32_dec_eq(v_c_481_, v___x_485_);
if (v___x_486_ == 0)
{
uint32_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = 45;
v___x_488_ = lean_uint32_dec_eq(v_c_481_, v___x_487_);
if (v___x_488_ == 0)
{
uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 43;
v___x_490_ = lean_uint32_dec_eq(v_c_481_, v___x_489_);
if (v___x_490_ == 0)
{
uint32_t v___x_491_; uint8_t v___x_492_; 
v___x_491_ = 46;
v___x_492_ = lean_uint32_dec_eq(v_c_481_, v___x_491_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
v___x_493_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_481_, v_next_x3f_482_);
return v___x_493_;
}
else
{
if (lean_obj_tag(v_prev_x3f_480_) == 0)
{
return v___x_490_;
}
else
{
lean_object* v_val_494_; uint32_t v___x_495_; uint32_t v___x_496_; uint8_t v___x_497_; 
v_val_494_ = lean_ctor_get(v_prev_x3f_480_, 0);
v___x_495_ = 48;
v___x_496_ = lean_unbox_uint32(v_val_494_);
v___x_497_ = lean_uint32_dec_le(v___x_495_, v___x_496_);
if (v___x_497_ == 0)
{
return v___x_497_;
}
else
{
uint32_t v___x_498_; uint32_t v___x_499_; uint8_t v___x_500_; 
v___x_498_ = 57;
v___x_499_ = lean_unbox_uint32(v_val_494_);
v___x_500_ = lean_uint32_dec_le(v___x_499_, v___x_498_);
if (v___x_500_ == 0)
{
return v___x_500_;
}
else
{
return v___y_484_;
}
}
}
}
}
else
{
return v___y_484_;
}
}
else
{
return v___y_484_;
}
}
else
{
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___boxed(lean_object* v_prev_x3f_504_, lean_object* v_c_505_, lean_object* v_next_x3f_506_){
_start:
{
uint32_t v_c_boxed_507_; uint8_t v_res_508_; lean_object* v_r_509_; 
v_c_boxed_507_ = lean_unbox_uint32(v_c_505_);
lean_dec(v_c_505_);
v_res_508_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_prev_x3f_504_, v_c_boxed_507_, v_next_x3f_506_);
lean_dec(v_next_x3f_506_);
lean_dec(v_prev_x3f_504_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0));
v___x_512_ = lean_string_utf8_byte_size(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0));
v___x_516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v___x_514_);
lean_ctor_set(v___x_516_, 2, v___x_513_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(uint32_t v___x_517_, lean_object* v___x_518_, lean_object* v_____r_519_, lean_object* v_s_x27_520_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint32_t v___x_534_; uint8_t v___x_535_; 
v___x_521_ = lean_string_push(v_s_x27_520_, v___x_517_);
v___x_522_ = lean_box_uint32(v___x_517_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
v___x_534_ = 48;
v___x_535_ = lean_uint32_dec_le(v___x_534_, v___x_517_);
if (v___x_535_ == 0)
{
goto v___jp_528_;
}
else
{
uint32_t v___x_536_; uint8_t v___x_537_; 
v___x_536_ = 57;
v___x_537_ = lean_uint32_dec_le(v___x_517_, v___x_536_);
if (v___x_537_ == 0)
{
goto v___jp_528_;
}
else
{
goto v___jp_524_;
}
}
v___jp_524_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_518_);
lean_ctor_set(v___x_525_, 1, v___x_523_);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_521_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
v___jp_528_:
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2);
v___x_530_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v___x_517_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_518_);
lean_ctor_set(v___x_531_, 1, v___x_523_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_521_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
else
{
goto v___jp_524_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed(lean_object* v___x_538_, lean_object* v___x_539_, lean_object* v_____r_540_, lean_object* v_s_x27_541_){
_start:
{
uint32_t v___x_2058__boxed_542_; lean_object* v_res_543_; 
v___x_2058__boxed_542_ = lean_unbox_uint32(v___x_538_);
lean_dec(v___x_538_);
v_res_543_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_2058__boxed_542_, v___x_539_, v_____r_540_, v_s_x27_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(lean_object* v_s_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___y_547_; lean_object* v_snd_551_; lean_object* v_fst_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_590_; 
v_snd_551_ = lean_ctor_get(v_a_545_, 1);
v_fst_552_ = lean_ctor_get(v_a_545_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_590_ == 0)
{
v___x_554_ = v_a_545_;
v_isShared_555_ = v_isSharedCheck_590_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_snd_551_);
lean_inc(v_fst_552_);
lean_dec(v_a_545_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_590_;
goto v_resetjp_553_;
}
v___jp_546_:
{
if (lean_obj_tag(v___y_547_) == 0)
{
lean_object* v_a_548_; 
v_a_548_ = lean_ctor_get(v___y_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___y_547_, 1);
return v_a_548_;
}
else
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v___y_547_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___y_547_, 1);
v_a_545_ = v_a_549_;
goto _start;
}
}
v_resetjp_553_:
{
lean_object* v_fst_556_; lean_object* v_snd_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_589_; 
v_fst_556_ = lean_ctor_get(v_snd_551_, 0);
v_snd_557_ = lean_ctor_get(v_snd_551_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_snd_551_);
if (v_isSharedCheck_589_ == 0)
{
v___x_559_ = v_snd_551_;
v_isShared_560_ = v_isSharedCheck_589_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_snd_557_);
lean_inc(v_fst_556_);
lean_dec(v_snd_551_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_589_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; uint8_t v_decide_562_; 
v___x_561_ = lean_string_utf8_byte_size(v_s_544_);
v_decide_562_ = lean_nat_dec_eq(v_fst_556_, v___x_561_);
if (v_decide_562_ == 0)
{
uint32_t v___x_563_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___f_576_; uint8_t v_decide_581_; 
lean_del_object(v___x_559_);
lean_del_object(v___x_554_);
v___x_563_ = lean_string_utf8_get_fast(v_s_544_, v_fst_556_);
v___x_574_ = lean_string_utf8_next_fast(v_s_544_, v_fst_556_);
lean_dec(v_fst_556_);
v___x_575_ = lean_box_uint32(v___x_563_);
v___f_576_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_576_, 0, v___x_575_);
lean_closure_set(v___f_576_, 1, v___x_574_);
v_decide_581_ = lean_nat_dec_eq(v___x_574_, v___x_561_);
if (v_decide_581_ == 0)
{
goto v___jp_577_;
}
else
{
if (v_decide_562_ == 0)
{
lean_object* v_prev_x3f_582_; 
v_prev_x3f_582_ = lean_box(0);
v___y_565_ = v___f_576_;
v___y_566_ = v_prev_x3f_582_;
goto v___jp_564_;
}
else
{
goto v___jp_577_;
}
}
v___jp_564_:
{
uint8_t v___x_567_; 
v___x_567_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_snd_557_, v___x_563_, v___y_566_);
lean_dec(v___y_566_);
lean_dec(v_snd_557_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_box(0);
v___x_569_ = lean_apply_2(v___y_565_, v___x_568_, v_fst_552_);
v___y_547_ = v___x_569_;
goto v___jp_546_;
}
else
{
uint32_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = 92;
v___x_571_ = lean_string_push(v_fst_552_, v___x_570_);
v___x_572_ = lean_box(0);
v___x_573_ = lean_apply_2(v___y_565_, v___x_572_, v___x_571_);
v___y_547_ = v___x_573_;
goto v___jp_546_;
}
}
v___jp_577_:
{
uint32_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_string_utf8_get_fast(v_s_544_, v___x_574_);
v___x_579_ = lean_box_uint32(v___x_578_);
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
v___y_565_ = v___f_576_;
v___y_566_ = v___x_580_;
goto v___jp_564_;
}
}
else
{
lean_object* v___x_584_; 
if (v_isShared_560_ == 0)
{
v___x_584_ = v___x_559_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_fst_556_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_snd_557_);
v___x_584_ = v_reuseFailAlloc_588_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___x_584_);
v___x_586_ = v___x_554_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_fst_552_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___boxed(lean_object* v_s_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_591_, v_a_592_);
lean_dec_ref(v_s_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(uint32_t v___x_594_, lean_object* v___x_595_, lean_object* v_____r_596_, lean_object* v_s_x27_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_string_push(v_s_x27_597_, v___x_594_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v___x_595_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0___boxed(lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v_____r_603_, lean_object* v_s_x27_604_){
_start:
{
uint32_t v___x_2188__boxed_605_; lean_object* v_res_606_; 
v___x_2188__boxed_605_ = lean_unbox_uint32(v___x_601_);
lean_dec(v___x_601_);
v_res_606_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_2188__boxed_605_, v___x_602_, v_____r_603_, v_s_x27_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(lean_object* v_s_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___y_610_; lean_object* v_fst_614_; lean_object* v_snd_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_640_; 
v_fst_614_ = lean_ctor_get(v_a_608_, 0);
v_snd_615_ = lean_ctor_get(v_a_608_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_a_608_);
if (v_isSharedCheck_640_ == 0)
{
v___x_617_ = v_a_608_;
v_isShared_618_ = v_isSharedCheck_640_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_snd_615_);
lean_inc(v_fst_614_);
lean_dec(v_a_608_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_640_;
goto v_resetjp_616_;
}
v___jp_609_:
{
if (lean_obj_tag(v___y_610_) == 0)
{
lean_object* v_a_611_; 
v_a_611_ = lean_ctor_get(v___y_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___y_610_, 1);
return v_a_611_;
}
else
{
lean_object* v_a_612_; 
v_a_612_ = lean_ctor_get(v___y_610_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v___y_610_, 1);
v_a_608_ = v_a_612_;
goto _start;
}
}
v_resetjp_616_:
{
lean_object* v___x_619_; uint8_t v_decide_620_; 
v___x_619_ = lean_string_utf8_byte_size(v_s_607_);
v_decide_620_ = lean_nat_dec_eq(v_snd_615_, v___x_619_);
if (v_decide_620_ == 0)
{
uint32_t v___x_621_; lean_object* v___x_622_; lean_object* v___y_624_; uint8_t v_decide_632_; 
lean_del_object(v___x_617_);
v___x_621_ = lean_string_utf8_get_fast(v_s_607_, v_snd_615_);
v___x_622_ = lean_string_utf8_next_fast(v_s_607_, v_snd_615_);
lean_dec(v_snd_615_);
v_decide_632_ = lean_nat_dec_eq(v___x_622_, v___x_619_);
if (v_decide_632_ == 0)
{
uint32_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_string_utf8_get_fast(v_s_607_, v___x_622_);
v___x_634_ = lean_box_uint32(v___x_633_);
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
v___y_624_ = v___x_635_;
goto v___jp_623_;
}
else
{
lean_object* v_prev_x3f_636_; 
v_prev_x3f_636_ = lean_box(0);
v___y_624_ = v_prev_x3f_636_;
goto v___jp_623_;
}
v___jp_623_:
{
uint8_t v___x_625_; 
v___x_625_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v___x_621_, v___y_624_);
lean_dec(v___y_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_box(0);
v___x_627_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_621_, v___x_622_, v___x_626_, v_fst_614_);
v___y_610_ = v___x_627_;
goto v___jp_609_;
}
else
{
uint32_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_628_ = 92;
v___x_629_ = lean_string_push(v_fst_614_, v___x_628_);
v___x_630_ = lean_box(0);
v___x_631_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_621_, v___x_622_, v___x_630_, v___x_629_);
v___y_610_ = v___x_631_;
goto v___jp_609_;
}
}
}
else
{
lean_object* v___x_638_; 
if (v_isShared_618_ == 0)
{
v___x_638_ = v___x_617_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_fst_614_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_snd_615_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___boxed(lean_object* v_s_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_641_, v_a_642_);
lean_dec_ref(v_s_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object* v_s_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_snd_653_; lean_object* v_fst_654_; lean_object* v_fst_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_664_; 
v___x_651_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1));
v___x_652_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_650_, v___x_651_);
v_snd_653_ = lean_ctor_get(v___x_652_, 1);
lean_inc(v_snd_653_);
v_fst_654_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_fst_654_);
lean_dec_ref(v___x_652_);
v_fst_655_ = lean_ctor_get(v_snd_653_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_snd_653_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v_snd_653_, 1);
lean_dec(v_unused_665_);
v___x_657_ = v_snd_653_;
v_isShared_658_ = v_isSharedCheck_664_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_fst_655_);
lean_dec(v_snd_653_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_664_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_fst_655_);
lean_ctor_set(v___x_657_, 0, v_fst_654_);
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_fst_654_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_fst_655_);
v___x_660_ = v_reuseFailAlloc_663_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; lean_object* v_fst_662_; 
v___x_661_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_650_, v___x_660_);
v_fst_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_fst_662_);
lean_dec_ref(v___x_661_);
return v_fst_662_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object* v_s_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_666_);
lean_dec_ref(v_s_666_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object* v_s_668_, lean_object* v_inst_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_668_, v_a_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object* v_s_672_, lean_object* v_inst_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_672_, v_inst_673_, v_a_674_);
lean_dec_ref(v_s_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(lean_object* v_s_676_, lean_object* v_inst_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_676_, v_a_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___boxed(lean_object* v_s_680_, lean_object* v_inst_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(v_s_680_, v_inst_681_, v_a_682_);
lean_dec_ref(v_s_680_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v_str_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_snd_686_; lean_object* v_fst_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_729_; 
v_snd_686_ = lean_ctor_get(v_a_685_, 1);
v_fst_687_ = lean_ctor_get(v_a_685_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v_a_685_);
if (v_isSharedCheck_729_ == 0)
{
v___x_689_ = v_a_685_;
v_isShared_690_ = v_isSharedCheck_729_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_snd_686_);
lean_inc(v_fst_687_);
lean_dec(v_a_685_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_729_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_fst_691_; lean_object* v_snd_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_728_; 
v_fst_691_ = lean_ctor_get(v_snd_686_, 0);
v_snd_692_ = lean_ctor_get(v_snd_686_, 1);
v_isSharedCheck_728_ = !lean_is_exclusive(v_snd_686_);
if (v_isSharedCheck_728_ == 0)
{
v___x_694_ = v_snd_686_;
v_isShared_695_ = v_isSharedCheck_728_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_snd_692_);
lean_inc(v_fst_691_);
lean_dec(v_snd_686_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_728_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; uint8_t v_decide_697_; 
v___x_696_ = lean_string_utf8_byte_size(v_str_684_);
v_decide_697_ = lean_nat_dec_eq(v_snd_692_, v___x_696_);
if (v_decide_697_ == 0)
{
uint32_t v___x_698_; lean_object* v___x_699_; uint32_t v___x_700_; uint8_t v___x_701_; 
v___x_698_ = lean_string_utf8_get_fast(v_str_684_, v_snd_692_);
v___x_699_ = lean_string_utf8_next_fast(v_str_684_, v_snd_692_);
lean_dec(v_snd_692_);
v___x_700_ = 96;
v___x_701_ = lean_uint32_dec_eq(v___x_698_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v_longest_702_; lean_object* v___y_704_; uint8_t v___x_712_; 
v_longest_702_ = lean_unsigned_to_nat(0u);
v___x_712_ = lean_nat_dec_le(v_fst_687_, v_fst_691_);
if (v___x_712_ == 0)
{
lean_dec(v_fst_691_);
v___y_704_ = v_fst_687_;
goto v___jp_703_;
}
else
{
lean_dec(v_fst_687_);
v___y_704_ = v_fst_691_;
goto v___jp_703_;
}
v___jp_703_:
{
lean_object* v___x_706_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_699_);
lean_ctor_set(v___x_694_, 0, v_longest_702_);
v___x_706_ = v___x_694_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_longest_702_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_699_);
v___x_706_ = v_reuseFailAlloc_711_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_706_);
lean_ctor_set(v___x_689_, 0, v___y_704_);
v___x_708_ = v___x_689_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___y_704_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_710_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
v_a_685_ = v___x_708_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = lean_nat_add(v_fst_691_, v___x_713_);
lean_dec(v_fst_691_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_699_);
lean_ctor_set(v___x_694_, 0, v___x_714_);
v___x_716_ = v___x_694_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_699_);
v___x_716_ = v_reuseFailAlloc_721_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_716_);
v___x_718_ = v___x_689_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_fst_687_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_720_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
v_a_685_ = v___x_718_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_723_; 
if (v_isShared_695_ == 0)
{
v___x_723_ = v___x_694_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_fst_691_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_snd_692_);
v___x_723_ = v_reuseFailAlloc_727_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_723_);
v___x_725_ = v___x_689_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_fst_687_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v_str_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_730_, v_a_731_);
lean_dec_ref(v_str_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(lean_object* v_str_738_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_snd_741_; lean_object* v_fst_742_; lean_object* v_fst_743_; uint8_t v___x_744_; 
v___x_739_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1));
v___x_740_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_738_, v___x_739_);
v_snd_741_ = lean_ctor_get(v___x_740_, 1);
lean_inc(v_snd_741_);
v_fst_742_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_fst_742_);
lean_dec_ref(v___x_740_);
v_fst_743_ = lean_ctor_get(v_snd_741_, 0);
lean_inc(v_fst_743_);
lean_dec(v_snd_741_);
v___x_744_ = lean_nat_dec_le(v_fst_742_, v_fst_743_);
if (v___x_744_ == 0)
{
lean_dec(v_fst_743_);
return v_fst_742_;
}
else
{
lean_dec(v_fst_742_);
return v_fst_743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___boxed(lean_object* v_str_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_745_);
lean_dec_ref(v_str_745_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(lean_object* v_str_747_, lean_object* v_inst_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_747_, v_a_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v_str_751_, lean_object* v_inst_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(v_str_751_, v_inst_752_, v_a_753_);
lean_dec_ref(v_str_751_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
lean_object* v_zero_757_; uint8_t v_isZero_758_; 
v_zero_757_ = lean_unsigned_to_nat(0u);
v_isZero_758_ = lean_nat_dec_eq(v_x_755_, v_zero_757_);
if (v_isZero_758_ == 1)
{
lean_dec(v_x_755_);
return v_x_756_;
}
else
{
uint32_t v___x_759_; lean_object* v_one_760_; lean_object* v_n_761_; lean_object* v___x_762_; 
v___x_759_ = 96;
v_one_760_ = lean_unsigned_to_nat(1u);
v_n_761_ = lean_nat_sub(v_x_755_, v_one_760_);
lean_dec(v_x_755_);
v___x_762_ = lean_string_push(v_x_756_, v___x_759_);
v_x_755_ = v_n_761_;
v_x_756_ = v___x_762_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(lean_object* v_atLeast_764_, lean_object* v_str_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___y_768_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_772_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_765_);
v___x_773_ = lean_nat_dec_le(v_atLeast_764_, v___x_772_);
if (v___x_773_ == 0)
{
lean_dec(v___x_772_);
v___y_768_ = v_atLeast_764_;
goto v___jp_767_;
}
else
{
lean_dec(v_atLeast_764_);
v___y_768_ = v___x_772_;
goto v___jp_767_;
}
v___jp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_unsigned_to_nat(1u);
v___x_770_ = lean_nat_add(v___y_768_, v___x_769_);
lean_dec(v___y_768_);
v___x_771_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(v___x_770_, v___x_766_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor___boxed(lean_object* v_atLeast_774_, lean_object* v_str_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v_atLeast_774_, v_str_775_);
lean_dec_ref(v_str_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object* v_str_778_){
_start:
{
lean_object* v___x_779_; lean_object* v_backticks_780_; lean_object* v___y_782_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_779_ = lean_unsigned_to_nat(0u);
v_backticks_780_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_779_, v_str_778_);
v___x_796_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1));
v___x_797_ = lean_string_utf8_byte_size(v_str_778_);
v___x_798_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2);
v___x_799_ = lean_nat_dec_le(v___x_798_, v___x_797_);
if (v___x_799_ == 0)
{
goto v___jp_789_;
}
else
{
uint8_t v___x_800_; 
v___x_800_ = lean_string_memcmp(v_str_778_, v___x_796_, v___x_779_, v___x_779_, v___x_798_);
if (v___x_800_ == 0)
{
goto v___jp_789_;
}
else
{
goto v___jp_785_;
}
}
v___jp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_inc_ref(v_backticks_780_);
v___x_783_ = lean_string_append(v_backticks_780_, v___y_782_);
lean_dec_ref(v___y_782_);
v___x_784_ = lean_string_append(v___x_783_, v_backticks_780_);
lean_dec_ref(v_backticks_780_);
return v___x_784_;
}
v___jp_785_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_787_ = lean_string_append(v___x_786_, v_str_778_);
lean_dec_ref(v_str_778_);
v___x_788_ = lean_string_append(v___x_787_, v___x_786_);
v___y_782_ = v___x_788_;
goto v___jp_781_;
}
v___jp_789_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_790_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1));
v___x_791_ = lean_string_utf8_byte_size(v_str_778_);
v___x_792_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2);
v___x_793_ = lean_nat_dec_le(v___x_792_, v___x_791_);
if (v___x_793_ == 0)
{
v___y_782_ = v_str_778_;
goto v___jp_781_;
}
else
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_nat_sub(v___x_791_, v___x_792_);
v___x_795_ = lean_string_memcmp(v_str_778_, v___x_790_, v___x_794_, v___x_779_, v___x_792_);
lean_dec(v___x_794_);
if (v___x_795_ == 0)
{
v___y_782_ = v_str_778_;
goto v___jp_781_;
}
else
{
goto v___jp_785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(lean_object* v_s_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0));
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___boxed(lean_object* v_s_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v_s_805_);
lean_dec_ref(v_s_805_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(lean_object* v_str_807_, lean_object* v___x_808_, lean_object* v___x_809_, lean_object* v_a_810_, lean_object* v_b_811_){
_start:
{
lean_object* v_it_813_; lean_object* v_startInclusive_814_; lean_object* v_endExclusive_815_; 
if (lean_obj_tag(v_a_810_) == 0)
{
lean_object* v_currPos_819_; lean_object* v_searcher_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_843_; 
v_currPos_819_ = lean_ctor_get(v_a_810_, 0);
v_searcher_820_ = lean_ctor_get(v_a_810_, 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v_a_810_);
if (v_isSharedCheck_843_ == 0)
{
v___x_822_ = v_a_810_;
v_isShared_823_ = v_isSharedCheck_843_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_searcher_820_);
lean_inc(v_currPos_819_);
lean_dec(v_a_810_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_843_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v_decide_824_; 
v_decide_824_ = lean_nat_dec_eq(v_searcher_820_, v___x_809_);
if (v_decide_824_ == 0)
{
uint32_t v___x_825_; uint32_t v___x_826_; uint8_t v___x_827_; 
v___x_825_ = 10;
v___x_826_ = lean_string_utf8_get_fast(v_str_807_, v_searcher_820_);
v___x_827_ = lean_uint32_dec_eq(v___x_826_, v___x_825_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_string_utf8_next_fast(v_str_807_, v_searcher_820_);
lean_dec(v_searcher_820_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_828_);
v___x_830_ = v___x_822_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_currPos_819_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___x_828_);
v___x_830_ = v_reuseFailAlloc_832_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
v_a_810_ = v___x_830_;
goto _start;
}
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v_slice_836_; lean_object* v_nextIt_838_; 
v___x_833_ = lean_string_utf8_next_fast(v_str_807_, v_searcher_820_);
v___x_834_ = lean_nat_sub(v___x_833_, v_searcher_820_);
v___x_835_ = lean_nat_add(v_searcher_820_, v___x_834_);
lean_dec(v___x_834_);
v_slice_836_ = l_String_Slice_subslice_x21(v___x_808_, v_currPos_819_, v_searcher_820_);
lean_inc(v___x_835_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_835_);
lean_ctor_set(v___x_822_, 0, v___x_835_);
v_nextIt_838_ = v___x_822_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_835_);
v_nextIt_838_ = v_reuseFailAlloc_841_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v_startInclusive_839_; lean_object* v_endExclusive_840_; 
v_startInclusive_839_ = lean_ctor_get(v_slice_836_, 0);
lean_inc(v_startInclusive_839_);
v_endExclusive_840_ = lean_ctor_get(v_slice_836_, 1);
lean_inc(v_endExclusive_840_);
lean_dec_ref(v_slice_836_);
v_it_813_ = v_nextIt_838_;
v_startInclusive_814_ = v_startInclusive_839_;
v_endExclusive_815_ = v_endExclusive_840_;
goto v___jp_812_;
}
}
}
else
{
lean_object* v___x_842_; 
lean_del_object(v___x_822_);
lean_dec(v_searcher_820_);
v___x_842_ = lean_box(1);
lean_inc(v___x_809_);
v_it_813_ = v___x_842_;
v_startInclusive_814_ = v_currPos_819_;
v_endExclusive_815_ = v___x_809_;
goto v___jp_812_;
}
}
}
else
{
lean_dec(v___x_809_);
return v_b_811_;
}
v___jp_812_:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_string_utf8_extract_fast(v_str_807_, v_startInclusive_814_, v_endExclusive_815_);
lean_dec(v_endExclusive_815_);
lean_dec(v_startInclusive_814_);
v___x_817_ = lean_array_push(v_b_811_, v___x_816_);
v_a_810_ = v_it_813_;
v_b_811_ = v___x_817_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg___boxed(lean_object* v_str_844_, lean_object* v___x_845_, lean_object* v___x_846_, lean_object* v_a_847_, lean_object* v_b_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_844_, v___x_845_, v___x_846_, v_a_847_, v_b_848_);
lean_dec_ref(v___x_845_);
lean_dec_ref(v_str_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(lean_object* v_str_850_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = lean_string_utf8_byte_size(v_str_850_);
lean_inc_ref(v_str_850_);
v___x_853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_853_, 0, v_str_850_);
lean_ctor_set(v___x_853_, 1, v___x_851_);
lean_ctor_set(v___x_853_, 2, v___x_852_);
v___x_854_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v___x_853_);
v___x_855_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_856_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_850_, v___x_853_, v___x_852_, v___x_854_, v___x_855_);
lean_dec_ref_known(v___x_853_, 3);
lean_dec_ref(v_str_850_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(lean_object* v_str_857_, lean_object* v___x_858_, lean_object* v___x_859_, lean_object* v_inst_860_, lean_object* v_R_861_, lean_object* v_a_862_, lean_object* v_b_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_857_, v___x_858_, v___x_859_, v_a_862_, v_b_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___boxed(lean_object* v_str_865_, lean_object* v___x_866_, lean_object* v___x_867_, lean_object* v_inst_868_, lean_object* v_R_869_, lean_object* v_a_870_, lean_object* v_b_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(v_str_865_, v___x_866_, v___x_867_, v_inst_868_, v_R_869_, v_a_870_, v_b_871_);
lean_dec_ref(v___x_866_);
lean_dec_ref(v_str_865_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(lean_object* v_str_873_){
_start:
{
lean_object* v___x_874_; lean_object* v_fence_875_; lean_object* v___y_877_; lean_object* v_body_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_874_ = lean_unsigned_to_nat(2u);
v_fence_875_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_874_, v_str_873_);
v_body_883_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(v_str_873_);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_array_get_size(v_body_883_);
v___x_886_ = lean_nat_dec_lt(v___x_884_, v___x_885_);
if (v___x_886_ == 0)
{
v___y_877_ = v_body_883_;
goto v___jp_876_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_nat_sub(v___x_885_, v___x_888_);
v___x_890_ = lean_array_get(v___x_887_, v_body_883_, v___x_889_);
lean_dec(v___x_889_);
v___x_891_ = lean_string_utf8_byte_size(v___x_890_);
lean_dec(v___x_890_);
v___x_892_ = lean_nat_dec_eq(v___x_891_, v___x_884_);
if (v___x_892_ == 0)
{
v___y_877_ = v_body_883_;
goto v___jp_876_;
}
else
{
lean_object* v___x_893_; 
v___x_893_ = lean_array_pop(v_body_883_);
v___y_877_ = v___x_893_;
goto v___jp_876_;
}
}
v___jp_876_:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = lean_mk_empty_array_with_capacity(v___x_878_);
v___x_880_ = lean_array_push(v___x_879_, v_fence_875_);
lean_inc_ref(v___x_880_);
v___x_881_ = l_Array_append___redArg(v___x_880_, v___y_877_);
lean_dec_ref(v___y_877_);
v___x_882_ = l_Array_append___redArg(v___x_881_, v___x_880_);
lean_dec_ref(v___x_880_);
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_894_, lean_object* v_pos_895_){
_start:
{
lean_object* v_str_896_; lean_object* v_startInclusive_897_; lean_object* v_endExclusive_898_; lean_object* v___x_899_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v_decide_910_; 
v_str_896_ = lean_ctor_get(v_s_894_, 0);
v_startInclusive_897_ = lean_ctor_get(v_s_894_, 1);
v_endExclusive_898_ = lean_ctor_get(v_s_894_, 2);
v___x_899_ = lean_nat_add(v_startInclusive_897_, v_pos_895_);
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_nat_sub(v_endExclusive_898_, v___x_899_);
v_decide_910_ = lean_nat_dec_eq(v___x_908_, v___x_909_);
lean_dec(v___x_909_);
if (v_decide_910_ == 0)
{
uint32_t v___x_911_; uint32_t v___x_912_; uint8_t v___x_913_; 
v___x_911_ = lean_string_utf8_get_fast(v_str_896_, v___x_899_);
v___x_912_ = 32;
v___x_913_ = lean_uint32_dec_eq(v___x_911_, v___x_912_);
if (v___x_913_ == 0)
{
uint32_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = 9;
v___x_915_ = lean_uint32_dec_eq(v___x_911_, v___x_914_);
if (v___x_915_ == 0)
{
uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 13;
v___x_917_ = lean_uint32_dec_eq(v___x_911_, v___x_916_);
if (v___x_917_ == 0)
{
uint32_t v___x_918_; uint8_t v___x_919_; 
v___x_918_ = 10;
v___x_919_ = lean_uint32_dec_eq(v___x_911_, v___x_918_);
if (v___x_919_ == 0)
{
lean_dec(v___x_899_);
return v_pos_895_;
}
else
{
goto v___jp_900_;
}
}
else
{
goto v___jp_900_;
}
}
else
{
goto v___jp_900_;
}
}
else
{
goto v___jp_900_;
}
}
else
{
lean_dec(v___x_899_);
return v_pos_895_;
}
v___jp_900_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_901_ = lean_string_utf8_next_fast(v_str_896_, v___x_899_);
v___x_902_ = lean_nat_sub(v___x_901_, v___x_899_);
lean_dec(v___x_899_);
v___x_903_ = lean_nat_add(v_pos_895_, v___x_902_);
lean_dec(v___x_902_);
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_nat_add(v_pos_895_, v___x_904_);
v___x_906_ = lean_nat_dec_le(v___x_905_, v___x_903_);
lean_dec(v___x_905_);
if (v___x_906_ == 0)
{
lean_dec(v___x_903_);
return v_pos_895_;
}
else
{
lean_dec(v_pos_895_);
v_pos_895_ = v___x_903_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object* v_s_920_, lean_object* v_pos_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_920_, v_pos_921_);
lean_dec_ref(v_s_920_);
return v_res_922_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Doc_Inline_empty(lean_box(0));
return v___x_923_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object* v_a_927_){
_start:
{
if (lean_obj_tag(v_a_927_) == 0)
{
lean_object* v___x_928_; 
v___x_928_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
return v___x_928_;
}
else
{
lean_object* v_head_929_; 
v_head_929_ = lean_ctor_get(v_a_927_, 0);
lean_inc(v_head_929_);
switch(lean_obj_tag(v_head_929_))
{
case 0:
{
lean_object* v_tail_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_974_; 
v_tail_930_ = lean_ctor_get(v_a_927_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_a_927_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v_a_927_, 0);
lean_dec(v_unused_975_);
v___x_932_ = v_a_927_;
v_isShared_933_ = v_isSharedCheck_974_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_tail_930_);
lean_dec(v_a_927_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_974_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_string_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_973_; 
v_string_934_ = lean_ctor_get(v_head_929_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v_head_929_);
if (v_isSharedCheck_973_ == 0)
{
v___x_936_ = v_head_929_;
v_isShared_937_ = v_isSharedCheck_973_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_string_934_);
lean_dec(v_head_929_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_973_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v_decide_942_; 
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = lean_string_utf8_byte_size(v_string_934_);
lean_inc_ref(v_string_934_);
v___x_940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_940_, 0, v_string_934_);
lean_ctor_set(v___x_940_, 1, v___x_938_);
lean_ctor_set(v___x_940_, 2, v___x_939_);
v___x_941_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_940_, v___x_938_);
lean_dec_ref_known(v___x_940_, 3);
v_decide_942_ = lean_nat_dec_eq(v___x_941_, v___x_939_);
if (v_decide_942_ == 0)
{
lean_object* v_s1_943_; lean_object* v_s2_944_; lean_object* v___x_946_; 
v_s1_943_ = lean_string_utf8_extract_fast(v_string_934_, v___x_938_, v___x_941_);
v_s2_944_ = lean_string_utf8_extract_fast(v_string_934_, v___x_941_, v___x_939_);
lean_dec(v___x_941_);
lean_dec_ref(v_string_934_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_s2_944_);
v___x_946_ = v___x_936_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_s2_944_);
v___x_946_ = v_reuseFailAlloc_961_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_947_ = lean_array_mk(v_tail_930_);
v___x_948_ = lean_array_get_size(v___x_947_);
v___x_949_ = lean_nat_dec_eq(v___x_948_, v___x_938_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_950_ = lean_unsigned_to_nat(1u);
v___x_951_ = lean_mk_empty_array_with_capacity(v___x_950_);
v___x_952_ = lean_array_push(v___x_951_, v___x_946_);
v___x_953_ = l_Array_append___redArg(v___x_952_, v___x_947_);
lean_dec_ref(v___x_947_);
v___x_954_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 0);
lean_ctor_set(v___x_932_, 1, v___x_954_);
lean_ctor_set(v___x_932_, 0, v_s1_943_);
v___x_956_ = v___x_932_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_s1_943_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
else
{
lean_object* v___x_959_; 
lean_dec_ref(v___x_947_);
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 0);
lean_ctor_set(v___x_932_, 1, v___x_946_);
lean_ctor_set(v___x_932_, 0, v_s1_943_);
v___x_959_ = v___x_932_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_s1_943_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v___x_946_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
else
{
lean_object* v___x_962_; lean_object* v_fst_963_; lean_object* v_snd_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_972_; 
lean_dec(v___x_941_);
lean_del_object(v___x_936_);
lean_del_object(v___x_932_);
v___x_962_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_930_);
v_fst_963_ = lean_ctor_get(v___x_962_, 0);
v_snd_964_ = lean_ctor_get(v___x_962_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_972_ == 0)
{
v___x_966_ = v___x_962_;
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_snd_964_);
lean_inc(v_fst_963_);
lean_dec(v___x_962_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = lean_string_append(v_string_934_, v_fst_963_);
lean_dec(v_fst_963_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_snd_964_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_976_; lean_object* v_content_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_tail_976_ = lean_ctor_get(v_a_927_, 1);
lean_inc(v_tail_976_);
lean_dec_ref_known(v_a_927_, 2);
v_content_977_ = lean_ctor_get(v_head_929_, 0);
lean_inc_ref(v_content_977_);
lean_dec_ref_known(v_head_929_, 1);
v___x_978_ = lean_array_to_list(v_content_977_);
v___x_979_ = l_List_appendTR___redArg(v___x_978_, v_tail_976_);
v_a_927_ = v___x_979_;
goto _start;
}
default: 
{
lean_object* v_tail_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1019_; 
v_tail_981_ = lean_ctor_get(v_a_927_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_a_927_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; 
v_unused_1020_ = lean_ctor_get(v_a_927_, 0);
lean_dec(v_unused_1020_);
v___x_983_ = v_a_927_;
v_isShared_984_ = v_isSharedCheck_1019_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_tail_981_);
lean_dec(v_a_927_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1019_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_986_ = lean_array_mk(v_tail_981_);
if (lean_obj_tag(v_head_929_) == 9)
{
lean_object* v_content_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v_content_987_ = lean_ctor_get(v_head_929_, 0);
v___x_988_ = lean_array_get_size(v_content_987_);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = lean_nat_dec_eq(v___x_988_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_array_get_size(v___x_986_);
v___x_992_ = lean_nat_dec_eq(v___x_991_, v___x_989_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
lean_inc_ref(v_content_987_);
lean_dec_ref_known(v_head_929_, 1);
v___x_993_ = l_Array_append___redArg(v_content_987_, v___x_986_);
lean_dec_ref(v___x_986_);
v___x_994_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 0);
lean_ctor_set(v___x_983_, 1, v___x_994_);
lean_ctor_set(v___x_983_, 0, v___x_985_);
v___x_996_ = v___x_983_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
lean_object* v___x_999_; 
lean_dec_ref(v___x_986_);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 0);
lean_ctor_set(v___x_983_, 1, v_head_929_);
lean_ctor_set(v___x_983_, 0, v___x_985_);
v___x_999_ = v___x_983_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_head_929_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
lean_dec_ref_known(v_head_929_, 1);
v___x_1001_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_986_);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 0);
lean_ctor_set(v___x_983_, 1, v___x_1001_);
lean_ctor_set(v___x_983_, 0, v___x_985_);
v___x_1003_ = v___x_983_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1005_ = lean_array_get_size(v___x_986_);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_nat_dec_eq(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1008_ = lean_unsigned_to_nat(1u);
v___x_1009_ = lean_mk_empty_array_with_capacity(v___x_1008_);
v___x_1010_ = lean_array_push(v___x_1009_, v_head_929_);
v___x_1011_ = l_Array_append___redArg(v___x_1010_, v___x_986_);
lean_dec_ref(v___x_986_);
v___x_1012_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 0);
lean_ctor_set(v___x_983_, 1, v___x_1012_);
lean_ctor_set(v___x_983_, 0, v___x_985_);
v___x_1014_ = v___x_983_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
else
{
lean_object* v___x_1017_; 
lean_dec_ref(v___x_986_);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 0);
lean_ctor_set(v___x_983_, 1, v_head_929_);
lean_ctor_set(v___x_983_, 0, v___x_985_);
v___x_1017_ = v___x_983_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_head_929_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_inline_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_1028_, lean_object* v_inline_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_1031_, lean_object* v_pos_1032_){
_start:
{
lean_object* v_str_1033_; lean_object* v_startInclusive_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v_decide_1038_; 
v_str_1033_ = lean_ctor_get(v_s_1031_, 0);
v_startInclusive_1034_ = lean_ctor_get(v_s_1031_, 1);
v___x_1035_ = lean_nat_add(v_startInclusive_1034_, v_pos_1032_);
v___x_1036_ = lean_nat_sub(v___x_1035_, v_startInclusive_1034_);
v___x_1037_ = lean_unsigned_to_nat(0u);
v_decide_1038_ = lean_nat_dec_eq(v___x_1036_, v___x_1037_);
if (v_decide_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1047_; uint32_t v___x_1048_; uint32_t v___x_1049_; uint8_t v___x_1050_; 
lean_inc(v_startInclusive_1034_);
lean_inc_ref(v_str_1033_);
v___x_1039_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1039_, 0, v_str_1033_);
lean_ctor_set(v___x_1039_, 1, v_startInclusive_1034_);
lean_ctor_set(v___x_1039_, 2, v___x_1035_);
v___x_1040_ = lean_unsigned_to_nat(1u);
v___x_1041_ = lean_nat_sub(v___x_1036_, v___x_1040_);
lean_dec(v___x_1036_);
v___x_1042_ = l_String_Slice_posLE(v___x_1039_, v___x_1041_);
lean_dec_ref_known(v___x_1039_, 3);
v___x_1047_ = lean_nat_add(v_startInclusive_1034_, v___x_1042_);
v___x_1048_ = lean_string_utf8_get_fast(v_str_1033_, v___x_1047_);
lean_dec(v___x_1047_);
v___x_1049_ = 32;
v___x_1050_ = lean_uint32_dec_eq(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
uint32_t v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = 9;
v___x_1052_ = lean_uint32_dec_eq(v___x_1048_, v___x_1051_);
if (v___x_1052_ == 0)
{
uint32_t v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = 13;
v___x_1054_ = lean_uint32_dec_eq(v___x_1048_, v___x_1053_);
if (v___x_1054_ == 0)
{
uint32_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = 10;
v___x_1056_ = lean_uint32_dec_eq(v___x_1048_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_dec(v___x_1042_);
return v_pos_1032_;
}
else
{
goto v___jp_1043_;
}
}
else
{
goto v___jp_1043_;
}
}
else
{
goto v___jp_1043_;
}
}
else
{
goto v___jp_1043_;
}
v___jp_1043_:
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_nat_add(v___x_1042_, v___x_1040_);
v___x_1045_ = lean_nat_dec_le(v___x_1044_, v_pos_1032_);
lean_dec(v___x_1044_);
if (v___x_1045_ == 0)
{
lean_dec(v___x_1042_);
return v_pos_1032_;
}
else
{
lean_dec(v_pos_1032_);
v_pos_1032_ = v___x_1042_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1036_);
lean_dec(v___x_1035_);
return v_pos_1032_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_1057_, lean_object* v_pos_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_1057_, v_pos_1058_);
lean_dec_ref(v_s_1057_);
return v_res_1059_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1061_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v___x_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_xs_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1064_ = lean_array_get_size(v_xs_1063_);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = lean_nat_dec_eq(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_unsigned_to_nat(1u);
v___x_1068_ = lean_nat_sub(v___x_1064_, v___x_1067_);
v___x_1069_ = lean_array_fget(v_xs_1063_, v___x_1068_);
lean_dec(v___x_1068_);
switch(lean_obj_tag(v___x_1069_))
{
case 0:
{
lean_object* v_string_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1100_; 
v_string_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1100_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_string_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1100_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v_decide_1077_; 
v___x_1074_ = lean_string_utf8_byte_size(v_string_1070_);
lean_inc_ref(v_string_1070_);
v___x_1075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1075_, 0, v_string_1070_);
lean_ctor_set(v___x_1075_, 1, v___x_1065_);
lean_ctor_set(v___x_1075_, 2, v___x_1074_);
v___x_1076_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_1075_, v___x_1065_);
v_decide_1077_ = lean_nat_dec_eq(v___x_1076_, v___x_1074_);
lean_dec(v___x_1076_);
if (v_decide_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1078_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_1075_, v___x_1074_);
lean_dec_ref_known(v___x_1075_, 3);
v___x_1079_ = lean_array_pop(v_xs_1063_);
v___x_1080_ = lean_string_utf8_extract_fast(v_string_1070_, v___x_1065_, v___x_1078_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1080_);
v___x_1082_ = v___x_1072_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1083_ = lean_array_push(v___x_1079_, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
v___x_1085_ = lean_string_utf8_extract_fast(v_string_1070_, v___x_1078_, v___x_1074_);
lean_dec(v___x_1078_);
lean_dec_ref(v_string_1070_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
return v___x_1086_;
}
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v_fst_1090_; lean_object* v_snd_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref_known(v___x_1075_, 3);
lean_del_object(v___x_1072_);
v___x_1088_ = lean_array_pop(v_xs_1063_);
v___x_1089_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1088_);
v_fst_1090_ = lean_ctor_get(v___x_1089_, 0);
v_snd_1091_ = lean_ctor_get(v___x_1089_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1093_ = v___x_1089_;
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_snd_1091_);
lean_inc(v_fst_1090_);
lean_dec(v___x_1089_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_string_append(v_snd_1091_, v_string_1070_);
lean_dec_ref(v_string_1070_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v___x_1095_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_fst_1090_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
case 9:
{
lean_object* v_content_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_content_1101_ = lean_ctor_get(v___x_1069_, 0);
lean_inc_ref(v_content_1101_);
lean_dec_ref_known(v___x_1069_, 1);
v___x_1102_ = lean_array_pop(v_xs_1063_);
v___x_1103_ = l_Array_append___redArg(v___x_1102_, v_content_1101_);
lean_dec_ref(v_content_1101_);
v_xs_1063_ = v___x_1103_;
goto _start;
}
default: 
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec(v___x_1069_);
v___x_1105_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1105_, 0, v_xs_1063_);
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
return v___x_1107_;
}
}
}
else
{
lean_object* v___x_1108_; 
lean_dec_ref(v_xs_1063_);
v___x_1108_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_1109_, lean_object* v_xs_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_xs_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_mk_empty_array_with_capacity(v___x_1113_);
v___x_1115_ = lean_array_push(v___x_1114_, v_inline_1112_);
v___x_1116_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_1117_, lean_object* v_inline_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v_fst_1122_; lean_object* v_snd_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1131_; 
v___x_1121_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1120_);
v_fst_1122_ = lean_ctor_get(v___x_1121_, 0);
v_snd_1123_ = lean_ctor_get(v___x_1121_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1125_ = v___x_1121_;
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_snd_1123_);
lean_inc(v_fst_1122_);
lean_dec(v___x_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_1123_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v___x_1127_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_fst_1122_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_1132_, lean_object* v_inline_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_instMonadEIO(lean_box(0));
return v___x_1135_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0);
v___x_1137_ = l_StateRefT_x27_instMonad___redArg(v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1166_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13));
v___x_1167_ = lean_unsigned_to_nat(3u);
v___x_1168_ = lean_mk_empty_array_with_capacity(v___x_1167_);
v___x_1169_ = lean_array_push(v___x_1168_, v___x_1166_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object* v_inst_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1172_, v_x_1173_, v_x_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_1180_, lean_object* v_x_1181_, lean_object* v_x_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_pieces_1188_; lean_object* v_pieces_1192_; lean_object* v___x_1195_; lean_object* v_toApplicative_1196_; lean_object* v_toFunctor_1197_; lean_object* v_toSeq_1198_; lean_object* v_toSeqLeft_1199_; lean_object* v_toSeqRight_1200_; lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1195_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1196_ = lean_ctor_get(v___x_1195_, 0);
v_toFunctor_1197_ = lean_ctor_get(v_toApplicative_1196_, 0);
v_toSeq_1198_ = lean_ctor_get(v_toApplicative_1196_, 2);
v_toSeqLeft_1199_ = lean_ctor_get(v_toApplicative_1196_, 3);
v_toSeqRight_1200_ = lean_ctor_get(v_toApplicative_1196_, 4);
v___f_1201_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1202_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1197_, 2);
v___f_1203_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1203_, 0, v_toFunctor_1197_);
v___f_1204_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1204_, 0, v_toFunctor_1197_);
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___f_1203_);
lean_ctor_set(v___x_1205_, 1, v___f_1204_);
lean_inc(v_toSeqRight_1200_);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toSeqRight_1200_);
lean_inc(v_toSeqLeft_1199_);
v___f_1207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1207_, 0, v_toSeqLeft_1199_);
lean_inc(v_toSeq_1198_);
v___f_1208_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1208_, 0, v_toSeq_1198_);
v___x_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1205_);
lean_ctor_set(v___x_1209_, 1, v___f_1201_);
lean_ctor_set(v___x_1209_, 2, v___f_1208_);
lean_ctor_set(v___x_1209_, 3, v___f_1207_);
lean_ctor_set(v___x_1209_, 4, v___f_1206_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___f_1202_);
v___x_1211_ = l_StateRefT_x27_instMonad___redArg(v___x_1210_);
switch(lean_obj_tag(v_x_1182_))
{
case 0:
{
lean_object* v_string_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v___x_1211_);
lean_dec_ref(v_x_1181_);
lean_dec_ref(v_inst_1180_);
v_string_1212_ = lean_ctor_get(v_x_1182_, 0);
lean_inc_ref(v_string_1212_);
lean_dec_ref_known(v_x_1182_, 1);
v___x_1213_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1212_);
lean_dec_ref(v_string_1212_);
v___x_1214_ = lean_unsigned_to_nat(1u);
v___x_1215_ = lean_mk_empty_array_with_capacity(v___x_1214_);
v___x_1216_ = lean_array_push(v___x_1215_, v___x_1213_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
case 1:
{
lean_object* v_content_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v___x_1211_);
v_content_1218_ = lean_ctor_get(v_x_1182_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1220_ = v_x_1182_;
v_isShared_1221_ = v_isSharedCheck_1269_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_content_1218_);
lean_dec(v_x_1182_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1269_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 9);
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_content_1218_);
v___x_1223_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v_snd_1225_; lean_object* v_fst_1226_; lean_object* v_fst_1227_; lean_object* v_snd_1228_; lean_object* v_pieces_1230_; uint8_t v_inEmph_1238_; uint8_t v_inBold_1239_; uint8_t v_inLink_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1267_; 
v___x_1224_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1223_);
v_snd_1225_ = lean_ctor_get(v___x_1224_, 1);
lean_inc(v_snd_1225_);
v_fst_1226_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_fst_1226_);
lean_dec_ref(v___x_1224_);
v_fst_1227_ = lean_ctor_get(v_snd_1225_, 0);
lean_inc(v_fst_1227_);
v_snd_1228_ = lean_ctor_get(v_snd_1225_, 1);
lean_inc(v_snd_1228_);
lean_dec(v_snd_1225_);
v_inEmph_1238_ = lean_ctor_get_uint8(v_x_1181_, 0);
v_inBold_1239_ = lean_ctor_get_uint8(v_x_1181_, 1);
v_inLink_1240_ = lean_ctor_get_uint8(v_x_1181_, 2);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_x_1181_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1242_ = v_x_1181_;
v_isShared_1243_ = v_isSharedCheck_1267_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v_x_1181_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1267_;
goto v_resetjp_1241_;
}
v___jp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1231_ = lean_string_utf8_byte_size(v_snd_1228_);
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = lean_nat_dec_eq(v___x_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_mk_empty_array_with_capacity(v___x_1234_);
v___x_1236_ = lean_array_push(v___x_1235_, v_snd_1228_);
v___x_1237_ = lean_array_push(v_pieces_1230_, v___x_1236_);
v_pieces_1192_ = v___x_1237_;
goto v___jp_1191_;
}
else
{
lean_dec(v_snd_1228_);
v_pieces_1192_ = v_pieces_1230_;
goto v___jp_1191_;
}
}
v_resetjp_1241_:
{
uint8_t v___x_1244_; lean_object* v___x_1246_; 
v___x_1244_ = 1;
if (v_isShared_1243_ == 0)
{
v___x_1246_ = v___x_1242_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1266_, 1, v_inBold_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1266_, 2, v_inLink_1240_);
v___x_1246_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1247_; 
lean_ctor_set_uint8(v___x_1246_, 0, v___x_1244_);
v___x_1247_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1180_, v___x_1246_, v_fst_1227_, v_a_1183_, v_a_1184_, v_a_1185_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v_pieces_1250_; lean_object* v_pieces_1255_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1260_ = lean_string_utf8_byte_size(v_fst_1226_);
v___x_1261_ = lean_nat_dec_eq(v___x_1260_, v___x_1258_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_mk_empty_array_with_capacity(v___x_1262_);
v___x_1264_ = lean_array_push(v___x_1263_, v_fst_1226_);
v___x_1265_ = lean_array_push(v___x_1259_, v___x_1264_);
v_pieces_1255_ = v___x_1265_;
goto v___jp_1254_;
}
else
{
lean_dec(v_fst_1226_);
v_pieces_1255_ = v___x_1259_;
goto v___jp_1254_;
}
v___jp_1249_:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_array_push(v_pieces_1250_, v_a_1248_);
if (v_inEmph_1238_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1253_ = lean_array_push(v___x_1251_, v___x_1252_);
v_pieces_1230_ = v___x_1253_;
goto v___jp_1229_;
}
else
{
v_pieces_1230_ = v___x_1251_;
goto v___jp_1229_;
}
}
v___jp_1254_:
{
if (v_inEmph_1238_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1257_ = lean_array_push(v_pieces_1255_, v___x_1256_);
v_pieces_1250_ = v___x_1257_;
goto v___jp_1249_;
}
else
{
v_pieces_1250_ = v_pieces_1255_;
goto v___jp_1249_;
}
}
}
else
{
lean_dec(v_snd_1228_);
lean_dec(v_fst_1226_);
return v___x_1247_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v___x_1211_);
v_content_1270_ = lean_ctor_get(v_x_1182_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1272_ = v_x_1182_;
v_isShared_1273_ = v_isSharedCheck_1321_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_content_1270_);
lean_dec(v_x_1182_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1321_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 9);
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_content_1270_);
v___x_1275_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; lean_object* v_snd_1277_; lean_object* v_fst_1278_; lean_object* v_fst_1279_; lean_object* v_snd_1280_; lean_object* v_pieces_1282_; uint8_t v_inEmph_1290_; uint8_t v_inBold_1291_; uint8_t v_inLink_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1319_; 
v___x_1276_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1275_);
v_snd_1277_ = lean_ctor_get(v___x_1276_, 1);
lean_inc(v_snd_1277_);
v_fst_1278_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_fst_1278_);
lean_dec_ref(v___x_1276_);
v_fst_1279_ = lean_ctor_get(v_snd_1277_, 0);
lean_inc(v_fst_1279_);
v_snd_1280_ = lean_ctor_get(v_snd_1277_, 1);
lean_inc(v_snd_1280_);
lean_dec(v_snd_1277_);
v_inEmph_1290_ = lean_ctor_get_uint8(v_x_1181_, 0);
v_inBold_1291_ = lean_ctor_get_uint8(v_x_1181_, 1);
v_inLink_1292_ = lean_ctor_get_uint8(v_x_1181_, 2);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_x_1181_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1294_ = v_x_1181_;
v_isShared_1295_ = v_isSharedCheck_1319_;
goto v_resetjp_1293_;
}
else
{
lean_dec(v_x_1181_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1319_;
goto v_resetjp_1293_;
}
v___jp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1283_ = lean_string_utf8_byte_size(v_snd_1280_);
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_nat_dec_eq(v___x_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = lean_unsigned_to_nat(1u);
v___x_1287_ = lean_mk_empty_array_with_capacity(v___x_1286_);
v___x_1288_ = lean_array_push(v___x_1287_, v_snd_1280_);
v___x_1289_ = lean_array_push(v_pieces_1282_, v___x_1288_);
v_pieces_1188_ = v___x_1289_;
goto v___jp_1187_;
}
else
{
lean_dec(v_snd_1280_);
v_pieces_1188_ = v_pieces_1282_;
goto v___jp_1187_;
}
}
v_resetjp_1293_:
{
uint8_t v___x_1296_; lean_object* v___x_1298_; 
v___x_1296_ = 1;
if (v_isShared_1295_ == 0)
{
v___x_1298_ = v___x_1294_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, 0, v_inEmph_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, 2, v_inLink_1292_);
v___x_1298_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1299_; 
lean_ctor_set_uint8(v___x_1298_, 1, v___x_1296_);
v___x_1299_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1180_, v___x_1298_, v_fst_1279_, v_a_1183_, v_a_1184_, v_a_1185_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v_pieces_1302_; lean_object* v_pieces_1307_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1299_, 1);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1312_ = lean_string_utf8_byte_size(v_fst_1278_);
v___x_1313_ = lean_nat_dec_eq(v___x_1312_, v___x_1310_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1314_ = lean_unsigned_to_nat(1u);
v___x_1315_ = lean_mk_empty_array_with_capacity(v___x_1314_);
v___x_1316_ = lean_array_push(v___x_1315_, v_fst_1278_);
v___x_1317_ = lean_array_push(v___x_1311_, v___x_1316_);
v_pieces_1307_ = v___x_1317_;
goto v___jp_1306_;
}
else
{
lean_dec(v_fst_1278_);
v_pieces_1307_ = v___x_1311_;
goto v___jp_1306_;
}
v___jp_1301_:
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_array_push(v_pieces_1302_, v_a_1300_);
if (v_inBold_1291_ == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1305_ = lean_array_push(v___x_1303_, v___x_1304_);
v_pieces_1282_ = v___x_1305_;
goto v___jp_1281_;
}
else
{
v_pieces_1282_ = v___x_1303_;
goto v___jp_1281_;
}
}
v___jp_1306_:
{
if (v_inBold_1291_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1309_ = lean_array_push(v_pieces_1307_, v___x_1308_);
v_pieces_1302_ = v___x_1309_;
goto v___jp_1301_;
}
else
{
v_pieces_1302_ = v_pieces_1307_;
goto v___jp_1301_;
}
}
}
else
{
lean_dec(v_snd_1280_);
lean_dec(v_fst_1278_);
return v___x_1299_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec_ref(v___x_1211_);
lean_dec_ref(v_x_1181_);
lean_dec_ref(v_inst_1180_);
v_string_1322_ = lean_ctor_get(v_x_1182_, 0);
lean_inc_ref(v_string_1322_);
lean_dec_ref_known(v_x_1182_, 1);
v___x_1323_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1322_);
v___x_1324_ = lean_unsigned_to_nat(1u);
v___x_1325_ = lean_mk_empty_array_with_capacity(v___x_1324_);
v___x_1326_ = lean_array_push(v___x_1325_, v___x_1323_);
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
case 4:
{
uint8_t v_mode_1328_; 
lean_dec_ref(v___x_1211_);
lean_dec_ref(v_x_1181_);
lean_dec_ref(v_inst_1180_);
v_mode_1328_ = lean_ctor_get_uint8(v_x_1182_, sizeof(void*)*1);
if (v_mode_1328_ == 0)
{
lean_object* v_string_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_string_1329_ = lean_ctor_get(v_x_1182_, 0);
lean_inc_ref(v_string_1329_);
lean_dec_ref_known(v_x_1182_, 1);
v___x_1330_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_1331_ = lean_string_append(v___x_1330_, v_string_1329_);
lean_dec_ref(v_string_1329_);
v___x_1332_ = lean_string_append(v___x_1331_, v___x_1330_);
v___x_1333_ = lean_unsigned_to_nat(1u);
v___x_1334_ = lean_mk_empty_array_with_capacity(v___x_1333_);
v___x_1335_ = lean_array_push(v___x_1334_, v___x_1332_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
return v___x_1336_;
}
else
{
lean_object* v_string_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_string_1337_ = lean_ctor_get(v_x_1182_, 0);
lean_inc_ref(v_string_1337_);
lean_dec_ref_known(v_x_1182_, 1);
v___x_1338_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_1339_ = lean_string_append(v___x_1338_, v_string_1337_);
lean_dec_ref(v_string_1337_);
v___x_1340_ = lean_string_append(v___x_1339_, v___x_1338_);
v___x_1341_ = lean_unsigned_to_nat(1u);
v___x_1342_ = lean_mk_empty_array_with_capacity(v___x_1341_);
v___x_1343_ = lean_array_push(v___x_1342_, v___x_1340_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
}
case 5:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec_ref_known(v_x_1182_, 1);
lean_dec_ref(v___x_1211_);
lean_dec_ref(v_x_1181_);
lean_dec_ref(v_inst_1180_);
v___x_1345_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
case 6:
{
uint8_t v_inLink_1347_; 
v_inLink_1347_ = lean_ctor_get_uint8(v_x_1181_, 2);
if (v_inLink_1347_ == 0)
{
lean_object* v_content_1348_; lean_object* v_url_1349_; uint8_t v_inEmph_1350_; uint8_t v_inBold_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref(v___x_1211_);
v_content_1348_ = lean_ctor_get(v_x_1182_, 0);
lean_inc_ref(v_content_1348_);
v_url_1349_ = lean_ctor_get(v_x_1182_, 1);
lean_inc_ref(v_url_1349_);
lean_dec_ref_known(v_x_1182_, 2);
v_inEmph_1350_ = lean_ctor_get_uint8(v_x_1181_, 0);
v_inBold_1351_ = lean_ctor_get_uint8(v_x_1181_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_x_1181_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1353_ = v_x_1181_;
v_isShared_1354_ = v_isSharedCheck_1380_;
goto v_resetjp_1352_;
}
else
{
lean_dec(v_x_1181_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1380_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
uint8_t v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = 1;
if (v_isShared_1354_ == 0)
{
v___x_1357_ = v___x_1353_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, 0, v_inEmph_1350_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, 1, v_inBold_1351_);
v___x_1357_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_ctor_set_uint8(v___x_1357_, 2, v___x_1355_);
v___x_1358_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_content_1348_);
v___x_1359_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1180_, v___x_1357_, v___x_1358_, v_a_1183_, v_a_1184_, v_a_1185_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1378_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1378_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1378_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1364_ = lean_unsigned_to_nat(1u);
v___x_1365_ = lean_mk_empty_array_with_capacity(v___x_1364_);
v___x_1366_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1367_ = lean_string_append(v___x_1366_, v_url_1349_);
lean_dec_ref(v_url_1349_);
v___x_1368_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1369_ = lean_string_append(v___x_1367_, v___x_1368_);
v___x_1370_ = lean_array_push(v___x_1365_, v___x_1369_);
v___x_1371_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_1372_ = lean_array_push(v___x_1371_, v_a_1360_);
v___x_1373_ = lean_array_push(v___x_1372_, v___x_1370_);
v___x_1374_ = l_Lean_Doc_joinInlines(v___x_1373_);
lean_dec_ref(v___x_1373_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1374_);
v___x_1376_ = v___x_1362_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
lean_dec_ref(v_url_1349_);
return v___x_1359_;
}
}
}
}
else
{
lean_object* v_content_1381_; lean_object* v___x_1382_; size_t v_sz_1383_; size_t v___x_1384_; lean_object* v___x_4335__overap_1385_; lean_object* v___x_1386_; 
v_content_1381_ = lean_ctor_get(v_x_1182_, 0);
lean_inc_ref(v_content_1381_);
lean_dec_ref_known(v_x_1182_, 2);
v___x_1382_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1382_, 0, v_inst_1180_);
lean_closure_set(v___x_1382_, 1, v_x_1181_);
v_sz_1383_ = lean_array_size(v_content_1381_);
v___x_1384_ = ((size_t)0ULL);
v___x_4335__overap_1385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1211_, v___x_1382_, v_sz_1383_, v___x_1384_, v_content_1381_);
lean_inc(v_a_1185_);
lean_inc_ref(v_a_1184_);
lean_inc(v_a_1183_);
v___x_1386_ = lean_apply_4(v___x_4335__overap_1385_, v_a_1183_, v_a_1184_, v_a_1185_, lean_box(0));
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1395_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = l_Lean_Doc_joinInlines(v_a_1387_);
lean_dec(v_a_1387_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1391_);
v___x_1393_ = v___x_1389_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
v_a_1396_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1386_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1386_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
case 7:
{
lean_object* v_name_1404_; lean_object* v_content_1405_; lean_object* v___x_1406_; size_t v_sz_1407_; size_t v___x_1408_; lean_object* v___x_4338__overap_1409_; lean_object* v___x_1410_; 
v_name_1404_ = lean_ctor_get(v_x_1182_, 0);
lean_inc_ref(v_name_1404_);
v_content_1405_ = lean_ctor_get(v_x_1182_, 1);
lean_inc_ref(v_content_1405_);
lean_dec_ref_known(v_x_1182_, 2);
v___x_1406_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1406_, 0, v_inst_1180_);
lean_closure_set(v___x_1406_, 1, v_x_1181_);
v_sz_1407_ = lean_array_size(v_content_1405_);
v___x_1408_ = ((size_t)0ULL);
v___x_4338__overap_1409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1211_, v___x_1406_, v_sz_1407_, v___x_1408_, v_content_1405_);
lean_inc(v_a_1185_);
lean_inc_ref(v_a_1184_);
lean_inc(v_a_1183_);
v___x_1410_ = lean_apply_4(v___x_4338__overap_1409_, v_a_1183_, v_a_1184_, v_a_1185_, lean_box(0));
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1412_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_1413_ = l_Lean_Doc_joinInlines(v_a_1411_);
lean_dec(v_a_1411_);
v___x_1414_ = lean_array_to_list(v___x_1413_);
v___x_1415_ = l_String_intercalate(v___x_1412_, v___x_1414_);
lean_inc_ref(v_name_1404_);
v___x_1416_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_1404_, v___x_1415_, v_a_1183_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1430_; 
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v___x_1416_, 0);
lean_dec(v_unused_1431_);
v___x_1418_ = v___x_1416_;
v_isShared_1419_ = v_isSharedCheck_1430_;
goto v_resetjp_1417_;
}
else
{
lean_dec(v___x_1416_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1430_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1420_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_1421_ = lean_string_append(v___x_1420_, v_name_1404_);
lean_dec_ref(v_name_1404_);
v___x_1422_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_1423_ = lean_string_append(v___x_1421_, v___x_1422_);
v___x_1424_ = lean_unsigned_to_nat(1u);
v___x_1425_ = lean_mk_empty_array_with_capacity(v___x_1424_);
v___x_1426_ = lean_array_push(v___x_1425_, v___x_1423_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1426_);
v___x_1428_ = v___x_1418_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec_ref(v_name_1404_);
v_a_1432_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1416_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1416_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec_ref(v_name_1404_);
v_a_1440_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1410_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1410_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
case 8:
{
lean_object* v_alt_1448_; lean_object* v_url_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_dec_ref(v___x_1211_);
lean_dec_ref(v_x_1181_);
lean_dec_ref(v_inst_1180_);
v_alt_1448_ = lean_ctor_get(v_x_1182_, 0);
lean_inc_ref(v_alt_1448_);
v_url_1449_ = lean_ctor_get(v_x_1182_, 1);
lean_inc_ref(v_url_1449_);
lean_dec_ref_known(v_x_1182_, 2);
v___x_1450_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_1451_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1448_);
lean_dec_ref(v_alt_1448_);
v___x_1452_ = lean_string_append(v___x_1450_, v___x_1451_);
lean_dec_ref(v___x_1451_);
v___x_1453_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1454_ = lean_string_append(v___x_1452_, v___x_1453_);
v___x_1455_ = lean_string_append(v___x_1454_, v_url_1449_);
lean_dec_ref(v_url_1449_);
v___x_1456_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1457_ = lean_string_append(v___x_1455_, v___x_1456_);
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1459_ = lean_mk_empty_array_with_capacity(v___x_1458_);
v___x_1460_ = lean_array_push(v___x_1459_, v___x_1457_);
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
return v___x_1461_;
}
case 9:
{
lean_object* v_content_1462_; lean_object* v___x_1463_; size_t v_sz_1464_; size_t v___x_1465_; lean_object* v___x_4341__overap_1466_; lean_object* v___x_1467_; 
v_content_1462_ = lean_ctor_get(v_x_1182_, 0);
lean_inc_ref(v_content_1462_);
lean_dec_ref_known(v_x_1182_, 1);
v___x_1463_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1463_, 0, v_inst_1180_);
lean_closure_set(v___x_1463_, 1, v_x_1181_);
v_sz_1464_ = lean_array_size(v_content_1462_);
v___x_1465_ = ((size_t)0ULL);
v___x_4341__overap_1466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1211_, v___x_1463_, v_sz_1464_, v___x_1465_, v_content_1462_);
lean_inc(v_a_1185_);
lean_inc_ref(v_a_1184_);
lean_inc(v_a_1183_);
v___x_1467_ = lean_apply_4(v___x_4341__overap_1466_, v_a_1183_, v_a_1184_, v_a_1185_, lean_box(0));
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1476_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = l_Lean_Doc_joinInlines(v_a_1468_);
lean_dec(v_a_1468_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
v_a_1477_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1467_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1467_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
default: 
{
lean_object* v_container_1485_; lean_object* v_content_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec_ref(v___x_1211_);
v_container_1485_ = lean_ctor_get(v_x_1182_, 0);
lean_inc(v_container_1485_);
v_content_1486_ = lean_ctor_get(v_x_1182_, 1);
lean_inc_ref(v_content_1486_);
lean_dec_ref_known(v_x_1182_, 2);
lean_inc_ref(v_inst_1180_);
v___x_1487_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1487_, 0, v_inst_1180_);
lean_closure_set(v___x_1487_, 1, v_x_1181_);
lean_inc(v_a_1185_);
lean_inc_ref(v_a_1184_);
lean_inc(v_a_1183_);
v___x_1488_ = lean_apply_7(v_inst_1180_, v___x_1487_, v_container_1485_, v_content_1486_, v_a_1183_, v_a_1184_, v_a_1185_, lean_box(0));
return v___x_1488_;
}
}
v___jp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = l_Lean_Doc_joinInlines(v_pieces_1188_);
lean_dec_ref(v_pieces_1188_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
v___jp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = l_Lean_Doc_joinInlines(v_pieces_1192_);
lean_dec_ref(v_pieces_1192_);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1489_, lean_object* v_inst_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1490_, v_x_1491_, v_x_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object* v_i_1498_, lean_object* v_inst_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(v_i_1498_, v_inst_1499_, v_x_1500_, v_x_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1514_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1507_, v___x_1513_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object* v_inst_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(v_inst_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1522_, lean_object* v_inst_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1530_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1523_, v___x_1529_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object* v_i_1531_, lean_object* v_inst_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(v_i_1531_, v_inst_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1540_, 0, lean_box(0));
lean_closure_set(v___x_1540_, 1, v_inst_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1541_, lean_object* v_inst_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1543_, 0, lean_box(0));
lean_closure_set(v___x_1543_, 1, v_inst_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(uint32_t v___x_1544_, lean_object* v_s_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_string_push(v_s_1545_, v___x_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object* v___x_1547_, lean_object* v_s_1548_){
_start:
{
uint32_t v___x_2710__boxed_1549_; lean_object* v_res_1550_; 
v___x_2710__boxed_1549_ = lean_unbox_uint32(v___x_1547_);
lean_dec(v___x_1547_);
v_res_1550_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v___x_2710__boxed_1549_, v_s_1548_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed(lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v___x_1555_, lean_object* v_item_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(v_inst_1553_, v_inst_1554_, v___x_1555_, v_item_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
return v_res_1561_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___f_1564_; 
v___x_1563_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___f_1564_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1564_, 0, v___x_1563_);
return v___f_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1565_, lean_object* v_inst_1566_, lean_object* v___x_1567_, lean_object* v___x_1568_, lean_object* v_a_1569_, lean_object* v_x_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; size_t v_sz_1577_; size_t v___x_1578_; lean_object* v___x_2643__overap_1579_; lean_object* v___x_1580_; 
v___x_1576_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1576_, 0, v_inst_1565_);
lean_closure_set(v___x_1576_, 1, v_inst_1566_);
v_sz_1577_ = lean_array_size(v_a_1569_);
v___x_1578_ = ((size_t)0ULL);
v___x_2643__overap_1579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1567_, v___x_1576_, v_sz_1577_, v___x_1578_, v_a_1569_);
lean_inc(v___y_1574_);
lean_inc_ref(v___y_1573_);
lean_inc(v___y_1572_);
v___x_1580_ = lean_apply_4(v___x_2643__overap_1579_, v___y_1572_, v___y_1573_, v___y_1574_, lean_box(0));
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1609_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1609_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1609_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_fst_1585_; lean_object* v_snd_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1608_; 
v_fst_1585_ = lean_ctor_get(v___y_1571_, 0);
v_snd_1586_ = lean_ctor_get(v___y_1571_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___y_1571_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1588_ = v___y_1571_;
v_isShared_1589_ = v_isSharedCheck_1608_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_snd_1586_);
lean_inc(v_fst_1585_);
lean_dec(v___y_1571_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1608_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___f_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
lean_inc(v_snd_1586_);
v___x_1590_ = l_Nat_reprFast(v_snd_1586_);
v___x_1591_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_1592_ = lean_string_append(v___x_1590_, v___x_1591_);
v___x_1593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_1594_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1);
v___x_1595_ = lean_string_utf8_byte_size(v___x_1592_);
v___x_1596_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1594_, v___x_1595_, v___x_1593_);
v___x_1597_ = l_Lean_Doc_joinBlocks(v_a_1581_);
lean_dec(v_a_1581_);
v___x_1598_ = l_Lean_Doc_prefixListLines(v___x_1592_, v___x_1596_, v___x_1597_);
v___x_1599_ = lean_array_push(v_fst_1585_, v___x_1598_);
v___x_1600_ = lean_nat_add(v_snd_1586_, v___x_1568_);
lean_dec(v_snd_1586_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v___x_1600_);
lean_ctor_set(v___x_1588_, 0, v___x_1599_);
v___x_1602_ = v___x_1588_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1603_);
v___x_1605_ = v___x_1583_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec_ref(v___y_1571_);
v_a_1610_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1580_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1580_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v___x_1620_, lean_object* v___x_1621_, lean_object* v_a_1622_, lean_object* v_x_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1618_, v_inst_1619_, v___x_1620_, v___x_1621_, v_a_1622_, v_x_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec(v___x_1621_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1635_, lean_object* v_inst_1636_, lean_object* v___x_1637_, lean_object* v_item_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v___x_1643_; lean_object* v_term_1644_; lean_object* v_desc_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1643_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_1644_ = lean_ctor_get(v_item_1638_, 0);
lean_inc_ref(v_term_1644_);
v_desc_1645_ = lean_ctor_get(v_item_1638_, 1);
lean_inc_ref(v_desc_1645_);
lean_dec_ref(v_item_1638_);
v___x_1646_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_term_1644_);
lean_inc_ref(v_inst_1635_);
v___x_1647_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1635_, v___x_1643_, v___x_1646_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; size_t v_sz_1650_; size_t v___x_1651_; lean_object* v___x_2679__overap_1652_; lean_object* v___x_1653_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1649_, 0, v_inst_1635_);
lean_closure_set(v___x_1649_, 1, v_inst_1636_);
v_sz_1650_ = lean_array_size(v_desc_1645_);
v___x_1651_ = ((size_t)0ULL);
lean_inc_ref(v_desc_1645_);
v___x_2679__overap_1652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1637_, v___x_1649_, v_sz_1650_, v___x_1651_, v_desc_1645_);
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1640_);
lean_inc(v___y_1639_);
v___x_1653_ = lean_apply_4(v___x_2679__overap_1652_, v___y_1639_, v___y_1640_, v___y_1641_, lean_box(0));
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1681_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1681_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1681_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___y_1659_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_mk_empty_array_with_capacity(v___x_1666_);
v___x_1668_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_1669_ = lean_unsigned_to_nat(2u);
v___x_1670_ = lean_mk_empty_array_with_capacity(v___x_1669_);
v___x_1671_ = lean_array_push(v___x_1670_, v_a_1648_);
v___x_1672_ = lean_array_push(v___x_1671_, v___x_1668_);
v___x_1673_ = l_Lean_Doc_joinInlines(v___x_1672_);
lean_dec_ref(v___x_1672_);
v___x_1674_ = lean_array_get_size(v_desc_1645_);
lean_dec_ref(v_desc_1645_);
v___x_1675_ = lean_nat_dec_le(v___x_1674_, v___x_1666_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = lean_array_push(v___x_1667_, v___x_1673_);
v___x_1677_ = l_Array_append___redArg(v___x_1676_, v_a_1654_);
lean_dec(v_a_1654_);
v___x_1678_ = l_Lean_Doc_joinBlocks(v___x_1677_);
lean_dec_ref(v___x_1677_);
v___y_1659_ = v___x_1678_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec_ref(v___x_1667_);
v___x_1679_ = l_Lean_Doc_joinBlocks(v_a_1654_);
lean_dec(v_a_1654_);
v___x_1680_ = l_Array_append___redArg(v___x_1673_, v___x_1679_);
lean_dec_ref(v___x_1679_);
v___y_1659_ = v___x_1680_;
goto v___jp_1658_;
}
v___jp_1658_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1660_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1661_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1662_ = l_Lean_Doc_prefixListLines(v___x_1660_, v___x_1661_, v___y_1659_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1662_);
v___x_1664_ = v___x_1656_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v_a_1648_);
lean_dec_ref(v_desc_1645_);
v_a_1682_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1653_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1653_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
lean_dec_ref(v_desc_1645_);
lean_dec_ref(v___x_1637_);
lean_dec_ref(v_inst_1636_);
lean_dec_ref(v_inst_1635_);
return v___x_1647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v___x_1692_, lean_object* v_item_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1690_, v_inst_1691_, v___x_1692_, v_item_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1700_, lean_object* v_inst_1701_, lean_object* v_x_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1707_; lean_object* v_toApplicative_1708_; lean_object* v_toFunctor_1709_; lean_object* v_toSeq_1710_; lean_object* v_toSeqLeft_1711_; lean_object* v_toSeqRight_1712_; lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___f_1715_; lean_object* v___f_1716_; lean_object* v___x_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___f_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1707_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1708_ = lean_ctor_get(v___x_1707_, 0);
v_toFunctor_1709_ = lean_ctor_get(v_toApplicative_1708_, 0);
v_toSeq_1710_ = lean_ctor_get(v_toApplicative_1708_, 2);
v_toSeqLeft_1711_ = lean_ctor_get(v_toApplicative_1708_, 3);
v_toSeqRight_1712_ = lean_ctor_get(v_toApplicative_1708_, 4);
v___f_1713_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1714_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1709_, 2);
v___f_1715_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1715_, 0, v_toFunctor_1709_);
v___f_1716_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1716_, 0, v_toFunctor_1709_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___f_1715_);
lean_ctor_set(v___x_1717_, 1, v___f_1716_);
lean_inc(v_toSeqRight_1712_);
v___f_1718_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1718_, 0, v_toSeqRight_1712_);
lean_inc(v_toSeqLeft_1711_);
v___f_1719_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1719_, 0, v_toSeqLeft_1711_);
lean_inc(v_toSeq_1710_);
v___f_1720_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1720_, 0, v_toSeq_1710_);
v___x_1721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1717_);
lean_ctor_set(v___x_1721_, 1, v___f_1713_);
lean_ctor_set(v___x_1721_, 2, v___f_1720_);
lean_ctor_set(v___x_1721_, 3, v___f_1719_);
lean_ctor_set(v___x_1721_, 4, v___f_1718_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v___f_1714_);
v___x_1723_ = l_StateRefT_x27_instMonad___redArg(v___x_1722_);
switch(lean_obj_tag(v_x_1702_))
{
case 0:
{
lean_object* v_contents_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1733_; 
lean_dec_ref(v___x_1723_);
lean_dec_ref(v_inst_1701_);
v_contents_1724_ = lean_ctor_get(v_x_1702_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_x_1702_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1726_ = v_x_1702_;
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_contents_1724_);
lean_dec(v_x_1702_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1728_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_1727_ == 0)
{
lean_ctor_set_tag(v___x_1726_, 9);
v___x_1730_ = v___x_1726_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_contents_1724_);
v___x_1730_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; 
v___x_1731_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1700_, v___x_1728_, v___x_1730_, v_a_1703_, v_a_1704_, v_a_1705_);
return v___x_1731_;
}
}
}
case 1:
{
lean_object* v_content_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref(v___x_1723_);
lean_dec_ref(v_inst_1701_);
lean_dec_ref(v_inst_1700_);
v_content_1734_ = lean_ctor_get(v_x_1702_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_x_1702_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1736_ = v_x_1702_;
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_content_1734_);
lean_dec(v_x_1702_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_1734_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set_tag(v___x_1736_, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
case 2:
{
lean_object* v_items_1743_; lean_object* v___f_1744_; size_t v_sz_1745_; size_t v___x_1746_; lean_object* v___x_2579__overap_1747_; lean_object* v___x_1748_; 
v_items_1743_ = lean_ctor_get(v_x_1702_, 0);
lean_inc_ref(v_items_1743_);
lean_dec_ref_known(v_x_1702_, 1);
lean_inc_ref(v___x_1723_);
v___f_1744_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1744_, 0, v_inst_1700_);
lean_closure_set(v___f_1744_, 1, v_inst_1701_);
lean_closure_set(v___f_1744_, 2, v___x_1723_);
v_sz_1745_ = lean_array_size(v_items_1743_);
v___x_1746_ = ((size_t)0ULL);
v___x_2579__overap_1747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1723_, v___f_1744_, v_sz_1745_, v___x_1746_, v_items_1743_);
lean_inc(v_a_1705_);
lean_inc_ref(v_a_1704_);
lean_inc(v_a_1703_);
v___x_1748_ = lean_apply_4(v___x_2579__overap_1747_, v_a_1703_, v_a_1704_, v_a_1705_, lean_box(0));
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1757_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1757_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1757_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = l_Lean_Doc_joinBlocks(v_a_1749_);
lean_dec(v_a_1749_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1753_);
v___x_1755_ = v___x_1751_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
v_a_1758_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1748_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1748_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
case 3:
{
lean_object* v_start_1766_; lean_object* v_items_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1803_; 
v_start_1766_ = lean_ctor_get(v_x_1702_, 0);
v_items_1767_ = lean_ctor_get(v_x_1702_, 1);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_x_1702_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1769_ = v_x_1702_;
v_isShared_1770_ = v_isSharedCheck_1803_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_items_1767_);
lean_inc(v_start_1766_);
lean_dec(v_x_1702_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1803_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v_out_1771_; lean_object* v___x_1772_; lean_object* v___f_1773_; lean_object* v___y_1775_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v_out_1771_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1772_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_1723_);
v___f_1773_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1773_, 0, v_inst_1700_);
lean_closure_set(v___f_1773_, 1, v_inst_1701_);
lean_closure_set(v___f_1773_, 2, v___x_1723_);
lean_closure_set(v___f_1773_, 3, v___x_1772_);
v___x_1801_ = l_Int_toNat(v_start_1766_);
lean_dec(v_start_1766_);
v___x_1802_ = lean_nat_dec_le(v___x_1772_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_dec(v___x_1801_);
v___y_1775_ = v___x_1772_;
goto v___jp_1774_;
}
else
{
v___y_1775_ = v___x_1801_;
goto v___jp_1774_;
}
v___jp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set_tag(v___x_1769_, 0);
lean_ctor_set(v___x_1769_, 1, v___y_1775_);
lean_ctor_set(v___x_1769_, 0, v_out_1771_);
v___x_1777_ = v___x_1769_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_out_1771_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v___y_1775_);
v___x_1777_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
size_t v_sz_1778_; size_t v___x_1779_; lean_object* v___x_2395__overap_1780_; lean_object* v___x_1781_; 
v_sz_1778_ = lean_array_size(v_items_1767_);
v___x_1779_ = ((size_t)0ULL);
v___x_2395__overap_1780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1723_, v_items_1767_, v___f_1773_, v_sz_1778_, v___x_1779_, v___x_1777_);
lean_inc(v_a_1705_);
lean_inc_ref(v_a_1704_);
lean_inc(v_a_1703_);
v___x_1781_ = lean_apply_4(v___x_2395__overap_1780_, v_a_1703_, v_a_1704_, v_a_1705_, lean_box(0));
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1791_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1791_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1791_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v_fst_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v_fst_1786_ = lean_ctor_get(v_a_1782_, 0);
lean_inc(v_fst_1786_);
lean_dec(v_a_1782_);
v___x_1787_ = l_Lean_Doc_joinBlocks(v_fst_1786_);
lean_dec(v_fst_1786_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1787_);
v___x_1789_ = v___x_1784_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
v_a_1792_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1781_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1781_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_1804_; lean_object* v___f_1805_; size_t v_sz_1806_; size_t v___x_1807_; lean_object* v___x_2585__overap_1808_; lean_object* v___x_1809_; 
v_items_1804_ = lean_ctor_get(v_x_1702_, 0);
lean_inc_ref(v_items_1804_);
lean_dec_ref_known(v_x_1702_, 1);
lean_inc_ref(v___x_1723_);
v___f_1805_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 8, 3);
lean_closure_set(v___f_1805_, 0, v_inst_1700_);
lean_closure_set(v___f_1805_, 1, v_inst_1701_);
lean_closure_set(v___f_1805_, 2, v___x_1723_);
v_sz_1806_ = lean_array_size(v_items_1804_);
v___x_1807_ = ((size_t)0ULL);
v___x_2585__overap_1808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1723_, v___f_1805_, v_sz_1806_, v___x_1807_, v_items_1804_);
lean_inc(v_a_1705_);
lean_inc_ref(v_a_1704_);
lean_inc(v_a_1703_);
v___x_1809_ = lean_apply_4(v___x_2585__overap_1808_, v_a_1703_, v_a_1704_, v_a_1705_, lean_box(0));
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1818_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1818_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1818_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = l_Lean_Doc_joinBlocks(v_a_1810_);
lean_dec(v_a_1810_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1814_);
v___x_1816_ = v___x_1812_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
v_a_1819_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1809_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1809_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
case 5:
{
lean_object* v_items_1827_; lean_object* v___x_1828_; size_t v_sz_1829_; size_t v___x_1830_; lean_object* v___x_2588__overap_1831_; lean_object* v___x_1832_; 
v_items_1827_ = lean_ctor_get(v_x_1702_, 0);
lean_inc_ref(v_items_1827_);
lean_dec_ref_known(v_x_1702_, 1);
v___x_1828_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1828_, 0, v_inst_1700_);
lean_closure_set(v___x_1828_, 1, v_inst_1701_);
v_sz_1829_ = lean_array_size(v_items_1827_);
v___x_1830_ = ((size_t)0ULL);
v___x_2588__overap_1831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1723_, v___x_1828_, v_sz_1829_, v___x_1830_, v_items_1827_);
lean_inc(v_a_1705_);
lean_inc_ref(v_a_1704_);
lean_inc(v_a_1703_);
v___x_1832_ = lean_apply_4(v___x_2588__overap_1831_, v_a_1703_, v_a_1704_, v_a_1705_, lean_box(0));
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1843_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1843_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1843_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1837_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_1838_ = l_Lean_Doc_joinBlocks(v_a_1833_);
lean_dec(v_a_1833_);
v___x_1839_ = l_Lean_Doc_prefixLines(v___x_1837_, v___x_1838_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1839_);
v___x_1841_ = v___x_1835_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
v_a_1844_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1832_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1832_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
case 6:
{
lean_object* v_content_1852_; lean_object* v___x_1853_; size_t v_sz_1854_; size_t v___x_1855_; lean_object* v___x_2591__overap_1856_; lean_object* v___x_1857_; 
v_content_1852_ = lean_ctor_get(v_x_1702_, 0);
lean_inc_ref(v_content_1852_);
lean_dec_ref_known(v_x_1702_, 1);
v___x_1853_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1853_, 0, v_inst_1700_);
lean_closure_set(v___x_1853_, 1, v_inst_1701_);
v_sz_1854_ = lean_array_size(v_content_1852_);
v___x_1855_ = ((size_t)0ULL);
v___x_2591__overap_1856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1723_, v___x_1853_, v_sz_1854_, v___x_1855_, v_content_1852_);
lean_inc(v_a_1705_);
lean_inc_ref(v_a_1704_);
lean_inc(v_a_1703_);
v___x_1857_ = lean_apply_4(v___x_2591__overap_1856_, v_a_1703_, v_a_1704_, v_a_1705_, lean_box(0));
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1866_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1862_ = l_Lean_Doc_joinBlocks(v_a_1858_);
lean_dec(v_a_1858_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1862_);
v___x_1864_ = v___x_1860_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_a_1867_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1857_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1857_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
default: 
{
lean_object* v_container_1875_; lean_object* v_content_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_dec_ref(v___x_1723_);
v_container_1875_ = lean_ctor_get(v_x_1702_, 0);
lean_inc(v_container_1875_);
v_content_1876_ = lean_ctor_get(v_x_1702_, 1);
lean_inc_ref(v_content_1876_);
lean_dec_ref_known(v_x_1702_, 2);
v___x_1877_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc_ref(v_inst_1700_);
v___x_1878_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed), 8, 3);
lean_closure_set(v___x_1878_, 0, lean_box(0));
lean_closure_set(v___x_1878_, 1, v_inst_1700_);
lean_closure_set(v___x_1878_, 2, v___x_1877_);
lean_inc_ref(v_inst_1701_);
v___x_1879_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1879_, 0, v_inst_1700_);
lean_closure_set(v___x_1879_, 1, v_inst_1701_);
lean_inc(v_a_1705_);
lean_inc_ref(v_a_1704_);
lean_inc(v_a_1703_);
v___x_1880_ = lean_apply_8(v_inst_1701_, v___x_1878_, v___x_1879_, v_container_1875_, v_content_1876_, v_a_1703_, v_a_1704_, v_a_1705_, lean_box(0));
return v___x_1880_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed(lean_object* v_inst_1881_, lean_object* v_inst_1882_, lean_object* v_x_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1881_, v_inst_1882_, v_x_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v___x_1891_, lean_object* v_item_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; size_t v_sz_1898_; size_t v___x_1899_; lean_object* v___x_2618__overap_1900_; lean_object* v___x_1901_; 
v___x_1897_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1897_, 0, v_inst_1889_);
lean_closure_set(v___x_1897_, 1, v_inst_1890_);
v_sz_1898_ = lean_array_size(v_item_1892_);
v___x_1899_ = ((size_t)0ULL);
v___x_2618__overap_1900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1891_, v___x_1897_, v_sz_1898_, v___x_1899_, v_item_1892_);
lean_inc(v___y_1895_);
lean_inc_ref(v___y_1894_);
lean_inc(v___y_1893_);
v___x_1901_ = lean_apply_4(v___x_2618__overap_1900_, v___y_1893_, v___y_1894_, v___y_1895_, lean_box(0));
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1913_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1913_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1913_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1906_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1907_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1908_ = l_Lean_Doc_joinBlocks(v_a_1902_);
lean_dec(v_a_1902_);
v___x_1909_ = l_Lean_Doc_prefixListLines(v___x_1906_, v___x_1907_, v___x_1908_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1909_);
v___x_1911_ = v___x_1904_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
v_a_1914_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1901_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1901_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1922_, lean_object* v_b_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_x_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1924_, v_inst_1925_, v_x_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object* v_i_1932_, lean_object* v_b_1933_, lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_x_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(v_i_1932_, v_b_1933_, v_inst_1934_, v_inst_1935_, v_x_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1942_, v_inst_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1950_, v_inst_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1958_, lean_object* v_b_1959_, lean_object* v_inst_1960_, lean_object* v_inst_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1960_, v_inst_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1968_, lean_object* v_b_1969_, lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1968_, v_b_1969_, v_inst_1970_, v_inst_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1978_, lean_object* v_inst_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_1980_, 0, lean_box(0));
lean_closure_set(v___x_1980_, 1, lean_box(0));
lean_closure_set(v___x_1980_, 2, v_inst_1978_);
lean_closure_set(v___x_1980_, 3, v_inst_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1981_, lean_object* v_b_1982_, lean_object* v_inst_1983_, lean_object* v_inst_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_1985_, 0, lean_box(0));
lean_closure_set(v___x_1985_, 1, lean_box(0));
lean_closure_set(v___x_1985_, 2, v_inst_1983_);
lean_closure_set(v___x_1985_, 3, v_inst_1984_);
return v___x_1985_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = 35;
v___x_1987_ = lean_box_uint32(v___x_1986_);
return v___x_1987_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___f_1989_; 
v___x_1988_ = l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1989_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1989_, 0, v___x_1988_);
return v___f_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1990_, lean_object* v_inst_1991_, lean_object* v_level_1992_, lean_object* v_part_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_Doc_partMarkdown___redArg(v_inst_1990_, v_inst_1991_, v_level_1992_, v_part_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
lean_dec(v_a_1994_);
lean_dec(v_level_1992_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg(lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_level_2001_, lean_object* v_part_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v___x_2007_; lean_object* v_toApplicative_2008_; lean_object* v_toFunctor_2009_; lean_object* v_toSeq_2010_; lean_object* v_toSeqLeft_2011_; lean_object* v_toSeqRight_2012_; lean_object* v___f_2013_; lean_object* v___f_2014_; lean_object* v___f_2015_; lean_object* v___f_2016_; lean_object* v___x_2017_; lean_object* v___f_2018_; lean_object* v___f_2019_; lean_object* v___f_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v_title_2024_; lean_object* v_content_2025_; lean_object* v_subParts_2026_; lean_object* v___x_2027_; size_t v_sz_2028_; size_t v___x_2029_; lean_object* v___x_680__overap_2030_; lean_object* v___x_2031_; 
v___x_2007_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2008_ = lean_ctor_get(v___x_2007_, 0);
v_toFunctor_2009_ = lean_ctor_get(v_toApplicative_2008_, 0);
v_toSeq_2010_ = lean_ctor_get(v_toApplicative_2008_, 2);
v_toSeqLeft_2011_ = lean_ctor_get(v_toApplicative_2008_, 3);
v_toSeqRight_2012_ = lean_ctor_get(v_toApplicative_2008_, 4);
v___f_2013_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2014_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2009_, 2);
v___f_2015_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2015_, 0, v_toFunctor_2009_);
v___f_2016_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2016_, 0, v_toFunctor_2009_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___f_2015_);
lean_ctor_set(v___x_2017_, 1, v___f_2016_);
lean_inc(v_toSeqRight_2012_);
v___f_2018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2018_, 0, v_toSeqRight_2012_);
lean_inc(v_toSeqLeft_2011_);
v___f_2019_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2019_, 0, v_toSeqLeft_2011_);
lean_inc(v_toSeq_2010_);
v___f_2020_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2020_, 0, v_toSeq_2010_);
v___x_2021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2017_);
lean_ctor_set(v___x_2021_, 1, v___f_2013_);
lean_ctor_set(v___x_2021_, 2, v___f_2020_);
lean_ctor_set(v___x_2021_, 3, v___f_2019_);
lean_ctor_set(v___x_2021_, 4, v___f_2018_);
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
lean_ctor_set(v___x_2022_, 1, v___f_2014_);
v___x_2023_ = l_StateRefT_x27_instMonad___redArg(v___x_2022_);
v_title_2024_ = lean_ctor_get(v_part_2002_, 0);
lean_inc_ref(v_title_2024_);
v_content_2025_ = lean_ctor_get(v_part_2002_, 3);
lean_inc_ref(v_content_2025_);
v_subParts_2026_ = lean_ctor_get(v_part_2002_, 4);
lean_inc_ref(v_subParts_2026_);
lean_dec_ref(v_part_2002_);
lean_inc_ref(v_inst_1999_);
v___x_2027_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_2027_, 0, lean_box(0));
lean_closure_set(v___x_2027_, 1, v_inst_1999_);
v_sz_2028_ = lean_array_size(v_title_2024_);
v___x_2029_ = ((size_t)0ULL);
lean_inc_ref(v___x_2023_);
v___x_680__overap_2030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2023_, v___x_2027_, v_sz_2028_, v___x_2029_, v_title_2024_);
lean_inc(v_a_2005_);
lean_inc_ref(v_a_2004_);
lean_inc(v_a_2003_);
v___x_2031_ = lean_apply_4(v___x_680__overap_2030_, v_a_2003_, v_a_2004_, v_a_2005_, lean_box(0));
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; size_t v_sz_2034_; lean_object* v___x_683__overap_2035_; lean_object* v___x_2036_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
lean_inc_ref(v_inst_2000_);
lean_inc_ref(v_inst_1999_);
v___x_2033_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_2033_, 0, lean_box(0));
lean_closure_set(v___x_2033_, 1, lean_box(0));
lean_closure_set(v___x_2033_, 2, v_inst_1999_);
lean_closure_set(v___x_2033_, 3, v_inst_2000_);
v_sz_2034_ = lean_array_size(v_content_2025_);
lean_inc_ref(v___x_2023_);
v___x_683__overap_2035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2023_, v___x_2033_, v_sz_2034_, v___x_2029_, v_content_2025_);
lean_inc(v_a_2005_);
lean_inc_ref(v_a_2004_);
lean_inc(v_a_2003_);
v___x_2036_ = lean_apply_4(v___x_683__overap_2035_, v_a_2003_, v_a_2004_, v_a_2005_, lean_box(0));
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; lean_object* v___f_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; size_t v_sz_2044_; lean_object* v___x_686__overap_2045_; lean_object* v___x_2046_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_2039_ = lean_obj_once(&l_Lean_Doc_partMarkdown___redArg___closed__0, &l_Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_partMarkdown___redArg___closed__0);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_add(v_level_2001_, v___x_2040_);
lean_inc(v___x_2041_);
v___x_2042_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_2039_, v___x_2041_, v___x_2038_);
v___x_2043_ = lean_alloc_closure((void*)(l_Lean_Doc_partMarkdown___redArg___boxed), 8, 3);
lean_closure_set(v___x_2043_, 0, v_inst_1999_);
lean_closure_set(v___x_2043_, 1, v_inst_2000_);
lean_closure_set(v___x_2043_, 2, v___x_2041_);
v_sz_2044_ = lean_array_size(v_subParts_2026_);
v___x_686__overap_2045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2023_, v___x_2043_, v_sz_2044_, v___x_2029_, v_subParts_2026_);
lean_inc(v_a_2005_);
lean_inc_ref(v_a_2004_);
lean_inc(v_a_2003_);
v___x_2046_ = lean_apply_4(v___x_686__overap_2045_, v_a_2003_, v_a_2004_, v_a_2005_, lean_box(0));
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2065_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2065_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2065_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2051_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_2052_ = lean_string_append(v___x_2042_, v___x_2051_);
v___x_2053_ = lean_mk_empty_array_with_capacity(v___x_2040_);
lean_inc_ref_n(v___x_2053_, 2);
v___x_2054_ = lean_array_push(v___x_2053_, v___x_2052_);
v___x_2055_ = lean_array_push(v___x_2053_, v___x_2054_);
v___x_2056_ = l_Array_append___redArg(v___x_2055_, v_a_2032_);
lean_dec(v_a_2032_);
v___x_2057_ = l_Lean_Doc_joinInlines(v___x_2056_);
lean_dec_ref(v___x_2056_);
v___x_2058_ = lean_array_push(v___x_2053_, v___x_2057_);
v___x_2059_ = l_Array_append___redArg(v___x_2058_, v_a_2037_);
lean_dec(v_a_2037_);
v___x_2060_ = l_Array_append___redArg(v___x_2059_, v_a_2047_);
lean_dec(v_a_2047_);
v___x_2061_ = l_Lean_Doc_joinBlocks(v___x_2060_);
lean_dec_ref(v___x_2060_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2061_);
v___x_2063_ = v___x_2049_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v___x_2042_);
lean_dec(v_a_2037_);
lean_dec(v_a_2032_);
v_a_2066_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2046_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2046_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_a_2032_);
lean_dec_ref(v_subParts_2026_);
lean_dec_ref(v___x_2023_);
lean_dec_ref(v_inst_2000_);
lean_dec_ref(v_inst_1999_);
v_a_2074_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2036_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2036_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref(v_subParts_2026_);
lean_dec_ref(v_content_2025_);
lean_dec_ref(v___x_2023_);
lean_dec_ref(v_inst_2000_);
lean_dec_ref(v_inst_1999_);
v_a_2082_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2031_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2031_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown(lean_object* v_i_2090_, lean_object* v_b_2091_, lean_object* v_p_2092_, lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_level_2095_, lean_object* v_part_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2093_, v_inst_2094_, v_level_2095_, v_part_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___boxed(lean_object* v_i_2102_, lean_object* v_b_2103_, lean_object* v_p_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_level_2107_, lean_object* v_part_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_Doc_partMarkdown(v_i_2102_, v_b_2103_, v_p_2104_, v_inst_2105_, v_inst_2106_, v_level_2107_, v_part_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec(v_level_2107_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_part_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2114_, v_inst_2115_, v___x_2121_, v_part_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_2123_, lean_object* v_inst_2124_, lean_object* v_part_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_2123_, v_inst_2124_, v_part_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_2131_, lean_object* v_inst_2132_){
_start:
{
lean_object* v___f_2133_; 
v___f_2133_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2133_, 0, v_inst_2131_);
lean_closure_set(v___f_2133_, 1, v_inst_2132_);
return v___f_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_2134_, lean_object* v_b_2135_, lean_object* v_p_2136_, lean_object* v_inst_2137_, lean_object* v_inst_2138_){
_start:
{
lean_object* v___f_2139_; 
v___f_2139_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2139_, 0, v_inst_2137_);
lean_closure_set(v___f_2139_, 1, v_inst_2138_);
return v___f_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg(lean_object* v_inst_2140_, lean_object* v_f_2141_, lean_object* v_go_2142_, lean_object* v_val_2143_, lean_object* v_content_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v___x_2149_; lean_object* v_toApplicative_2150_; lean_object* v_toFunctor_2151_; lean_object* v_toSeq_2152_; lean_object* v_toSeqLeft_2153_; lean_object* v_toSeqRight_2154_; lean_object* v___f_2155_; lean_object* v___f_2156_; lean_object* v___f_2157_; lean_object* v___f_2158_; lean_object* v___x_2159_; lean_object* v___f_2160_; lean_object* v___f_2161_; lean_object* v___f_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2149_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2150_ = lean_ctor_get(v___x_2149_, 0);
v_toFunctor_2151_ = lean_ctor_get(v_toApplicative_2150_, 0);
v_toSeq_2152_ = lean_ctor_get(v_toApplicative_2150_, 2);
v_toSeqLeft_2153_ = lean_ctor_get(v_toApplicative_2150_, 3);
v_toSeqRight_2154_ = lean_ctor_get(v_toApplicative_2150_, 4);
v___f_2155_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2156_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2151_, 2);
v___f_2157_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2157_, 0, v_toFunctor_2151_);
v___f_2158_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2158_, 0, v_toFunctor_2151_);
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___f_2157_);
lean_ctor_set(v___x_2159_, 1, v___f_2158_);
lean_inc(v_toSeqRight_2154_);
v___f_2160_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2160_, 0, v_toSeqRight_2154_);
lean_inc(v_toSeqLeft_2153_);
v___f_2161_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2161_, 0, v_toSeqLeft_2153_);
lean_inc(v_toSeq_2152_);
v___f_2162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2162_, 0, v_toSeq_2152_);
v___x_2163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2159_);
lean_ctor_set(v___x_2163_, 1, v___f_2155_);
lean_ctor_set(v___x_2163_, 2, v___f_2162_);
lean_ctor_set(v___x_2163_, 3, v___f_2161_);
lean_ctor_set(v___x_2163_, 4, v___f_2160_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
lean_ctor_set(v___x_2164_, 1, v___f_2156_);
v___x_2165_ = l_StateRefT_x27_instMonad___redArg(v___x_2164_);
v___x_2166_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2143_, v_inst_2140_);
if (lean_obj_tag(v___x_2166_) == 0)
{
size_t v_sz_2167_; size_t v___x_2168_; lean_object* v___x_288__overap_2169_; lean_object* v___x_2170_; 
lean_dec_ref(v_f_2141_);
v_sz_2167_ = lean_array_size(v_content_2144_);
v___x_2168_ = ((size_t)0ULL);
v___x_288__overap_2169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2165_, v_go_2142_, v_sz_2167_, v___x_2168_, v_content_2144_);
lean_inc(v_a_2147_);
lean_inc_ref(v_a_2146_);
lean_inc(v_a_2145_);
v___x_2170_ = lean_apply_4(v___x_288__overap_2169_, v_a_2145_, v_a_2146_, v_a_2147_, lean_box(0));
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2179_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2179_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2179_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
v___x_2175_ = l_Lean_Doc_joinInlines(v_a_2171_);
lean_dec(v_a_2171_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2175_);
v___x_2177_ = v___x_2173_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
v_a_2180_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2170_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2170_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v_val_2188_; lean_object* v___x_2189_; 
lean_dec_ref(v___x_2165_);
v_val_2188_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_val_2188_);
lean_dec_ref_known(v___x_2166_, 1);
lean_inc(v_a_2147_);
lean_inc_ref(v_a_2146_);
lean_inc(v_a_2145_);
v___x_2189_ = lean_apply_7(v_f_2141_, v_go_2142_, v_val_2188_, v_content_2144_, v_a_2145_, v_a_2146_, v_a_2147_, lean_box(0));
return v___x_2189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg___boxed(lean_object* v_inst_2190_, lean_object* v_f_2191_, lean_object* v_go_2192_, lean_object* v_val_2193_, lean_object* v_content_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2190_, v_f_2191_, v_go_2192_, v_val_2193_, v_content_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec(v_val_2193_);
lean_dec(v_inst_2190_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer(lean_object* v_00_u03b1_2200_, lean_object* v_inst_2201_, lean_object* v_f_2202_, lean_object* v_go_2203_, lean_object* v_val_2204_, lean_object* v_content_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2201_, v_f_2202_, v_go_2203_, v_val_2204_, v_content_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___boxed(lean_object* v_00_u03b1_2211_, lean_object* v_inst_2212_, lean_object* v_f_2213_, lean_object* v_go_2214_, lean_object* v_val_2215_, lean_object* v_content_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_Doc_mkInlineMdRenderer(v_00_u03b1_2211_, v_inst_2212_, v_f_2213_, v_go_2214_, v_val_2215_, v_content_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_val_2215_);
lean_dec(v_inst_2212_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg(lean_object* v_inst_2222_, lean_object* v_f_2223_, lean_object* v_goI_2224_, lean_object* v_goB_2225_, lean_object* v_val_2226_, lean_object* v_content_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v___x_2232_; lean_object* v_toApplicative_2233_; lean_object* v_toFunctor_2234_; lean_object* v_toSeq_2235_; lean_object* v_toSeqLeft_2236_; lean_object* v_toSeqRight_2237_; lean_object* v___f_2238_; lean_object* v___f_2239_; lean_object* v___f_2240_; lean_object* v___f_2241_; lean_object* v___x_2242_; lean_object* v___f_2243_; lean_object* v___f_2244_; lean_object* v___f_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2232_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2233_ = lean_ctor_get(v___x_2232_, 0);
v_toFunctor_2234_ = lean_ctor_get(v_toApplicative_2233_, 0);
v_toSeq_2235_ = lean_ctor_get(v_toApplicative_2233_, 2);
v_toSeqLeft_2236_ = lean_ctor_get(v_toApplicative_2233_, 3);
v_toSeqRight_2237_ = lean_ctor_get(v_toApplicative_2233_, 4);
v___f_2238_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2239_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2234_, 2);
v___f_2240_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2240_, 0, v_toFunctor_2234_);
v___f_2241_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2241_, 0, v_toFunctor_2234_);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___f_2240_);
lean_ctor_set(v___x_2242_, 1, v___f_2241_);
lean_inc(v_toSeqRight_2237_);
v___f_2243_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2243_, 0, v_toSeqRight_2237_);
lean_inc(v_toSeqLeft_2236_);
v___f_2244_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2244_, 0, v_toSeqLeft_2236_);
lean_inc(v_toSeq_2235_);
v___f_2245_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2245_, 0, v_toSeq_2235_);
v___x_2246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2242_);
lean_ctor_set(v___x_2246_, 1, v___f_2238_);
lean_ctor_set(v___x_2246_, 2, v___f_2245_);
lean_ctor_set(v___x_2246_, 3, v___f_2244_);
lean_ctor_set(v___x_2246_, 4, v___f_2243_);
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set(v___x_2247_, 1, v___f_2239_);
v___x_2248_ = l_StateRefT_x27_instMonad___redArg(v___x_2247_);
v___x_2249_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2226_, v_inst_2222_);
if (lean_obj_tag(v___x_2249_) == 0)
{
size_t v_sz_2250_; size_t v___x_2251_; lean_object* v___x_288__overap_2252_; lean_object* v___x_2253_; 
lean_dec_ref(v_goI_2224_);
lean_dec_ref(v_f_2223_);
v_sz_2250_ = lean_array_size(v_content_2227_);
v___x_2251_ = ((size_t)0ULL);
v___x_288__overap_2252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2248_, v_goB_2225_, v_sz_2250_, v___x_2251_, v_content_2227_);
lean_inc(v_a_2230_);
lean_inc_ref(v_a_2229_);
lean_inc(v_a_2228_);
v___x_2253_ = lean_apply_4(v___x_288__overap_2252_, v_a_2228_, v_a_2229_, v_a_2230_, lean_box(0));
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2262_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2262_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2262_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2258_ = l_Lean_Doc_joinBlocks(v_a_2254_);
lean_dec(v_a_2254_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v___x_2258_);
v___x_2260_ = v___x_2256_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
v_a_2263_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2253_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2253_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
lean_object* v_val_2271_; lean_object* v___x_2272_; 
lean_dec_ref(v___x_2248_);
v_val_2271_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_val_2271_);
lean_dec_ref_known(v___x_2249_, 1);
lean_inc(v_a_2230_);
lean_inc_ref(v_a_2229_);
lean_inc(v_a_2228_);
v___x_2272_ = lean_apply_8(v_f_2223_, v_goI_2224_, v_goB_2225_, v_val_2271_, v_content_2227_, v_a_2228_, v_a_2229_, v_a_2230_, lean_box(0));
return v___x_2272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg___boxed(lean_object* v_inst_2273_, lean_object* v_f_2274_, lean_object* v_goI_2275_, lean_object* v_goB_2276_, lean_object* v_val_2277_, lean_object* v_content_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2273_, v_f_2274_, v_goI_2275_, v_goB_2276_, v_val_2277_, v_content_2278_, v_a_2279_, v_a_2280_, v_a_2281_);
lean_dec(v_a_2281_);
lean_dec_ref(v_a_2280_);
lean_dec(v_a_2279_);
lean_dec(v_val_2277_);
lean_dec(v_inst_2273_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer(lean_object* v_00_u03b1_2284_, lean_object* v_inst_2285_, lean_object* v_f_2286_, lean_object* v_goI_2287_, lean_object* v_goB_2288_, lean_object* v_val_2289_, lean_object* v_content_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2285_, v_f_2286_, v_goI_2287_, v_goB_2288_, v_val_2289_, v_content_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___boxed(lean_object* v_00_u03b1_2296_, lean_object* v_inst_2297_, lean_object* v_f_2298_, lean_object* v_goI_2299_, lean_object* v_goB_2300_, lean_object* v_val_2301_, lean_object* v_content_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_Doc_mkBlockMdRenderer(v_00_u03b1_2296_, v_inst_2297_, v_f_2298_, v_goI_2299_, v_goB_2300_, v_val_2301_, v_content_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec(v_val_2301_);
lean_dec(v_inst_2297_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(lean_object* v_as_2312_, size_t v_i_2313_, size_t v_stop_2314_, lean_object* v_b_2315_){
_start:
{
uint8_t v___x_2316_; 
v___x_2316_ = lean_usize_dec_eq(v_i_2313_, v_stop_2314_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; lean_object* v_fst_2318_; lean_object* v_snd_2319_; lean_object* v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; 
v___x_2317_ = lean_array_uget_borrowed(v_as_2312_, v_i_2313_);
v_fst_2318_ = lean_ctor_get(v___x_2317_, 0);
v_snd_2319_ = lean_ctor_get(v___x_2317_, 1);
lean_inc(v_snd_2319_);
lean_inc(v_fst_2318_);
v___x_2320_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2318_, v_snd_2319_, v_b_2315_);
v___x_2321_ = ((size_t)1ULL);
v___x_2322_ = lean_usize_add(v_i_2313_, v___x_2321_);
v_i_2313_ = v___x_2322_;
v_b_2315_ = v___x_2320_;
goto _start;
}
else
{
return v_b_2315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0___boxed(lean_object* v_as_2324_, lean_object* v_i_2325_, lean_object* v_stop_2326_, lean_object* v_b_2327_){
_start:
{
size_t v_i_boxed_2328_; size_t v_stop_boxed_2329_; lean_object* v_res_2330_; 
v_i_boxed_2328_ = lean_unbox_usize(v_i_2325_);
lean_dec(v_i_2325_);
v_stop_boxed_2329_ = lean_unbox_usize(v_stop_2326_);
lean_dec(v_stop_2326_);
v_res_2330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v_as_2324_, v_i_boxed_2328_, v_stop_boxed_2329_, v_b_2327_);
lean_dec_ref(v_as_2324_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(lean_object* v_as_2331_, size_t v_i_2332_, size_t v_stop_2333_, lean_object* v_b_2334_){
_start:
{
lean_object* v___y_2336_; uint8_t v___x_2340_; 
v___x_2340_ = lean_usize_dec_eq(v_i_2332_, v_stop_2333_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2341_ = lean_array_uget_borrowed(v_as_2331_, v_i_2332_);
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = lean_array_get_size(v___x_2341_);
v___x_2344_ = lean_nat_dec_lt(v___x_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
v___y_2336_ = v_b_2334_;
goto v___jp_2335_;
}
else
{
uint8_t v___x_2345_; 
v___x_2345_ = lean_nat_dec_le(v___x_2343_, v___x_2343_);
if (v___x_2345_ == 0)
{
if (v___x_2344_ == 0)
{
v___y_2336_ = v_b_2334_;
goto v___jp_2335_;
}
else
{
size_t v___x_2346_; size_t v___x_2347_; lean_object* v___x_2348_; 
v___x_2346_ = ((size_t)0ULL);
v___x_2347_ = lean_usize_of_nat(v___x_2343_);
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2341_, v___x_2346_, v___x_2347_, v_b_2334_);
v___y_2336_ = v___x_2348_;
goto v___jp_2335_;
}
}
else
{
size_t v___x_2349_; size_t v___x_2350_; lean_object* v___x_2351_; 
v___x_2349_ = ((size_t)0ULL);
v___x_2350_ = lean_usize_of_nat(v___x_2343_);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2341_, v___x_2349_, v___x_2350_, v_b_2334_);
v___y_2336_ = v___x_2351_;
goto v___jp_2335_;
}
}
}
else
{
return v_b_2334_;
}
v___jp_2335_:
{
size_t v___x_2337_; size_t v___x_2338_; 
v___x_2337_ = ((size_t)1ULL);
v___x_2338_ = lean_usize_add(v_i_2332_, v___x_2337_);
v_i_2332_ = v___x_2338_;
v_b_2334_ = v___y_2336_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1___boxed(lean_object* v_as_2352_, lean_object* v_i_2353_, lean_object* v_stop_2354_, lean_object* v_b_2355_){
_start:
{
size_t v_i_boxed_2356_; size_t v_stop_boxed_2357_; lean_object* v_res_2358_; 
v_i_boxed_2356_ = lean_unbox_usize(v_i_2353_);
lean_dec(v_i_2353_);
v_stop_boxed_2357_ = lean_unbox_usize(v_stop_2354_);
lean_dec(v_stop_2354_);
v_res_2358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_as_2352_, v_i_boxed_2356_, v_stop_boxed_2357_, v_b_2355_);
lean_dec_ref(v_as_2352_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(lean_object* v_init_2359_, lean_object* v_es_2360_){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = lean_array_get_size(v_es_2360_);
v___x_2363_ = lean_nat_dec_lt(v___x_2361_, v___x_2362_);
if (v___x_2363_ == 0)
{
return v_init_2359_;
}
else
{
uint8_t v___x_2364_; 
v___x_2364_ = lean_nat_dec_le(v___x_2362_, v___x_2362_);
if (v___x_2364_ == 0)
{
if (v___x_2363_ == 0)
{
return v_init_2359_;
}
else
{
size_t v___x_2365_; size_t v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = ((size_t)0ULL);
v___x_2366_ = lean_usize_of_nat(v___x_2362_);
v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2360_, v___x_2365_, v___x_2366_, v_init_2359_);
return v___x_2367_;
}
}
else
{
size_t v___x_2368_; size_t v___x_2369_; lean_object* v___x_2370_; 
v___x_2368_ = ((size_t)0ULL);
v___x_2369_ = lean_usize_of_nat(v___x_2362_);
v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2360_, v___x_2368_, v___x_2369_, v_init_2359_);
return v___x_2370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries___boxed(lean_object* v_init_2371_, lean_object* v_es_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v_init_2371_, v_es_2372_);
lean_dec_ref(v_es_2372_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_2374_, lean_object* v_x_2375_){
_start:
{
if (lean_obj_tag(v_x_2375_) == 0)
{
lean_object* v_k_2376_; lean_object* v_v_2377_; lean_object* v_l_2378_; lean_object* v_r_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v_k_2376_ = lean_ctor_get(v_x_2375_, 1);
v_v_2377_ = lean_ctor_get(v_x_2375_, 2);
v_l_2378_ = lean_ctor_get(v_x_2375_, 3);
v_r_2379_ = lean_ctor_get(v_x_2375_, 4);
v___x_2380_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2374_, v_l_2378_);
lean_inc(v_v_2377_);
lean_inc(v_k_2376_);
v___x_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2381_, 0, v_k_2376_);
lean_ctor_set(v___x_2381_, 1, v_v_2377_);
v___x_2382_ = lean_array_push(v___x_2380_, v___x_2381_);
v_init_2374_ = v___x_2382_;
v_x_2375_ = v_r_2379_;
goto _start;
}
else
{
return v_init_2374_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_2384_, lean_object* v_x_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2384_, v_x_2385_);
lean_dec(v_x_2385_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2389_){
_start:
{
lean_object* v_current_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v_current_2390_ = lean_ctor_get(v_s_2389_, 1);
v___x_2391_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2392_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2391_, v_current_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_s_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_s_2393_);
lean_dec_ref(v_s_2393_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_box(0);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2397_);
lean_dec_ref(v_x_2397_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2399_, lean_object* v_s_2400_){
_start:
{
lean_object* v_current_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v_current_2401_ = lean_ctor_get(v_s_2400_, 1);
v___x_2402_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2403_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2402_, v_current_2401_);
lean_inc_ref_n(v___x_2403_, 2);
v___x_2404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
lean_ctor_set(v___x_2404_, 2, v___x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2405_, lean_object* v_s_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2405_, v_s_2406_);
lean_dec_ref(v_s_2406_);
lean_dec_ref(v_x_2405_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2408_, lean_object* v_x_2409_){
_start:
{
lean_object* v_fst_2410_; lean_object* v_snd_2411_; lean_object* v_imported_2412_; lean_object* v_current_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2421_; 
v_fst_2410_ = lean_ctor_get(v_x_2409_, 0);
lean_inc(v_fst_2410_);
v_snd_2411_ = lean_ctor_get(v_x_2409_, 1);
lean_inc(v_snd_2411_);
lean_dec_ref(v_x_2409_);
v_imported_2412_ = lean_ctor_get(v_s_2408_, 0);
v_current_2413_ = lean_ctor_get(v_s_2408_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_s_2408_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2415_ = v_s_2408_;
v_isShared_2416_ = v_isSharedCheck_2421_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_current_2413_);
lean_inc(v_imported_2412_);
lean_dec(v_s_2408_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2421_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2417_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2410_, v_snd_2411_, v_current_2413_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 1, v___x_2417_);
v___x_2419_ = v___x_2415_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_imported_2412_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2422_, lean_object* v_es_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_inc(v___x_2422_);
v___x_2426_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v___x_2422_, v_es_2423_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v___x_2422_);
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2429_, lean_object* v_es_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2429_, v_es_2430_, v___y_2431_);
lean_dec_ref(v___y_2431_);
lean_dec_ref(v_es_2430_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2434_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2437_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2469_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_();
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(lean_object* v_init_2472_, lean_object* v_t_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2472_, v_t_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_2475_, lean_object* v_t_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(v_init_2475_, v_t_2476_);
lean_dec(v_t_2476_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_));
v___x_2497_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2____boxed(lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_();
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = lean_box(1);
v___x_2502_ = lean_st_mk_ref(v___x_2501_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2____boxed(lean_object* v_a_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_();
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = lean_box(1);
v___x_2508_ = lean_st_mk_ref(v___x_2507_);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2____boxed(lean_object* v_a_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_();
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer(lean_object* v_type_2512_, lean_object* v_r_2513_){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2515_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2516_ = lean_st_ref_take(v___x_2515_);
v___x_2517_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2512_, v_r_2513_, v___x_2516_);
v___x_2518_ = lean_st_ref_put(v___x_2515_, v___x_2517_);
v___x_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer___boxed(lean_object* v_type_2520_, lean_object* v_r_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_Doc_addBuiltinInlineMdRenderer(v_type_2520_, v_r_2521_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer(lean_object* v_type_2524_, lean_object* v_r_2525_){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2527_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2528_ = lean_st_ref_take(v___x_2527_);
v___x_2529_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2524_, v_r_2525_, v___x_2528_);
v___x_2530_ = lean_st_ref_put(v___x_2527_, v___x_2529_);
v___x_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer___boxed(lean_object* v_type_2532_, lean_object* v_r_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lean_Doc_addBuiltinBlockMdRenderer(v_type_2532_, v_r_2533_);
return v_res_2535_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2536_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
return v___x_2538_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2540_ = lean_unsigned_to_nat(0u);
v___x_2541_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
lean_ctor_set(v___x_2541_, 2, v___x_2540_);
lean_ctor_set(v___x_2541_, 3, v___x_2540_);
lean_ctor_set(v___x_2541_, 4, v___x_2539_);
lean_ctor_set(v___x_2541_, 5, v___x_2539_);
lean_ctor_set(v___x_2541_, 6, v___x_2539_);
lean_ctor_set(v___x_2541_, 7, v___x_2539_);
lean_ctor_set(v___x_2541_, 8, v___x_2539_);
lean_ctor_set(v___x_2541_, 9, v___x_2539_);
lean_ctor_set(v___x_2541_, 10, v___x_2539_);
return v___x_2541_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_unsigned_to_nat(32u);
v___x_2543_ = lean_mk_empty_array_with_capacity(v___x_2542_);
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2545_ = ((size_t)5ULL);
v___x_2546_ = lean_unsigned_to_nat(0u);
v___x_2547_ = lean_unsigned_to_nat(32u);
v___x_2548_ = lean_mk_empty_array_with_capacity(v___x_2547_);
v___x_2549_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_2550_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___x_2548_);
lean_ctor_set(v___x_2550_, 2, v___x_2546_);
lean_ctor_set(v___x_2550_, 3, v___x_2546_);
lean_ctor_set_usize(v___x_2550_, 4, v___x_2545_);
return v___x_2550_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2551_ = lean_box(1);
v___x_2552_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_2553_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
lean_ctor_set(v___x_2554_, 1, v___x_2552_);
lean_ctor_set(v___x_2554_, 2, v___x_2551_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v_env_2560_; lean_object* v_options_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2559_ = lean_st_ref_get(v___y_2557_);
v_env_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc_ref(v_env_2560_);
lean_dec(v___x_2559_);
v_options_2561_ = lean_ctor_get(v___y_2556_, 2);
v___x_2562_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_2563_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_2561_);
v___x_2564_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2564_, 0, v_env_2560_);
lean_ctor_set(v___x_2564_, 1, v___x_2562_);
lean_ctor_set(v___x_2564_, 2, v___x_2563_);
lean_ctor_set(v___x_2564_, 3, v_options_2561_);
v___x_2565_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
lean_ctor_set(v___x_2565_, 1, v_msgData_2555_);
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_ref_2576_; lean_object* v___x_2577_; lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2586_; 
v_ref_2576_ = lean_ctor_get(v___y_2573_, 5);
v___x_2577_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_2572_, v___y_2573_, v___y_2574_);
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2586_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2586_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2584_; 
lean_inc(v_ref_2576_);
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v_ref_2576_);
lean_ctor_set(v___x_2582_, 1, v_a_2578_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 1);
lean_ctor_set(v___x_2580_, 0, v___x_2582_);
v___x_2584_ = v___x_2580_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(lean_object* v_x_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
if (lean_obj_tag(v_x_2592_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_a_2596_ = lean_ctor_get(v_x_2592_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v_x_2592_, 1);
v___x_2597_ = l_Lean_stringToMessageData(v_a_2596_);
v___x_2598_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v___x_2597_, v___y_2593_, v___y_2594_);
return v___x_2598_;
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
v_a_2599_ = lean_ctor_get(v_x_2592_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_x_2592_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v_x_2592_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v_x_2592_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
lean_ctor_set_tag(v___x_2601_, 0);
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
return v_res_2611_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_box(0);
v___x_2613_ = l_Lean_Elab_abortCommandExceptionId;
v___x_2614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v___x_2612_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(lean_object* v_constName_2620_, uint8_t v_checkMeta_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; lean_object* v_env_2626_; uint8_t v___x_2627_; 
v___x_2625_ = lean_st_ref_get(v___y_2623_);
v_env_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc_ref(v_env_2626_);
lean_dec(v___x_2625_);
lean_inc(v_constName_2620_);
v___x_2627_ = lean_has_compile_error(v_env_2626_, v_constName_2620_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v_env_2629_; lean_object* v_options_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2628_ = lean_st_ref_get(v___y_2623_);
v_env_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc_ref(v_env_2629_);
lean_dec(v___x_2628_);
v_options_2630_ = lean_ctor_get(v___y_2622_, 2);
v___x_2631_ = l_Lean_Environment_evalConst___redArg(v_env_2629_, v_options_2630_, v_constName_2620_, v_checkMeta_2621_);
lean_dec(v_constName_2620_);
lean_dec_ref(v_env_2629_);
v___x_2632_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2631_, v___y_2622_, v___y_2623_);
return v___x_2632_;
}
else
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v___x_2634_; lean_object* v_env_2635_; lean_object* v_options_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_dec_ref_known(v___x_2633_, 1);
v___x_2634_ = lean_st_ref_get(v___y_2623_);
v_env_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc_ref(v_env_2635_);
lean_dec(v___x_2634_);
v_options_2636_ = lean_ctor_get(v___y_2622_, 2);
v___x_2637_ = l_Lean_Environment_evalConst___redArg(v_env_2635_, v_options_2636_, v_constName_2620_, v_checkMeta_2621_);
lean_dec(v_constName_2620_);
lean_dec_ref(v_env_2635_);
v___x_2638_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2637_, v___y_2622_, v___y_2623_);
return v___x_2638_;
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v_constName_2620_);
v_a_2639_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2633_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2633_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg___boxed(lean_object* v_constName_2647_, lean_object* v_checkMeta_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
uint8_t v_checkMeta_boxed_2652_; lean_object* v_res_2653_; 
v_checkMeta_boxed_2652_ = lean_unbox(v_checkMeta_2648_);
v_res_2653_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2647_, v_checkMeta_boxed_2652_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(lean_object* v_type_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v___x_2658_; lean_object* v___y_2660_; lean_object* v_env_2691_; lean_object* v___x_2692_; lean_object* v_toEnvExtension_2693_; lean_object* v_asyncMode_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v_imported_2698_; lean_object* v_current_2699_; lean_object* v___x_2700_; 
v___x_2658_ = lean_st_ref_get(v_a_2656_);
v_env_2691_ = lean_ctor_get(v___x_2658_, 0);
lean_inc_ref(v_env_2691_);
lean_dec(v___x_2658_);
v___x_2692_ = l_Lean_Doc_docInlineMdExt;
v_toEnvExtension_2693_ = lean_ctor_get(v___x_2692_, 0);
v_asyncMode_2694_ = lean_ctor_get(v_toEnvExtension_2693_, 2);
v___x_2695_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2696_ = lean_box(0);
v___x_2697_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2695_, v___x_2692_, v_env_2691_, v_asyncMode_2694_, v___x_2696_);
v_imported_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_imported_2698_);
v_current_2699_ = lean_ctor_get(v___x_2697_, 1);
lean_inc(v_current_2699_);
lean_dec(v___x_2697_);
v___x_2700_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2699_, v_type_2654_);
lean_dec(v_current_2699_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2698_, v_type_2654_);
lean_dec(v_imported_2698_);
v___y_2660_ = v___x_2701_;
goto v___jp_2659_;
}
else
{
lean_dec(v_imported_2698_);
v___y_2660_ = v___x_2700_;
goto v___jp_2659_;
}
v___jp_2659_:
{
if (lean_obj_tag(v___y_2660_) == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2661_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2662_ = lean_st_ref_get(v___x_2661_);
v___x_2663_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2662_, v_type_2654_);
lean_dec(v___x_2662_);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
return v___x_2664_;
}
else
{
lean_object* v_val_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2690_; 
v_val_2665_ = lean_ctor_get(v___y_2660_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___y_2660_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2667_ = v___y_2660_;
v_isShared_2668_ = v_isSharedCheck_2690_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_val_2665_);
lean_dec(v___y_2660_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2690_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
uint8_t v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = 1;
v___x_2670_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2665_, v___x_2669_, v_a_2655_, v_a_2656_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2681_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2673_ = v___x_2670_;
v_isShared_2674_ = v_isSharedCheck_2681_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2681_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v_a_2671_);
v___x_2676_ = v___x_2667_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2678_; 
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2676_);
v___x_2678_ = v___x_2673_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_del_object(v___x_2667_);
v_a_2682_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2670_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2670_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe___boxed(lean_object* v_type_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v_type_2702_, v_a_2703_, v_a_2704_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_type_2702_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(v_00_u03b1_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(lean_object* v_00_u03b1_2717_, lean_object* v_constName_2718_, uint8_t v_checkMeta_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2718_, v_checkMeta_2719_, v___y_2720_, v___y_2721_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___boxed(lean_object* v_00_u03b1_2724_, lean_object* v_constName_2725_, lean_object* v_checkMeta_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
uint8_t v_checkMeta_boxed_2730_; lean_object* v_res_2731_; 
v_checkMeta_boxed_2730_ = lean_unbox(v_checkMeta_2726_);
v_res_2731_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(v_00_u03b1_2724_, v_constName_2725_, v_checkMeta_boxed_2730_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_2732_, lean_object* v_x_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2733_, v___y_2734_, v___y_2735_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2738_, lean_object* v_x_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(v_00_u03b1_2738_, v_x_2739_, v___y_2740_, v___y_2741_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2744_, lean_object* v_msg_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2745_, v___y_2746_, v___y_2747_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2750_, lean_object* v_msg_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_2750_, v_msg_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(lean_object* v_typeName_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___x_2760_; lean_object* v___y_2762_; lean_object* v_env_2793_; lean_object* v___x_2794_; lean_object* v_toEnvExtension_2795_; lean_object* v_asyncMode_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v_imported_2800_; lean_object* v_current_2801_; lean_object* v___x_2802_; 
v___x_2760_ = lean_st_ref_get(v_a_2758_);
v_env_2793_ = lean_ctor_get(v___x_2760_, 0);
lean_inc_ref(v_env_2793_);
lean_dec(v___x_2760_);
v___x_2794_ = l_Lean_Doc_docBlockMdExt;
v_toEnvExtension_2795_ = lean_ctor_get(v___x_2794_, 0);
v_asyncMode_2796_ = lean_ctor_get(v_toEnvExtension_2795_, 2);
v___x_2797_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2798_ = lean_box(0);
v___x_2799_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2797_, v___x_2794_, v_env_2793_, v_asyncMode_2796_, v___x_2798_);
v_imported_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_imported_2800_);
v_current_2801_ = lean_ctor_get(v___x_2799_, 1);
lean_inc(v_current_2801_);
lean_dec(v___x_2799_);
v___x_2802_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2801_, v_typeName_2756_);
lean_dec(v_current_2801_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2800_, v_typeName_2756_);
lean_dec(v_imported_2800_);
v___y_2762_ = v___x_2803_;
goto v___jp_2761_;
}
else
{
lean_dec(v_imported_2800_);
v___y_2762_ = v___x_2802_;
goto v___jp_2761_;
}
v___jp_2761_:
{
if (lean_obj_tag(v___y_2762_) == 0)
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2763_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2764_ = lean_st_ref_get(v___x_2763_);
v___x_2765_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2764_, v_typeName_2756_);
lean_dec(v___x_2764_);
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
return v___x_2766_;
}
else
{
lean_object* v_val_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2792_; 
v_val_2767_ = lean_ctor_get(v___y_2762_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___y_2762_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2769_ = v___y_2762_;
v_isShared_2770_ = v_isSharedCheck_2792_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_val_2767_);
lean_dec(v___y_2762_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2792_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
uint8_t v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = 1;
v___x_2772_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2767_, v___x_2771_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2783_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2775_ = v___x_2772_;
v_isShared_2776_ = v_isSharedCheck_2783_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2772_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2783_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v_a_2773_);
v___x_2778_ = v___x_2769_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2780_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___x_2778_);
v___x_2780_ = v___x_2775_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_del_object(v___x_2769_);
v_a_2784_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2772_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2772_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe___boxed(lean_object* v_typeName_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v_typeName_2804_, v_a_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_typeName_2804_);
return v_res_2808_;
}
}
static lean_object* _init_l_Lean_Doc_mdRendererHeartbeats(void){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = lean_unsigned_to_nat(200000u);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg(lean_object* v_x_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v___x_2815_; lean_object* v_fileName_2816_; lean_object* v_fileMap_2817_; lean_object* v_options_2818_; lean_object* v_currRecDepth_2819_; lean_object* v_maxRecDepth_2820_; lean_object* v_ref_2821_; lean_object* v_currNamespace_2822_; lean_object* v_openDecls_2823_; lean_object* v_quotContext_2824_; lean_object* v_currMacroScope_2825_; uint8_t v_diag_2826_; lean_object* v_cancelTk_x3f_2827_; uint8_t v_suppressElabErrors_2828_; lean_object* v_inheritedTraceOptions_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2815_ = lean_io_get_num_heartbeats();
v_fileName_2816_ = lean_ctor_get(v_a_2812_, 0);
v_fileMap_2817_ = lean_ctor_get(v_a_2812_, 1);
v_options_2818_ = lean_ctor_get(v_a_2812_, 2);
v_currRecDepth_2819_ = lean_ctor_get(v_a_2812_, 3);
v_maxRecDepth_2820_ = lean_ctor_get(v_a_2812_, 4);
v_ref_2821_ = lean_ctor_get(v_a_2812_, 5);
v_currNamespace_2822_ = lean_ctor_get(v_a_2812_, 6);
v_openDecls_2823_ = lean_ctor_get(v_a_2812_, 7);
v_quotContext_2824_ = lean_ctor_get(v_a_2812_, 10);
v_currMacroScope_2825_ = lean_ctor_get(v_a_2812_, 11);
v_diag_2826_ = lean_ctor_get_uint8(v_a_2812_, sizeof(void*)*14);
v_cancelTk_x3f_2827_ = lean_ctor_get(v_a_2812_, 12);
v_suppressElabErrors_2828_ = lean_ctor_get_uint8(v_a_2812_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2829_ = lean_ctor_get(v_a_2812_, 13);
v___x_2830_ = lean_unsigned_to_nat(200000u);
lean_inc_ref(v_inheritedTraceOptions_2829_);
lean_inc(v_cancelTk_x3f_2827_);
lean_inc(v_currMacroScope_2825_);
lean_inc(v_quotContext_2824_);
lean_inc(v_openDecls_2823_);
lean_inc(v_currNamespace_2822_);
lean_inc(v_ref_2821_);
lean_inc(v_maxRecDepth_2820_);
lean_inc(v_currRecDepth_2819_);
lean_inc_ref(v_options_2818_);
lean_inc_ref(v_fileMap_2817_);
lean_inc_ref(v_fileName_2816_);
v___x_2831_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2831_, 0, v_fileName_2816_);
lean_ctor_set(v___x_2831_, 1, v_fileMap_2817_);
lean_ctor_set(v___x_2831_, 2, v_options_2818_);
lean_ctor_set(v___x_2831_, 3, v_currRecDepth_2819_);
lean_ctor_set(v___x_2831_, 4, v_maxRecDepth_2820_);
lean_ctor_set(v___x_2831_, 5, v_ref_2821_);
lean_ctor_set(v___x_2831_, 6, v_currNamespace_2822_);
lean_ctor_set(v___x_2831_, 7, v_openDecls_2823_);
lean_ctor_set(v___x_2831_, 8, v___x_2815_);
lean_ctor_set(v___x_2831_, 9, v___x_2830_);
lean_ctor_set(v___x_2831_, 10, v_quotContext_2824_);
lean_ctor_set(v___x_2831_, 11, v_currMacroScope_2825_);
lean_ctor_set(v___x_2831_, 12, v_cancelTk_x3f_2827_);
lean_ctor_set(v___x_2831_, 13, v_inheritedTraceOptions_2829_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*14, v_diag_2826_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*14 + 1, v_suppressElabErrors_2828_);
lean_inc(v_a_2813_);
lean_inc(v_a_2811_);
v___x_2832_ = lean_apply_4(v_x_2810_, v_a_2811_, v___x_2831_, v_a_2813_, lean_box(0));
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg___boxed(lean_object* v_x_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
lean_dec(v_a_2836_);
lean_dec_ref(v_a_2835_);
lean_dec(v_a_2834_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget(lean_object* v_00_u03b1_2839_, lean_object* v_x_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___boxed(lean_object* v_00_u03b1_2846_, lean_object* v_x_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_Doc_withMdRendererBudget(v_00_u03b1_2846_, v_x_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback(lean_object* v_fallback_2853_, lean_object* v_act_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = lean_st_ref_get(v_a_2855_);
v___x_2860_ = l_Lean_Doc_withMdRendererBudget___redArg(v_act_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_dec(v___x_2859_);
lean_dec_ref(v_fallback_2853_);
return v___x_2860_;
}
else
{
lean_object* v_a_2861_; uint8_t v___x_2862_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
v___x_2862_ = l_Lean_Exception_isInterrupt(v_a_2861_);
lean_dec(v_a_2861_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_dec_ref_known(v___x_2860_, 1);
v___x_2863_ = lean_st_ref_swap(v_a_2855_, v___x_2859_);
lean_dec(v___x_2863_);
lean_inc(v_a_2857_);
lean_inc_ref(v_a_2856_);
lean_inc(v_a_2855_);
v___x_2864_ = lean_apply_4(v_fallback_2853_, v_a_2855_, v_a_2856_, v_a_2857_, lean_box(0));
return v___x_2864_;
}
else
{
lean_dec(v___x_2859_);
lean_dec_ref(v_fallback_2853_);
return v___x_2860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback___boxed(lean_object* v_fallback_2865_, lean_object* v_act_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_Doc_withRendererFallback(v_fallback_2865_, v_act_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
lean_dec(v_a_2867_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0(lean_object* v_____do__lift_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = l_Lean_Doc_joinInlines(v_____do__lift_2872_);
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0___boxed(lean_object* v_____do__lift_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__0(v_____do__lift_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v_____do__lift_2879_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1(lean_object* v___x_2885_, lean_object* v___f_2886_, lean_object* v___x_2887_, lean_object* v_go_2888_, lean_object* v_container_2889_, lean_object* v_content_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
if (lean_obj_tag(v_container_2889_) == 0)
{
lean_object* v_val_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_val_2895_ = lean_ctor_get(v_container_2889_, 0);
lean_inc(v_val_2895_);
lean_dec_ref_known(v_container_2889_, 1);
v___x_2896_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2895_);
v___x_2897_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_2896_, v___y_2892_, v___y_2893_);
lean_dec(v___x_2896_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v___x_2897_, 1);
if (lean_obj_tag(v_a_2898_) == 0)
{
size_t v_sz_2899_; size_t v___x_2900_; lean_object* v___x_541__overap_2901_; lean_object* v___x_2902_; 
lean_dec(v_val_2895_);
lean_dec_ref(v___x_2887_);
v_sz_2899_ = lean_array_size(v_content_2890_);
v___x_2900_ = ((size_t)0ULL);
v___x_541__overap_2901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2885_, v_go_2888_, v_sz_2899_, v___x_2900_, v_content_2890_);
lean_inc(v___y_2893_);
lean_inc_ref(v___y_2892_);
lean_inc(v___y_2891_);
v___x_2902_ = lean_apply_4(v___x_541__overap_2901_, v___y_2891_, v___y_2892_, v___y_2893_, lean_box(0));
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2904_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref_known(v___x_2902_, 1);
lean_inc(v___y_2893_);
lean_inc_ref(v___y_2892_);
lean_inc(v___y_2891_);
v___x_2904_ = lean_apply_5(v___f_2886_, v_a_2903_, v___y_2891_, v___y_2892_, v___y_2893_, lean_box(0));
return v___x_2904_;
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec_ref(v___f_2886_);
v_a_2905_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2902_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2902_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_val_2913_; size_t v_sz_2914_; size_t v___x_2915_; lean_object* v___x_2916_; lean_object* v_fallback_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_val_2913_ = lean_ctor_get(v_a_2898_, 0);
lean_inc(v_val_2913_);
lean_dec_ref_known(v_a_2898_, 1);
v_sz_2914_ = lean_array_size(v_content_2890_);
v___x_2915_ = ((size_t)0ULL);
lean_inc_ref(v_content_2890_);
lean_inc_ref(v_go_2888_);
v___x_2916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2885_, v_go_2888_, v_sz_2914_, v___x_2915_, v_content_2890_);
v_fallback_2917_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_2917_, 0, lean_box(0));
lean_closure_set(v_fallback_2917_, 1, lean_box(0));
lean_closure_set(v_fallback_2917_, 2, v___x_2887_);
lean_closure_set(v_fallback_2917_, 3, lean_box(0));
lean_closure_set(v_fallback_2917_, 4, lean_box(0));
lean_closure_set(v_fallback_2917_, 5, v___x_2916_);
lean_closure_set(v_fallback_2917_, 6, v___f_2886_);
v___x_2918_ = lean_apply_3(v_val_2913_, v_go_2888_, v_val_2895_, v_content_2890_);
v___x_2919_ = l_Lean_Doc_withRendererFallback(v_fallback_2917_, v___x_2918_, v___y_2891_, v___y_2892_, v___y_2893_);
return v___x_2919_;
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_val_2895_);
lean_dec_ref(v_content_2890_);
lean_dec_ref(v_go_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___f_2886_);
lean_dec_ref(v___x_2885_);
v_a_2920_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2897_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2897_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
size_t v_sz_2928_; size_t v___x_2929_; lean_object* v___x_558__overap_2930_; lean_object* v___x_2931_; 
lean_dec_ref_known(v_container_2889_, 1);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___f_2886_);
v_sz_2928_ = lean_array_size(v_content_2890_);
v___x_2929_ = ((size_t)0ULL);
v___x_558__overap_2930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2885_, v_go_2888_, v_sz_2928_, v___x_2929_, v_content_2890_);
lean_inc(v___y_2893_);
lean_inc_ref(v___y_2892_);
lean_inc(v___y_2891_);
v___x_2931_ = lean_apply_4(v___x_558__overap_2930_, v___y_2891_, v___y_2892_, v___y_2893_, lean_box(0));
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2940_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2934_ = v___x_2931_;
v_isShared_2935_ = v_isSharedCheck_2940_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2940_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2936_ = l_Lean_Doc_joinInlines(v_a_2932_);
lean_dec(v_a_2932_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 0, v___x_2936_);
v___x_2938_ = v___x_2934_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
v_a_2941_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2931_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2931_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed(lean_object* v___x_2949_, lean_object* v___f_2950_, lean_object* v___x_2951_, lean_object* v_go_2952_, lean_object* v_container_2953_, lean_object* v_content_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__1(v___x_2949_, v___f_2950_, v___x_2951_, v_go_2952_, v_container_2953_, v_content_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
return v_res_2959_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownInlineElabInline(void){
_start:
{
lean_object* v___x_2961_; lean_object* v_toApplicative_2962_; lean_object* v_toFunctor_2963_; lean_object* v_toSeq_2964_; lean_object* v_toSeqLeft_2965_; lean_object* v_toSeqRight_2966_; lean_object* v___f_2967_; lean_object* v___f_2968_; lean_object* v___f_2969_; lean_object* v___f_2970_; lean_object* v___f_2971_; lean_object* v___x_2972_; lean_object* v___f_2973_; lean_object* v___f_2974_; lean_object* v___f_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___f_2979_; 
v___x_2961_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2962_ = lean_ctor_get(v___x_2961_, 0);
v_toFunctor_2963_ = lean_ctor_get(v_toApplicative_2962_, 0);
v_toSeq_2964_ = lean_ctor_get(v_toApplicative_2962_, 2);
v_toSeqLeft_2965_ = lean_ctor_get(v_toApplicative_2962_, 3);
v_toSeqRight_2966_ = lean_ctor_get(v_toApplicative_2962_, 4);
v___f_2967_ = ((lean_object*)(l_Lean_Doc_instMarkdownInlineElabInline___closed__0));
v___f_2968_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2969_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2963_, 2);
v___f_2970_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2970_, 0, v_toFunctor_2963_);
v___f_2971_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2971_, 0, v_toFunctor_2963_);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___f_2970_);
lean_ctor_set(v___x_2972_, 1, v___f_2971_);
lean_inc(v_toSeqRight_2966_);
v___f_2973_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2973_, 0, v_toSeqRight_2966_);
lean_inc(v_toSeqLeft_2965_);
v___f_2974_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2974_, 0, v_toSeqLeft_2965_);
lean_inc(v_toSeq_2964_);
v___f_2975_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2975_, 0, v_toSeq_2964_);
v___x_2976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2972_);
lean_ctor_set(v___x_2976_, 1, v___f_2968_);
lean_ctor_set(v___x_2976_, 2, v___f_2975_);
lean_ctor_set(v___x_2976_, 3, v___f_2974_);
lean_ctor_set(v___x_2976_, 4, v___f_2973_);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
lean_ctor_set(v___x_2977_, 1, v___f_2969_);
lean_inc_ref(v___x_2977_);
v___x_2978_ = l_StateRefT_x27_instMonad___redArg(v___x_2977_);
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2979_, 0, v___x_2978_);
lean_closure_set(v___f_2979_, 1, v___f_2967_);
lean_closure_set(v___f_2979_, 2, v___x_2977_);
return v___f_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v_____do__lift_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = l_Lean_Doc_joinBlocks(v_____do__lift_2980_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object* v_____do__lift_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(v_____do__lift_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v_____do__lift_2987_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object* v___x_2993_, lean_object* v___f_2994_, lean_object* v___x_2995_, lean_object* v_goI_2996_, lean_object* v_goB_2997_, lean_object* v_container_2998_, lean_object* v_content_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
if (lean_obj_tag(v_container_2998_) == 0)
{
lean_object* v_val_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_val_3004_ = lean_ctor_get(v_container_2998_, 0);
lean_inc(v_val_3004_);
lean_dec_ref_known(v_container_2998_, 1);
v___x_3005_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3004_);
v___x_3006_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_3005_, v___y_3001_, v___y_3002_);
lean_dec(v___x_3005_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
if (lean_obj_tag(v_a_3007_) == 0)
{
size_t v_sz_3008_; size_t v___x_3009_; lean_object* v___x_541__overap_3010_; lean_object* v___x_3011_; 
lean_dec(v_val_3004_);
lean_dec_ref(v_goI_2996_);
lean_dec_ref(v___x_2995_);
v_sz_3008_ = lean_array_size(v_content_2999_);
v___x_3009_ = ((size_t)0ULL);
v___x_541__overap_3010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2993_, v_goB_2997_, v_sz_3008_, v___x_3009_, v_content_2999_);
lean_inc(v___y_3002_);
lean_inc_ref(v___y_3001_);
lean_inc(v___y_3000_);
v___x_3011_ = lean_apply_4(v___x_541__overap_3010_, v___y_3000_, v___y_3001_, v___y_3002_, lean_box(0));
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
lean_inc(v___y_3002_);
lean_inc_ref(v___y_3001_);
lean_inc(v___y_3000_);
v___x_3013_ = lean_apply_5(v___f_2994_, v_a_3012_, v___y_3000_, v___y_3001_, v___y_3002_, lean_box(0));
return v___x_3013_;
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec_ref(v___f_2994_);
v_a_3014_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_3011_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3011_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v_val_3022_; size_t v_sz_3023_; size_t v___x_3024_; lean_object* v___x_3025_; lean_object* v_fallback_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_val_3022_ = lean_ctor_get(v_a_3007_, 0);
lean_inc(v_val_3022_);
lean_dec_ref_known(v_a_3007_, 1);
v_sz_3023_ = lean_array_size(v_content_2999_);
v___x_3024_ = ((size_t)0ULL);
lean_inc_ref(v_content_2999_);
lean_inc_ref(v_goB_2997_);
v___x_3025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2993_, v_goB_2997_, v_sz_3023_, v___x_3024_, v_content_2999_);
v_fallback_3026_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_3026_, 0, lean_box(0));
lean_closure_set(v_fallback_3026_, 1, lean_box(0));
lean_closure_set(v_fallback_3026_, 2, v___x_2995_);
lean_closure_set(v_fallback_3026_, 3, lean_box(0));
lean_closure_set(v_fallback_3026_, 4, lean_box(0));
lean_closure_set(v_fallback_3026_, 5, v___x_3025_);
lean_closure_set(v_fallback_3026_, 6, v___f_2994_);
v___x_3027_ = lean_apply_4(v_val_3022_, v_goI_2996_, v_goB_2997_, v_val_3004_, v_content_2999_);
v___x_3028_ = l_Lean_Doc_withRendererFallback(v_fallback_3026_, v___x_3027_, v___y_3000_, v___y_3001_, v___y_3002_);
return v___x_3028_;
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec(v_val_3004_);
lean_dec_ref(v_content_2999_);
lean_dec_ref(v_goB_2997_);
lean_dec_ref(v_goI_2996_);
lean_dec_ref(v___x_2995_);
lean_dec_ref(v___f_2994_);
lean_dec_ref(v___x_2993_);
v_a_3029_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3006_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3006_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
else
{
size_t v_sz_3037_; size_t v___x_3038_; lean_object* v___x_558__overap_3039_; lean_object* v___x_3040_; 
lean_dec_ref_known(v_container_2998_, 1);
lean_dec_ref(v_goI_2996_);
lean_dec_ref(v___x_2995_);
lean_dec_ref(v___f_2994_);
v_sz_3037_ = lean_array_size(v_content_2999_);
v___x_3038_ = ((size_t)0ULL);
v___x_558__overap_3039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2993_, v_goB_2997_, v_sz_3037_, v___x_3038_, v_content_2999_);
lean_inc(v___y_3002_);
lean_inc_ref(v___y_3001_);
lean_inc(v___y_3000_);
v___x_3040_ = lean_apply_4(v___x_558__overap_3039_, v___y_3000_, v___y_3001_, v___y_3002_, lean_box(0));
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3049_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3045_ = l_Lean_Doc_joinBlocks(v_a_3041_);
lean_dec(v_a_3041_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3045_);
v___x_3047_ = v___x_3043_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
v_a_3050_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3040_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3040_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object* v___x_3058_, lean_object* v___f_3059_, lean_object* v___x_3060_, lean_object* v_goI_3061_, lean_object* v_goB_3062_, lean_object* v_container_3063_, lean_object* v_content_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_3058_, v___f_3059_, v___x_3060_, v_goI_3061_, v_goB_3062_, v_container_3063_, v_content_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
return v_res_3069_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownBlockElabInlineElabBlock(void){
_start:
{
lean_object* v___x_3071_; lean_object* v_toApplicative_3072_; lean_object* v_toFunctor_3073_; lean_object* v_toSeq_3074_; lean_object* v_toSeqLeft_3075_; lean_object* v_toSeqRight_3076_; lean_object* v___f_3077_; lean_object* v___f_3078_; lean_object* v___f_3079_; lean_object* v___f_3080_; lean_object* v___f_3081_; lean_object* v___x_3082_; lean_object* v___f_3083_; lean_object* v___f_3084_; lean_object* v___f_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___f_3089_; 
v___x_3071_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3072_ = lean_ctor_get(v___x_3071_, 0);
v_toFunctor_3073_ = lean_ctor_get(v_toApplicative_3072_, 0);
v_toSeq_3074_ = lean_ctor_get(v_toApplicative_3072_, 2);
v_toSeqLeft_3075_ = lean_ctor_get(v_toApplicative_3072_, 3);
v_toSeqRight_3076_ = lean_ctor_get(v_toApplicative_3072_, 4);
v___f_3077_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___closed__0));
v___f_3078_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3079_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3073_, 2);
v___f_3080_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3080_, 0, v_toFunctor_3073_);
v___f_3081_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3081_, 0, v_toFunctor_3073_);
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___f_3080_);
lean_ctor_set(v___x_3082_, 1, v___f_3081_);
lean_inc(v_toSeqRight_3076_);
v___f_3083_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3083_, 0, v_toSeqRight_3076_);
lean_inc(v_toSeqLeft_3075_);
v___f_3084_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3084_, 0, v_toSeqLeft_3075_);
lean_inc(v_toSeq_3074_);
v___f_3085_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3085_, 0, v_toSeq_3074_);
v___x_3086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3082_);
lean_ctor_set(v___x_3086_, 1, v___f_3078_);
lean_ctor_set(v___x_3086_, 2, v___f_3085_);
lean_ctor_set(v___x_3086_, 3, v___f_3084_);
lean_ctor_set(v___x_3086_, 4, v___f_3083_);
v___x_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
lean_ctor_set(v___x_3087_, 1, v___f_3079_);
lean_inc_ref(v___x_3087_);
v___x_3088_ = l_StateRefT_x27_instMonad___redArg(v___x_3087_);
v___f_3089_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3089_, 0, v___x_3088_);
lean_closure_set(v___f_3089_, 1, v___f_3077_);
lean_closure_set(v___f_3089_, 2, v___x_3087_);
return v___f_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0(lean_object* v___x_3090_, lean_object* v___x_3091_, lean_object* v_part_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = lean_unsigned_to_nat(0u);
v___x_3098_ = l_Lean_Doc_partMarkdown___redArg(v___x_3090_, v___x_3091_, v___x_3097_, v_part_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed(lean_object* v___x_3099_, lean_object* v___x_3100_, lean_object* v_part_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__0(v___x_3099_, v___x_3100_, v_part_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1(lean_object* v___x_3107_, lean_object* v___x_3108_, lean_object* v___x_3109_, lean_object* v___f_3110_, lean_object* v_x_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v_text_3116_; lean_object* v_subsections_3117_; lean_object* v___x_3118_; size_t v_sz_3119_; size_t v___x_3120_; lean_object* v___x_440__overap_3121_; lean_object* v___x_3122_; 
v_text_3116_ = lean_ctor_get(v_x_3111_, 0);
lean_inc_ref(v_text_3116_);
v_subsections_3117_ = lean_ctor_get(v_x_3111_, 1);
lean_inc_ref(v_subsections_3117_);
lean_dec_ref(v_x_3111_);
v___x_3118_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3118_, 0, lean_box(0));
lean_closure_set(v___x_3118_, 1, lean_box(0));
lean_closure_set(v___x_3118_, 2, v___x_3107_);
lean_closure_set(v___x_3118_, 3, v___x_3108_);
v_sz_3119_ = lean_array_size(v_text_3116_);
v___x_3120_ = ((size_t)0ULL);
lean_inc_ref(v___x_3109_);
v___x_440__overap_3121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3109_, v___x_3118_, v_sz_3119_, v___x_3120_, v_text_3116_);
lean_inc(v___y_3114_);
lean_inc_ref(v___y_3113_);
lean_inc(v___y_3112_);
v___x_3122_ = lean_apply_4(v___x_440__overap_3121_, v___y_3112_, v___y_3113_, v___y_3114_, lean_box(0));
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; size_t v_sz_3124_; lean_object* v___x_443__overap_3125_; lean_object* v___x_3126_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___x_3122_, 1);
v_sz_3124_ = lean_array_size(v_subsections_3117_);
v___x_443__overap_3125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3109_, v___f_3110_, v_sz_3124_, v___x_3120_, v_subsections_3117_);
lean_inc(v___y_3114_);
lean_inc_ref(v___y_3113_);
lean_inc(v___y_3112_);
v___x_3126_ = lean_apply_4(v___x_443__overap_3125_, v___y_3112_, v___y_3113_, v___y_3114_, lean_box(0));
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3136_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3136_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3126_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3136_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3131_ = l_Array_append___redArg(v_a_3123_, v_a_3127_);
lean_dec(v_a_3127_);
v___x_3132_ = l_Lean_Doc_joinBlocks(v___x_3131_);
lean_dec_ref(v___x_3131_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3132_);
v___x_3134_ = v___x_3129_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v_a_3123_);
v_a_3137_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3126_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3126_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref(v_subsections_3117_);
lean_dec_ref(v___f_3110_);
lean_dec_ref(v___x_3109_);
v_a_3145_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3122_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3122_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed(lean_object* v___x_3153_, lean_object* v___x_3154_, lean_object* v___x_3155_, lean_object* v___f_3156_, lean_object* v_x_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__1(v___x_3153_, v___x_3154_, v___x_3155_, v___f_3156_, v_x_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
return v_res_3162_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0(void){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___f_3165_; 
v___x_3163_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3164_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3165_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3165_, 0, v___x_3164_);
lean_closure_set(v___f_3165_, 1, v___x_3163_);
return v___f_3165_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString(void){
_start:
{
lean_object* v___x_3166_; lean_object* v_toApplicative_3167_; lean_object* v_toFunctor_3168_; lean_object* v_toSeq_3169_; lean_object* v_toSeqLeft_3170_; lean_object* v_toSeqRight_3171_; lean_object* v___f_3172_; lean_object* v___f_3173_; lean_object* v___f_3174_; lean_object* v___f_3175_; lean_object* v___x_3176_; lean_object* v___f_3177_; lean_object* v___f_3178_; lean_object* v___f_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___f_3185_; lean_object* v___f_3186_; 
v___x_3166_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3167_ = lean_ctor_get(v___x_3166_, 0);
v_toFunctor_3168_ = lean_ctor_get(v_toApplicative_3167_, 0);
v_toSeq_3169_ = lean_ctor_get(v_toApplicative_3167_, 2);
v_toSeqLeft_3170_ = lean_ctor_get(v_toApplicative_3167_, 3);
v_toSeqRight_3171_ = lean_ctor_get(v_toApplicative_3167_, 4);
v___f_3172_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3173_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3168_, 2);
v___f_3174_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3174_, 0, v_toFunctor_3168_);
v___f_3175_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3175_, 0, v_toFunctor_3168_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___f_3174_);
lean_ctor_set(v___x_3176_, 1, v___f_3175_);
lean_inc(v_toSeqRight_3171_);
v___f_3177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3177_, 0, v_toSeqRight_3171_);
lean_inc(v_toSeqLeft_3170_);
v___f_3178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3178_, 0, v_toSeqLeft_3170_);
lean_inc(v_toSeq_3169_);
v___f_3179_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3179_, 0, v_toSeq_3169_);
v___x_3180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3176_);
lean_ctor_set(v___x_3180_, 1, v___f_3172_);
lean_ctor_set(v___x_3180_, 2, v___f_3179_);
lean_ctor_set(v___x_3180_, 3, v___f_3178_);
lean_ctor_set(v___x_3180_, 4, v___f_3177_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set(v___x_3181_, 1, v___f_3173_);
v___x_3182_ = l_StateRefT_x27_instMonad___redArg(v___x_3181_);
v___x_3183_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3184_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3185_ = lean_obj_once(&l_Lean_Doc_instToMarkdownVersoDocString___closed__0, &l_Lean_Doc_instToMarkdownVersoDocString___closed__0_once, _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0);
v___f_3186_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3186_, 0, v___x_3183_);
lean_closure_set(v___f_3186_, 1, v___x_3184_);
lean_closure_set(v___f_3186_, 2, v___x_3182_);
lean_closure_set(v___f_3186_, 3, v___f_3185_);
return v___f_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0(lean_object* v___x_3187_, lean_object* v___x_3188_, lean_object* v_x_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v_snd_3194_; lean_object* v_fst_3195_; lean_object* v_snd_3196_; lean_object* v___x_3197_; 
v_snd_3194_ = lean_ctor_get(v_x_3189_, 1);
lean_inc(v_snd_3194_);
v_fst_3195_ = lean_ctor_get(v_x_3189_, 0);
lean_inc(v_fst_3195_);
lean_dec_ref(v_x_3189_);
v_snd_3196_ = lean_ctor_get(v_snd_3194_, 1);
lean_inc(v_snd_3196_);
lean_dec(v_snd_3194_);
v___x_3197_ = l_Lean_Doc_partMarkdown___redArg(v___x_3187_, v___x_3188_, v_fst_3195_, v_snd_3196_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v_fst_3195_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_3198_, lean_object* v___x_3199_, lean_object* v_x_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_Doc_instToMarkdownSnippet___lam__0(v___x_3198_, v___x_3199_, v_x_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1(lean_object* v___x_3206_, lean_object* v___x_3207_, lean_object* v___x_3208_, lean_object* v___f_3209_, lean_object* v_x_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_text_3215_; lean_object* v_sections_3216_; lean_object* v___x_3217_; size_t v_sz_3218_; size_t v___x_3219_; lean_object* v___x_487__overap_3220_; lean_object* v___x_3221_; 
v_text_3215_ = lean_ctor_get(v_x_3210_, 0);
lean_inc_ref(v_text_3215_);
v_sections_3216_ = lean_ctor_get(v_x_3210_, 1);
lean_inc_ref(v_sections_3216_);
lean_dec_ref(v_x_3210_);
v___x_3217_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3217_, 0, lean_box(0));
lean_closure_set(v___x_3217_, 1, lean_box(0));
lean_closure_set(v___x_3217_, 2, v___x_3206_);
lean_closure_set(v___x_3217_, 3, v___x_3207_);
v_sz_3218_ = lean_array_size(v_text_3215_);
v___x_3219_ = ((size_t)0ULL);
lean_inc_ref(v___x_3208_);
v___x_487__overap_3220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3208_, v___x_3217_, v_sz_3218_, v___x_3219_, v_text_3215_);
lean_inc(v___y_3213_);
lean_inc_ref(v___y_3212_);
lean_inc(v___y_3211_);
v___x_3221_ = lean_apply_4(v___x_487__overap_3220_, v___y_3211_, v___y_3212_, v___y_3213_, lean_box(0));
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; size_t v_sz_3223_; lean_object* v___x_490__overap_3224_; lean_object* v___x_3225_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3221_, 1);
v_sz_3223_ = lean_array_size(v_sections_3216_);
v___x_490__overap_3224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3208_, v___f_3209_, v_sz_3223_, v___x_3219_, v_sections_3216_);
lean_inc(v___y_3213_);
lean_inc_ref(v___y_3212_);
lean_inc(v___y_3211_);
v___x_3225_ = lean_apply_4(v___x_490__overap_3224_, v___y_3211_, v___y_3212_, v___y_3213_, lean_box(0));
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3235_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3235_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3235_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3230_ = l_Array_append___redArg(v_a_3222_, v_a_3226_);
lean_dec(v_a_3226_);
v___x_3231_ = l_Lean_Doc_joinBlocks(v___x_3230_);
lean_dec_ref(v___x_3230_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3231_);
v___x_3233_ = v___x_3228_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec(v_a_3222_);
v_a_3236_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3225_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3225_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec_ref(v_sections_3216_);
lean_dec_ref(v___f_3209_);
lean_dec_ref(v___x_3208_);
v_a_3244_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3221_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3221_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_3252_, lean_object* v___x_3253_, lean_object* v___x_3254_, lean_object* v___f_3255_, lean_object* v_x_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Lean_Doc_instToMarkdownSnippet___lam__1(v___x_3252_, v___x_3253_, v___x_3254_, v___f_3255_, v_x_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
return v_res_3261_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___f_3264_; 
v___x_3262_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3263_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3264_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3264_, 0, v___x_3263_);
lean_closure_set(v___f_3264_, 1, v___x_3262_);
return v___f_3264_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet(void){
_start:
{
lean_object* v___x_3265_; lean_object* v_toApplicative_3266_; lean_object* v_toFunctor_3267_; lean_object* v_toSeq_3268_; lean_object* v_toSeqLeft_3269_; lean_object* v_toSeqRight_3270_; lean_object* v___f_3271_; lean_object* v___f_3272_; lean_object* v___f_3273_; lean_object* v___f_3274_; lean_object* v___x_3275_; lean_object* v___f_3276_; lean_object* v___f_3277_; lean_object* v___f_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___f_3284_; lean_object* v___f_3285_; 
v___x_3265_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3266_ = lean_ctor_get(v___x_3265_, 0);
v_toFunctor_3267_ = lean_ctor_get(v_toApplicative_3266_, 0);
v_toSeq_3268_ = lean_ctor_get(v_toApplicative_3266_, 2);
v_toSeqLeft_3269_ = lean_ctor_get(v_toApplicative_3266_, 3);
v_toSeqRight_3270_ = lean_ctor_get(v_toApplicative_3266_, 4);
v___f_3271_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3272_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3267_, 2);
v___f_3273_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3273_, 0, v_toFunctor_3267_);
v___f_3274_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3274_, 0, v_toFunctor_3267_);
v___x_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___f_3273_);
lean_ctor_set(v___x_3275_, 1, v___f_3274_);
lean_inc(v_toSeqRight_3270_);
v___f_3276_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3276_, 0, v_toSeqRight_3270_);
lean_inc(v_toSeqLeft_3269_);
v___f_3277_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3277_, 0, v_toSeqLeft_3269_);
lean_inc(v_toSeq_3268_);
v___f_3278_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3278_, 0, v_toSeq_3268_);
v___x_3279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3275_);
lean_ctor_set(v___x_3279_, 1, v___f_3271_);
lean_ctor_set(v___x_3279_, 2, v___f_3278_);
lean_ctor_set(v___x_3279_, 3, v___f_3277_);
lean_ctor_set(v___x_3279_, 4, v___f_3276_);
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
lean_ctor_set(v___x_3280_, 1, v___f_3272_);
v___x_3281_ = l_StateRefT_x27_instMonad___redArg(v___x_3280_);
v___x_3282_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3283_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3284_ = lean_obj_once(&l_Lean_Doc_instToMarkdownSnippet___closed__0, &l_Lean_Doc_instToMarkdownSnippet___closed__0_once, _init_l_Lean_Doc_instToMarkdownSnippet___closed__0);
v___f_3285_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3285_, 0, v___x_3282_);
lean_closure_set(v___f_3285_, 1, v___x_3283_);
lean_closure_set(v___f_3285_, 2, v___x_3281_);
lean_closure_set(v___f_3285_, 3, v___f_3284_);
return v___f_3285_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(lean_object* v_opts_3286_, lean_object* v_opt_3287_){
_start:
{
lean_object* v_name_3288_; lean_object* v_defValue_3289_; lean_object* v_map_3290_; lean_object* v___x_3291_; 
v_name_3288_ = lean_ctor_get(v_opt_3287_, 0);
v_defValue_3289_ = lean_ctor_get(v_opt_3287_, 1);
v_map_3290_ = lean_ctor_get(v_opts_3286_, 0);
v___x_3291_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3290_, v_name_3288_);
if (lean_obj_tag(v___x_3291_) == 0)
{
uint8_t v___x_3292_; 
v___x_3292_ = lean_unbox(v_defValue_3289_);
return v___x_3292_;
}
else
{
lean_object* v_val_3293_; 
v_val_3293_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_val_3293_);
lean_dec_ref_known(v___x_3291_, 1);
if (lean_obj_tag(v_val_3293_) == 1)
{
uint8_t v_v_3294_; 
v_v_3294_ = lean_ctor_get_uint8(v_val_3293_, 0);
lean_dec_ref_known(v_val_3293_, 0);
return v_v_3294_;
}
else
{
uint8_t v___x_3295_; 
lean_dec(v_val_3293_);
v___x_3295_ = lean_unbox(v_defValue_3289_);
return v___x_3295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0___boxed(lean_object* v_opts_3296_, lean_object* v_opt_3297_){
_start:
{
uint8_t v_res_3298_; lean_object* v_r_3299_; 
v_res_3298_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_opts_3296_, v_opt_3297_);
lean_dec_ref(v_opt_3297_);
lean_dec_ref(v_opts_3296_);
v_r_3299_ = lean_box(v_res_3298_);
return v_r_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(lean_object* v_opts_3300_, lean_object* v_opt_3301_){
_start:
{
lean_object* v_name_3302_; lean_object* v_defValue_3303_; lean_object* v_map_3304_; lean_object* v___x_3305_; 
v_name_3302_ = lean_ctor_get(v_opt_3301_, 0);
v_defValue_3303_ = lean_ctor_get(v_opt_3301_, 1);
v_map_3304_ = lean_ctor_get(v_opts_3300_, 0);
v___x_3305_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3304_, v_name_3302_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_inc(v_defValue_3303_);
return v_defValue_3303_;
}
else
{
lean_object* v_val_3306_; 
v_val_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_val_3306_);
lean_dec_ref_known(v___x_3305_, 1);
if (lean_obj_tag(v_val_3306_) == 3)
{
lean_object* v_v_3307_; 
v_v_3307_ = lean_ctor_get(v_val_3306_, 0);
lean_inc(v_v_3307_);
lean_dec_ref_known(v_val_3306_, 1);
return v_v_3307_;
}
else
{
lean_dec(v_val_3306_);
lean_inc(v_defValue_3303_);
return v_defValue_3303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1___boxed(lean_object* v_opts_3308_, lean_object* v_opt_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(v_opts_3308_, v_opt_3309_);
lean_dec_ref(v_opt_3309_);
lean_dec_ref(v_opts_3308_);
return v_res_3310_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3311_ = lean_unsigned_to_nat(32u);
v___x_3312_ = lean_mk_empty_array_with_capacity(v___x_3311_);
v___x_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
return v___x_3313_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__1(void){
_start:
{
size_t v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3314_ = ((size_t)5ULL);
v___x_3315_ = lean_unsigned_to_nat(0u);
v___x_3316_ = lean_unsigned_to_nat(32u);
v___x_3317_ = lean_mk_empty_array_with_capacity(v___x_3316_);
v___x_3318_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__0, &l_Lean_Doc_runMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__0);
v___x_3319_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
lean_ctor_set(v___x_3319_, 1, v___x_3317_);
lean_ctor_set(v___x_3319_, 2, v___x_3315_);
lean_ctor_set(v___x_3319_, 3, v___x_3315_);
lean_ctor_set_usize(v___x_3319_, 4, v___x_3314_);
return v___x_3319_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__2(void){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3320_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__3(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__2, &l_Lean_Doc_runMarkdown___redArg___closed__2_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__2);
v___x_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__4(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__3, &l_Lean_Doc_runMarkdown___redArg___closed__3_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__3);
v___x_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
return v___x_3324_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__5(void){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3325_ = l_Lean_NameSet_empty;
v___x_3326_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
lean_ctor_set(v___x_3327_, 2, v___x_3325_);
return v___x_3327_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__6(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3328_ = lean_unsigned_to_nat(1u);
v___x_3329_ = l_Lean_firstFrontendMacroScope;
v___x_3330_ = lean_nat_add(v___x_3329_, v___x_3328_);
return v___x_3330_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__11(void){
_start:
{
lean_object* v___x_3341_; uint64_t v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3342_ = 0ULL;
v___x_3343_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3343_, 0, v___x_3341_);
lean_ctor_set_uint64(v___x_3343_, sizeof(void*)*1, v___x_3342_);
return v___x_3343_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__12(void){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; lean_object* v___x_3347_; 
v___x_3344_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3345_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__3, &l_Lean_Doc_runMarkdown___redArg___closed__3_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__3);
v___x_3346_ = 1;
v___x_3347_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3347_, 0, v___x_3345_);
lean_ctor_set(v___x_3347_, 1, v___x_3345_);
lean_ctor_set(v___x_3347_, 2, v___x_3344_);
lean_ctor_set_uint8(v___x_3347_, sizeof(void*)*3, v___x_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg(lean_object* v_env_3354_, lean_object* v_act_3355_, lean_object* v_options_3356_, lean_object* v_currNamespace_3357_, lean_object* v_openDecls_3358_, lean_object* v_cancelTk_x3f_3359_){
_start:
{
lean_object* v_a_3362_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v_env_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; lean_object* v_fileName_3392_; lean_object* v_fileMap_3393_; lean_object* v_currRecDepth_3394_; lean_object* v_ref_3395_; lean_object* v_currNamespace_3396_; lean_object* v_openDecls_3397_; lean_object* v_initHeartbeats_3398_; lean_object* v_maxHeartbeats_3399_; lean_object* v_quotContext_3400_; lean_object* v_currMacroScope_3401_; lean_object* v_cancelTk_x3f_3402_; uint8_t v_suppressElabErrors_3403_; lean_object* v_inheritedTraceOptions_3404_; lean_object* v___y_3405_; uint8_t v___y_3442_; uint8_t v___x_3462_; 
v___x_3365_ = lean_unsigned_to_nat(0u);
v___x_3366_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__4, &l_Lean_Doc_runMarkdown___redArg___closed__4_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__4);
v___x_3367_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__5, &l_Lean_Doc_runMarkdown___redArg___closed__5_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__5);
v___x_3368_ = lean_io_get_num_heartbeats();
v___x_3369_ = l_Lean_firstFrontendMacroScope;
v___x_3370_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__6, &l_Lean_Doc_runMarkdown___redArg___closed__6_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__6);
v___x_3371_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__9));
v___x_3372_ = lean_box(0);
v___x_3373_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__10));
v___x_3374_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__11, &l_Lean_Doc_runMarkdown___redArg___closed__11_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__11);
v___x_3375_ = 1;
v___x_3376_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__12, &l_Lean_Doc_runMarkdown___redArg___closed__12_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__12);
v___x_3377_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__13));
v___x_3378_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3378_, 0, v_env_3354_);
lean_ctor_set(v___x_3378_, 1, v___x_3370_);
lean_ctor_set(v___x_3378_, 2, v___x_3371_);
lean_ctor_set(v___x_3378_, 3, v___x_3373_);
lean_ctor_set(v___x_3378_, 4, v___x_3374_);
lean_ctor_set(v___x_3378_, 5, v___x_3366_);
lean_ctor_set(v___x_3378_, 6, v___x_3367_);
lean_ctor_set(v___x_3378_, 7, v___x_3376_);
lean_ctor_set(v___x_3378_, 8, v___x_3377_);
v___x_3379_ = lean_st_mk_ref(v___x_3378_);
v___x_3380_ = l_Lean_inheritedTraceOptions;
v___x_3381_ = lean_st_ref_get(v___x_3380_);
v___x_3382_ = lean_st_ref_get(v___x_3379_);
v_env_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc_ref(v_env_3383_);
lean_dec(v___x_3382_);
v___x_3384_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__14));
v___x_3385_ = l_Lean_instInhabitedFileMap_default;
v___x_3386_ = lean_box(0);
v___x_3387_ = l_Lean_Core_getMaxHeartbeats(v_options_3356_);
v___x_3388_ = 0;
v___x_3389_ = l_Lean_diagnostics;
v___x_3390_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_options_3356_, v___x_3389_);
v___x_3462_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3383_);
lean_dec_ref(v_env_3383_);
if (v___x_3390_ == 0)
{
if (v___x_3462_ == 0)
{
lean_inc(v___x_3379_);
v_fileName_3392_ = v___x_3384_;
v_fileMap_3393_ = v___x_3385_;
v_currRecDepth_3394_ = v___x_3365_;
v_ref_3395_ = v___x_3386_;
v_currNamespace_3396_ = v_currNamespace_3357_;
v_openDecls_3397_ = v_openDecls_3358_;
v_initHeartbeats_3398_ = v___x_3368_;
v_maxHeartbeats_3399_ = v___x_3387_;
v_quotContext_3400_ = v___x_3372_;
v_currMacroScope_3401_ = v___x_3369_;
v_cancelTk_x3f_3402_ = v_cancelTk_x3f_3359_;
v_suppressElabErrors_3403_ = v___x_3388_;
v_inheritedTraceOptions_3404_ = v___x_3381_;
v___y_3405_ = v___x_3379_;
goto v___jp_3391_;
}
else
{
v___y_3442_ = v___x_3390_;
goto v___jp_3441_;
}
}
else
{
v___y_3442_ = v___x_3462_;
goto v___jp_3441_;
}
v___jp_3361_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = lean_mk_io_user_error(v_a_3362_);
v___x_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
return v___x_3364_;
}
v___jp_3391_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3406_ = l_Lean_maxRecDepth;
v___x_3407_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(v_options_3356_, v___x_3406_);
lean_inc(v_currMacroScope_3401_);
lean_inc(v_quotContext_3400_);
lean_inc(v_ref_3395_);
lean_inc_ref(v_fileMap_3393_);
lean_inc_ref(v_fileName_3392_);
v___x_3408_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3408_, 0, v_fileName_3392_);
lean_ctor_set(v___x_3408_, 1, v_fileMap_3393_);
lean_ctor_set(v___x_3408_, 2, v_options_3356_);
lean_ctor_set(v___x_3408_, 3, v_currRecDepth_3394_);
lean_ctor_set(v___x_3408_, 4, v___x_3407_);
lean_ctor_set(v___x_3408_, 5, v_ref_3395_);
lean_ctor_set(v___x_3408_, 6, v_currNamespace_3396_);
lean_ctor_set(v___x_3408_, 7, v_openDecls_3397_);
lean_ctor_set(v___x_3408_, 8, v_initHeartbeats_3398_);
lean_ctor_set(v___x_3408_, 9, v_maxHeartbeats_3399_);
lean_ctor_set(v___x_3408_, 10, v_quotContext_3400_);
lean_ctor_set(v___x_3408_, 11, v_currMacroScope_3401_);
lean_ctor_set(v___x_3408_, 12, v_cancelTk_x3f_3402_);
lean_ctor_set(v___x_3408_, 13, v_inheritedTraceOptions_3404_);
lean_ctor_set_uint8(v___x_3408_, sizeof(void*)*14, v___x_3390_);
lean_ctor_set_uint8(v___x_3408_, sizeof(void*)*14 + 1, v_suppressElabErrors_3403_);
v___x_3409_ = lean_apply_3(v_act_3355_, v___x_3408_, v___y_3405_, lean_box(0));
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3418_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3412_ = v___x_3409_;
v_isShared_3413_ = v_isSharedCheck_3418_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3409_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3418_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
v___x_3414_ = lean_st_ref_get(v___x_3379_);
lean_dec(v___x_3379_);
lean_dec(v___x_3414_);
if (v_isShared_3413_ == 0)
{
v___x_3416_ = v___x_3412_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3410_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3440_; 
lean_dec(v___x_3379_);
v_a_3419_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3421_ = v___x_3409_;
v_isShared_3422_ = v_isSharedCheck_3440_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3409_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3440_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
if (lean_obj_tag(v_a_3419_) == 0)
{
lean_object* v_msg_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
v_msg_3423_ = lean_ctor_get(v_a_3419_, 1);
lean_inc_ref(v_msg_3423_);
lean_dec_ref_known(v_a_3419_, 2);
v___x_3424_ = l_Lean_MessageData_toString(v_msg_3423_);
v___x_3425_ = lean_mk_io_user_error(v___x_3424_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3425_);
v___x_3427_ = v___x_3421_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
else
{
lean_object* v_id_3429_; lean_object* v___x_3430_; 
lean_del_object(v___x_3421_);
v_id_3429_ = lean_ctor_get(v_a_3419_, 0);
lean_inc(v_id_3429_);
lean_dec_ref_known(v_a_3419_, 2);
v___x_3430_ = l_Lean_InternalExceptionId_getName(v_id_3429_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_dec(v_id_3429_);
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3430_, 1);
v___x_3432_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__15));
v___x_3433_ = l_Lean_Name_toString(v_a_3431_, v___x_3375_);
v___x_3434_ = lean_string_append(v___x_3432_, v___x_3433_);
lean_dec_ref(v___x_3433_);
v_a_3362_ = v___x_3434_;
goto v___jp_3361_;
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
lean_dec_ref_known(v___x_3430_, 1);
v___x_3435_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__16));
v___x_3436_ = l_Nat_reprFast(v_id_3429_);
v___x_3437_ = lean_string_append(v___x_3435_, v___x_3436_);
lean_dec_ref(v___x_3436_);
v___x_3438_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__17));
v___x_3439_ = lean_string_append(v___x_3437_, v___x_3438_);
v_a_3362_ = v___x_3439_;
goto v___jp_3361_;
}
}
}
}
}
v___jp_3441_:
{
if (v___y_3442_ == 0)
{
lean_object* v___x_3443_; lean_object* v_env_3444_; lean_object* v_nextMacroScope_3445_; lean_object* v_ngen_3446_; lean_object* v_auxDeclNGen_3447_; lean_object* v_traceState_3448_; lean_object* v_messages_3449_; lean_object* v_infoState_3450_; lean_object* v_snapshotTasks_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3460_; 
v___x_3443_ = lean_st_ref_take(v___x_3379_);
v_env_3444_ = lean_ctor_get(v___x_3443_, 0);
v_nextMacroScope_3445_ = lean_ctor_get(v___x_3443_, 1);
v_ngen_3446_ = lean_ctor_get(v___x_3443_, 2);
v_auxDeclNGen_3447_ = lean_ctor_get(v___x_3443_, 3);
v_traceState_3448_ = lean_ctor_get(v___x_3443_, 4);
v_messages_3449_ = lean_ctor_get(v___x_3443_, 6);
v_infoState_3450_ = lean_ctor_get(v___x_3443_, 7);
v_snapshotTasks_3451_ = lean_ctor_get(v___x_3443_, 8);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v___x_3443_, 5);
lean_dec(v_unused_3461_);
v___x_3453_ = v___x_3443_;
v_isShared_3454_ = v_isSharedCheck_3460_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_snapshotTasks_3451_);
lean_inc(v_infoState_3450_);
lean_inc(v_messages_3449_);
lean_inc(v_traceState_3448_);
lean_inc(v_auxDeclNGen_3447_);
lean_inc(v_ngen_3446_);
lean_inc(v_nextMacroScope_3445_);
lean_inc(v_env_3444_);
lean_dec(v___x_3443_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3460_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3455_ = l_Lean_Kernel_enableDiag(v_env_3444_, v___x_3390_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 5, v___x_3366_);
lean_ctor_set(v___x_3453_, 0, v___x_3455_);
v___x_3457_ = v___x_3453_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_nextMacroScope_3445_);
lean_ctor_set(v_reuseFailAlloc_3459_, 2, v_ngen_3446_);
lean_ctor_set(v_reuseFailAlloc_3459_, 3, v_auxDeclNGen_3447_);
lean_ctor_set(v_reuseFailAlloc_3459_, 4, v_traceState_3448_);
lean_ctor_set(v_reuseFailAlloc_3459_, 5, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3459_, 6, v_messages_3449_);
lean_ctor_set(v_reuseFailAlloc_3459_, 7, v_infoState_3450_);
lean_ctor_set(v_reuseFailAlloc_3459_, 8, v_snapshotTasks_3451_);
v___x_3457_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_st_ref_put(v___x_3379_, v___x_3457_);
lean_inc(v___x_3379_);
v_fileName_3392_ = v___x_3384_;
v_fileMap_3393_ = v___x_3385_;
v_currRecDepth_3394_ = v___x_3365_;
v_ref_3395_ = v___x_3386_;
v_currNamespace_3396_ = v_currNamespace_3357_;
v_openDecls_3397_ = v_openDecls_3358_;
v_initHeartbeats_3398_ = v___x_3368_;
v_maxHeartbeats_3399_ = v___x_3387_;
v_quotContext_3400_ = v___x_3372_;
v_currMacroScope_3401_ = v___x_3369_;
v_cancelTk_x3f_3402_ = v_cancelTk_x3f_3359_;
v_suppressElabErrors_3403_ = v___x_3388_;
v_inheritedTraceOptions_3404_ = v___x_3381_;
v___y_3405_ = v___x_3379_;
goto v___jp_3391_;
}
}
}
else
{
lean_inc(v___x_3379_);
v_fileName_3392_ = v___x_3384_;
v_fileMap_3393_ = v___x_3385_;
v_currRecDepth_3394_ = v___x_3365_;
v_ref_3395_ = v___x_3386_;
v_currNamespace_3396_ = v_currNamespace_3357_;
v_openDecls_3397_ = v_openDecls_3358_;
v_initHeartbeats_3398_ = v___x_3368_;
v_maxHeartbeats_3399_ = v___x_3387_;
v_quotContext_3400_ = v___x_3372_;
v_currMacroScope_3401_ = v___x_3369_;
v_cancelTk_x3f_3402_ = v_cancelTk_x3f_3359_;
v_suppressElabErrors_3403_ = v___x_3388_;
v_inheritedTraceOptions_3404_ = v___x_3381_;
v___y_3405_ = v___x_3379_;
goto v___jp_3391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg___boxed(lean_object* v_env_3463_, lean_object* v_act_3464_, lean_object* v_options_3465_, lean_object* v_currNamespace_3466_, lean_object* v_openDecls_3467_, lean_object* v_cancelTk_x3f_3468_, lean_object* v_a_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_Doc_runMarkdown___redArg(v_env_3463_, v_act_3464_, v_options_3465_, v_currNamespace_3466_, v_openDecls_3467_, v_cancelTk_x3f_3468_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown(lean_object* v_00_u03b1_3471_, lean_object* v_env_3472_, lean_object* v_act_3473_, lean_object* v_options_3474_, lean_object* v_currNamespace_3475_, lean_object* v_openDecls_3476_, lean_object* v_cancelTk_x3f_3477_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l_Lean_Doc_runMarkdown___redArg(v_env_3472_, v_act_3473_, v_options_3474_, v_currNamespace_3475_, v_openDecls_3476_, v_cancelTk_x3f_3477_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___boxed(lean_object* v_00_u03b1_3480_, lean_object* v_env_3481_, lean_object* v_act_3482_, lean_object* v_options_3483_, lean_object* v_currNamespace_3484_, lean_object* v_openDecls_3485_, lean_object* v_cancelTk_x3f_3486_, lean_object* v_a_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_Doc_runMarkdown(v_00_u03b1_3480_, v_env_3481_, v_act_3482_, v_options_3483_, v_currNamespace_3484_, v_openDecls_3485_, v_cancelTk_x3f_3486_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(lean_object* v_x_3489_, size_t v_sz_3490_, size_t v_i_3491_, lean_object* v_bs_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
uint8_t v___x_3497_; 
v___x_3497_ = lean_usize_dec_lt(v_i_3491_, v_sz_3490_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; 
lean_dec_ref(v_x_3489_);
v___x_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3498_, 0, v_bs_3492_);
return v___x_3498_;
}
else
{
lean_object* v_v_3499_; lean_object* v___x_3500_; 
v_v_3499_ = lean_array_uget_borrowed(v_bs_3492_, v_i_3491_);
lean_inc(v_v_3499_);
lean_inc_ref(v_x_3489_);
v___x_3500_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3489_, v_v_3499_, v___y_3493_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3502_; lean_object* v_bs_x27_3503_; size_t v___x_3504_; size_t v___x_3505_; lean_object* v___x_3506_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = lean_unsigned_to_nat(0u);
v_bs_x27_3503_ = lean_array_uset(v_bs_3492_, v_i_3491_, v___x_3502_);
v___x_3504_ = ((size_t)1ULL);
v___x_3505_ = lean_usize_add(v_i_3491_, v___x_3504_);
v___x_3506_ = lean_array_uset(v_bs_x27_3503_, v_i_3491_, v_a_3501_);
v_i_3491_ = v___x_3505_;
v_bs_3492_ = v___x_3506_;
goto _start;
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v_bs_3492_);
lean_dec_ref(v_x_3489_);
v_a_3508_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3500_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3500_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed(lean_object* v_x_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(v_x_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(lean_object* v_x_3525_, size_t v_sz_3526_, size_t v___x_3527_, lean_object* v_content_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3525_, v_sz_3526_, v___x_3527_, v_content_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3542_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3536_ = v___x_3533_;
v_isShared_3537_ = v_isSharedCheck_3542_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3533_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3542_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3538_; lean_object* v___x_3540_; 
v___x_3538_ = l_Lean_Doc_joinInlines(v_a_3534_);
lean_dec(v_a_3534_);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v___x_3538_);
v___x_3540_ = v___x_3536_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
v_a_3543_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3533_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3533_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed(lean_object* v_x_3551_, lean_object* v_sz_3552_, lean_object* v___x_3553_, lean_object* v_content_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
size_t v_sz_boxed_3559_; size_t v___x_3971__boxed_3560_; lean_object* v_res_3561_; 
v_sz_boxed_3559_ = lean_unbox_usize(v_sz_3552_);
lean_dec(v_sz_3552_);
v___x_3971__boxed_3560_ = lean_unbox_usize(v___x_3553_);
lean_dec(v___x_3553_);
v_res_3561_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(v_x_3551_, v_sz_boxed_3559_, v___x_3971__boxed_3560_, v_content_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(lean_object* v_x_3562_, lean_object* v_x_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v_pieces_3569_; lean_object* v_pieces_3573_; 
switch(lean_obj_tag(v_x_3563_))
{
case 0:
{
lean_object* v_string_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
lean_dec_ref(v_x_3562_);
v_string_3576_ = lean_ctor_get(v_x_3563_, 0);
lean_inc_ref(v_string_3576_);
lean_dec_ref_known(v_x_3563_, 1);
v___x_3577_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_3576_);
lean_dec_ref(v_string_3576_);
v___x_3578_ = lean_unsigned_to_nat(1u);
v___x_3579_ = lean_mk_empty_array_with_capacity(v___x_3578_);
v___x_3580_ = lean_array_push(v___x_3579_, v___x_3577_);
v___x_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
return v___x_3581_;
}
case 1:
{
lean_object* v_content_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3637_; 
v_content_3582_ = lean_ctor_get(v_x_3563_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_x_3563_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3584_ = v_x_3563_;
v_isShared_3585_ = v_isSharedCheck_3637_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_content_3582_);
lean_dec(v_x_3563_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3637_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set_tag(v___x_3584_, 9);
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_content_3582_);
v___x_3587_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3588_; lean_object* v_snd_3589_; lean_object* v_fst_3590_; lean_object* v_fst_3591_; lean_object* v_snd_3592_; lean_object* v_pieces_3594_; uint8_t v_inEmph_3602_; uint8_t v_inBold_3603_; uint8_t v_inLink_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3635_; 
v___x_3588_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3587_);
v_snd_3589_ = lean_ctor_get(v___x_3588_, 1);
lean_inc(v_snd_3589_);
v_fst_3590_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_fst_3590_);
lean_dec_ref(v___x_3588_);
v_fst_3591_ = lean_ctor_get(v_snd_3589_, 0);
lean_inc(v_fst_3591_);
v_snd_3592_ = lean_ctor_get(v_snd_3589_, 1);
lean_inc(v_snd_3592_);
lean_dec(v_snd_3589_);
v_inEmph_3602_ = lean_ctor_get_uint8(v_x_3562_, 0);
v_inBold_3603_ = lean_ctor_get_uint8(v_x_3562_, 1);
v_inLink_3604_ = lean_ctor_get_uint8(v_x_3562_, 2);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_x_3562_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3606_ = v_x_3562_;
v_isShared_3607_ = v_isSharedCheck_3635_;
goto v_resetjp_3605_;
}
else
{
lean_dec(v_x_3562_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3635_;
goto v_resetjp_3605_;
}
v___jp_3593_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; uint8_t v___x_3597_; 
v___x_3595_ = lean_string_utf8_byte_size(v_snd_3592_);
v___x_3596_ = lean_unsigned_to_nat(0u);
v___x_3597_ = lean_nat_dec_eq(v___x_3595_, v___x_3596_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3598_ = lean_unsigned_to_nat(1u);
v___x_3599_ = lean_mk_empty_array_with_capacity(v___x_3598_);
v___x_3600_ = lean_array_push(v___x_3599_, v_snd_3592_);
v___x_3601_ = lean_array_push(v_pieces_3594_, v___x_3600_);
v_pieces_3573_ = v___x_3601_;
goto v___jp_3572_;
}
else
{
lean_dec(v_snd_3592_);
v_pieces_3573_ = v_pieces_3594_;
goto v___jp_3572_;
}
}
v_resetjp_3605_:
{
uint8_t v___x_3608_; lean_object* v___x_3610_; 
v___x_3608_ = 1;
if (v_isShared_3607_ == 0)
{
v___x_3610_ = v___x_3606_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3634_, 1, v_inBold_3603_);
lean_ctor_set_uint8(v_reuseFailAlloc_3634_, 2, v_inLink_3604_);
v___x_3610_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; 
lean_ctor_set_uint8(v___x_3610_, 0, v___x_3608_);
v___x_3611_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3610_, v_fst_3591_, v_a_3564_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v_pieces_3614_; lean_object* v_pieces_3621_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; uint8_t v___x_3629_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v___x_3611_, 1);
v___x_3626_ = lean_unsigned_to_nat(0u);
v___x_3627_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3628_ = lean_string_utf8_byte_size(v_fst_3590_);
v___x_3629_ = lean_nat_dec_eq(v___x_3628_, v___x_3626_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3630_ = lean_unsigned_to_nat(1u);
v___x_3631_ = lean_mk_empty_array_with_capacity(v___x_3630_);
v___x_3632_ = lean_array_push(v___x_3631_, v_fst_3590_);
v___x_3633_ = lean_array_push(v___x_3627_, v___x_3632_);
v_pieces_3621_ = v___x_3633_;
goto v___jp_3620_;
}
else
{
lean_dec(v_fst_3590_);
v_pieces_3621_ = v___x_3627_;
goto v___jp_3620_;
}
v___jp_3613_:
{
lean_object* v___x_3615_; 
v___x_3615_ = lean_array_push(v_pieces_3614_, v_a_3612_);
if (v_inEmph_3602_ == 0)
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3616_ = lean_unsigned_to_nat(1u);
v___x_3617_ = lean_mk_empty_array_with_capacity(v___x_3616_);
lean_dec_ref(v___x_3617_);
v___x_3618_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3619_ = lean_array_push(v___x_3615_, v___x_3618_);
v_pieces_3594_ = v___x_3619_;
goto v___jp_3593_;
}
else
{
v_pieces_3594_ = v___x_3615_;
goto v___jp_3593_;
}
}
v___jp_3620_:
{
if (v_inEmph_3602_ == 0)
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3622_ = lean_unsigned_to_nat(1u);
v___x_3623_ = lean_mk_empty_array_with_capacity(v___x_3622_);
lean_dec_ref(v___x_3623_);
v___x_3624_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3625_ = lean_array_push(v_pieces_3621_, v___x_3624_);
v_pieces_3614_ = v___x_3625_;
goto v___jp_3613_;
}
else
{
v_pieces_3614_ = v_pieces_3621_;
goto v___jp_3613_;
}
}
}
else
{
lean_dec(v_snd_3592_);
lean_dec(v_fst_3590_);
return v___x_3611_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3693_; 
v_content_3638_ = lean_ctor_get(v_x_3563_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_x_3563_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3640_ = v_x_3563_;
v_isShared_3641_ = v_isSharedCheck_3693_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_content_3638_);
lean_dec(v_x_3563_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3693_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
lean_ctor_set_tag(v___x_3640_, 9);
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_content_3638_);
v___x_3643_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3644_; lean_object* v_snd_3645_; lean_object* v_fst_3646_; lean_object* v_fst_3647_; lean_object* v_snd_3648_; lean_object* v_pieces_3650_; uint8_t v_inEmph_3658_; uint8_t v_inBold_3659_; uint8_t v_inLink_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3691_; 
v___x_3644_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3643_);
v_snd_3645_ = lean_ctor_get(v___x_3644_, 1);
lean_inc(v_snd_3645_);
v_fst_3646_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_fst_3646_);
lean_dec_ref(v___x_3644_);
v_fst_3647_ = lean_ctor_get(v_snd_3645_, 0);
lean_inc(v_fst_3647_);
v_snd_3648_ = lean_ctor_get(v_snd_3645_, 1);
lean_inc(v_snd_3648_);
lean_dec(v_snd_3645_);
v_inEmph_3658_ = lean_ctor_get_uint8(v_x_3562_, 0);
v_inBold_3659_ = lean_ctor_get_uint8(v_x_3562_, 1);
v_inLink_3660_ = lean_ctor_get_uint8(v_x_3562_, 2);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_x_3562_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3662_ = v_x_3562_;
v_isShared_3663_ = v_isSharedCheck_3691_;
goto v_resetjp_3661_;
}
else
{
lean_dec(v_x_3562_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3691_;
goto v_resetjp_3661_;
}
v___jp_3649_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; uint8_t v___x_3653_; 
v___x_3651_ = lean_string_utf8_byte_size(v_snd_3648_);
v___x_3652_ = lean_unsigned_to_nat(0u);
v___x_3653_ = lean_nat_dec_eq(v___x_3651_, v___x_3652_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3654_ = lean_unsigned_to_nat(1u);
v___x_3655_ = lean_mk_empty_array_with_capacity(v___x_3654_);
v___x_3656_ = lean_array_push(v___x_3655_, v_snd_3648_);
v___x_3657_ = lean_array_push(v_pieces_3650_, v___x_3656_);
v_pieces_3569_ = v___x_3657_;
goto v___jp_3568_;
}
else
{
lean_dec(v_snd_3648_);
v_pieces_3569_ = v_pieces_3650_;
goto v___jp_3568_;
}
}
v_resetjp_3661_:
{
uint8_t v___x_3664_; lean_object* v___x_3666_; 
v___x_3664_ = 1;
if (v_isShared_3663_ == 0)
{
v___x_3666_ = v___x_3662_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 0, v_inEmph_3658_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 2, v_inLink_3660_);
v___x_3666_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3667_; 
lean_ctor_set_uint8(v___x_3666_, 1, v___x_3664_);
v___x_3667_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3666_, v_fst_3647_, v_a_3564_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v_pieces_3670_; lean_object* v_pieces_3677_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref_known(v___x_3667_, 1);
v___x_3682_ = lean_unsigned_to_nat(0u);
v___x_3683_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3684_ = lean_string_utf8_byte_size(v_fst_3646_);
v___x_3685_ = lean_nat_dec_eq(v___x_3684_, v___x_3682_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3686_ = lean_unsigned_to_nat(1u);
v___x_3687_ = lean_mk_empty_array_with_capacity(v___x_3686_);
v___x_3688_ = lean_array_push(v___x_3687_, v_fst_3646_);
v___x_3689_ = lean_array_push(v___x_3683_, v___x_3688_);
v_pieces_3677_ = v___x_3689_;
goto v___jp_3676_;
}
else
{
lean_dec(v_fst_3646_);
v_pieces_3677_ = v___x_3683_;
goto v___jp_3676_;
}
v___jp_3669_:
{
lean_object* v___x_3671_; 
v___x_3671_ = lean_array_push(v_pieces_3670_, v_a_3668_);
if (v_inBold_3659_ == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3672_ = lean_unsigned_to_nat(1u);
v___x_3673_ = lean_mk_empty_array_with_capacity(v___x_3672_);
lean_dec_ref(v___x_3673_);
v___x_3674_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3675_ = lean_array_push(v___x_3671_, v___x_3674_);
v_pieces_3650_ = v___x_3675_;
goto v___jp_3649_;
}
else
{
v_pieces_3650_ = v___x_3671_;
goto v___jp_3649_;
}
}
v___jp_3676_:
{
if (v_inBold_3659_ == 0)
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3678_ = lean_unsigned_to_nat(1u);
v___x_3679_ = lean_mk_empty_array_with_capacity(v___x_3678_);
lean_dec_ref(v___x_3679_);
v___x_3680_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3681_ = lean_array_push(v_pieces_3677_, v___x_3680_);
v_pieces_3670_ = v___x_3681_;
goto v___jp_3669_;
}
else
{
v_pieces_3670_ = v_pieces_3677_;
goto v___jp_3669_;
}
}
}
else
{
lean_dec(v_snd_3648_);
lean_dec(v_fst_3646_);
return v___x_3667_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec_ref(v_x_3562_);
v_string_3694_ = lean_ctor_get(v_x_3563_, 0);
lean_inc_ref(v_string_3694_);
lean_dec_ref_known(v_x_3563_, 1);
v___x_3695_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_3694_);
v___x_3696_ = lean_unsigned_to_nat(1u);
v___x_3697_ = lean_mk_empty_array_with_capacity(v___x_3696_);
v___x_3698_ = lean_array_push(v___x_3697_, v___x_3695_);
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
case 4:
{
uint8_t v_mode_3700_; 
lean_dec_ref(v_x_3562_);
v_mode_3700_ = lean_ctor_get_uint8(v_x_3563_, sizeof(void*)*1);
if (v_mode_3700_ == 0)
{
lean_object* v_string_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v_string_3701_ = lean_ctor_get(v_x_3563_, 0);
lean_inc_ref(v_string_3701_);
lean_dec_ref_known(v_x_3563_, 1);
v___x_3702_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_3703_ = lean_string_append(v___x_3702_, v_string_3701_);
lean_dec_ref(v_string_3701_);
v___x_3704_ = lean_string_append(v___x_3703_, v___x_3702_);
v___x_3705_ = lean_unsigned_to_nat(1u);
v___x_3706_ = lean_mk_empty_array_with_capacity(v___x_3705_);
v___x_3707_ = lean_array_push(v___x_3706_, v___x_3704_);
v___x_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
return v___x_3708_;
}
else
{
lean_object* v_string_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v_string_3709_ = lean_ctor_get(v_x_3563_, 0);
lean_inc_ref(v_string_3709_);
lean_dec_ref_known(v_x_3563_, 1);
v___x_3710_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_3711_ = lean_string_append(v___x_3710_, v_string_3709_);
lean_dec_ref(v_string_3709_);
v___x_3712_ = lean_string_append(v___x_3711_, v___x_3710_);
v___x_3713_ = lean_unsigned_to_nat(1u);
v___x_3714_ = lean_mk_empty_array_with_capacity(v___x_3713_);
v___x_3715_ = lean_array_push(v___x_3714_, v___x_3712_);
v___x_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
return v___x_3716_;
}
}
case 5:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
lean_dec_ref_known(v_x_3563_, 1);
lean_dec_ref(v_x_3562_);
v___x_3717_ = lean_unsigned_to_nat(2u);
v___x_3718_ = lean_mk_empty_array_with_capacity(v___x_3717_);
lean_dec_ref(v___x_3718_);
v___x_3719_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
return v___x_3720_;
}
case 6:
{
uint8_t v_inLink_3721_; 
v_inLink_3721_ = lean_ctor_get_uint8(v_x_3562_, 2);
if (v_inLink_3721_ == 0)
{
lean_object* v_content_3722_; lean_object* v_url_3723_; uint8_t v_inEmph_3724_; uint8_t v_inBold_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3756_; 
v_content_3722_ = lean_ctor_get(v_x_3563_, 0);
lean_inc_ref(v_content_3722_);
v_url_3723_ = lean_ctor_get(v_x_3563_, 1);
lean_inc_ref(v_url_3723_);
lean_dec_ref_known(v_x_3563_, 2);
v_inEmph_3724_ = lean_ctor_get_uint8(v_x_3562_, 0);
v_inBold_3725_ = lean_ctor_get_uint8(v_x_3562_, 1);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_x_3562_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3727_ = v_x_3562_;
v_isShared_3728_ = v_isSharedCheck_3756_;
goto v_resetjp_3726_;
}
else
{
lean_dec(v_x_3562_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3756_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
uint8_t v___x_3729_; lean_object* v___x_3731_; 
v___x_3729_ = 1;
if (v_isShared_3728_ == 0)
{
v___x_3731_ = v___x_3727_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3755_, 0, v_inEmph_3724_);
lean_ctor_set_uint8(v_reuseFailAlloc_3755_, 1, v_inBold_3725_);
v___x_3731_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
lean_ctor_set_uint8(v___x_3731_, 2, v___x_3729_);
v___x_3732_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3732_, 0, v_content_3722_);
v___x_3733_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3731_, v___x_3732_, v_a_3564_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3754_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3754_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3754_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
v___x_3738_ = lean_unsigned_to_nat(1u);
v___x_3739_ = lean_mk_empty_array_with_capacity(v___x_3738_);
v___x_3740_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3741_ = lean_string_append(v___x_3740_, v_url_3723_);
lean_dec_ref(v_url_3723_);
v___x_3742_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3743_ = lean_string_append(v___x_3741_, v___x_3742_);
v___x_3744_ = lean_array_push(v___x_3739_, v___x_3743_);
v___x_3745_ = lean_unsigned_to_nat(3u);
v___x_3746_ = lean_mk_empty_array_with_capacity(v___x_3745_);
lean_dec_ref(v___x_3746_);
v___x_3747_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_3748_ = lean_array_push(v___x_3747_, v_a_3734_);
v___x_3749_ = lean_array_push(v___x_3748_, v___x_3744_);
v___x_3750_ = l_Lean_Doc_joinInlines(v___x_3749_);
lean_dec_ref(v___x_3749_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v___x_3750_);
v___x_3752_ = v___x_3736_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
else
{
lean_dec_ref(v_url_3723_);
return v___x_3733_;
}
}
}
}
else
{
lean_object* v_content_3757_; size_t v_sz_3758_; size_t v___x_3759_; lean_object* v___x_3760_; 
v_content_3757_ = lean_ctor_get(v_x_3563_, 0);
lean_inc_ref(v_content_3757_);
lean_dec_ref_known(v_x_3563_, 2);
v_sz_3758_ = lean_array_size(v_content_3757_);
v___x_3759_ = ((size_t)0ULL);
v___x_3760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3562_, v_sz_3758_, v___x_3759_, v_content_3757_, v_a_3564_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3769_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3769_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3769_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
v___x_3765_ = l_Lean_Doc_joinInlines(v_a_3761_);
lean_dec(v_a_3761_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3765_);
v___x_3767_ = v___x_3763_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
v_a_3770_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3760_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3760_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
}
case 7:
{
lean_object* v_name_3778_; lean_object* v_content_3779_; size_t v_sz_3780_; size_t v___x_3781_; lean_object* v___x_3782_; 
v_name_3778_ = lean_ctor_get(v_x_3563_, 0);
lean_inc_ref(v_name_3778_);
v_content_3779_ = lean_ctor_get(v_x_3563_, 1);
lean_inc_ref(v_content_3779_);
lean_dec_ref_known(v_x_3563_, 2);
v_sz_3780_ = lean_array_size(v_content_3779_);
v___x_3781_ = ((size_t)0ULL);
v___x_3782_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3562_, v_sz_3780_, v___x_3781_, v_content_3779_, v_a_3564_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
v___x_3784_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_3785_ = l_Lean_Doc_joinInlines(v_a_3783_);
lean_dec(v_a_3783_);
v___x_3786_ = lean_array_to_list(v___x_3785_);
v___x_3787_ = l_String_intercalate(v___x_3784_, v___x_3786_);
lean_inc_ref(v_name_3778_);
v___x_3788_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_3778_, v___x_3787_, v_a_3564_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3802_; 
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3802_ == 0)
{
lean_object* v_unused_3803_; 
v_unused_3803_ = lean_ctor_get(v___x_3788_, 0);
lean_dec(v_unused_3803_);
v___x_3790_ = v___x_3788_;
v_isShared_3791_ = v_isSharedCheck_3802_;
goto v_resetjp_3789_;
}
else
{
lean_dec(v___x_3788_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3802_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3800_; 
v___x_3792_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_3793_ = lean_string_append(v___x_3792_, v_name_3778_);
lean_dec_ref(v_name_3778_);
v___x_3794_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_3795_ = lean_string_append(v___x_3793_, v___x_3794_);
v___x_3796_ = lean_unsigned_to_nat(1u);
v___x_3797_ = lean_mk_empty_array_with_capacity(v___x_3796_);
v___x_3798_ = lean_array_push(v___x_3797_, v___x_3795_);
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v___x_3798_);
v___x_3800_ = v___x_3790_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
lean_dec_ref(v_name_3778_);
v_a_3804_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3788_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3788_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v_name_3778_);
v_a_3812_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3782_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3782_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
case 8:
{
lean_object* v_alt_3820_; lean_object* v_url_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
lean_dec_ref(v_x_3562_);
v_alt_3820_ = lean_ctor_get(v_x_3563_, 0);
lean_inc_ref(v_alt_3820_);
v_url_3821_ = lean_ctor_get(v_x_3563_, 1);
lean_inc_ref(v_url_3821_);
lean_dec_ref_known(v_x_3563_, 2);
v___x_3822_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_3823_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_3820_);
lean_dec_ref(v_alt_3820_);
v___x_3824_ = lean_string_append(v___x_3822_, v___x_3823_);
lean_dec_ref(v___x_3823_);
v___x_3825_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3826_ = lean_string_append(v___x_3824_, v___x_3825_);
v___x_3827_ = lean_string_append(v___x_3826_, v_url_3821_);
lean_dec_ref(v_url_3821_);
v___x_3828_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3829_ = lean_string_append(v___x_3827_, v___x_3828_);
v___x_3830_ = lean_unsigned_to_nat(1u);
v___x_3831_ = lean_mk_empty_array_with_capacity(v___x_3830_);
v___x_3832_ = lean_array_push(v___x_3831_, v___x_3829_);
v___x_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
return v___x_3833_;
}
case 9:
{
lean_object* v_content_3834_; size_t v_sz_3835_; size_t v___x_3836_; lean_object* v___x_3837_; 
v_content_3834_ = lean_ctor_get(v_x_3563_, 0);
lean_inc_ref(v_content_3834_);
lean_dec_ref_known(v_x_3563_, 1);
v_sz_3835_ = lean_array_size(v_content_3834_);
v___x_3836_ = ((size_t)0ULL);
v___x_3837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3562_, v_sz_3835_, v___x_3836_, v_content_3834_, v_a_3564_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3846_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3840_ = v___x_3837_;
v_isShared_3841_ = v_isSharedCheck_3846_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3837_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3846_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3842_; lean_object* v___x_3844_; 
v___x_3842_ = l_Lean_Doc_joinInlines(v_a_3838_);
lean_dec(v_a_3838_);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v___x_3842_);
v___x_3844_ = v___x_3840_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
v_a_3847_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3837_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3837_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
default: 
{
lean_object* v_container_3855_; 
v_container_3855_ = lean_ctor_get(v_x_3563_, 0);
if (lean_obj_tag(v_container_3855_) == 0)
{
lean_object* v_content_3856_; lean_object* v_val_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
lean_inc_ref(v_container_3855_);
v_content_3856_ = lean_ctor_get(v_x_3563_, 1);
lean_inc_ref(v_content_3856_);
lean_dec_ref_known(v_x_3563_, 2);
v_val_3857_ = lean_ctor_get(v_container_3855_, 0);
lean_inc(v_val_3857_);
lean_dec_ref_known(v_container_3855_, 1);
v___x_3858_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3857_);
v___x_3859_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_3858_, v_a_3565_, v_a_3566_);
lean_dec(v___x_3858_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v___x_3859_, 1);
if (lean_obj_tag(v_a_3860_) == 0)
{
size_t v_sz_3861_; size_t v___x_3862_; lean_object* v___x_3863_; 
lean_dec(v_val_3857_);
v_sz_3861_ = lean_array_size(v_content_3856_);
v___x_3862_ = ((size_t)0ULL);
v___x_3863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3562_, v_sz_3861_, v___x_3862_, v_content_3856_, v_a_3564_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3872_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3866_ = v___x_3863_;
v_isShared_3867_ = v_isSharedCheck_3872_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3863_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3872_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3868_ = l_Lean_Doc_joinInlines(v_a_3864_);
lean_dec(v_a_3864_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 0, v___x_3868_);
v___x_3870_ = v___x_3866_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
v_a_3873_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3863_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3863_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
else
{
lean_object* v_val_3881_; lean_object* v___f_3882_; size_t v_sz_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v_fallback_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v_val_3881_ = lean_ctor_get(v_a_3860_, 0);
lean_inc(v_val_3881_);
lean_dec_ref_known(v_a_3860_, 1);
lean_inc_ref(v_x_3562_);
v___f_3882_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3882_, 0, v_x_3562_);
v_sz_3883_ = lean_array_size(v_content_3856_);
v___x_3884_ = lean_box_usize(v_sz_3883_);
v___x_3885_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
lean_inc_ref(v_content_3856_);
v_fallback_3886_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v_fallback_3886_, 0, v_x_3562_);
lean_closure_set(v_fallback_3886_, 1, v___x_3884_);
lean_closure_set(v_fallback_3886_, 2, v___x_3885_);
lean_closure_set(v_fallback_3886_, 3, v_content_3856_);
v___x_3887_ = lean_apply_3(v_val_3881_, v___f_3882_, v_val_3857_, v_content_3856_);
v___x_3888_ = l_Lean_Doc_withRendererFallback(v_fallback_3886_, v___x_3887_, v_a_3564_, v_a_3565_, v_a_3566_);
return v___x_3888_;
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec(v_val_3857_);
lean_dec_ref(v_content_3856_);
lean_dec_ref(v_x_3562_);
v_a_3889_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3859_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3859_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
else
{
lean_object* v_content_3897_; size_t v_sz_3898_; size_t v___x_3899_; lean_object* v___x_3900_; 
v_content_3897_ = lean_ctor_get(v_x_3563_, 1);
lean_inc_ref(v_content_3897_);
lean_dec_ref_known(v_x_3563_, 2);
v_sz_3898_ = lean_array_size(v_content_3897_);
v___x_3899_ = ((size_t)0ULL);
v___x_3900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3562_, v_sz_3898_, v___x_3899_, v_content_3897_, v_a_3564_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3909_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3903_ = v___x_3900_;
v_isShared_3904_ = v_isSharedCheck_3909_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3900_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3909_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3905_ = l_Lean_Doc_joinInlines(v_a_3901_);
lean_dec(v_a_3901_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 0, v___x_3905_);
v___x_3907_ = v___x_3903_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
v_a_3910_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3900_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3900_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
}
}
v___jp_3568_:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = l_Lean_Doc_joinInlines(v_pieces_3569_);
lean_dec_ref(v_pieces_3569_);
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
return v___x_3571_;
}
v___jp_3572_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = l_Lean_Doc_joinInlines(v_pieces_3573_);
lean_dec_ref(v_pieces_3573_);
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
return v___x_3575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(lean_object* v_x_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
lean_object* v___x_3924_; 
v___x_3924_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3925_, lean_object* v_sz_3926_, lean_object* v_i_3927_, lean_object* v_bs_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
size_t v_sz_boxed_3933_; size_t v_i_boxed_3934_; lean_object* v_res_3935_; 
v_sz_boxed_3933_ = lean_unbox_usize(v_sz_3926_);
lean_dec(v_sz_3926_);
v_i_boxed_3934_ = lean_unbox_usize(v_i_3927_);
lean_dec(v_i_3927_);
v_res_3935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3925_, v_sz_boxed_3933_, v_i_boxed_3934_, v_bs_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed(lean_object* v_x_3936_, lean_object* v_x_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3936_, v_x_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(lean_object* v___x_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0___boxed(lean_object* v___x_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(v___x_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(lean_object* v_x_3957_, lean_object* v_x_3958_){
_start:
{
lean_object* v_zero_3959_; uint8_t v_isZero_3960_; 
v_zero_3959_ = lean_unsigned_to_nat(0u);
v_isZero_3960_ = lean_nat_dec_eq(v_x_3957_, v_zero_3959_);
if (v_isZero_3960_ == 1)
{
lean_dec(v_x_3957_);
return v_x_3958_;
}
else
{
uint32_t v___x_3961_; lean_object* v_one_3962_; lean_object* v_n_3963_; lean_object* v___x_3964_; 
v___x_3961_ = 32;
v_one_3962_ = lean_unsigned_to_nat(1u);
v_n_3963_ = lean_nat_sub(v_x_3957_, v_one_3962_);
lean_dec(v_x_3957_);
v___x_3964_ = lean_string_push(v_x_3958_, v___x_3961_);
v_x_3957_ = v_n_3963_;
v_x_3958_ = v___x_3964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(size_t v_sz_3966_, size_t v_i_3967_, lean_object* v_bs_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
uint8_t v___x_3973_; 
v___x_3973_ = lean_usize_dec_lt(v_i_3967_, v_sz_3966_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; 
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v_bs_3968_);
return v___x_3974_;
}
else
{
lean_object* v_v_3975_; size_t v_sz_3976_; size_t v___x_3977_; lean_object* v___x_3978_; 
v_v_3975_ = lean_array_uget_borrowed(v_bs_3968_, v_i_3967_);
v_sz_3976_ = lean_array_size(v_v_3975_);
v___x_3977_ = ((size_t)0ULL);
lean_inc(v_v_3975_);
v___x_3978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_3976_, v___x_3977_, v_v_3975_, v___y_3969_, v___y_3970_, v___y_3971_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v___x_3980_; lean_object* v_bs_x27_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; size_t v___x_3986_; size_t v___x_3987_; lean_object* v___x_3988_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3979_);
lean_dec_ref_known(v___x_3978_, 1);
v___x_3980_ = lean_unsigned_to_nat(0u);
v_bs_x27_3981_ = lean_array_uset(v_bs_3968_, v_i_3967_, v___x_3980_);
v___x_3982_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_3983_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_3984_ = l_Lean_Doc_joinBlocks(v_a_3979_);
lean_dec(v_a_3979_);
v___x_3985_ = l_Lean_Doc_prefixListLines(v___x_3982_, v___x_3983_, v___x_3984_);
v___x_3986_ = ((size_t)1ULL);
v___x_3987_ = lean_usize_add(v_i_3967_, v___x_3986_);
v___x_3988_ = lean_array_uset(v_bs_x27_3981_, v_i_3967_, v___x_3985_);
v_i_3967_ = v___x_3987_;
v_bs_3968_ = v___x_3988_;
goto _start;
}
else
{
lean_dec_ref(v_bs_3968_);
return v___x_3978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(lean_object* v_as_3990_, size_t v_sz_3991_, size_t v_i_3992_, lean_object* v_b_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
uint8_t v___x_3998_; 
v___x_3998_ = lean_usize_dec_lt(v_i_3992_, v_sz_3991_);
if (v___x_3998_ == 0)
{
lean_object* v___x_3999_; 
v___x_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3999_, 0, v_b_3993_);
return v___x_3999_;
}
else
{
lean_object* v_a_4000_; size_t v_sz_4001_; size_t v___x_4002_; lean_object* v___x_4003_; 
v_a_4000_ = lean_array_uget_borrowed(v_as_3990_, v_i_3992_);
v_sz_4001_ = lean_array_size(v_a_4000_);
v___x_4002_ = ((size_t)0ULL);
lean_inc(v_a_4000_);
v___x_4003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4001_, v___x_4002_, v_a_4000_, v___y_3994_, v___y_3995_, v___y_3996_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v_fst_4005_; lean_object* v_snd_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4027_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_4003_, 1);
v_fst_4005_ = lean_ctor_get(v_b_3993_, 0);
v_snd_4006_ = lean_ctor_get(v_b_3993_, 1);
v_isSharedCheck_4027_ = !lean_is_exclusive(v_b_3993_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4008_ = v_b_3993_;
v_isShared_4009_ = v_isSharedCheck_4027_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_snd_4006_);
lean_inc(v_fst_4005_);
lean_dec(v_b_3993_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4027_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4022_; 
v___x_4010_ = lean_unsigned_to_nat(1u);
lean_inc(v_snd_4006_);
v___x_4011_ = l_Nat_reprFast(v_snd_4006_);
v___x_4012_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_4013_ = lean_string_append(v___x_4011_, v___x_4012_);
v___x_4014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4015_ = lean_string_utf8_byte_size(v___x_4013_);
v___x_4016_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(v___x_4015_, v___x_4014_);
v___x_4017_ = l_Lean_Doc_joinBlocks(v_a_4004_);
lean_dec(v_a_4004_);
v___x_4018_ = l_Lean_Doc_prefixListLines(v___x_4013_, v___x_4016_, v___x_4017_);
v___x_4019_ = lean_array_push(v_fst_4005_, v___x_4018_);
v___x_4020_ = lean_nat_add(v_snd_4006_, v___x_4010_);
lean_dec(v_snd_4006_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 1, v___x_4020_);
lean_ctor_set(v___x_4008_, 0, v___x_4019_);
v___x_4022_ = v___x_4008_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v___x_4019_);
lean_ctor_set(v_reuseFailAlloc_4026_, 1, v___x_4020_);
v___x_4022_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
size_t v___x_4023_; size_t v___x_4024_; 
v___x_4023_ = ((size_t)1ULL);
v___x_4024_ = lean_usize_add(v_i_3992_, v___x_4023_);
v_i_3992_ = v___x_4024_;
v_b_3993_ = v___x_4022_;
goto _start;
}
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec_ref(v_b_3993_);
v_a_4028_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4003_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4003_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(size_t v_sz_4036_, size_t v_i_4037_, lean_object* v_bs_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
uint8_t v___x_4043_; 
v___x_4043_ = lean_usize_dec_lt(v_i_4037_, v_sz_4036_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4044_; 
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v_bs_4038_);
return v___x_4044_;
}
else
{
lean_object* v_v_4045_; lean_object* v___x_4046_; lean_object* v_term_4047_; lean_object* v_desc_4048_; lean_object* v___x_4049_; lean_object* v_bs_x27_4050_; lean_object* v_a_4052_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v_v_4045_ = lean_array_uget_borrowed(v_bs_4038_, v_i_4037_);
v___x_4046_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_4047_ = lean_ctor_get(v_v_4045_, 0);
lean_inc_ref(v_term_4047_);
v_desc_4048_ = lean_ctor_get(v_v_4045_, 1);
lean_inc_ref(v_desc_4048_);
v___x_4049_ = lean_unsigned_to_nat(0u);
v_bs_x27_4050_ = lean_array_uset(v_bs_4038_, v_i_4037_, v___x_4049_);
v___x_4057_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4057_, 0, v_term_4047_);
v___x_4058_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4046_, v___x_4057_, v___y_4039_, v___y_4040_, v___y_4041_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; size_t v_sz_4060_; size_t v___x_4061_; lean_object* v___x_4062_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4058_, 1);
v_sz_4060_ = lean_array_size(v_desc_4048_);
v___x_4061_ = ((size_t)0ULL);
lean_inc_ref(v_desc_4048_);
v___x_4062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4060_, v___x_4061_, v_desc_4048_, v___y_4039_, v___y_4040_, v___y_4041_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___y_4065_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; uint8_t v___x_4078_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref_known(v___x_4062_, 1);
v___x_4069_ = lean_unsigned_to_nat(1u);
v___x_4070_ = lean_mk_empty_array_with_capacity(v___x_4069_);
v___x_4071_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_4072_ = lean_unsigned_to_nat(2u);
v___x_4073_ = lean_mk_empty_array_with_capacity(v___x_4072_);
v___x_4074_ = lean_array_push(v___x_4073_, v_a_4059_);
v___x_4075_ = lean_array_push(v___x_4074_, v___x_4071_);
v___x_4076_ = l_Lean_Doc_joinInlines(v___x_4075_);
lean_dec_ref(v___x_4075_);
v___x_4077_ = lean_array_get_size(v_desc_4048_);
lean_dec_ref(v_desc_4048_);
v___x_4078_ = lean_nat_dec_le(v___x_4077_, v___x_4069_);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4079_ = lean_array_push(v___x_4070_, v___x_4076_);
v___x_4080_ = l_Array_append___redArg(v___x_4079_, v_a_4063_);
lean_dec(v_a_4063_);
v___x_4081_ = l_Lean_Doc_joinBlocks(v___x_4080_);
lean_dec_ref(v___x_4080_);
v___y_4065_ = v___x_4081_;
goto v___jp_4064_;
}
else
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
lean_dec_ref(v___x_4070_);
v___x_4082_ = l_Lean_Doc_joinBlocks(v_a_4063_);
lean_dec(v_a_4063_);
v___x_4083_ = l_Array_append___redArg(v___x_4076_, v___x_4082_);
lean_dec_ref(v___x_4082_);
v___y_4065_ = v___x_4083_;
goto v___jp_4064_;
}
v___jp_4064_:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4066_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_4067_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_4068_ = l_Lean_Doc_prefixListLines(v___x_4066_, v___x_4067_, v___y_4065_);
v_a_4052_ = v___x_4068_;
goto v___jp_4051_;
}
}
else
{
lean_dec(v_a_4059_);
lean_dec_ref(v_bs_x27_4050_);
lean_dec_ref(v_desc_4048_);
return v___x_4062_;
}
}
else
{
lean_dec_ref(v_desc_4048_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4084_; 
v_a_4084_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4084_);
lean_dec_ref_known(v___x_4058_, 1);
v_a_4052_ = v_a_4084_;
goto v___jp_4051_;
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec_ref(v_bs_x27_4050_);
v_a_4085_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4058_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4058_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
v___jp_4051_:
{
size_t v___x_4053_; size_t v___x_4054_; lean_object* v___x_4055_; 
v___x_4053_ = ((size_t)1ULL);
v___x_4054_ = lean_usize_add(v_i_4037_, v___x_4053_);
v___x_4055_ = lean_array_uset(v_bs_x27_4050_, v_i_4037_, v_a_4052_);
v_i_4037_ = v___x_4054_;
v_bs_4038_ = v___x_4055_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed(lean_object* v_x_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_){
_start:
{
lean_object* v_res_4098_; 
v_res_4098_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_x_4093_, v_a_4094_, v_a_4095_, v_a_4096_);
lean_dec(v_a_4096_);
lean_dec_ref(v_a_4095_);
lean_dec(v_a_4094_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed(lean_object* v_sz_4101_, lean_object* v___x_4102_, lean_object* v_content_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
size_t v_sz_boxed_4108_; size_t v___x_4827__boxed_4109_; lean_object* v_res_4110_; 
v_sz_boxed_4108_ = lean_unbox_usize(v_sz_4101_);
lean_dec(v_sz_4101_);
v___x_4827__boxed_4109_ = lean_unbox_usize(v___x_4102_);
lean_dec(v___x_4102_);
v_res_4110_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(v_sz_boxed_4108_, v___x_4827__boxed_4109_, v_content_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(lean_object* v_x_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_){
_start:
{
switch(lean_obj_tag(v_x_4111_))
{
case 0:
{
lean_object* v_contents_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4125_; 
v_contents_4116_ = lean_ctor_get(v_x_4111_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v_x_4111_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4118_ = v_x_4111_;
v_isShared_4119_ = v_isSharedCheck_4125_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_contents_4116_);
lean_dec(v_x_4111_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4125_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4120_; lean_object* v___x_4122_; 
v___x_4120_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_4119_ == 0)
{
lean_ctor_set_tag(v___x_4118_, 9);
v___x_4122_ = v___x_4118_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_contents_4116_);
v___x_4122_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
lean_object* v___x_4123_; 
v___x_4123_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4120_, v___x_4122_, v_a_4112_, v_a_4113_, v_a_4114_);
return v___x_4123_;
}
}
}
case 1:
{
lean_object* v_content_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4134_; 
v_content_4126_ = lean_ctor_get(v_x_4111_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v_x_4111_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4128_ = v_x_4111_;
v_isShared_4129_ = v_isSharedCheck_4134_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_content_4126_);
lean_dec(v_x_4111_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4134_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4130_; lean_object* v___x_4132_; 
v___x_4130_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_4126_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set_tag(v___x_4128_, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4130_);
v___x_4132_ = v___x_4128_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4130_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
case 2:
{
lean_object* v_items_4135_; size_t v_sz_4136_; size_t v___x_4137_; lean_object* v___x_4138_; 
v_items_4135_ = lean_ctor_get(v_x_4111_, 0);
lean_inc_ref(v_items_4135_);
lean_dec_ref_known(v_x_4111_, 1);
v_sz_4136_ = lean_array_size(v_items_4135_);
v___x_4137_ = ((size_t)0ULL);
v___x_4138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_4136_, v___x_4137_, v_items_4135_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4147_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4141_ = v___x_4138_;
v_isShared_4142_ = v_isSharedCheck_4147_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4138_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4147_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4143_; lean_object* v___x_4145_; 
v___x_4143_ = l_Lean_Doc_joinBlocks(v_a_4139_);
lean_dec(v_a_4139_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v___x_4143_);
v___x_4145_ = v___x_4141_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
v_a_4148_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4138_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4138_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
case 3:
{
lean_object* v_start_4156_; lean_object* v_items_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4191_; 
v_start_4156_ = lean_ctor_get(v_x_4111_, 0);
v_items_4157_ = lean_ctor_get(v_x_4111_, 1);
v_isSharedCheck_4191_ = !lean_is_exclusive(v_x_4111_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4159_ = v_x_4111_;
v_isShared_4160_ = v_isSharedCheck_4191_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_items_4157_);
lean_inc(v_start_4156_);
lean_dec(v_x_4111_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4191_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v_out_4161_; lean_object* v___y_4163_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v_out_4161_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_4188_ = lean_unsigned_to_nat(1u);
v___x_4189_ = l_Int_toNat(v_start_4156_);
lean_dec(v_start_4156_);
v___x_4190_ = lean_nat_dec_le(v___x_4188_, v___x_4189_);
if (v___x_4190_ == 0)
{
lean_dec(v___x_4189_);
v___y_4163_ = v___x_4188_;
goto v___jp_4162_;
}
else
{
v___y_4163_ = v___x_4189_;
goto v___jp_4162_;
}
v___jp_4162_:
{
lean_object* v___x_4165_; 
if (v_isShared_4160_ == 0)
{
lean_ctor_set_tag(v___x_4159_, 0);
lean_ctor_set(v___x_4159_, 1, v___y_4163_);
lean_ctor_set(v___x_4159_, 0, v_out_4161_);
v___x_4165_ = v___x_4159_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_out_4161_);
lean_ctor_set(v_reuseFailAlloc_4187_, 1, v___y_4163_);
v___x_4165_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
size_t v_sz_4166_; size_t v___x_4167_; lean_object* v___x_4168_; 
v_sz_4166_ = lean_array_size(v_items_4157_);
v___x_4167_ = ((size_t)0ULL);
v___x_4168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_items_4157_, v_sz_4166_, v___x_4167_, v___x_4165_, v_a_4112_, v_a_4113_, v_a_4114_);
lean_dec_ref(v_items_4157_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4178_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4171_ = v___x_4168_;
v_isShared_4172_ = v_isSharedCheck_4178_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4168_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4178_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v_fst_4173_; lean_object* v___x_4174_; lean_object* v___x_4176_; 
v_fst_4173_ = lean_ctor_get(v_a_4169_, 0);
lean_inc(v_fst_4173_);
lean_dec(v_a_4169_);
v___x_4174_ = l_Lean_Doc_joinBlocks(v_fst_4173_);
lean_dec(v_fst_4173_);
if (v_isShared_4172_ == 0)
{
lean_ctor_set(v___x_4171_, 0, v___x_4174_);
v___x_4176_ = v___x_4171_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
v_a_4179_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4168_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4168_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_4192_; size_t v_sz_4193_; size_t v___x_4194_; lean_object* v___x_4195_; 
v_items_4192_ = lean_ctor_get(v_x_4111_, 0);
lean_inc_ref(v_items_4192_);
lean_dec_ref_known(v_x_4111_, 1);
v_sz_4193_ = lean_array_size(v_items_4192_);
v___x_4194_ = ((size_t)0ULL);
v___x_4195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_4193_, v___x_4194_, v_items_4192_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4204_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4198_ = v___x_4195_;
v_isShared_4199_ = v_isSharedCheck_4204_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4195_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4204_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4200_; lean_object* v___x_4202_; 
v___x_4200_ = l_Lean_Doc_joinBlocks(v_a_4196_);
lean_dec(v_a_4196_);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v___x_4200_);
v___x_4202_ = v___x_4198_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4200_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
v_a_4205_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4195_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4195_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
case 5:
{
lean_object* v_items_4213_; size_t v_sz_4214_; size_t v___x_4215_; lean_object* v___x_4216_; 
v_items_4213_ = lean_ctor_get(v_x_4111_, 0);
lean_inc_ref(v_items_4213_);
lean_dec_ref_known(v_x_4111_, 1);
v_sz_4214_ = lean_array_size(v_items_4213_);
v___x_4215_ = ((size_t)0ULL);
v___x_4216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4214_, v___x_4215_, v_items_4213_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4227_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4219_ = v___x_4216_;
v_isShared_4220_ = v_isSharedCheck_4227_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4216_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4227_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4225_; 
v___x_4221_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_4222_ = l_Lean_Doc_joinBlocks(v_a_4217_);
lean_dec(v_a_4217_);
v___x_4223_ = l_Lean_Doc_prefixLines(v___x_4221_, v___x_4222_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 0, v___x_4223_);
v___x_4225_ = v___x_4219_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
v_a_4228_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4216_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4216_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
case 6:
{
lean_object* v_content_4236_; size_t v_sz_4237_; size_t v___x_4238_; lean_object* v___x_4239_; 
v_content_4236_ = lean_ctor_get(v_x_4111_, 0);
lean_inc_ref(v_content_4236_);
lean_dec_ref_known(v_x_4111_, 1);
v_sz_4237_ = lean_array_size(v_content_4236_);
v___x_4238_ = ((size_t)0ULL);
v___x_4239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4237_, v___x_4238_, v_content_4236_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4248_; 
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4242_ = v___x_4239_;
v_isShared_4243_ = v_isSharedCheck_4248_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4239_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4248_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4244_; lean_object* v___x_4246_; 
v___x_4244_ = l_Lean_Doc_joinBlocks(v_a_4240_);
lean_dec(v_a_4240_);
if (v_isShared_4243_ == 0)
{
lean_ctor_set(v___x_4242_, 0, v___x_4244_);
v___x_4246_ = v___x_4242_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v___x_4244_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
v_a_4249_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4239_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4239_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
default: 
{
lean_object* v_container_4257_; 
v_container_4257_ = lean_ctor_get(v_x_4111_, 0);
if (lean_obj_tag(v_container_4257_) == 0)
{
lean_object* v_content_4258_; lean_object* v_val_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
lean_inc_ref(v_container_4257_);
v_content_4258_ = lean_ctor_get(v_x_4111_, 1);
lean_inc_ref(v_content_4258_);
lean_dec_ref_known(v_x_4111_, 2);
v_val_4259_ = lean_ctor_get(v_container_4257_, 0);
lean_inc(v_val_4259_);
lean_dec_ref_known(v_container_4257_, 1);
v___x_4260_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_4259_);
v___x_4261_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_4260_, v_a_4113_, v_a_4114_);
lean_dec(v___x_4260_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v___x_4261_, 1);
if (lean_obj_tag(v_a_4262_) == 0)
{
size_t v_sz_4263_; size_t v___x_4264_; lean_object* v___x_4265_; 
lean_dec(v_val_4259_);
v_sz_4263_ = lean_array_size(v_content_4258_);
v___x_4264_ = ((size_t)0ULL);
v___x_4265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4263_, v___x_4264_, v_content_4258_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4274_; 
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4268_ = v___x_4265_;
v_isShared_4269_ = v_isSharedCheck_4274_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___x_4265_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4274_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4270_; lean_object* v___x_4272_; 
v___x_4270_ = l_Lean_Doc_joinBlocks(v_a_4266_);
lean_dec(v_a_4266_);
if (v_isShared_4269_ == 0)
{
lean_ctor_set(v___x_4268_, 0, v___x_4270_);
v___x_4272_ = v___x_4268_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4270_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
v_a_4275_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4265_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4265_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
else
{
lean_object* v_val_4283_; lean_object* v___f_4284_; lean_object* v___f_4285_; size_t v_sz_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v_fallback_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v_val_4283_ = lean_ctor_get(v_a_4262_, 0);
lean_inc(v_val_4283_);
lean_dec_ref_known(v_a_4262_, 1);
v___f_4284_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed), 5, 0);
v___f_4285_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___closed__0));
v_sz_4286_ = lean_array_size(v_content_4258_);
v___x_4287_ = lean_box_usize(v_sz_4286_);
v___x_4288_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
lean_inc_ref(v_content_4258_);
v_fallback_4289_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_fallback_4289_, 0, v___x_4287_);
lean_closure_set(v_fallback_4289_, 1, v___x_4288_);
lean_closure_set(v_fallback_4289_, 2, v_content_4258_);
v___x_4290_ = lean_apply_4(v_val_4283_, v___f_4285_, v___f_4284_, v_val_4259_, v_content_4258_);
v___x_4291_ = l_Lean_Doc_withRendererFallback(v_fallback_4289_, v___x_4290_, v_a_4112_, v_a_4113_, v_a_4114_);
return v___x_4291_;
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_dec(v_val_4259_);
lean_dec_ref(v_content_4258_);
v_a_4292_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4261_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4261_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
else
{
lean_object* v_content_4300_; size_t v_sz_4301_; size_t v___x_4302_; lean_object* v___x_4303_; 
v_content_4300_ = lean_ctor_get(v_x_4111_, 1);
lean_inc_ref(v_content_4300_);
lean_dec_ref_known(v_x_4111_, 2);
v_sz_4301_ = lean_array_size(v_content_4300_);
v___x_4302_ = ((size_t)0ULL);
v___x_4303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4301_, v___x_4302_, v_content_4300_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4312_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4306_ = v___x_4303_;
v_isShared_4307_ = v_isSharedCheck_4312_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4303_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4312_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4308_; lean_object* v___x_4310_; 
v___x_4308_ = l_Lean_Doc_joinBlocks(v_a_4304_);
lean_dec(v_a_4304_);
if (v_isShared_4307_ == 0)
{
lean_ctor_set(v___x_4306_, 0, v___x_4308_);
v___x_4310_ = v___x_4306_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4308_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
v_a_4313_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___x_4303_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4303_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(size_t v_sz_4321_, size_t v_i_4322_, lean_object* v_bs_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
uint8_t v___x_4328_; 
v___x_4328_ = lean_usize_dec_lt(v_i_4322_, v_sz_4321_);
if (v___x_4328_ == 0)
{
lean_object* v___x_4329_; 
v___x_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4329_, 0, v_bs_4323_);
return v___x_4329_;
}
else
{
lean_object* v_v_4330_; lean_object* v___x_4331_; 
v_v_4330_ = lean_array_uget_borrowed(v_bs_4323_, v_i_4322_);
lean_inc(v_v_4330_);
v___x_4331_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_v_4330_, v___y_4324_, v___y_4325_, v___y_4326_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v_a_4332_; lean_object* v___x_4333_; lean_object* v_bs_x27_4334_; size_t v___x_4335_; size_t v___x_4336_; lean_object* v___x_4337_; 
v_a_4332_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v___x_4331_, 1);
v___x_4333_ = lean_unsigned_to_nat(0u);
v_bs_x27_4334_ = lean_array_uset(v_bs_4323_, v_i_4322_, v___x_4333_);
v___x_4335_ = ((size_t)1ULL);
v___x_4336_ = lean_usize_add(v_i_4322_, v___x_4335_);
v___x_4337_ = lean_array_uset(v_bs_x27_4334_, v_i_4322_, v_a_4332_);
v_i_4322_ = v___x_4336_;
v_bs_4323_ = v___x_4337_;
goto _start;
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec_ref(v_bs_4323_);
v_a_4339_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4331_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4331_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(size_t v_sz_4347_, size_t v___x_4348_, lean_object* v_content_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4347_, v___x_4348_, v_content_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4363_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4357_ = v___x_4354_;
v_isShared_4358_ = v_isSharedCheck_4363_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4354_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4363_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4359_; lean_object* v___x_4361_; 
v___x_4359_ = l_Lean_Doc_joinBlocks(v_a_4355_);
lean_dec(v_a_4355_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 0, v___x_4359_);
v___x_4361_ = v___x_4357_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v___x_4359_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
v_a_4364_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4354_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4354_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2___boxed(lean_object* v_sz_4372_, lean_object* v_i_4373_, lean_object* v_bs_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
size_t v_sz_boxed_4379_; size_t v_i_boxed_4380_; lean_object* v_res_4381_; 
v_sz_boxed_4379_ = lean_unbox_usize(v_sz_4372_);
lean_dec(v_sz_4372_);
v_i_boxed_4380_ = lean_unbox_usize(v_i_4373_);
lean_dec(v_i_4373_);
v_res_4381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_boxed_4379_, v_i_boxed_4380_, v_bs_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5___boxed(lean_object* v_sz_4382_, lean_object* v_i_4383_, lean_object* v_bs_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
size_t v_sz_boxed_4389_; size_t v_i_boxed_4390_; lean_object* v_res_4391_; 
v_sz_boxed_4389_ = lean_unbox_usize(v_sz_4382_);
lean_dec(v_sz_4382_);
v_i_boxed_4390_ = lean_unbox_usize(v_i_4383_);
lean_dec(v_i_4383_);
v_res_4391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_boxed_4389_, v_i_boxed_4390_, v_bs_4384_, v___y_4385_, v___y_4386_, v___y_4387_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec(v___y_4385_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7___boxed(lean_object* v_as_4392_, lean_object* v_sz_4393_, lean_object* v_i_4394_, lean_object* v_b_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_){
_start:
{
size_t v_sz_boxed_4400_; size_t v_i_boxed_4401_; lean_object* v_res_4402_; 
v_sz_boxed_4400_ = lean_unbox_usize(v_sz_4393_);
lean_dec(v_sz_4393_);
v_i_boxed_4401_ = lean_unbox_usize(v_i_4394_);
lean_dec(v_i_4394_);
v_res_4402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_as_4392_, v_sz_boxed_4400_, v_i_boxed_4401_, v_b_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
lean_dec(v___y_4398_);
lean_dec_ref(v___y_4397_);
lean_dec(v___y_4396_);
lean_dec_ref(v_as_4392_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8___boxed(lean_object* v_sz_4403_, lean_object* v_i_4404_, lean_object* v_bs_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
size_t v_sz_boxed_4410_; size_t v_i_boxed_4411_; lean_object* v_res_4412_; 
v_sz_boxed_4410_ = lean_unbox_usize(v_sz_4403_);
lean_dec(v_sz_4403_);
v_i_boxed_4411_ = lean_unbox_usize(v_i_4404_);
lean_dec(v_i_4404_);
v_res_4412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_boxed_4410_, v_i_boxed_4411_, v_bs_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(size_t v_sz_4413_, size_t v_i_4414_, lean_object* v_bs_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
uint8_t v___x_4420_; 
v___x_4420_ = lean_usize_dec_lt(v_i_4414_, v_sz_4413_);
if (v___x_4420_ == 0)
{
lean_object* v___x_4421_; 
v___x_4421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4421_, 0, v_bs_4415_);
return v___x_4421_;
}
else
{
lean_object* v_v_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v_v_4422_ = lean_array_uget_borrowed(v_bs_4415_, v_i_4414_);
v___x_4423_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc(v_v_4422_);
v___x_4424_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4423_, v_v_4422_, v___y_4416_, v___y_4417_, v___y_4418_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4426_; lean_object* v_bs_x27_4427_; size_t v___x_4428_; size_t v___x_4429_; lean_object* v___x_4430_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4425_);
lean_dec_ref_known(v___x_4424_, 1);
v___x_4426_ = lean_unsigned_to_nat(0u);
v_bs_x27_4427_ = lean_array_uset(v_bs_4415_, v_i_4414_, v___x_4426_);
v___x_4428_ = ((size_t)1ULL);
v___x_4429_ = lean_usize_add(v_i_4414_, v___x_4428_);
v___x_4430_ = lean_array_uset(v_bs_x27_4427_, v_i_4414_, v_a_4425_);
v_i_4414_ = v___x_4429_;
v_bs_4415_ = v___x_4430_;
goto _start;
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_dec_ref(v_bs_4415_);
v_a_4432_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4424_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4424_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1___boxed(lean_object* v_sz_4440_, lean_object* v_i_4441_, lean_object* v_bs_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
size_t v_sz_boxed_4447_; size_t v_i_boxed_4448_; lean_object* v_res_4449_; 
v_sz_boxed_4447_ = lean_unbox_usize(v_sz_4440_);
lean_dec(v_sz_4440_);
v_i_boxed_4448_ = lean_unbox_usize(v_i_4441_);
lean_dec(v_i_4441_);
v_res_4449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_boxed_4447_, v_i_boxed_4448_, v_bs_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v___y_4443_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(lean_object* v_x_4450_, lean_object* v_x_4451_){
_start:
{
lean_object* v_zero_4452_; uint8_t v_isZero_4453_; 
v_zero_4452_ = lean_unsigned_to_nat(0u);
v_isZero_4453_ = lean_nat_dec_eq(v_x_4450_, v_zero_4452_);
if (v_isZero_4453_ == 1)
{
lean_dec(v_x_4450_);
return v_x_4451_;
}
else
{
uint32_t v___x_4454_; lean_object* v_one_4455_; lean_object* v_n_4456_; lean_object* v___x_4457_; 
v___x_4454_ = 35;
v_one_4455_ = lean_unsigned_to_nat(1u);
v_n_4456_ = lean_nat_sub(v_x_4450_, v_one_4455_);
lean_dec(v_x_4450_);
v___x_4457_ = lean_string_push(v_x_4451_, v___x_4454_);
v_x_4450_ = v_n_4456_;
v_x_4451_ = v___x_4457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(lean_object* v_level_4459_, lean_object* v_part_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_){
_start:
{
lean_object* v_title_4465_; lean_object* v_content_4466_; lean_object* v_subParts_4467_; size_t v_sz_4468_; size_t v___x_4469_; lean_object* v___x_4470_; 
v_title_4465_ = lean_ctor_get(v_part_4460_, 0);
lean_inc_ref(v_title_4465_);
v_content_4466_ = lean_ctor_get(v_part_4460_, 3);
lean_inc_ref(v_content_4466_);
v_subParts_4467_ = lean_ctor_get(v_part_4460_, 4);
lean_inc_ref(v_subParts_4467_);
lean_dec_ref(v_part_4460_);
v_sz_4468_ = lean_array_size(v_title_4465_);
v___x_4469_ = ((size_t)0ULL);
v___x_4470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_4468_, v___x_4469_, v_title_4465_, v_a_4461_, v_a_4462_, v_a_4463_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_a_4471_; size_t v_sz_4472_; lean_object* v___x_4473_; 
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
lean_inc(v_a_4471_);
lean_dec_ref_known(v___x_4470_, 1);
v_sz_4472_ = lean_array_size(v_content_4466_);
v___x_4473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4472_, v___x_4469_, v_content_4466_, v_a_4461_, v_a_4462_, v_a_4463_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; size_t v_sz_4479_; lean_object* v___x_4480_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4474_);
lean_dec_ref_known(v___x_4473_, 1);
v___x_4475_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4476_ = lean_unsigned_to_nat(1u);
v___x_4477_ = lean_nat_add(v_level_4459_, v___x_4476_);
lean_inc(v___x_4477_);
v___x_4478_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(v___x_4477_, v___x_4475_);
v_sz_4479_ = lean_array_size(v_subParts_4467_);
v___x_4480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4477_, v_sz_4479_, v___x_4469_, v_subParts_4467_, v_a_4461_, v_a_4462_, v_a_4463_);
lean_dec(v___x_4477_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4499_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4483_ = v___x_4480_;
v_isShared_4484_ = v_isSharedCheck_4499_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4480_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4499_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4497_; 
v___x_4485_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_4486_ = lean_string_append(v___x_4478_, v___x_4485_);
v___x_4487_ = lean_mk_empty_array_with_capacity(v___x_4476_);
lean_inc_ref_n(v___x_4487_, 2);
v___x_4488_ = lean_array_push(v___x_4487_, v___x_4486_);
v___x_4489_ = lean_array_push(v___x_4487_, v___x_4488_);
v___x_4490_ = l_Array_append___redArg(v___x_4489_, v_a_4471_);
lean_dec(v_a_4471_);
v___x_4491_ = l_Lean_Doc_joinInlines(v___x_4490_);
lean_dec_ref(v___x_4490_);
v___x_4492_ = lean_array_push(v___x_4487_, v___x_4491_);
v___x_4493_ = l_Array_append___redArg(v___x_4492_, v_a_4474_);
lean_dec(v_a_4474_);
v___x_4494_ = l_Array_append___redArg(v___x_4493_, v_a_4481_);
lean_dec(v_a_4481_);
v___x_4495_ = l_Lean_Doc_joinBlocks(v___x_4494_);
lean_dec_ref(v___x_4494_);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 0, v___x_4495_);
v___x_4497_ = v___x_4483_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4495_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
lean_dec_ref(v___x_4478_);
lean_dec(v_a_4474_);
lean_dec(v_a_4471_);
v_a_4500_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4480_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4480_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
lean_dec(v_a_4471_);
lean_dec_ref(v_subParts_4467_);
v_a_4508_ = lean_ctor_get(v___x_4473_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4473_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4473_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_dec_ref(v_subParts_4467_);
lean_dec_ref(v_content_4466_);
v_a_4516_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4470_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4470_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(lean_object* v___x_4524_, size_t v_sz_4525_, size_t v_i_4526_, lean_object* v_bs_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
uint8_t v___x_4532_; 
v___x_4532_ = lean_usize_dec_lt(v_i_4526_, v_sz_4525_);
if (v___x_4532_ == 0)
{
lean_object* v___x_4533_; 
v___x_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4533_, 0, v_bs_4527_);
return v___x_4533_;
}
else
{
lean_object* v_v_4534_; lean_object* v___x_4535_; 
v_v_4534_ = lean_array_uget_borrowed(v_bs_4527_, v_i_4526_);
lean_inc(v_v_4534_);
v___x_4535_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4524_, v_v_4534_, v___y_4528_, v___y_4529_, v___y_4530_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v___x_4537_; lean_object* v_bs_x27_4538_; size_t v___x_4539_; size_t v___x_4540_; lean_object* v___x_4541_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref_known(v___x_4535_, 1);
v___x_4537_ = lean_unsigned_to_nat(0u);
v_bs_x27_4538_ = lean_array_uset(v_bs_4527_, v_i_4526_, v___x_4537_);
v___x_4539_ = ((size_t)1ULL);
v___x_4540_ = lean_usize_add(v_i_4526_, v___x_4539_);
v___x_4541_ = lean_array_uset(v_bs_x27_4538_, v_i_4526_, v_a_4536_);
v_i_4526_ = v___x_4540_;
v_bs_4527_ = v___x_4541_;
goto _start;
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
lean_dec_ref(v_bs_4527_);
v_a_4543_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4535_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4535_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg___boxed(lean_object* v___x_4551_, lean_object* v_sz_4552_, lean_object* v_i_4553_, lean_object* v_bs_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
size_t v_sz_boxed_4559_; size_t v_i_boxed_4560_; lean_object* v_res_4561_; 
v_sz_boxed_4559_ = lean_unbox_usize(v_sz_4552_);
lean_dec(v_sz_4552_);
v_i_boxed_4560_ = lean_unbox_usize(v_i_4553_);
lean_dec(v_i_4553_);
v_res_4561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4551_, v_sz_boxed_4559_, v_i_boxed_4560_, v_bs_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec(v___x_4551_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg___boxed(lean_object* v_level_4562_, lean_object* v_part_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4562_, v_part_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
lean_dec(v_a_4566_);
lean_dec_ref(v_a_4565_);
lean_dec(v_a_4564_);
lean_dec(v_level_4562_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(size_t v_sz_4569_, size_t v_i_4570_, lean_object* v_bs_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
uint8_t v___x_4576_; 
v___x_4576_ = lean_usize_dec_lt(v_i_4570_, v_sz_4569_);
if (v___x_4576_ == 0)
{
lean_object* v___x_4577_; 
v___x_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4577_, 0, v_bs_4571_);
return v___x_4577_;
}
else
{
lean_object* v_v_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v_v_4578_ = lean_array_uget_borrowed(v_bs_4571_, v_i_4570_);
v___x_4579_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_4578_);
v___x_4580_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4579_, v_v_4578_, v___y_4572_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v_bs_x27_4582_; size_t v___x_4583_; size_t v___x_4584_; lean_object* v___x_4585_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
lean_inc(v_a_4581_);
lean_dec_ref_known(v___x_4580_, 1);
v_bs_x27_4582_ = lean_array_uset(v_bs_4571_, v_i_4570_, v___x_4579_);
v___x_4583_ = ((size_t)1ULL);
v___x_4584_ = lean_usize_add(v_i_4570_, v___x_4583_);
v___x_4585_ = lean_array_uset(v_bs_x27_4582_, v_i_4570_, v_a_4581_);
v_i_4570_ = v___x_4584_;
v_bs_4571_ = v___x_4585_;
goto _start;
}
else
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
lean_dec_ref(v_bs_4571_);
v_a_4587_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4589_ = v___x_4580_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4580_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4587_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3___boxed(lean_object* v_sz_4595_, lean_object* v_i_4596_, lean_object* v_bs_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
size_t v_sz_boxed_4602_; size_t v_i_boxed_4603_; lean_object* v_res_4604_; 
v_sz_boxed_4602_ = lean_unbox_usize(v_sz_4595_);
lean_dec(v_sz_4595_);
v_i_boxed_4603_ = lean_unbox_usize(v_i_4596_);
lean_dec(v_i_4596_);
v_res_4604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_boxed_4602_, v_i_boxed_4603_, v_bs_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0(lean_object* v_val_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
lean_object* v_text_4610_; lean_object* v_subsections_4611_; size_t v_sz_4612_; size_t v___x_4613_; lean_object* v___x_4614_; 
v_text_4610_ = lean_ctor_get(v_val_4605_, 0);
lean_inc_ref(v_text_4610_);
v_subsections_4611_ = lean_ctor_get(v_val_4605_, 1);
lean_inc_ref(v_subsections_4611_);
lean_dec_ref(v_val_4605_);
v_sz_4612_ = lean_array_size(v_text_4610_);
v___x_4613_ = ((size_t)0ULL);
v___x_4614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4612_, v___x_4613_, v_text_4610_, v___y_4606_, v___y_4607_, v___y_4608_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; size_t v_sz_4616_; lean_object* v___x_4617_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
lean_inc(v_a_4615_);
lean_dec_ref_known(v___x_4614_, 1);
v_sz_4616_ = lean_array_size(v_subsections_4611_);
v___x_4617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_4616_, v___x_4613_, v_subsections_4611_, v___y_4606_, v___y_4607_, v___y_4608_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4627_; 
v_a_4618_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4620_ = v___x_4617_;
v_isShared_4621_ = v_isSharedCheck_4627_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4617_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4627_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4625_; 
v___x_4622_ = l_Array_append___redArg(v_a_4615_, v_a_4618_);
lean_dec(v_a_4618_);
v___x_4623_ = l_Lean_Doc_joinBlocks(v___x_4622_);
lean_dec_ref(v___x_4622_);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 0, v___x_4623_);
v___x_4625_ = v___x_4620_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
lean_dec(v_a_4615_);
v_a_4628_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4617_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4617_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec_ref(v_subsections_4611_);
v_a_4636_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4614_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4614_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0___boxed(lean_object* v_val_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_Lean_findSimpleDocString_x3f___lam__0(v_val_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
lean_dec(v___y_4645_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_4650_, lean_object* v_declName_4651_, uint8_t v_includeBuiltin_4652_, lean_object* v_options_4653_, lean_object* v_currNamespace_4654_, lean_object* v_openDecls_4655_, lean_object* v_cancelTk_x3f_4656_){
_start:
{
lean_object* v___x_4658_; 
lean_inc_ref(v_env_4650_);
v___x_4658_ = l_Lean_findInternalDocString_x3f(v_env_4650_, v_declName_4651_, v_includeBuiltin_4652_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4702_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4661_ = v___x_4658_;
v_isShared_4662_ = v_isSharedCheck_4702_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4658_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4702_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
if (lean_obj_tag(v_a_4659_) == 0)
{
lean_object* v___x_4663_; lean_object* v___x_4665_; 
lean_dec(v_cancelTk_x3f_4656_);
lean_dec(v_openDecls_4655_);
lean_dec(v_currNamespace_4654_);
lean_dec_ref(v_options_4653_);
lean_dec_ref(v_env_4650_);
v___x_4663_ = lean_box(0);
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 0, v___x_4663_);
v___x_4665_ = v___x_4661_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4663_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
else
{
lean_object* v_val_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4701_; 
v_val_4667_ = lean_ctor_get(v_a_4659_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v_a_4659_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4669_ = v_a_4659_;
v_isShared_4670_ = v_isSharedCheck_4701_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_val_4667_);
lean_dec(v_a_4659_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4701_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
if (lean_obj_tag(v_val_4667_) == 0)
{
lean_object* v_val_4671_; lean_object* v___x_4673_; 
lean_dec(v_cancelTk_x3f_4656_);
lean_dec(v_openDecls_4655_);
lean_dec(v_currNamespace_4654_);
lean_dec_ref(v_options_4653_);
lean_dec_ref(v_env_4650_);
v_val_4671_ = lean_ctor_get(v_val_4667_, 0);
lean_inc(v_val_4671_);
lean_dec_ref_known(v_val_4667_, 1);
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 0, v_val_4671_);
v___x_4673_ = v___x_4669_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_val_4671_);
v___x_4673_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
lean_object* v___x_4675_; 
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 0, v___x_4673_);
v___x_4675_ = v___x_4661_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4673_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
else
{
lean_object* v_val_4678_; lean_object* v___f_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
lean_del_object(v___x_4661_);
v_val_4678_ = lean_ctor_get(v_val_4667_, 0);
lean_inc(v_val_4678_);
lean_dec_ref_known(v_val_4667_, 1);
v___f_4679_ = lean_alloc_closure((void*)(l_Lean_findSimpleDocString_x3f___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4679_, 0, v_val_4678_);
v___x_4680_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_4680_, 0, v___f_4679_);
v___x_4681_ = l_Lean_Doc_runMarkdown___redArg(v_env_4650_, v___x_4680_, v_options_4653_, v_currNamespace_4654_, v_openDecls_4655_, v_cancelTk_x3f_4656_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4692_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4684_ = v___x_4681_;
v_isShared_4685_ = v_isSharedCheck_4692_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4681_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4692_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 0, v_a_4682_);
v___x_4687_ = v___x_4669_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
lean_object* v___x_4689_; 
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 0, v___x_4687_);
v___x_4689_ = v___x_4684_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v___x_4687_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
else
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4700_; 
lean_del_object(v___x_4669_);
v_a_4693_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4695_ = v___x_4681_;
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4681_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4698_; 
if (v_isShared_4696_ == 0)
{
v___x_4698_ = v___x_4695_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4693_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4710_; 
lean_dec(v_cancelTk_x3f_4656_);
lean_dec(v_openDecls_4655_);
lean_dec(v_currNamespace_4654_);
lean_dec_ref(v_options_4653_);
lean_dec_ref(v_env_4650_);
v_a_4703_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4705_ = v___x_4658_;
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4658_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_4711_, lean_object* v_declName_4712_, lean_object* v_includeBuiltin_4713_, lean_object* v_options_4714_, lean_object* v_currNamespace_4715_, lean_object* v_openDecls_4716_, lean_object* v_cancelTk_x3f_4717_, lean_object* v_a_4718_){
_start:
{
uint8_t v_includeBuiltin_boxed_4719_; lean_object* v_res_4720_; 
v_includeBuiltin_boxed_4719_ = lean_unbox(v_includeBuiltin_4713_);
v_res_4720_ = l_Lean_findSimpleDocString_x3f(v_env_4711_, v_declName_4712_, v_includeBuiltin_boxed_4719_, v_options_4714_, v_currNamespace_4715_, v_openDecls_4716_, v_cancelTk_x3f_4717_);
return v_res_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(lean_object* v_p_4721_, lean_object* v_level_4722_, lean_object* v_part_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v___x_4728_; 
v___x_4728_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4722_, v_part_4723_, v_a_4724_, v_a_4725_, v_a_4726_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___boxed(lean_object* v_p_4729_, lean_object* v_level_4730_, lean_object* v_part_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(v_p_4729_, v_level_4730_, v_part_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
lean_dec(v_a_4734_);
lean_dec_ref(v_a_4733_);
lean_dec(v_a_4732_);
lean_dec(v_level_4730_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(lean_object* v_p_4737_, lean_object* v___x_4738_, size_t v_sz_4739_, size_t v_i_4740_, lean_object* v_bs_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v___x_4746_; 
v___x_4746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4738_, v_sz_4739_, v_i_4740_, v_bs_4741_, v___y_4742_, v___y_4743_, v___y_4744_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___boxed(lean_object* v_p_4747_, lean_object* v___x_4748_, lean_object* v_sz_4749_, lean_object* v_i_4750_, lean_object* v_bs_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_){
_start:
{
size_t v_sz_boxed_4756_; size_t v_i_boxed_4757_; lean_object* v_res_4758_; 
v_sz_boxed_4756_ = lean_unbox_usize(v_sz_4749_);
lean_dec(v_sz_4749_);
v_i_boxed_4757_ = lean_unbox_usize(v_i_4750_);
lean_dec(v_i_4750_);
v_res_4758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(v_p_4747_, v___x_4748_, v_sz_boxed_4756_, v_i_boxed_4757_, v_bs_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
lean_dec(v___y_4754_);
lean_dec_ref(v___y_4753_);
lean_dec(v___y_4752_);
lean_dec(v___x_4748_);
return v_res_4758_;
}
}
lean_object* runtime_initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Markdown(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
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
res = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Doc_docInlineMdExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Doc_docInlineMdExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Doc_docBlockMdExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Doc_docBlockMdExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers);
lean_dec_ref(res);
res = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers);
lean_dec_ref(res);
l_Lean_Doc_mdRendererHeartbeats = _init_l_Lean_Doc_mdRendererHeartbeats();
lean_mark_persistent(l_Lean_Doc_mdRendererHeartbeats);
l_Lean_Doc_instMarkdownInlineElabInline = _init_l_Lean_Doc_instMarkdownInlineElabInline();
lean_mark_persistent(l_Lean_Doc_instMarkdownInlineElabInline);
l_Lean_Doc_instMarkdownBlockElabInlineElabBlock = _init_l_Lean_Doc_instMarkdownBlockElabInlineElabBlock();
lean_mark_persistent(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock);
l_Lean_Doc_instToMarkdownVersoDocString = _init_l_Lean_Doc_instToMarkdownVersoDocString();
lean_mark_persistent(l_Lean_Doc_instToMarkdownVersoDocString);
l_Lean_Doc_instToMarkdownSnippet = _init_l_Lean_Doc_instToMarkdownSnippet();
lean_mark_persistent(l_Lean_Doc_instToMarkdownSnippet);
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
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
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
res = initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
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
