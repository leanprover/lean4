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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
v___x_8_ = lean_st_ref_set(v_a_3_, v___x_7_);
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
lean_object* v_str_107_; lean_object* v_startInclusive_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_str_107_ = lean_ctor_get(v_s_105_, 0);
v_startInclusive_108_ = lean_ctor_get(v_s_105_, 1);
v___x_109_ = lean_nat_add(v_startInclusive_108_, v_pos_106_);
v___x_110_ = lean_nat_sub(v___x_109_, v_startInclusive_108_);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_nat_dec_eq(v___x_110_, v___x_111_);
if (v___x_112_ == 0)
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
uint8_t v___x_121_; 
v___x_121_ = lean_nat_dec_lt(v___x_117_, v_pos_106_);
if (v___x_121_ == 0)
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0___boxed(lean_object* v_s_123_, lean_object* v_pos_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(v_s_123_, v_pos_124_);
lean_dec_ref(v_s_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(lean_object* v_s_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_string_utf8_byte_size(v_s_126_);
lean_inc_ref(v_s_126_);
v___x_129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_129_, 0, v_s_126_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
lean_ctor_set(v___x_129_, 2, v___x_128_);
v___x_130_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(v___x_129_, v___x_128_);
lean_dec_ref_known(v___x_129_, 3);
v___x_131_ = lean_string_utf8_extract(v_s_126_, v___x_127_, v___x_130_);
lean_dec(v___x_130_);
lean_dec_ref(v_s_126_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(lean_object* v_p_132_, lean_object* v_pTrim_133_, size_t v_sz_134_, size_t v_i_135_, lean_object* v_bs_136_){
_start:
{
uint8_t v___x_137_; 
v___x_137_ = lean_usize_dec_lt(v_i_135_, v_sz_134_);
if (v___x_137_ == 0)
{
lean_dec_ref(v_pTrim_133_);
lean_dec_ref(v_p_132_);
return v_bs_136_;
}
else
{
lean_object* v_v_138_; lean_object* v___x_139_; lean_object* v_bs_x27_140_; lean_object* v___y_142_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_v_138_ = lean_array_uget(v_bs_136_, v_i_135_);
v___x_139_ = lean_unsigned_to_nat(0u);
v_bs_x27_140_ = lean_array_uset(v_bs_136_, v_i_135_, v___x_139_);
v___x_147_ = lean_string_utf8_byte_size(v_v_138_);
v___x_148_ = lean_nat_dec_eq(v___x_147_, v___x_139_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; 
lean_inc_ref(v_p_132_);
v___x_149_ = lean_string_append(v_p_132_, v_v_138_);
lean_dec(v_v_138_);
v___y_142_ = v___x_149_;
goto v___jp_141_;
}
else
{
lean_dec(v_v_138_);
lean_inc_ref(v_pTrim_133_);
v___y_142_ = v_pTrim_133_;
goto v___jp_141_;
}
v___jp_141_:
{
size_t v___x_143_; size_t v___x_144_; lean_object* v___x_145_; 
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_add(v_i_135_, v___x_143_);
v___x_145_ = lean_array_uset(v_bs_x27_140_, v_i_135_, v___y_142_);
v_i_135_ = v___x_144_;
v_bs_136_ = v___x_145_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0___boxed(lean_object* v_p_150_, lean_object* v_pTrim_151_, lean_object* v_sz_152_, lean_object* v_i_153_, lean_object* v_bs_154_){
_start:
{
size_t v_sz_boxed_155_; size_t v_i_boxed_156_; lean_object* v_res_157_; 
v_sz_boxed_155_ = lean_unbox_usize(v_sz_152_);
lean_dec(v_sz_152_);
v_i_boxed_156_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_res_157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(v_p_150_, v_pTrim_151_, v_sz_boxed_155_, v_i_boxed_156_, v_bs_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_prefixLines(lean_object* v_p_158_, lean_object* v_lines_159_){
_start:
{
lean_object* v_pTrim_160_; size_t v_sz_161_; size_t v___x_162_; lean_object* v___x_163_; 
lean_inc_ref(v_p_158_);
v_pTrim_160_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_p_158_);
v_sz_161_ = lean_array_size(v_lines_159_);
v___x_162_ = ((size_t)0ULL);
v___x_163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(v_p_158_, v_pTrim_160_, v_sz_161_, v___x_162_, v_lines_159_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(lean_object* v_rest_164_, lean_object* v_restTrim_165_, lean_object* v_head_166_, lean_object* v_headTrim_167_, size_t v_sz_168_, size_t v_i_169_, lean_object* v_bs_170_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = lean_usize_dec_lt(v_i_169_, v_sz_168_);
if (v___x_171_ == 0)
{
lean_dec_ref(v_headTrim_167_);
lean_dec_ref(v_head_166_);
lean_dec_ref(v_restTrim_165_);
lean_dec_ref(v_rest_164_);
return v_bs_170_;
}
else
{
lean_object* v_v_172_; lean_object* v___x_173_; lean_object* v_bs_x27_174_; lean_object* v___y_176_; lean_object* v_fst_182_; lean_object* v_snd_183_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_v_172_ = lean_array_uget(v_bs_170_, v_i_169_);
v___x_173_ = lean_unsigned_to_nat(0u);
v_bs_x27_174_ = lean_array_uset(v_bs_170_, v_i_169_, v___x_173_);
v___x_187_ = lean_usize_to_nat(v_i_169_);
v___x_188_ = lean_nat_dec_eq(v___x_187_, v___x_173_);
lean_dec(v___x_187_);
if (v___x_188_ == 0)
{
lean_inc_ref(v_restTrim_165_);
lean_inc_ref(v_rest_164_);
v_fst_182_ = v_rest_164_;
v_snd_183_ = v_restTrim_165_;
goto v___jp_181_;
}
else
{
lean_inc_ref(v_headTrim_167_);
lean_inc_ref(v_head_166_);
v_fst_182_ = v_head_166_;
v_snd_183_ = v_headTrim_167_;
goto v___jp_181_;
}
v___jp_175_:
{
size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((size_t)1ULL);
v___x_178_ = lean_usize_add(v_i_169_, v___x_177_);
v___x_179_ = lean_array_uset(v_bs_x27_174_, v_i_169_, v___y_176_);
v_i_169_ = v___x_178_;
v_bs_170_ = v___x_179_;
goto _start;
}
v___jp_181_:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_string_utf8_byte_size(v_v_172_);
v___x_185_ = lean_nat_dec_eq(v___x_184_, v___x_173_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
lean_dec_ref(v_snd_183_);
v___x_186_ = lean_string_append(v_fst_182_, v_v_172_);
lean_dec(v_v_172_);
v___y_176_ = v___x_186_;
goto v___jp_175_;
}
else
{
lean_dec_ref(v_fst_182_);
lean_dec(v_v_172_);
v___y_176_ = v_snd_183_;
goto v___jp_175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg___boxed(lean_object* v_rest_189_, lean_object* v_restTrim_190_, lean_object* v_head_191_, lean_object* v_headTrim_192_, lean_object* v_sz_193_, lean_object* v_i_194_, lean_object* v_bs_195_){
_start:
{
size_t v_sz_boxed_196_; size_t v_i_boxed_197_; lean_object* v_res_198_; 
v_sz_boxed_196_ = lean_unbox_usize(v_sz_193_);
lean_dec(v_sz_193_);
v_i_boxed_197_ = lean_unbox_usize(v_i_194_);
lean_dec(v_i_194_);
v_res_198_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_189_, v_restTrim_190_, v_head_191_, v_headTrim_192_, v_sz_boxed_196_, v_i_boxed_197_, v_bs_195_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_prefixListLines(lean_object* v_head_199_, lean_object* v_rest_200_, lean_object* v_lines_201_){
_start:
{
lean_object* v_headTrim_202_; lean_object* v_restTrim_203_; size_t v_sz_204_; size_t v___x_205_; lean_object* v___x_206_; 
lean_inc_ref(v_head_199_);
v_headTrim_202_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_head_199_);
lean_inc_ref(v_rest_200_);
v_restTrim_203_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_rest_200_);
v_sz_204_ = lean_array_size(v_lines_201_);
v___x_205_ = ((size_t)0ULL);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_200_, v_restTrim_203_, v_head_199_, v_headTrim_202_, v_sz_204_, v___x_205_, v_lines_201_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0(lean_object* v_rest_207_, lean_object* v_restTrim_208_, lean_object* v_head_209_, lean_object* v_headTrim_210_, lean_object* v_as_211_, size_t v_sz_212_, size_t v_i_213_, lean_object* v_bs_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_207_, v_restTrim_208_, v_head_209_, v_headTrim_210_, v_sz_212_, v_i_213_, v_bs_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___boxed(lean_object* v_rest_216_, lean_object* v_restTrim_217_, lean_object* v_head_218_, lean_object* v_headTrim_219_, lean_object* v_as_220_, lean_object* v_sz_221_, lean_object* v_i_222_, lean_object* v_bs_223_){
_start:
{
size_t v_sz_boxed_224_; size_t v_i_boxed_225_; lean_object* v_res_226_; 
v_sz_boxed_224_ = lean_unbox_usize(v_sz_221_);
lean_dec(v_sz_221_);
v_i_boxed_225_ = lean_unbox_usize(v_i_222_);
lean_dec(v_i_222_);
v_res_226_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0(v_rest_216_, v_restTrim_217_, v_head_218_, v_headTrim_219_, v_as_220_, v_sz_boxed_224_, v_i_boxed_225_, v_bs_223_);
lean_dec_ref(v_as_220_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(lean_object* v_as_228_, size_t v_i_229_, size_t v_stop_230_, lean_object* v_b_231_){
_start:
{
lean_object* v___y_233_; uint8_t v___x_237_; 
v___x_237_ = lean_usize_dec_eq(v_i_229_, v_stop_230_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_238_ = lean_array_uget_borrowed(v_as_228_, v_i_229_);
v___x_239_ = lean_array_get_size(v___x_238_);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_nat_dec_eq(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_array_get_size(v_b_231_);
v___x_243_ = lean_nat_dec_eq(v___x_242_, v___x_240_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_245_ = lean_array_push(v_b_231_, v___x_244_);
v___x_246_ = l_Array_append___redArg(v___x_245_, v___x_238_);
v___y_233_ = v___x_246_;
goto v___jp_232_;
}
else
{
lean_dec_ref(v_b_231_);
lean_inc(v___x_238_);
v___y_233_ = v___x_238_;
goto v___jp_232_;
}
}
else
{
v___y_233_ = v_b_231_;
goto v___jp_232_;
}
}
else
{
return v_b_231_;
}
v___jp_232_:
{
size_t v___x_234_; size_t v___x_235_; 
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_add(v_i_229_, v___x_234_);
v_i_229_ = v___x_235_;
v_b_231_ = v___y_233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___boxed(lean_object* v_as_247_, lean_object* v_i_248_, lean_object* v_stop_249_, lean_object* v_b_250_){
_start:
{
size_t v_i_boxed_251_; size_t v_stop_boxed_252_; lean_object* v_res_253_; 
v_i_boxed_251_ = lean_unbox_usize(v_i_248_);
lean_dec(v_i_248_);
v_stop_boxed_252_ = lean_unbox_usize(v_stop_249_);
lean_dec(v_stop_249_);
v_res_253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_as_247_, v_i_boxed_251_, v_stop_boxed_252_, v_b_250_);
lean_dec_ref(v_as_247_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks(lean_object* v_blocks_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_259_ = lean_array_get_size(v_blocks_256_);
v___x_260_ = lean_nat_dec_lt(v___x_257_, v___x_259_);
if (v___x_260_ == 0)
{
return v___x_258_;
}
else
{
uint8_t v___x_261_; 
v___x_261_ = lean_nat_dec_le(v___x_259_, v___x_259_);
if (v___x_261_ == 0)
{
if (v___x_260_ == 0)
{
return v___x_258_;
}
else
{
size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; 
v___x_262_ = ((size_t)0ULL);
v___x_263_ = lean_usize_of_nat(v___x_259_);
v___x_264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_256_, v___x_262_, v___x_263_, v___x_258_);
return v___x_264_;
}
}
else
{
size_t v___x_265_; size_t v___x_266_; lean_object* v___x_267_; 
v___x_265_ = ((size_t)0ULL);
v___x_266_ = lean_usize_of_nat(v___x_259_);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_256_, v___x_265_, v___x_266_, v___x_258_);
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks___boxed(lean_object* v_blocks_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Doc_joinBlocks(v_blocks_268_);
lean_dec_ref(v_blocks_268_);
return v_res_269_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_272_ = lean_string_utf8_byte_size(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(lean_object* v_l_274_, lean_object* v_r_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_276_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_277_ = lean_string_utf8_byte_size(v_l_274_);
v___x_278_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1);
v___x_279_ = lean_nat_dec_le(v___x_278_, v___x_277_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
v___x_280_ = lean_string_append(v_l_274_, v_r_275_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_nat_sub(v___x_277_, v___x_278_);
v___x_283_ = lean_string_memcmp(v_l_274_, v___x_276_, v___x_282_, v___x_281_, v___x_278_);
lean_dec(v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_string_append(v_l_274_, v_r_275_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_string_utf8_byte_size(v_r_275_);
v___x_286_ = lean_nat_dec_le(v___x_278_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
v___x_287_ = lean_string_append(v_l_274_, v_r_275_);
return v___x_287_;
}
else
{
uint8_t v___x_288_; 
v___x_288_ = lean_string_memcmp(v_r_275_, v___x_276_, v___x_281_, v___x_281_, v___x_278_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; 
v___x_289_ = lean_string_append(v_l_274_, v_r_275_);
return v___x_289_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2));
v___x_291_ = lean_string_append(v_l_274_, v___x_290_);
v___x_292_ = lean_string_append(v___x_291_, v_r_275_);
return v___x_292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___boxed(lean_object* v_l_293_, lean_object* v_r_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v_l_293_, v_r_294_);
lean_dec_ref(v_r_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(lean_object* v_as_296_, size_t v_i_297_, size_t v_stop_298_, lean_object* v_b_299_){
_start:
{
lean_object* v___y_301_; uint8_t v___x_305_; 
v___x_305_ = lean_usize_dec_eq(v_i_297_, v_stop_298_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_306_ = lean_array_uget_borrowed(v_as_296_, v_i_297_);
v___x_307_ = lean_array_get_size(v___x_306_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_nat_dec_eq(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = lean_array_get_size(v_b_299_);
v___x_311_ = lean_nat_dec_eq(v___x_310_, v___x_308_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v_lastIdx_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v_glued_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_312_ = lean_unsigned_to_nat(1u);
v_lastIdx_313_ = lean_nat_sub(v___x_310_, v___x_312_);
v___x_314_ = lean_array_fget_borrowed(v_b_299_, v_lastIdx_313_);
v___x_315_ = lean_array_fget_borrowed(v___x_306_, v___x_308_);
lean_inc(v___x_314_);
v_glued_316_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v___x_314_, v___x_315_);
v___x_317_ = lean_array_fset(v_b_299_, v_lastIdx_313_, v_glued_316_);
lean_dec(v_lastIdx_313_);
v___x_318_ = l_Array_extract___redArg(v___x_306_, v___x_312_, v___x_307_);
v___x_319_ = l_Array_append___redArg(v___x_317_, v___x_318_);
lean_dec_ref(v___x_318_);
v___y_301_ = v___x_319_;
goto v___jp_300_;
}
else
{
lean_dec_ref(v_b_299_);
lean_inc(v___x_306_);
v___y_301_ = v___x_306_;
goto v___jp_300_;
}
}
else
{
v___y_301_ = v_b_299_;
goto v___jp_300_;
}
}
else
{
return v_b_299_;
}
v___jp_300_:
{
size_t v___x_302_; size_t v___x_303_; 
v___x_302_ = ((size_t)1ULL);
v___x_303_ = lean_usize_add(v_i_297_, v___x_302_);
v_i_297_ = v___x_303_;
v_b_299_ = v___y_301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0___boxed(lean_object* v_as_320_, lean_object* v_i_321_, lean_object* v_stop_322_, lean_object* v_b_323_){
_start:
{
size_t v_i_boxed_324_; size_t v_stop_boxed_325_; lean_object* v_res_326_; 
v_i_boxed_324_ = lean_unbox_usize(v_i_321_);
lean_dec(v_i_321_);
v_stop_boxed_325_ = lean_unbox_usize(v_stop_322_);
lean_dec(v_stop_322_);
v_res_326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_as_320_, v_i_boxed_324_, v_stop_boxed_325_, v_b_323_);
lean_dec_ref(v_as_320_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines(lean_object* v_parts_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_330_ = lean_array_get_size(v_parts_327_);
v___x_331_ = lean_nat_dec_lt(v___x_328_, v___x_330_);
if (v___x_331_ == 0)
{
return v___x_329_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = lean_nat_dec_le(v___x_330_, v___x_330_);
if (v___x_332_ == 0)
{
if (v___x_331_ == 0)
{
return v___x_329_;
}
else
{
size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; 
v___x_333_ = ((size_t)0ULL);
v___x_334_ = lean_usize_of_nat(v___x_330_);
v___x_335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_327_, v___x_333_, v___x_334_, v___x_329_);
return v___x_335_;
}
}
else
{
size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; 
v___x_336_ = ((size_t)0ULL);
v___x_337_ = lean_usize_of_nat(v___x_330_);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_327_, v___x_336_, v___x_337_, v___x_329_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines___boxed(lean_object* v_parts_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Doc_joinInlines(v_parts_339_);
lean_dec_ref(v_parts_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object* v_a_341_, uint8_t v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
uint8_t v_a_19__boxed_355_; lean_object* v_res_356_; 
v_a_19__boxed_355_ = lean_unbox(v_a_349_);
v_res_356_ = l_Lean_Doc_instMarkdownInlineEmpty___lam__0(v_a_348_, v_a_19__boxed_355_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec_ref(v_a_348_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0(lean_object* v_a_359_, lean_object* v_a_360_, uint8_t v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed(lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
uint8_t v_a_23__boxed_375_; lean_object* v_res_376_; 
v_a_23__boxed_375_ = lean_unbox(v_a_369_);
v_res_376_ = l_Lean_Doc_instMarkdownBlockEmpty___lam__0(v_a_367_, v_a_368_, v_a_23__boxed_375_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec_ref(v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object* v_i_378_){
_start:
{
lean_object* v___f_379_; 
v___f_379_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___closed__0));
return v___f_379_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_380_) == 0)
{
if (lean_obj_tag(v_x_381_) == 0)
{
uint8_t v___x_382_; 
v___x_382_ = 1;
return v___x_382_;
}
else
{
uint8_t v___x_383_; 
v___x_383_ = 0;
return v___x_383_;
}
}
else
{
if (lean_obj_tag(v_x_381_) == 0)
{
uint8_t v___x_384_; 
v___x_384_ = 0;
return v___x_384_;
}
else
{
lean_object* v_val_385_; lean_object* v_val_386_; uint32_t v___x_387_; uint32_t v___x_388_; uint8_t v___x_389_; 
v_val_385_ = lean_ctor_get(v_x_380_, 0);
v_val_386_ = lean_ctor_get(v_x_381_, 0);
v___x_387_ = lean_unbox_uint32(v_val_385_);
v___x_388_ = lean_unbox_uint32(v_val_386_);
v___x_389_ = lean_uint32_dec_eq(v___x_387_, v___x_388_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1___boxed(lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_x_390_, v_x_391_);
lean_dec(v_x_391_);
lean_dec(v_x_390_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(lean_object* v_s_394_, uint32_t v_c_395_, lean_object* v_a_396_, uint8_t v_b_397_){
_start:
{
lean_object* v_str_398_; lean_object* v_startInclusive_399_; lean_object* v_endExclusive_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_str_398_ = lean_ctor_get(v_s_394_, 0);
v_startInclusive_399_ = lean_ctor_get(v_s_394_, 1);
v_endExclusive_400_ = lean_ctor_get(v_s_394_, 2);
v___x_401_ = lean_nat_sub(v_endExclusive_400_, v_startInclusive_399_);
v___x_402_ = lean_nat_dec_eq(v_a_396_, v___x_401_);
lean_dec(v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_403_ = lean_nat_add(v_startInclusive_399_, v_a_396_);
lean_dec(v_a_396_);
v___x_404_ = lean_string_utf8_get_fast(v_str_398_, v___x_403_);
v___x_405_ = lean_uint32_dec_eq(v___x_404_, v_c_395_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_string_utf8_next_fast(v_str_398_, v___x_403_);
lean_dec(v___x_403_);
v___x_407_ = lean_nat_sub(v___x_406_, v_startInclusive_399_);
v_a_396_ = v___x_407_;
v_b_397_ = v___x_405_;
goto _start;
}
else
{
lean_dec(v___x_403_);
return v___x_405_;
}
}
else
{
lean_dec(v_a_396_);
return v_b_397_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg___boxed(lean_object* v_s_409_, lean_object* v_c_410_, lean_object* v_a_411_, lean_object* v_b_412_){
_start:
{
uint32_t v_c_boxed_413_; uint8_t v_b_boxed_414_; uint8_t v_res_415_; lean_object* v_r_416_; 
v_c_boxed_413_ = lean_unbox_uint32(v_c_410_);
lean_dec(v_c_410_);
v_b_boxed_414_ = lean_unbox(v_b_412_);
v_res_415_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_409_, v_c_boxed_413_, v_a_411_, v_b_boxed_414_);
lean_dec_ref(v_s_409_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(uint32_t v_c_417_, lean_object* v_s_418_){
_start:
{
lean_object* v_searcher_419_; uint8_t v___x_420_; uint8_t v___x_421_; 
v_searcher_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = 0;
v___x_421_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_418_, v_c_417_, v_searcher_419_, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0___boxed(lean_object* v_c_422_, lean_object* v_s_423_){
_start:
{
uint32_t v_c_boxed_424_; uint8_t v_res_425_; lean_object* v_r_426_; 
v_c_boxed_424_ = lean_unbox_uint32(v_c_422_);
lean_dec(v_c_422_);
v_res_425_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_boxed_424_, v_s_423_);
lean_dec_ref(v_s_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0));
v___x_429_ = lean_string_utf8_byte_size(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_430_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0));
v___x_433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_431_);
lean_ctor_set(v___x_433_, 2, v___x_430_);
return v___x_433_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_434_; lean_object* v___x_435_; 
v___x_434_ = 91;
v___x_435_ = lean_box_uint32(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1;
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(uint32_t v_c_438_, lean_object* v_next_x3f_439_){
_start:
{
uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = 33;
v___x_441_ = lean_uint32_dec_eq(v_c_438_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2);
v___x_443_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_438_, v___x_442_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3);
v___x_445_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_439_, v___x_444_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___boxed(lean_object* v_c_446_, lean_object* v_next_x3f_447_){
_start:
{
uint32_t v_c_boxed_448_; uint8_t v_res_449_; lean_object* v_r_450_; 
v_c_boxed_448_ = lean_unbox_uint32(v_c_446_);
lean_dec(v_c_446_);
v_res_449_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_boxed_448_, v_next_x3f_447_);
lean_dec(v_next_x3f_447_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(lean_object* v_s_451_, uint32_t v_c_452_, lean_object* v_inst_453_, lean_object* v_R_454_, lean_object* v_a_455_, uint8_t v_b_456_, lean_object* v_c_457_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_451_, v_c_452_, v_a_455_, v_b_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___boxed(lean_object* v_s_459_, lean_object* v_c_460_, lean_object* v_inst_461_, lean_object* v_R_462_, lean_object* v_a_463_, lean_object* v_b_464_, lean_object* v_c_465_){
_start:
{
uint32_t v_c_boxed_466_; uint8_t v_b_boxed_467_; uint8_t v_res_468_; lean_object* v_r_469_; 
v_c_boxed_466_ = lean_unbox_uint32(v_c_460_);
lean_dec(v_c_460_);
v_b_boxed_467_ = lean_unbox(v_b_464_);
v_res_468_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(v_s_459_, v_c_boxed_466_, v_inst_461_, v_R_462_, v_a_463_, v_b_boxed_467_, v_c_465_);
lean_dec_ref(v_s_459_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_470_; lean_object* v___x_471_; 
v___x_470_ = 32;
v___x_471_ = lean_box_uint32(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(lean_object* v_prev_x3f_474_, uint32_t v_c_475_, lean_object* v_next_x3f_476_){
_start:
{
uint8_t v___y_478_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0);
v___x_496_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_476_, v___x_495_);
if (v___x_496_ == 0)
{
if (lean_obj_tag(v_next_x3f_476_) == 0)
{
uint8_t v___x_497_; 
v___x_497_ = 1;
v___y_478_ = v___x_497_;
goto v___jp_477_;
}
else
{
v___y_478_ = v___x_496_;
goto v___jp_477_;
}
}
else
{
v___y_478_ = v___x_496_;
goto v___jp_477_;
}
v___jp_477_:
{
uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_479_ = 62;
v___x_480_ = lean_uint32_dec_eq(v_c_475_, v___x_479_);
if (v___x_480_ == 0)
{
uint32_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = 45;
v___x_482_ = lean_uint32_dec_eq(v_c_475_, v___x_481_);
if (v___x_482_ == 0)
{
uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 43;
v___x_484_ = lean_uint32_dec_eq(v_c_475_, v___x_483_);
if (v___x_484_ == 0)
{
uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 46;
v___x_486_ = lean_uint32_dec_eq(v_c_475_, v___x_485_);
if (v___x_486_ == 0)
{
uint8_t v___x_487_; 
v___x_487_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_475_, v_next_x3f_476_);
return v___x_487_;
}
else
{
if (lean_obj_tag(v_prev_x3f_474_) == 0)
{
return v___x_484_;
}
else
{
lean_object* v_val_488_; uint32_t v___x_489_; uint32_t v___x_490_; uint8_t v___x_491_; 
v_val_488_ = lean_ctor_get(v_prev_x3f_474_, 0);
v___x_489_ = 48;
v___x_490_ = lean_unbox_uint32(v_val_488_);
v___x_491_ = lean_uint32_dec_le(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
if (v___x_491_ == 0)
{
return v___x_491_;
}
else
{
return v___y_478_;
}
}
else
{
uint32_t v___x_492_; uint32_t v___x_493_; uint8_t v___x_494_; 
v___x_492_ = 57;
v___x_493_ = lean_unbox_uint32(v_val_488_);
v___x_494_ = lean_uint32_dec_le(v___x_493_, v___x_492_);
if (v___x_494_ == 0)
{
return v___x_494_;
}
else
{
return v___y_478_;
}
}
}
}
}
else
{
return v___y_478_;
}
}
else
{
return v___y_478_;
}
}
else
{
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___boxed(lean_object* v_prev_x3f_498_, lean_object* v_c_499_, lean_object* v_next_x3f_500_){
_start:
{
uint32_t v_c_boxed_501_; uint8_t v_res_502_; lean_object* v_r_503_; 
v_c_boxed_501_ = lean_unbox_uint32(v_c_499_);
lean_dec(v_c_499_);
v_res_502_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_prev_x3f_498_, v_c_boxed_501_, v_next_x3f_500_);
lean_dec(v_next_x3f_500_);
lean_dec(v_prev_x3f_498_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0));
v___x_506_ = lean_string_utf8_byte_size(v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_507_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1);
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0));
v___x_510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v___x_508_);
lean_ctor_set(v___x_510_, 2, v___x_507_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(uint32_t v___x_511_, lean_object* v___x_512_, lean_object* v_____r_513_, lean_object* v_s_x27_514_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___y_523_; uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_515_ = lean_string_push(v_s_x27_514_, v___x_511_);
v___x_516_ = lean_box_uint32(v___x_511_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
v___x_529_ = 48;
v___x_530_ = lean_uint32_dec_le(v___x_529_, v___x_511_);
if (v___x_530_ == 0)
{
v___y_523_ = v___x_530_;
goto v___jp_522_;
}
else
{
uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 57;
v___x_532_ = lean_uint32_dec_le(v___x_511_, v___x_531_);
v___y_523_ = v___x_532_;
goto v___jp_522_;
}
v___jp_518_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_512_);
lean_ctor_set(v___x_519_, 1, v___x_517_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_515_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
v___jp_522_:
{
if (v___y_523_ == 0)
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2);
v___x_525_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v___x_511_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_512_);
lean_ctor_set(v___x_526_, 1, v___x_517_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_515_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
else
{
goto v___jp_518_;
}
}
else
{
goto v___jp_518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed(lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v_____r_535_, lean_object* v_s_x27_536_){
_start:
{
uint32_t v___x_1753__boxed_537_; lean_object* v_res_538_; 
v___x_1753__boxed_537_ = lean_unbox_uint32(v___x_533_);
lean_dec(v___x_533_);
v_res_538_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_1753__boxed_537_, v___x_534_, v_____r_535_, v_s_x27_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(lean_object* v_s_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___y_542_; lean_object* v_snd_546_; lean_object* v_fst_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_581_; 
v_snd_546_ = lean_ctor_get(v_a_540_, 1);
v_fst_547_ = lean_ctor_get(v_a_540_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v_a_540_);
if (v_isSharedCheck_581_ == 0)
{
v___x_549_ = v_a_540_;
v_isShared_550_ = v_isSharedCheck_581_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_snd_546_);
lean_inc(v_fst_547_);
lean_dec(v_a_540_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_581_;
goto v_resetjp_548_;
}
v___jp_541_:
{
if (lean_obj_tag(v___y_542_) == 0)
{
lean_object* v_a_543_; 
v_a_543_ = lean_ctor_get(v___y_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___y_542_, 1);
return v_a_543_;
}
else
{
lean_object* v_a_544_; 
v_a_544_ = lean_ctor_get(v___y_542_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___y_542_, 1);
v_a_540_ = v_a_544_;
goto _start;
}
}
v_resetjp_548_:
{
lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_580_; 
v_fst_551_ = lean_ctor_get(v_snd_546_, 0);
v_snd_552_ = lean_ctor_get(v_snd_546_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_snd_546_);
if (v_isSharedCheck_580_ == 0)
{
v___x_554_ = v_snd_546_;
v_isShared_555_ = v_isSharedCheck_580_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_snd_552_);
lean_inc(v_fst_551_);
lean_dec(v_snd_546_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_580_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_string_utf8_byte_size(v_s_539_);
v___x_557_ = lean_nat_dec_eq(v_fst_551_, v___x_556_);
if (v___x_557_ == 0)
{
uint32_t v___x_558_; lean_object* v___x_559_; lean_object* v___y_561_; uint8_t v___x_569_; 
lean_del_object(v___x_554_);
lean_del_object(v___x_549_);
v___x_558_ = lean_string_utf8_get_fast(v_s_539_, v_fst_551_);
v___x_559_ = lean_string_utf8_next_fast(v_s_539_, v_fst_551_);
lean_dec(v_fst_551_);
v___x_569_ = lean_nat_dec_eq(v___x_559_, v___x_556_);
if (v___x_569_ == 0)
{
uint32_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_string_utf8_get_fast(v_s_539_, v___x_559_);
v___x_571_ = lean_box_uint32(v___x_570_);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
v___y_561_ = v___x_572_;
goto v___jp_560_;
}
else
{
lean_object* v_prev_x3f_573_; 
v_prev_x3f_573_ = lean_box(0);
v___y_561_ = v_prev_x3f_573_;
goto v___jp_560_;
}
v___jp_560_:
{
uint8_t v___x_562_; 
v___x_562_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_snd_552_, v___x_558_, v___y_561_);
lean_dec(v___y_561_);
lean_dec(v_snd_552_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_box(0);
v___x_564_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_558_, v___x_559_, v___x_563_, v_fst_547_);
v___y_542_ = v___x_564_;
goto v___jp_541_;
}
else
{
uint32_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_565_ = 92;
v___x_566_ = lean_string_push(v_fst_547_, v___x_565_);
v___x_567_ = lean_box(0);
v___x_568_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_558_, v___x_559_, v___x_567_, v___x_566_);
v___y_542_ = v___x_568_;
goto v___jp_541_;
}
}
}
else
{
lean_object* v___x_575_; 
if (v_isShared_555_ == 0)
{
v___x_575_ = v___x_554_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_fst_551_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_snd_552_);
v___x_575_ = v_reuseFailAlloc_579_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_577_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_575_);
v___x_577_ = v___x_549_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_fst_547_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___boxed(lean_object* v_s_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_582_, v_a_583_);
lean_dec_ref(v_s_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(uint32_t v___x_585_, lean_object* v___x_586_, lean_object* v_____r_587_, lean_object* v_s_x27_588_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_string_push(v_s_x27_588_, v___x_585_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___x_586_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0___boxed(lean_object* v___x_592_, lean_object* v___x_593_, lean_object* v_____r_594_, lean_object* v_s_x27_595_){
_start:
{
uint32_t v___x_1877__boxed_596_; lean_object* v_res_597_; 
v___x_1877__boxed_596_ = lean_unbox_uint32(v___x_592_);
lean_dec(v___x_592_);
v_res_597_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_1877__boxed_596_, v___x_593_, v_____r_594_, v_s_x27_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(lean_object* v_s_598_, lean_object* v_a_599_){
_start:
{
lean_object* v___y_601_; lean_object* v_fst_605_; lean_object* v_snd_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_631_; 
v_fst_605_ = lean_ctor_get(v_a_599_, 0);
v_snd_606_ = lean_ctor_get(v_a_599_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_a_599_);
if (v_isSharedCheck_631_ == 0)
{
v___x_608_ = v_a_599_;
v_isShared_609_ = v_isSharedCheck_631_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snd_606_);
lean_inc(v_fst_605_);
lean_dec(v_a_599_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_631_;
goto v_resetjp_607_;
}
v___jp_600_:
{
if (lean_obj_tag(v___y_601_) == 0)
{
lean_object* v_a_602_; 
v_a_602_ = lean_ctor_get(v___y_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___y_601_, 1);
return v_a_602_;
}
else
{
lean_object* v_a_603_; 
v_a_603_ = lean_ctor_get(v___y_601_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___y_601_, 1);
v_a_599_ = v_a_603_;
goto _start;
}
}
v_resetjp_607_:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_string_utf8_byte_size(v_s_598_);
v___x_611_ = lean_nat_dec_eq(v_snd_606_, v___x_610_);
if (v___x_611_ == 0)
{
uint32_t v___x_612_; lean_object* v___x_613_; lean_object* v___y_615_; uint8_t v___x_623_; 
lean_del_object(v___x_608_);
v___x_612_ = lean_string_utf8_get_fast(v_s_598_, v_snd_606_);
v___x_613_ = lean_string_utf8_next_fast(v_s_598_, v_snd_606_);
lean_dec(v_snd_606_);
v___x_623_ = lean_nat_dec_eq(v___x_613_, v___x_610_);
if (v___x_623_ == 0)
{
uint32_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_string_utf8_get_fast(v_s_598_, v___x_613_);
v___x_625_ = lean_box_uint32(v___x_624_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___y_615_ = v___x_626_;
goto v___jp_614_;
}
else
{
lean_object* v_prev_x3f_627_; 
v_prev_x3f_627_ = lean_box(0);
v___y_615_ = v_prev_x3f_627_;
goto v___jp_614_;
}
v___jp_614_:
{
uint8_t v___x_616_; 
v___x_616_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v___x_612_, v___y_615_);
lean_dec(v___y_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_box(0);
v___x_618_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_612_, v___x_613_, v___x_617_, v_fst_605_);
v___y_601_ = v___x_618_;
goto v___jp_600_;
}
else
{
uint32_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_619_ = 92;
v___x_620_ = lean_string_push(v_fst_605_, v___x_619_);
v___x_621_ = lean_box(0);
v___x_622_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_612_, v___x_613_, v___x_621_, v___x_620_);
v___y_601_ = v___x_622_;
goto v___jp_600_;
}
}
}
else
{
lean_object* v___x_629_; 
if (v_isShared_609_ == 0)
{
v___x_629_ = v___x_608_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_fst_605_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_snd_606_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___boxed(lean_object* v_s_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_632_, v_a_633_);
lean_dec_ref(v_s_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object* v_s_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v_snd_644_; lean_object* v_fst_645_; lean_object* v_fst_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_655_; 
v___x_642_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1));
v___x_643_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_641_, v___x_642_);
v_snd_644_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_snd_644_);
v_fst_645_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_fst_645_);
lean_dec_ref(v___x_643_);
v_fst_646_ = lean_ctor_get(v_snd_644_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v_snd_644_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v_snd_644_, 1);
lean_dec(v_unused_656_);
v___x_648_ = v_snd_644_;
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_fst_646_);
lean_dec(v_snd_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v_fst_646_);
lean_ctor_set(v___x_648_, 0, v_fst_645_);
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_fst_645_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_fst_646_);
v___x_651_ = v_reuseFailAlloc_654_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; lean_object* v_fst_653_; 
v___x_652_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_641_, v___x_651_);
v_fst_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_fst_653_);
lean_dec_ref(v___x_652_);
return v_fst_653_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object* v_s_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_657_);
lean_dec_ref(v_s_657_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object* v_s_659_, lean_object* v_inst_660_, lean_object* v_a_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_659_, v_a_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object* v_s_663_, lean_object* v_inst_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_663_, v_inst_664_, v_a_665_);
lean_dec_ref(v_s_663_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(lean_object* v_s_667_, lean_object* v_inst_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_667_, v_a_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___boxed(lean_object* v_s_671_, lean_object* v_inst_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(v_s_671_, v_inst_672_, v_a_673_);
lean_dec_ref(v_s_671_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v_str_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_snd_677_; lean_object* v_fst_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_720_; 
v_snd_677_ = lean_ctor_get(v_a_676_, 1);
v_fst_678_ = lean_ctor_get(v_a_676_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v_a_676_);
if (v_isSharedCheck_720_ == 0)
{
v___x_680_ = v_a_676_;
v_isShared_681_ = v_isSharedCheck_720_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_snd_677_);
lean_inc(v_fst_678_);
lean_dec(v_a_676_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_720_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_fst_682_; lean_object* v_snd_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_719_; 
v_fst_682_ = lean_ctor_get(v_snd_677_, 0);
v_snd_683_ = lean_ctor_get(v_snd_677_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_snd_677_);
if (v_isSharedCheck_719_ == 0)
{
v___x_685_ = v_snd_677_;
v_isShared_686_ = v_isSharedCheck_719_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_snd_683_);
lean_inc(v_fst_682_);
lean_dec(v_snd_677_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_719_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_string_utf8_byte_size(v_str_675_);
v___x_688_ = lean_nat_dec_eq(v_snd_683_, v___x_687_);
if (v___x_688_ == 0)
{
uint32_t v___x_689_; lean_object* v___x_690_; uint32_t v___x_691_; uint8_t v___x_692_; 
v___x_689_ = lean_string_utf8_get_fast(v_str_675_, v_snd_683_);
v___x_690_ = lean_string_utf8_next_fast(v_str_675_, v_snd_683_);
lean_dec(v_snd_683_);
v___x_691_ = 96;
v___x_692_ = lean_uint32_dec_eq(v___x_689_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v_longest_693_; lean_object* v___y_695_; uint8_t v___x_703_; 
v_longest_693_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_nat_dec_le(v_fst_678_, v_fst_682_);
if (v___x_703_ == 0)
{
lean_dec(v_fst_682_);
v___y_695_ = v_fst_678_;
goto v___jp_694_;
}
else
{
lean_dec(v_fst_678_);
v___y_695_ = v_fst_682_;
goto v___jp_694_;
}
v___jp_694_:
{
lean_object* v___x_697_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_690_);
lean_ctor_set(v___x_685_, 0, v_longest_693_);
v___x_697_ = v___x_685_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_longest_693_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_690_);
v___x_697_ = v_reuseFailAlloc_702_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_697_);
lean_ctor_set(v___x_680_, 0, v___y_695_);
v___x_699_ = v___x_680_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___y_695_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v_a_676_ = v___x_699_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_add(v_fst_682_, v___x_704_);
lean_dec(v_fst_682_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_690_);
lean_ctor_set(v___x_685_, 0, v___x_705_);
v___x_707_ = v___x_685_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_690_);
v___x_707_ = v_reuseFailAlloc_712_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_707_);
v___x_709_ = v___x_680_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_fst_678_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_707_);
v___x_709_ = v_reuseFailAlloc_711_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v_a_676_ = v___x_709_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_714_; 
if (v_isShared_686_ == 0)
{
v___x_714_ = v___x_685_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_fst_682_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_snd_683_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_714_);
v___x_716_ = v___x_680_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_fst_678_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v_str_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_721_, v_a_722_);
lean_dec_ref(v_str_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(lean_object* v_str_729_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v_snd_732_; lean_object* v_fst_733_; lean_object* v_fst_734_; uint8_t v___x_735_; 
v___x_730_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1));
v___x_731_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_729_, v___x_730_);
v_snd_732_ = lean_ctor_get(v___x_731_, 1);
lean_inc(v_snd_732_);
v_fst_733_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_fst_733_);
lean_dec_ref(v___x_731_);
v_fst_734_ = lean_ctor_get(v_snd_732_, 0);
lean_inc(v_fst_734_);
lean_dec(v_snd_732_);
v___x_735_ = lean_nat_dec_le(v_fst_733_, v_fst_734_);
if (v___x_735_ == 0)
{
lean_dec(v_fst_734_);
return v_fst_733_;
}
else
{
lean_dec(v_fst_733_);
return v_fst_734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___boxed(lean_object* v_str_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_736_);
lean_dec_ref(v_str_736_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(lean_object* v_str_738_, lean_object* v_inst_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_738_, v_a_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v_str_742_, lean_object* v_inst_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(v_str_742_, v_inst_743_, v_a_744_);
lean_dec_ref(v_str_742_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
lean_object* v_zero_748_; uint8_t v_isZero_749_; 
v_zero_748_ = lean_unsigned_to_nat(0u);
v_isZero_749_ = lean_nat_dec_eq(v_x_746_, v_zero_748_);
if (v_isZero_749_ == 1)
{
lean_dec(v_x_746_);
return v_x_747_;
}
else
{
uint32_t v___x_750_; lean_object* v_one_751_; lean_object* v_n_752_; lean_object* v___x_753_; 
v___x_750_ = 96;
v_one_751_ = lean_unsigned_to_nat(1u);
v_n_752_ = lean_nat_sub(v_x_746_, v_one_751_);
lean_dec(v_x_746_);
v___x_753_ = lean_string_push(v_x_747_, v___x_750_);
v_x_746_ = v_n_752_;
v_x_747_ = v___x_753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(lean_object* v_atLeast_755_, lean_object* v_str_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___y_759_; lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_763_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_756_);
v___x_764_ = lean_nat_dec_le(v_atLeast_755_, v___x_763_);
if (v___x_764_ == 0)
{
lean_dec(v___x_763_);
v___y_759_ = v_atLeast_755_;
goto v___jp_758_;
}
else
{
lean_dec(v_atLeast_755_);
v___y_759_ = v___x_763_;
goto v___jp_758_;
}
v___jp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_add(v___y_759_, v___x_760_);
lean_dec(v___y_759_);
v___x_762_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(v___x_761_, v___x_757_);
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor___boxed(lean_object* v_atLeast_765_, lean_object* v_str_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v_atLeast_765_, v_str_766_);
lean_dec_ref(v_str_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object* v_str_769_){
_start:
{
lean_object* v___x_770_; lean_object* v_backticks_771_; lean_object* v___y_773_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_770_ = lean_unsigned_to_nat(0u);
v_backticks_771_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_770_, v_str_769_);
v___x_787_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_788_ = lean_string_utf8_byte_size(v_str_769_);
v___x_789_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1);
v___x_790_ = lean_nat_dec_le(v___x_789_, v___x_788_);
if (v___x_790_ == 0)
{
goto v___jp_780_;
}
else
{
uint8_t v___x_791_; 
v___x_791_ = lean_string_memcmp(v_str_769_, v___x_787_, v___x_770_, v___x_770_, v___x_789_);
if (v___x_791_ == 0)
{
goto v___jp_780_;
}
else
{
goto v___jp_776_;
}
}
v___jp_772_:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
lean_inc_ref(v_backticks_771_);
v___x_774_ = lean_string_append(v_backticks_771_, v___y_773_);
lean_dec_ref(v___y_773_);
v___x_775_ = lean_string_append(v___x_774_, v_backticks_771_);
lean_dec_ref(v_backticks_771_);
return v___x_775_;
}
v___jp_776_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_777_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_778_ = lean_string_append(v___x_777_, v_str_769_);
lean_dec_ref(v_str_769_);
v___x_779_ = lean_string_append(v___x_778_, v___x_777_);
v___y_773_ = v___x_779_;
goto v___jp_772_;
}
v___jp_780_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_781_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_782_ = lean_string_utf8_byte_size(v_str_769_);
v___x_783_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1);
v___x_784_ = lean_nat_dec_le(v___x_783_, v___x_782_);
if (v___x_784_ == 0)
{
v___y_773_ = v_str_769_;
goto v___jp_772_;
}
else
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = lean_nat_sub(v___x_782_, v___x_783_);
v___x_786_ = lean_string_memcmp(v_str_769_, v___x_781_, v___x_785_, v___x_770_, v___x_783_);
lean_dec(v___x_785_);
if (v___x_786_ == 0)
{
v___y_773_ = v_str_769_;
goto v___jp_772_;
}
else
{
goto v___jp_776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(lean_object* v_s_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0));
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___boxed(lean_object* v_s_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v_s_796_);
lean_dec_ref(v_s_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(lean_object* v_str_798_, lean_object* v___x_799_, lean_object* v___x_800_, lean_object* v_a_801_, lean_object* v_b_802_){
_start:
{
lean_object* v_it_804_; lean_object* v_startInclusive_805_; lean_object* v_endExclusive_806_; 
if (lean_obj_tag(v_a_801_) == 0)
{
lean_object* v_currPos_810_; lean_object* v_searcher_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_837_; 
v_currPos_810_ = lean_ctor_get(v_a_801_, 0);
v_searcher_811_ = lean_ctor_get(v_a_801_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v_a_801_);
if (v_isSharedCheck_837_ == 0)
{
v___x_813_ = v_a_801_;
v_isShared_814_ = v_isSharedCheck_837_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_searcher_811_);
lean_inc(v_currPos_810_);
lean_dec(v_a_801_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_837_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_startInclusive_815_; lean_object* v_endExclusive_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_startInclusive_815_ = lean_ctor_get(v___x_799_, 1);
v_endExclusive_816_ = lean_ctor_get(v___x_799_, 2);
v___x_817_ = lean_nat_sub(v_endExclusive_816_, v_startInclusive_815_);
v___x_818_ = lean_nat_dec_eq(v_searcher_811_, v___x_817_);
lean_dec(v___x_817_);
if (v___x_818_ == 0)
{
uint32_t v___x_819_; uint32_t v___x_820_; uint8_t v___x_821_; 
v___x_819_ = 10;
v___x_820_ = lean_string_utf8_get_fast(v_str_798_, v_searcher_811_);
v___x_821_ = lean_uint32_dec_eq(v___x_820_, v___x_819_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_string_utf8_next_fast(v_str_798_, v_searcher_811_);
lean_dec(v_searcher_811_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v___x_822_);
v___x_824_ = v___x_813_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_currPos_810_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___x_822_);
v___x_824_ = v_reuseFailAlloc_826_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
v_a_801_ = v___x_824_;
goto _start;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_slice_830_; lean_object* v_nextIt_832_; 
v___x_827_ = lean_string_utf8_next_fast(v_str_798_, v_searcher_811_);
v___x_828_ = lean_nat_sub(v___x_827_, v_searcher_811_);
v___x_829_ = lean_nat_add(v_searcher_811_, v___x_828_);
lean_dec(v___x_828_);
v_slice_830_ = l_String_Slice_subslice_x21(v___x_799_, v_currPos_810_, v_searcher_811_);
lean_inc(v___x_829_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v___x_829_);
lean_ctor_set(v___x_813_, 0, v___x_829_);
v_nextIt_832_ = v___x_813_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_829_);
v_nextIt_832_ = v_reuseFailAlloc_835_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v_startInclusive_833_; lean_object* v_endExclusive_834_; 
v_startInclusive_833_ = lean_ctor_get(v_slice_830_, 0);
lean_inc(v_startInclusive_833_);
v_endExclusive_834_ = lean_ctor_get(v_slice_830_, 1);
lean_inc(v_endExclusive_834_);
lean_dec_ref(v_slice_830_);
v_it_804_ = v_nextIt_832_;
v_startInclusive_805_ = v_startInclusive_833_;
v_endExclusive_806_ = v_endExclusive_834_;
goto v___jp_803_;
}
}
}
else
{
lean_object* v___x_836_; 
lean_del_object(v___x_813_);
lean_dec(v_searcher_811_);
v___x_836_ = lean_box(1);
lean_inc(v___x_800_);
v_it_804_ = v___x_836_;
v_startInclusive_805_ = v_currPos_810_;
v_endExclusive_806_ = v___x_800_;
goto v___jp_803_;
}
}
}
else
{
lean_dec(v___x_800_);
return v_b_802_;
}
v___jp_803_:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_string_utf8_extract(v_str_798_, v_startInclusive_805_, v_endExclusive_806_);
lean_dec(v_endExclusive_806_);
lean_dec(v_startInclusive_805_);
v___x_808_ = lean_array_push(v_b_802_, v___x_807_);
v_a_801_ = v_it_804_;
v_b_802_ = v___x_808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg___boxed(lean_object* v_str_838_, lean_object* v___x_839_, lean_object* v___x_840_, lean_object* v_a_841_, lean_object* v_b_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_838_, v___x_839_, v___x_840_, v_a_841_, v_b_842_);
lean_dec_ref(v___x_839_);
lean_dec_ref(v_str_838_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(lean_object* v_str_844_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_string_utf8_byte_size(v_str_844_);
lean_inc_ref(v_str_844_);
v___x_847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_847_, 0, v_str_844_);
lean_ctor_set(v___x_847_, 1, v___x_845_);
lean_ctor_set(v___x_847_, 2, v___x_846_);
v___x_848_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v___x_847_);
v___x_849_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_850_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_844_, v___x_847_, v___x_846_, v___x_848_, v___x_849_);
lean_dec_ref_known(v___x_847_, 3);
lean_dec_ref(v_str_844_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(lean_object* v_str_851_, lean_object* v___x_852_, lean_object* v___x_853_, lean_object* v_inst_854_, lean_object* v_R_855_, lean_object* v_a_856_, lean_object* v_b_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_851_, v___x_852_, v___x_853_, v_a_856_, v_b_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___boxed(lean_object* v_str_859_, lean_object* v___x_860_, lean_object* v___x_861_, lean_object* v_inst_862_, lean_object* v_R_863_, lean_object* v_a_864_, lean_object* v_b_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(v_str_859_, v___x_860_, v___x_861_, v_inst_862_, v_R_863_, v_a_864_, v_b_865_);
lean_dec_ref(v___x_860_);
lean_dec_ref(v_str_859_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(lean_object* v_str_867_){
_start:
{
lean_object* v___x_868_; lean_object* v_fence_869_; lean_object* v___y_871_; lean_object* v_body_877_; uint8_t v___y_879_; lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_868_ = lean_unsigned_to_nat(2u);
v_fence_869_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_868_, v_str_867_);
v_body_877_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(v_str_867_);
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_array_get_size(v_body_877_);
v___x_883_ = lean_nat_dec_lt(v___x_881_, v___x_882_);
if (v___x_883_ == 0)
{
v___y_879_ = v___x_883_;
goto v___jp_878_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_885_ = lean_unsigned_to_nat(1u);
v___x_886_ = lean_nat_sub(v___x_882_, v___x_885_);
v___x_887_ = lean_array_get(v___x_884_, v_body_877_, v___x_886_);
lean_dec(v___x_886_);
v___x_888_ = lean_string_utf8_byte_size(v___x_887_);
lean_dec(v___x_887_);
v___x_889_ = lean_nat_dec_eq(v___x_888_, v___x_881_);
v___y_879_ = v___x_889_;
goto v___jp_878_;
}
v___jp_870_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_mk_empty_array_with_capacity(v___x_872_);
v___x_874_ = lean_array_push(v___x_873_, v_fence_869_);
lean_inc_ref(v___x_874_);
v___x_875_ = l_Array_append___redArg(v___x_874_, v___y_871_);
lean_dec_ref(v___y_871_);
v___x_876_ = l_Array_append___redArg(v___x_875_, v___x_874_);
lean_dec_ref(v___x_874_);
return v___x_876_;
}
v___jp_878_:
{
if (v___y_879_ == 0)
{
v___y_871_ = v_body_877_;
goto v___jp_870_;
}
else
{
lean_object* v___x_880_; 
v___x_880_ = lean_array_pop(v_body_877_);
v___y_871_ = v___x_880_;
goto v___jp_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_890_, lean_object* v_pos_891_){
_start:
{
lean_object* v_str_892_; lean_object* v_startInclusive_893_; lean_object* v_endExclusive_894_; lean_object* v___x_895_; uint8_t v___y_903_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_str_892_ = lean_ctor_get(v_s_890_, 0);
v_startInclusive_893_ = lean_ctor_get(v_s_890_, 1);
v_endExclusive_894_ = lean_ctor_get(v_s_890_, 2);
v___x_895_ = lean_nat_add(v_startInclusive_893_, v_pos_891_);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_nat_sub(v_endExclusive_894_, v___x_895_);
v___x_906_ = lean_nat_dec_eq(v___x_904_, v___x_905_);
lean_dec(v___x_905_);
if (v___x_906_ == 0)
{
uint32_t v___x_907_; uint8_t v___y_909_; uint32_t v___x_914_; uint8_t v___x_915_; 
v___x_907_ = lean_string_utf8_get_fast(v_str_892_, v___x_895_);
v___x_914_ = 32;
v___x_915_ = lean_uint32_dec_eq(v___x_907_, v___x_914_);
if (v___x_915_ == 0)
{
uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 9;
v___x_917_ = lean_uint32_dec_eq(v___x_907_, v___x_916_);
v___y_909_ = v___x_917_;
goto v___jp_908_;
}
else
{
v___y_909_ = v___x_915_;
goto v___jp_908_;
}
v___jp_908_:
{
if (v___y_909_ == 0)
{
uint32_t v___x_910_; uint8_t v___x_911_; 
v___x_910_ = 13;
v___x_911_ = lean_uint32_dec_eq(v___x_907_, v___x_910_);
if (v___x_911_ == 0)
{
uint32_t v___x_912_; uint8_t v___x_913_; 
v___x_912_ = 10;
v___x_913_ = lean_uint32_dec_eq(v___x_907_, v___x_912_);
v___y_903_ = v___x_913_;
goto v___jp_902_;
}
else
{
v___y_903_ = v___x_911_;
goto v___jp_902_;
}
}
else
{
goto v___jp_896_;
}
}
}
else
{
lean_dec(v___x_895_);
return v_pos_891_;
}
v___jp_896_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_897_ = lean_string_utf8_next_fast(v_str_892_, v___x_895_);
v___x_898_ = lean_nat_sub(v___x_897_, v___x_895_);
lean_dec(v___x_895_);
v___x_899_ = lean_nat_add(v_pos_891_, v___x_898_);
lean_dec(v___x_898_);
v___x_900_ = lean_nat_dec_lt(v_pos_891_, v___x_899_);
if (v___x_900_ == 0)
{
lean_dec(v___x_899_);
return v_pos_891_;
}
else
{
lean_dec(v_pos_891_);
v_pos_891_ = v___x_899_;
goto _start;
}
}
v___jp_902_:
{
if (v___y_903_ == 0)
{
lean_dec(v___x_895_);
return v_pos_891_;
}
else
{
goto v___jp_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object* v_s_918_, lean_object* v_pos_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_918_, v_pos_919_);
lean_dec_ref(v_s_918_);
return v_res_920_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Doc_Inline_empty(lean_box(0));
return v___x_921_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object* v_a_925_){
_start:
{
if (lean_obj_tag(v_a_925_) == 0)
{
lean_object* v___x_926_; 
v___x_926_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
return v___x_926_;
}
else
{
lean_object* v_head_927_; 
v_head_927_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_head_927_);
switch(lean_obj_tag(v_head_927_))
{
case 0:
{
lean_object* v_tail_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_972_; 
v_tail_928_ = lean_ctor_get(v_a_925_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v_a_925_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v_a_925_, 0);
lean_dec(v_unused_973_);
v___x_930_ = v_a_925_;
v_isShared_931_ = v_isSharedCheck_972_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_tail_928_);
lean_dec(v_a_925_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_972_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_string_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_971_; 
v_string_932_ = lean_ctor_get(v_head_927_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v_head_927_);
if (v_isSharedCheck_971_ == 0)
{
v___x_934_ = v_head_927_;
v_isShared_935_ = v_isSharedCheck_971_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_string_932_);
lean_dec(v_head_927_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_971_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_string_utf8_byte_size(v_string_932_);
lean_inc_ref(v_string_932_);
v___x_938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_938_, 0, v_string_932_);
lean_ctor_set(v___x_938_, 1, v___x_936_);
lean_ctor_set(v___x_938_, 2, v___x_937_);
v___x_939_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_938_, v___x_936_);
lean_dec_ref_known(v___x_938_, 3);
v___x_940_ = lean_nat_dec_eq(v___x_939_, v___x_937_);
if (v___x_940_ == 0)
{
lean_object* v_s1_941_; lean_object* v_s2_942_; lean_object* v___x_944_; 
v_s1_941_ = lean_string_utf8_extract(v_string_932_, v___x_936_, v___x_939_);
v_s2_942_ = lean_string_utf8_extract(v_string_932_, v___x_939_, v___x_937_);
lean_dec(v___x_939_);
lean_dec_ref(v_string_932_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v_s2_942_);
v___x_944_ = v___x_934_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_s2_942_);
v___x_944_ = v_reuseFailAlloc_959_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_945_ = lean_array_mk(v_tail_928_);
v___x_946_ = lean_array_get_size(v___x_945_);
v___x_947_ = lean_nat_dec_eq(v___x_946_, v___x_936_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = lean_mk_empty_array_with_capacity(v___x_948_);
v___x_950_ = lean_array_push(v___x_949_, v___x_944_);
v___x_951_ = l_Array_append___redArg(v___x_950_, v___x_945_);
lean_dec_ref(v___x_945_);
v___x_952_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
if (v_isShared_931_ == 0)
{
lean_ctor_set_tag(v___x_930_, 0);
lean_ctor_set(v___x_930_, 1, v___x_952_);
lean_ctor_set(v___x_930_, 0, v_s1_941_);
v___x_954_ = v___x_930_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_s1_941_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
else
{
lean_object* v___x_957_; 
lean_dec_ref(v___x_945_);
if (v_isShared_931_ == 0)
{
lean_ctor_set_tag(v___x_930_, 0);
lean_ctor_set(v___x_930_, 1, v___x_944_);
lean_ctor_set(v___x_930_, 0, v_s1_941_);
v___x_957_ = v___x_930_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_s1_941_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_944_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
lean_object* v___x_960_; lean_object* v_fst_961_; lean_object* v_snd_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_970_; 
lean_dec(v___x_939_);
lean_del_object(v___x_934_);
lean_del_object(v___x_930_);
v___x_960_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_928_);
v_fst_961_ = lean_ctor_get(v___x_960_, 0);
v_snd_962_ = lean_ctor_get(v___x_960_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_970_ == 0)
{
v___x_964_ = v___x_960_;
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_snd_962_);
lean_inc(v_fst_961_);
lean_dec(v___x_960_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = lean_string_append(v_string_932_, v_fst_961_);
lean_dec(v_fst_961_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_snd_962_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_974_; lean_object* v_content_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_tail_974_ = lean_ctor_get(v_a_925_, 1);
lean_inc(v_tail_974_);
lean_dec_ref_known(v_a_925_, 2);
v_content_975_ = lean_ctor_get(v_head_927_, 0);
lean_inc_ref(v_content_975_);
lean_dec_ref_known(v_head_927_, 1);
v___x_976_ = lean_array_to_list(v_content_975_);
v___x_977_ = l_List_appendTR___redArg(v___x_976_, v_tail_974_);
v_a_925_ = v___x_977_;
goto _start;
}
default: 
{
lean_object* v_tail_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1017_; 
v_tail_979_ = lean_ctor_get(v_a_925_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_a_925_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v_a_925_, 0);
lean_dec(v_unused_1018_);
v___x_981_ = v_a_925_;
v_isShared_982_ = v_isSharedCheck_1017_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_tail_979_);
lean_dec(v_a_925_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1017_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_984_ = lean_array_mk(v_tail_979_);
if (lean_obj_tag(v_head_927_) == 9)
{
lean_object* v_content_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_content_985_ = lean_ctor_get(v_head_927_, 0);
v___x_986_ = lean_array_get_size(v_content_985_);
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_nat_dec_eq(v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = lean_array_get_size(v___x_984_);
v___x_990_ = lean_nat_dec_eq(v___x_989_, v___x_987_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
lean_inc_ref(v_content_985_);
lean_dec_ref_known(v_head_927_, 1);
v___x_991_ = l_Array_append___redArg(v_content_985_, v___x_984_);
lean_dec_ref(v___x_984_);
v___x_992_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 0);
lean_ctor_set(v___x_981_, 1, v___x_992_);
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_994_ = v___x_981_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
else
{
lean_object* v___x_997_; 
lean_dec_ref(v___x_984_);
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 0);
lean_ctor_set(v___x_981_, 1, v_head_927_);
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_997_ = v___x_981_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_head_927_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_dec_ref_known(v_head_927_, 1);
v___x_999_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_984_);
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 0);
lean_ctor_set(v___x_981_, 1, v___x_999_);
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_1001_ = v___x_981_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = lean_array_get_size(v___x_984_);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_nat_dec_eq(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1006_ = lean_unsigned_to_nat(1u);
v___x_1007_ = lean_mk_empty_array_with_capacity(v___x_1006_);
v___x_1008_ = lean_array_push(v___x_1007_, v_head_927_);
v___x_1009_ = l_Array_append___redArg(v___x_1008_, v___x_984_);
lean_dec_ref(v___x_984_);
v___x_1010_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 0);
lean_ctor_set(v___x_981_, 1, v___x_1010_);
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_1012_ = v___x_981_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
else
{
lean_object* v___x_1015_; 
lean_dec_ref(v___x_984_);
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 0);
lean_ctor_set(v___x_981_, 1, v_head_927_);
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_1015_ = v___x_981_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_head_927_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = lean_box(0);
v___x_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_inline_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_1026_, lean_object* v_inline_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_1029_, lean_object* v_pos_1030_){
_start:
{
lean_object* v_str_1031_; lean_object* v_startInclusive_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v_str_1031_ = lean_ctor_get(v_s_1029_, 0);
v_startInclusive_1032_ = lean_ctor_get(v_s_1029_, 1);
v___x_1033_ = lean_nat_add(v_startInclusive_1032_, v_pos_1030_);
v___x_1034_ = lean_nat_sub(v___x_1033_, v_startInclusive_1032_);
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = lean_nat_dec_eq(v___x_1034_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___y_1045_; lean_object* v___x_1046_; uint32_t v___x_1047_; uint8_t v___y_1049_; uint32_t v___x_1054_; uint8_t v___x_1055_; 
lean_inc(v_startInclusive_1032_);
lean_inc_ref(v_str_1031_);
v___x_1037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1037_, 0, v_str_1031_);
lean_ctor_set(v___x_1037_, 1, v_startInclusive_1032_);
lean_ctor_set(v___x_1037_, 2, v___x_1033_);
v___x_1038_ = lean_unsigned_to_nat(1u);
v___x_1039_ = lean_nat_sub(v___x_1034_, v___x_1038_);
lean_dec(v___x_1034_);
v___x_1040_ = l_String_Slice_posLE(v___x_1037_, v___x_1039_);
lean_dec_ref_known(v___x_1037_, 3);
v___x_1046_ = lean_nat_add(v_startInclusive_1032_, v___x_1040_);
v___x_1047_ = lean_string_utf8_get_fast(v_str_1031_, v___x_1046_);
lean_dec(v___x_1046_);
v___x_1054_ = 32;
v___x_1055_ = lean_uint32_dec_eq(v___x_1047_, v___x_1054_);
if (v___x_1055_ == 0)
{
uint32_t v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = 9;
v___x_1057_ = lean_uint32_dec_eq(v___x_1047_, v___x_1056_);
v___y_1049_ = v___x_1057_;
goto v___jp_1048_;
}
else
{
v___y_1049_ = v___x_1055_;
goto v___jp_1048_;
}
v___jp_1041_:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_nat_dec_lt(v___x_1040_, v_pos_1030_);
if (v___x_1042_ == 0)
{
lean_dec(v___x_1040_);
return v_pos_1030_;
}
else
{
lean_dec(v_pos_1030_);
v_pos_1030_ = v___x_1040_;
goto _start;
}
}
v___jp_1044_:
{
if (v___y_1045_ == 0)
{
lean_dec(v___x_1040_);
return v_pos_1030_;
}
else
{
goto v___jp_1041_;
}
}
v___jp_1048_:
{
if (v___y_1049_ == 0)
{
uint32_t v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = 13;
v___x_1051_ = lean_uint32_dec_eq(v___x_1047_, v___x_1050_);
if (v___x_1051_ == 0)
{
uint32_t v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = 10;
v___x_1053_ = lean_uint32_dec_eq(v___x_1047_, v___x_1052_);
v___y_1045_ = v___x_1053_;
goto v___jp_1044_;
}
else
{
v___y_1045_ = v___x_1051_;
goto v___jp_1044_;
}
}
else
{
goto v___jp_1041_;
}
}
}
else
{
lean_dec(v___x_1034_);
lean_dec(v___x_1033_);
return v_pos_1030_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_1058_, lean_object* v_pos_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_1058_, v_pos_1059_);
lean_dec_ref(v_s_1058_);
return v_res_1060_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1062_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___x_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_xs_1064_){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = lean_array_get_size(v_xs_1064_);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_nat_dec_eq(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_nat_sub(v___x_1065_, v___x_1068_);
v___x_1070_ = lean_array_fget(v_xs_1064_, v___x_1069_);
lean_dec(v___x_1069_);
switch(lean_obj_tag(v___x_1070_))
{
case 0:
{
lean_object* v_string_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1101_; 
v_string_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1101_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_string_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1101_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1075_ = lean_string_utf8_byte_size(v_string_1071_);
lean_inc_ref(v_string_1071_);
v___x_1076_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1076_, 0, v_string_1071_);
lean_ctor_set(v___x_1076_, 1, v___x_1066_);
lean_ctor_set(v___x_1076_, 2, v___x_1075_);
v___x_1077_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_1076_, v___x_1066_);
v___x_1078_ = lean_nat_dec_eq(v___x_1077_, v___x_1075_);
lean_dec(v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1079_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_1076_, v___x_1075_);
lean_dec_ref_known(v___x_1076_, 3);
v___x_1080_ = lean_array_pop(v_xs_1064_);
v___x_1081_ = lean_string_utf8_extract(v_string_1071_, v___x_1066_, v___x_1079_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1081_);
v___x_1083_ = v___x_1073_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1084_ = lean_array_push(v___x_1080_, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
v___x_1086_ = lean_string_utf8_extract(v_string_1071_, v___x_1079_, v___x_1075_);
lean_dec(v___x_1079_);
lean_dec_ref(v_string_1071_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
return v___x_1087_;
}
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_fst_1091_; lean_object* v_snd_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1100_; 
lean_dec_ref_known(v___x_1076_, 3);
lean_del_object(v___x_1073_);
v___x_1089_ = lean_array_pop(v_xs_1064_);
v___x_1090_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1089_);
v_fst_1091_ = lean_ctor_get(v___x_1090_, 0);
v_snd_1092_ = lean_ctor_get(v___x_1090_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1094_ = v___x_1090_;
v_isShared_1095_ = v_isSharedCheck_1100_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_snd_1092_);
lean_inc(v_fst_1091_);
lean_dec(v___x_1090_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1100_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = lean_string_append(v_snd_1092_, v_string_1071_);
lean_dec_ref(v_string_1071_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v___x_1096_);
v___x_1098_ = v___x_1094_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_fst_1091_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
case 9:
{
lean_object* v_content_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_content_1102_ = lean_ctor_get(v___x_1070_, 0);
lean_inc_ref(v_content_1102_);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1103_ = lean_array_pop(v_xs_1064_);
v___x_1104_ = l_Array_append___redArg(v___x_1103_, v_content_1102_);
lean_dec_ref(v_content_1102_);
v_xs_1064_ = v___x_1104_;
goto _start;
}
default: 
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v___x_1070_);
v___x_1106_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_xs_1064_);
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
return v___x_1108_;
}
}
}
else
{
lean_object* v___x_1109_; 
lean_dec_ref(v_xs_1064_);
v___x_1109_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_1110_, lean_object* v_xs_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_xs_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1114_ = lean_unsigned_to_nat(1u);
v___x_1115_ = lean_mk_empty_array_with_capacity(v___x_1114_);
v___x_1116_ = lean_array_push(v___x_1115_, v_inline_1113_);
v___x_1117_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_1118_, lean_object* v_inline_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_1121_){
_start:
{
lean_object* v___x_1122_; lean_object* v_fst_1123_; lean_object* v_snd_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1132_; 
v___x_1122_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1121_);
v_fst_1123_ = lean_ctor_get(v___x_1122_, 0);
v_snd_1124_ = lean_ctor_get(v___x_1122_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1126_ = v___x_1122_;
v_isShared_1127_ = v_isSharedCheck_1132_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_snd_1124_);
lean_inc(v_fst_1123_);
lean_dec(v___x_1122_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1132_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_1124_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 1, v___x_1128_);
v___x_1130_ = v___x_1126_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_fst_1123_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_1133_, lean_object* v_inline_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_1134_);
return v___x_1135_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_instMonadEIO(lean_box(0));
return v___x_1136_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0);
v___x_1138_ = l_StateRefT_x27_instMonad___redArg(v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1167_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13));
v___x_1168_ = lean_unsigned_to_nat(3u);
v___x_1169_ = lean_mk_empty_array_with_capacity(v___x_1168_);
v___x_1170_ = lean_array_push(v___x_1169_, v___x_1167_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object* v_inst_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1173_, v_x_1174_, v_x_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_pieces_1189_; lean_object* v_pieces_1193_; lean_object* v___x_1196_; lean_object* v_toApplicative_1197_; lean_object* v_toFunctor_1198_; lean_object* v_toSeq_1199_; lean_object* v_toSeqLeft_1200_; lean_object* v_toSeqRight_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___f_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1196_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1197_ = lean_ctor_get(v___x_1196_, 0);
v_toFunctor_1198_ = lean_ctor_get(v_toApplicative_1197_, 0);
v_toSeq_1199_ = lean_ctor_get(v_toApplicative_1197_, 2);
v_toSeqLeft_1200_ = lean_ctor_get(v_toApplicative_1197_, 3);
v_toSeqRight_1201_ = lean_ctor_get(v_toApplicative_1197_, 4);
v___f_1202_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1203_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1198_, 2);
v___f_1204_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1204_, 0, v_toFunctor_1198_);
v___f_1205_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1205_, 0, v_toFunctor_1198_);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___f_1204_);
lean_ctor_set(v___x_1206_, 1, v___f_1205_);
lean_inc(v_toSeqRight_1201_);
v___f_1207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1207_, 0, v_toSeqRight_1201_);
lean_inc(v_toSeqLeft_1200_);
v___f_1208_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1208_, 0, v_toSeqLeft_1200_);
lean_inc(v_toSeq_1199_);
v___f_1209_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1209_, 0, v_toSeq_1199_);
v___x_1210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1206_);
lean_ctor_set(v___x_1210_, 1, v___f_1202_);
lean_ctor_set(v___x_1210_, 2, v___f_1209_);
lean_ctor_set(v___x_1210_, 3, v___f_1208_);
lean_ctor_set(v___x_1210_, 4, v___f_1207_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___f_1203_);
v___x_1212_ = l_StateRefT_x27_instMonad___redArg(v___x_1211_);
switch(lean_obj_tag(v_x_1183_))
{
case 0:
{
lean_object* v_string_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec_ref(v___x_1212_);
lean_dec_ref(v_x_1182_);
lean_dec_ref(v_inst_1181_);
v_string_1213_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_string_1213_);
lean_dec_ref_known(v_x_1183_, 1);
v___x_1214_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1213_);
lean_dec_ref(v_string_1213_);
v___x_1215_ = lean_unsigned_to_nat(1u);
v___x_1216_ = lean_mk_empty_array_with_capacity(v___x_1215_);
v___x_1217_ = lean_array_push(v___x_1216_, v___x_1214_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
case 1:
{
lean_object* v_content_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v___x_1212_);
v_content_1219_ = lean_ctor_get(v_x_1183_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_x_1183_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1221_ = v_x_1183_;
v_isShared_1222_ = v_isSharedCheck_1270_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_content_1219_);
lean_dec(v_x_1183_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1270_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 9);
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_content_1219_);
v___x_1224_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; lean_object* v_snd_1226_; lean_object* v_fst_1227_; lean_object* v_fst_1228_; lean_object* v_snd_1229_; lean_object* v_pieces_1231_; uint8_t v_inEmph_1239_; uint8_t v_inBold_1240_; uint8_t v_inLink_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1268_; 
v___x_1225_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1224_);
v_snd_1226_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_snd_1226_);
v_fst_1227_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_fst_1227_);
lean_dec_ref(v___x_1225_);
v_fst_1228_ = lean_ctor_get(v_snd_1226_, 0);
lean_inc(v_fst_1228_);
v_snd_1229_ = lean_ctor_get(v_snd_1226_, 1);
lean_inc(v_snd_1229_);
lean_dec(v_snd_1226_);
v_inEmph_1239_ = lean_ctor_get_uint8(v_x_1182_, 0);
v_inBold_1240_ = lean_ctor_get_uint8(v_x_1182_, 1);
v_inLink_1241_ = lean_ctor_get_uint8(v_x_1182_, 2);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1243_ = v_x_1182_;
v_isShared_1244_ = v_isSharedCheck_1268_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v_x_1182_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1268_;
goto v_resetjp_1242_;
}
v___jp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1232_ = lean_string_utf8_byte_size(v_snd_1229_);
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = lean_nat_dec_eq(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = lean_mk_empty_array_with_capacity(v___x_1235_);
v___x_1237_ = lean_array_push(v___x_1236_, v_snd_1229_);
v___x_1238_ = lean_array_push(v_pieces_1231_, v___x_1237_);
v_pieces_1193_ = v___x_1238_;
goto v___jp_1192_;
}
else
{
lean_dec(v_snd_1229_);
v_pieces_1193_ = v_pieces_1231_;
goto v___jp_1192_;
}
}
v_resetjp_1242_:
{
uint8_t v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = 1;
if (v_isShared_1244_ == 0)
{
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, 1, v_inBold_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, 2, v_inLink_1241_);
v___x_1247_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; 
lean_ctor_set_uint8(v___x_1247_, 0, v___x_1245_);
v___x_1248_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1181_, v___x_1247_, v_fst_1228_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v_pieces_1251_; lean_object* v_pieces_1256_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1261_ = lean_string_utf8_byte_size(v_fst_1227_);
v___x_1262_ = lean_nat_dec_eq(v___x_1261_, v___x_1259_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_mk_empty_array_with_capacity(v___x_1263_);
v___x_1265_ = lean_array_push(v___x_1264_, v_fst_1227_);
v___x_1266_ = lean_array_push(v___x_1260_, v___x_1265_);
v_pieces_1256_ = v___x_1266_;
goto v___jp_1255_;
}
else
{
lean_dec(v_fst_1227_);
v_pieces_1256_ = v___x_1260_;
goto v___jp_1255_;
}
v___jp_1250_:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_array_push(v_pieces_1251_, v_a_1249_);
if (v_inEmph_1239_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1254_ = lean_array_push(v___x_1252_, v___x_1253_);
v_pieces_1231_ = v___x_1254_;
goto v___jp_1230_;
}
else
{
v_pieces_1231_ = v___x_1252_;
goto v___jp_1230_;
}
}
v___jp_1255_:
{
if (v_inEmph_1239_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1258_ = lean_array_push(v_pieces_1256_, v___x_1257_);
v_pieces_1251_ = v___x_1258_;
goto v___jp_1250_;
}
else
{
v_pieces_1251_ = v_pieces_1256_;
goto v___jp_1250_;
}
}
}
else
{
lean_dec(v_snd_1229_);
lean_dec(v_fst_1227_);
return v___x_1248_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v___x_1212_);
v_content_1271_ = lean_ctor_get(v_x_1183_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_x_1183_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1273_ = v_x_1183_;
v_isShared_1274_ = v_isSharedCheck_1322_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_content_1271_);
lean_dec(v_x_1183_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1322_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 9);
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_content_1271_);
v___x_1276_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; lean_object* v_snd_1278_; lean_object* v_fst_1279_; lean_object* v_fst_1280_; lean_object* v_snd_1281_; lean_object* v_pieces_1283_; uint8_t v_inEmph_1291_; uint8_t v_inBold_1292_; uint8_t v_inLink_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1320_; 
v___x_1277_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1276_);
v_snd_1278_ = lean_ctor_get(v___x_1277_, 1);
lean_inc(v_snd_1278_);
v_fst_1279_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_fst_1279_);
lean_dec_ref(v___x_1277_);
v_fst_1280_ = lean_ctor_get(v_snd_1278_, 0);
lean_inc(v_fst_1280_);
v_snd_1281_ = lean_ctor_get(v_snd_1278_, 1);
lean_inc(v_snd_1281_);
lean_dec(v_snd_1278_);
v_inEmph_1291_ = lean_ctor_get_uint8(v_x_1182_, 0);
v_inBold_1292_ = lean_ctor_get_uint8(v_x_1182_, 1);
v_inLink_1293_ = lean_ctor_get_uint8(v_x_1182_, 2);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1295_ = v_x_1182_;
v_isShared_1296_ = v_isSharedCheck_1320_;
goto v_resetjp_1294_;
}
else
{
lean_dec(v_x_1182_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1320_;
goto v_resetjp_1294_;
}
v___jp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1284_ = lean_string_utf8_byte_size(v_snd_1281_);
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = lean_nat_dec_eq(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_mk_empty_array_with_capacity(v___x_1287_);
v___x_1289_ = lean_array_push(v___x_1288_, v_snd_1281_);
v___x_1290_ = lean_array_push(v_pieces_1283_, v___x_1289_);
v_pieces_1189_ = v___x_1290_;
goto v___jp_1188_;
}
else
{
lean_dec(v_snd_1281_);
v_pieces_1189_ = v_pieces_1283_;
goto v___jp_1188_;
}
}
v_resetjp_1294_:
{
uint8_t v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = 1;
if (v_isShared_1296_ == 0)
{
v___x_1299_ = v___x_1295_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 0, v_inEmph_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 2, v_inLink_1293_);
v___x_1299_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1300_; 
lean_ctor_set_uint8(v___x_1299_, 1, v___x_1297_);
v___x_1300_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1181_, v___x_1299_, v_fst_1280_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v_pieces_1303_; lean_object* v_pieces_1308_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1313_ = lean_string_utf8_byte_size(v_fst_1279_);
v___x_1314_ = lean_nat_dec_eq(v___x_1313_, v___x_1311_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1315_ = lean_unsigned_to_nat(1u);
v___x_1316_ = lean_mk_empty_array_with_capacity(v___x_1315_);
v___x_1317_ = lean_array_push(v___x_1316_, v_fst_1279_);
v___x_1318_ = lean_array_push(v___x_1312_, v___x_1317_);
v_pieces_1308_ = v___x_1318_;
goto v___jp_1307_;
}
else
{
lean_dec(v_fst_1279_);
v_pieces_1308_ = v___x_1312_;
goto v___jp_1307_;
}
v___jp_1302_:
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_array_push(v_pieces_1303_, v_a_1301_);
if (v_inBold_1292_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1306_ = lean_array_push(v___x_1304_, v___x_1305_);
v_pieces_1283_ = v___x_1306_;
goto v___jp_1282_;
}
else
{
v_pieces_1283_ = v___x_1304_;
goto v___jp_1282_;
}
}
v___jp_1307_:
{
if (v_inBold_1292_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1310_ = lean_array_push(v_pieces_1308_, v___x_1309_);
v_pieces_1303_ = v___x_1310_;
goto v___jp_1302_;
}
else
{
v_pieces_1303_ = v_pieces_1308_;
goto v___jp_1302_;
}
}
}
else
{
lean_dec(v_snd_1281_);
lean_dec(v_fst_1279_);
return v___x_1300_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec_ref(v___x_1212_);
lean_dec_ref(v_x_1182_);
lean_dec_ref(v_inst_1181_);
v_string_1323_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_string_1323_);
lean_dec_ref_known(v_x_1183_, 1);
v___x_1324_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1323_);
v___x_1325_ = lean_unsigned_to_nat(1u);
v___x_1326_ = lean_mk_empty_array_with_capacity(v___x_1325_);
v___x_1327_ = lean_array_push(v___x_1326_, v___x_1324_);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
return v___x_1328_;
}
case 4:
{
uint8_t v_mode_1329_; 
lean_dec_ref(v___x_1212_);
lean_dec_ref(v_x_1182_);
lean_dec_ref(v_inst_1181_);
v_mode_1329_ = lean_ctor_get_uint8(v_x_1183_, sizeof(void*)*1);
if (v_mode_1329_ == 0)
{
lean_object* v_string_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_string_1330_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_string_1330_);
lean_dec_ref_known(v_x_1183_, 1);
v___x_1331_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_1332_ = lean_string_append(v___x_1331_, v_string_1330_);
lean_dec_ref(v_string_1330_);
v___x_1333_ = lean_string_append(v___x_1332_, v___x_1331_);
v___x_1334_ = lean_unsigned_to_nat(1u);
v___x_1335_ = lean_mk_empty_array_with_capacity(v___x_1334_);
v___x_1336_ = lean_array_push(v___x_1335_, v___x_1333_);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
return v___x_1337_;
}
else
{
lean_object* v_string_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_string_1338_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_string_1338_);
lean_dec_ref_known(v_x_1183_, 1);
v___x_1339_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_1340_ = lean_string_append(v___x_1339_, v_string_1338_);
lean_dec_ref(v_string_1338_);
v___x_1341_ = lean_string_append(v___x_1340_, v___x_1339_);
v___x_1342_ = lean_unsigned_to_nat(1u);
v___x_1343_ = lean_mk_empty_array_with_capacity(v___x_1342_);
v___x_1344_ = lean_array_push(v___x_1343_, v___x_1341_);
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
return v___x_1345_;
}
}
case 5:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec_ref_known(v_x_1183_, 1);
lean_dec_ref(v___x_1212_);
lean_dec_ref(v_x_1182_);
lean_dec_ref(v_inst_1181_);
v___x_1346_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
case 6:
{
uint8_t v_inLink_1348_; 
v_inLink_1348_ = lean_ctor_get_uint8(v_x_1182_, 2);
if (v_inLink_1348_ == 0)
{
lean_object* v_content_1349_; lean_object* v_url_1350_; uint8_t v_inEmph_1351_; uint8_t v_inBold_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1381_; 
lean_dec_ref(v___x_1212_);
v_content_1349_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_content_1349_);
v_url_1350_ = lean_ctor_get(v_x_1183_, 1);
lean_inc_ref(v_url_1350_);
lean_dec_ref_known(v_x_1183_, 2);
v_inEmph_1351_ = lean_ctor_get_uint8(v_x_1182_, 0);
v_inBold_1352_ = lean_ctor_get_uint8(v_x_1182_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1354_ = v_x_1182_;
v_isShared_1355_ = v_isSharedCheck_1381_;
goto v_resetjp_1353_;
}
else
{
lean_dec(v_x_1182_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1381_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
uint8_t v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = 1;
if (v_isShared_1355_ == 0)
{
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1380_, 0, v_inEmph_1351_);
lean_ctor_set_uint8(v_reuseFailAlloc_1380_, 1, v_inBold_1352_);
v___x_1358_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_ctor_set_uint8(v___x_1358_, 2, v___x_1356_);
v___x_1359_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_content_1349_);
v___x_1360_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1181_, v___x_1358_, v___x_1359_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1379_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1379_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1379_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1365_ = lean_unsigned_to_nat(1u);
v___x_1366_ = lean_mk_empty_array_with_capacity(v___x_1365_);
v___x_1367_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1368_ = lean_string_append(v___x_1367_, v_url_1350_);
lean_dec_ref(v_url_1350_);
v___x_1369_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1370_ = lean_string_append(v___x_1368_, v___x_1369_);
v___x_1371_ = lean_array_push(v___x_1366_, v___x_1370_);
v___x_1372_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_1373_ = lean_array_push(v___x_1372_, v_a_1361_);
v___x_1374_ = lean_array_push(v___x_1373_, v___x_1371_);
v___x_1375_ = l_Lean_Doc_joinInlines(v___x_1374_);
lean_dec_ref(v___x_1374_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1375_);
v___x_1377_ = v___x_1363_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_dec_ref(v_url_1350_);
return v___x_1360_;
}
}
}
}
else
{
lean_object* v_content_1382_; lean_object* v___x_1383_; size_t v_sz_1384_; size_t v___x_1385_; lean_object* v___x_4875__overap_1386_; lean_object* v___x_1387_; 
v_content_1382_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_content_1382_);
lean_dec_ref_known(v_x_1183_, 2);
v___x_1383_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1383_, 0, v_inst_1181_);
lean_closure_set(v___x_1383_, 1, v_x_1182_);
v_sz_1384_ = lean_array_size(v_content_1382_);
v___x_1385_ = ((size_t)0ULL);
v___x_4875__overap_1386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1212_, v___x_1383_, v_sz_1384_, v___x_1385_, v_content_1382_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
v___x_1387_ = lean_apply_4(v___x_4875__overap_1386_, v_a_1184_, v_a_1185_, v_a_1186_, lean_box(0));
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1396_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1396_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1396_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1392_ = l_Lean_Doc_joinInlines(v_a_1388_);
lean_dec(v_a_1388_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1392_);
v___x_1394_ = v___x_1390_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_a_1397_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1387_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1387_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
case 7:
{
lean_object* v_name_1405_; lean_object* v_content_1406_; lean_object* v___x_1407_; size_t v_sz_1408_; size_t v___x_1409_; lean_object* v___x_4878__overap_1410_; lean_object* v___x_1411_; 
v_name_1405_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_name_1405_);
v_content_1406_ = lean_ctor_get(v_x_1183_, 1);
lean_inc_ref(v_content_1406_);
lean_dec_ref_known(v_x_1183_, 2);
v___x_1407_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1407_, 0, v_inst_1181_);
lean_closure_set(v___x_1407_, 1, v_x_1182_);
v_sz_1408_ = lean_array_size(v_content_1406_);
v___x_1409_ = ((size_t)0ULL);
v___x_4878__overap_1410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1212_, v___x_1407_, v_sz_1408_, v___x_1409_, v_content_1406_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
v___x_1411_ = lean_apply_4(v___x_4878__overap_1410_, v_a_1184_, v_a_1185_, v_a_1186_, lean_box(0));
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___x_1413_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_1414_ = l_Lean_Doc_joinInlines(v_a_1412_);
lean_dec(v_a_1412_);
v___x_1415_ = lean_array_to_list(v___x_1414_);
v___x_1416_ = l_String_intercalate(v___x_1413_, v___x_1415_);
lean_inc_ref(v_name_1405_);
v___x_1417_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_1405_, v___x_1416_, v_a_1184_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1431_; 
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v___x_1417_, 0);
lean_dec(v_unused_1432_);
v___x_1419_ = v___x_1417_;
v_isShared_1420_ = v_isSharedCheck_1431_;
goto v_resetjp_1418_;
}
else
{
lean_dec(v___x_1417_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1431_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1421_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_1422_ = lean_string_append(v___x_1421_, v_name_1405_);
lean_dec_ref(v_name_1405_);
v___x_1423_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_1424_ = lean_string_append(v___x_1422_, v___x_1423_);
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = lean_mk_empty_array_with_capacity(v___x_1425_);
v___x_1427_ = lean_array_push(v___x_1426_, v___x_1424_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1427_);
v___x_1429_ = v___x_1419_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v_name_1405_);
v_a_1433_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1417_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1417_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec_ref(v_name_1405_);
v_a_1441_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1411_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1411_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
case 8:
{
lean_object* v_alt_1449_; lean_object* v_url_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref(v___x_1212_);
lean_dec_ref(v_x_1182_);
lean_dec_ref(v_inst_1181_);
v_alt_1449_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_alt_1449_);
v_url_1450_ = lean_ctor_get(v_x_1183_, 1);
lean_inc_ref(v_url_1450_);
lean_dec_ref_known(v_x_1183_, 2);
v___x_1451_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_1452_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1449_);
lean_dec_ref(v_alt_1449_);
v___x_1453_ = lean_string_append(v___x_1451_, v___x_1452_);
lean_dec_ref(v___x_1452_);
v___x_1454_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1455_ = lean_string_append(v___x_1453_, v___x_1454_);
v___x_1456_ = lean_string_append(v___x_1455_, v_url_1450_);
lean_dec_ref(v_url_1450_);
v___x_1457_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1458_ = lean_string_append(v___x_1456_, v___x_1457_);
v___x_1459_ = lean_unsigned_to_nat(1u);
v___x_1460_ = lean_mk_empty_array_with_capacity(v___x_1459_);
v___x_1461_ = lean_array_push(v___x_1460_, v___x_1458_);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
case 9:
{
lean_object* v_content_1463_; lean_object* v___x_1464_; size_t v_sz_1465_; size_t v___x_1466_; lean_object* v___x_4881__overap_1467_; lean_object* v___x_1468_; 
v_content_1463_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_content_1463_);
lean_dec_ref_known(v_x_1183_, 1);
v___x_1464_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1464_, 0, v_inst_1181_);
lean_closure_set(v___x_1464_, 1, v_x_1182_);
v_sz_1465_ = lean_array_size(v_content_1463_);
v___x_1466_ = ((size_t)0ULL);
v___x_4881__overap_1467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1212_, v___x_1464_, v_sz_1465_, v___x_1466_, v_content_1463_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
v___x_1468_ = lean_apply_4(v___x_4881__overap_1467_, v_a_1184_, v_a_1185_, v_a_1186_, lean_box(0));
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1477_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = l_Lean_Doc_joinInlines(v_a_1469_);
lean_dec(v_a_1469_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1473_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
v_a_1478_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1468_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1468_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
default: 
{
lean_object* v_container_1486_; lean_object* v_content_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref(v___x_1212_);
v_container_1486_ = lean_ctor_get(v_x_1183_, 0);
lean_inc(v_container_1486_);
v_content_1487_ = lean_ctor_get(v_x_1183_, 1);
lean_inc_ref(v_content_1487_);
lean_dec_ref_known(v_x_1183_, 2);
lean_inc_ref(v_inst_1181_);
v___x_1488_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1488_, 0, v_inst_1181_);
lean_closure_set(v___x_1488_, 1, v_x_1182_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
v___x_1489_ = lean_apply_7(v_inst_1181_, v___x_1488_, v_container_1486_, v_content_1487_, v_a_1184_, v_a_1185_, v_a_1186_, lean_box(0));
return v___x_1489_;
}
}
v___jp_1188_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = l_Lean_Doc_joinInlines(v_pieces_1189_);
lean_dec_ref(v_pieces_1189_);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
v___jp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = l_Lean_Doc_joinInlines(v_pieces_1193_);
lean_dec_ref(v_pieces_1193_);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1490_, lean_object* v_inst_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1491_, v_x_1492_, v_x_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object* v_i_1499_, lean_object* v_inst_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(v_i_1499_, v_inst_1500_, v_x_1501_, v_x_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1515_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1508_, v___x_1514_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object* v_inst_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(v_inst_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1523_, lean_object* v_inst_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1531_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1524_, v___x_1530_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object* v_i_1532_, lean_object* v_inst_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(v_i_1532_, v_inst_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1541_, 0, lean_box(0));
lean_closure_set(v___x_1541_, 1, v_inst_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1542_, lean_object* v_inst_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1544_, 0, lean_box(0));
lean_closure_set(v___x_1544_, 1, v_inst_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(uint32_t v___x_1545_, lean_object* v_s_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_string_push(v_s_1546_, v___x_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object* v___x_1548_, lean_object* v_s_1549_){
_start:
{
uint32_t v___x_2723__boxed_1550_; lean_object* v_res_1551_; 
v___x_2723__boxed_1550_ = lean_unbox_uint32(v___x_1548_);
lean_dec(v___x_1548_);
v_res_1551_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v___x_2723__boxed_1550_, v_s_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed(lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v___x_1556_, lean_object* v_item_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(v_inst_1554_, v_inst_1555_, v___x_1556_, v_item_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
return v_res_1562_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___f_1565_; 
v___x_1564_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___f_1565_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1565_, 0, v___x_1564_);
return v___f_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1566_, lean_object* v_inst_1567_, lean_object* v___x_1568_, lean_object* v___x_1569_, lean_object* v_a_1570_, lean_object* v_x_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; size_t v_sz_1578_; size_t v___x_1579_; lean_object* v___x_2656__overap_1580_; lean_object* v___x_1581_; 
v___x_1577_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1577_, 0, v_inst_1566_);
lean_closure_set(v___x_1577_, 1, v_inst_1567_);
v_sz_1578_ = lean_array_size(v_a_1570_);
v___x_1579_ = ((size_t)0ULL);
v___x_2656__overap_1580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1568_, v___x_1577_, v_sz_1578_, v___x_1579_, v_a_1570_);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
lean_inc(v___y_1573_);
v___x_1581_ = lean_apply_4(v___x_2656__overap_1580_, v___y_1573_, v___y_1574_, v___y_1575_, lean_box(0));
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1610_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1610_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1610_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v_fst_1586_; lean_object* v_snd_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1609_; 
v_fst_1586_ = lean_ctor_get(v___y_1572_, 0);
v_snd_1587_ = lean_ctor_get(v___y_1572_, 1);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___y_1572_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1589_ = v___y_1572_;
v_isShared_1590_ = v_isSharedCheck_1609_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_snd_1587_);
lean_inc(v_fst_1586_);
lean_dec(v___y_1572_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1609_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___f_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
lean_inc(v_snd_1587_);
v___x_1591_ = l_Nat_reprFast(v_snd_1587_);
v___x_1592_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_1593_ = lean_string_append(v___x_1591_, v___x_1592_);
v___x_1594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_1595_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1);
v___x_1596_ = lean_string_utf8_byte_size(v___x_1593_);
v___x_1597_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1595_, v___x_1596_, v___x_1594_);
v___x_1598_ = l_Lean_Doc_joinBlocks(v_a_1582_);
lean_dec(v_a_1582_);
v___x_1599_ = l_Lean_Doc_prefixListLines(v___x_1593_, v___x_1597_, v___x_1598_);
v___x_1600_ = lean_array_push(v_fst_1586_, v___x_1599_);
v___x_1601_ = lean_nat_add(v_snd_1587_, v___x_1569_);
lean_dec(v_snd_1587_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 1, v___x_1601_);
lean_ctor_set(v___x_1589_, 0, v___x_1600_);
v___x_1603_ = v___x_1589_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1604_);
v___x_1606_ = v___x_1584_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v___y_1572_);
v_a_1611_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1581_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1581_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v___x_1621_, lean_object* v___x_1622_, lean_object* v_a_1623_, lean_object* v_x_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1619_, v_inst_1620_, v___x_1621_, v___x_1622_, v_a_1623_, v_x_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec(v___x_1622_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v___x_1638_, lean_object* v_item_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v_term_1645_; lean_object* v_desc_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1644_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_1645_ = lean_ctor_get(v_item_1639_, 0);
lean_inc_ref(v_term_1645_);
v_desc_1646_ = lean_ctor_get(v_item_1639_, 1);
lean_inc_ref(v_desc_1646_);
lean_dec_ref(v_item_1639_);
v___x_1647_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_term_1645_);
lean_inc_ref(v_inst_1636_);
v___x_1648_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1636_, v___x_1644_, v___x_1647_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; size_t v_sz_1651_; size_t v___x_1652_; lean_object* v___x_2692__overap_1653_; lean_object* v___x_1654_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1650_, 0, v_inst_1636_);
lean_closure_set(v___x_1650_, 1, v_inst_1637_);
v_sz_1651_ = lean_array_size(v_desc_1646_);
v___x_1652_ = ((size_t)0ULL);
lean_inc_ref(v_desc_1646_);
v___x_2692__overap_1653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1638_, v___x_1650_, v_sz_1651_, v___x_1652_, v_desc_1646_);
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
lean_inc(v___y_1640_);
v___x_1654_ = lean_apply_4(v___x_2692__overap_1653_, v___y_1640_, v___y_1641_, v___y_1642_, lean_box(0));
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1682_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1682_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1682_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___y_1660_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_mk_empty_array_with_capacity(v___x_1667_);
v___x_1669_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_1670_ = lean_unsigned_to_nat(2u);
v___x_1671_ = lean_mk_empty_array_with_capacity(v___x_1670_);
v___x_1672_ = lean_array_push(v___x_1671_, v_a_1649_);
v___x_1673_ = lean_array_push(v___x_1672_, v___x_1669_);
v___x_1674_ = l_Lean_Doc_joinInlines(v___x_1673_);
lean_dec_ref(v___x_1673_);
v___x_1675_ = lean_array_get_size(v_desc_1646_);
lean_dec_ref(v_desc_1646_);
v___x_1676_ = lean_nat_dec_le(v___x_1675_, v___x_1667_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_array_push(v___x_1668_, v___x_1674_);
v___x_1678_ = l_Array_append___redArg(v___x_1677_, v_a_1655_);
lean_dec(v_a_1655_);
v___x_1679_ = l_Lean_Doc_joinBlocks(v___x_1678_);
lean_dec_ref(v___x_1678_);
v___y_1660_ = v___x_1679_;
goto v___jp_1659_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec_ref(v___x_1668_);
v___x_1680_ = l_Lean_Doc_joinBlocks(v_a_1655_);
lean_dec(v_a_1655_);
v___x_1681_ = l_Array_append___redArg(v___x_1674_, v___x_1680_);
lean_dec_ref(v___x_1680_);
v___y_1660_ = v___x_1681_;
goto v___jp_1659_;
}
v___jp_1659_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1661_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1662_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1663_ = l_Lean_Doc_prefixListLines(v___x_1661_, v___x_1662_, v___y_1660_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1663_);
v___x_1665_ = v___x_1657_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec(v_a_1649_);
lean_dec_ref(v_desc_1646_);
v_a_1683_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1654_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1654_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_dec_ref(v_desc_1646_);
lean_dec_ref(v___x_1638_);
lean_dec_ref(v_inst_1637_);
lean_dec_ref(v_inst_1636_);
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v___x_1693_, lean_object* v_item_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1691_, v_inst_1692_, v___x_1693_, v_item_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_x_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v___x_1708_; lean_object* v_toApplicative_1709_; lean_object* v_toFunctor_1710_; lean_object* v_toSeq_1711_; lean_object* v_toSeqLeft_1712_; lean_object* v_toSeqRight_1713_; lean_object* v___f_1714_; lean_object* v___f_1715_; lean_object* v___f_1716_; lean_object* v___f_1717_; lean_object* v___x_1718_; lean_object* v___f_1719_; lean_object* v___f_1720_; lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1708_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1709_ = lean_ctor_get(v___x_1708_, 0);
v_toFunctor_1710_ = lean_ctor_get(v_toApplicative_1709_, 0);
v_toSeq_1711_ = lean_ctor_get(v_toApplicative_1709_, 2);
v_toSeqLeft_1712_ = lean_ctor_get(v_toApplicative_1709_, 3);
v_toSeqRight_1713_ = lean_ctor_get(v_toApplicative_1709_, 4);
v___f_1714_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1715_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1710_, 2);
v___f_1716_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1716_, 0, v_toFunctor_1710_);
v___f_1717_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1717_, 0, v_toFunctor_1710_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___f_1716_);
lean_ctor_set(v___x_1718_, 1, v___f_1717_);
lean_inc(v_toSeqRight_1713_);
v___f_1719_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1719_, 0, v_toSeqRight_1713_);
lean_inc(v_toSeqLeft_1712_);
v___f_1720_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1720_, 0, v_toSeqLeft_1712_);
lean_inc(v_toSeq_1711_);
v___f_1721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1721_, 0, v_toSeq_1711_);
v___x_1722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1718_);
lean_ctor_set(v___x_1722_, 1, v___f_1714_);
lean_ctor_set(v___x_1722_, 2, v___f_1721_);
lean_ctor_set(v___x_1722_, 3, v___f_1720_);
lean_ctor_set(v___x_1722_, 4, v___f_1719_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v___f_1715_);
v___x_1724_ = l_StateRefT_x27_instMonad___redArg(v___x_1723_);
switch(lean_obj_tag(v_x_1703_))
{
case 0:
{
lean_object* v_contents_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1734_; 
lean_dec_ref(v___x_1724_);
lean_dec_ref(v_inst_1702_);
v_contents_1725_ = lean_ctor_get(v_x_1703_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_x_1703_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1727_ = v_x_1703_;
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_contents_1725_);
lean_dec(v_x_1703_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 9);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_contents_1725_);
v___x_1731_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; 
v___x_1732_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1701_, v___x_1729_, v___x_1731_, v_a_1704_, v_a_1705_, v_a_1706_);
return v___x_1732_;
}
}
}
case 1:
{
lean_object* v_content_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1743_; 
lean_dec_ref(v___x_1724_);
lean_dec_ref(v_inst_1702_);
lean_dec_ref(v_inst_1701_);
v_content_1735_ = lean_ctor_get(v_x_1703_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_x_1703_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1737_ = v_x_1703_;
v_isShared_1738_ = v_isSharedCheck_1743_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_content_1735_);
lean_dec(v_x_1703_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1743_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_1735_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1739_);
v___x_1741_ = v___x_1737_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
case 2:
{
lean_object* v_items_1744_; lean_object* v___f_1745_; size_t v_sz_1746_; size_t v___x_1747_; lean_object* v___x_2592__overap_1748_; lean_object* v___x_1749_; 
v_items_1744_ = lean_ctor_get(v_x_1703_, 0);
lean_inc_ref(v_items_1744_);
lean_dec_ref_known(v_x_1703_, 1);
lean_inc_ref(v___x_1724_);
v___f_1745_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1745_, 0, v_inst_1701_);
lean_closure_set(v___f_1745_, 1, v_inst_1702_);
lean_closure_set(v___f_1745_, 2, v___x_1724_);
v_sz_1746_ = lean_array_size(v_items_1744_);
v___x_1747_ = ((size_t)0ULL);
v___x_2592__overap_1748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1724_, v___f_1745_, v_sz_1746_, v___x_1747_, v_items_1744_);
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
lean_inc(v_a_1704_);
v___x_1749_ = lean_apply_4(v___x_2592__overap_1748_, v_a_1704_, v_a_1705_, v_a_1706_, lean_box(0));
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1758_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1758_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1758_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1754_ = l_Lean_Doc_joinBlocks(v_a_1750_);
lean_dec(v_a_1750_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1754_);
v___x_1756_ = v___x_1752_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
v_a_1759_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1749_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1749_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
case 3:
{
lean_object* v_start_1767_; lean_object* v_items_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1804_; 
v_start_1767_ = lean_ctor_get(v_x_1703_, 0);
v_items_1768_ = lean_ctor_get(v_x_1703_, 1);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_x_1703_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1770_ = v_x_1703_;
v_isShared_1771_ = v_isSharedCheck_1804_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_items_1768_);
lean_inc(v_start_1767_);
lean_dec(v_x_1703_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1804_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_out_1772_; lean_object* v___x_1773_; lean_object* v___f_1774_; lean_object* v___y_1776_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v_out_1772_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1773_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_1724_);
v___f_1774_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1774_, 0, v_inst_1701_);
lean_closure_set(v___f_1774_, 1, v_inst_1702_);
lean_closure_set(v___f_1774_, 2, v___x_1724_);
lean_closure_set(v___f_1774_, 3, v___x_1773_);
v___x_1802_ = l_Int_toNat(v_start_1767_);
lean_dec(v_start_1767_);
v___x_1803_ = lean_nat_dec_le(v___x_1773_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_dec(v___x_1802_);
v___y_1776_ = v___x_1773_;
goto v___jp_1775_;
}
else
{
v___y_1776_ = v___x_1802_;
goto v___jp_1775_;
}
v___jp_1775_:
{
lean_object* v___x_1778_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 0);
lean_ctor_set(v___x_1770_, 1, v___y_1776_);
lean_ctor_set(v___x_1770_, 0, v_out_1772_);
v___x_1778_ = v___x_1770_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_out_1772_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v___y_1776_);
v___x_1778_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
size_t v_sz_1779_; size_t v___x_1780_; lean_object* v___x_2406__overap_1781_; lean_object* v___x_1782_; 
v_sz_1779_ = lean_array_size(v_items_1768_);
v___x_1780_ = ((size_t)0ULL);
v___x_2406__overap_1781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1724_, v_items_1768_, v___f_1774_, v_sz_1779_, v___x_1780_, v___x_1778_);
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
lean_inc(v_a_1704_);
v___x_1782_ = lean_apply_4(v___x_2406__overap_1781_, v_a_1704_, v_a_1705_, v_a_1706_, lean_box(0));
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1792_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1792_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1792_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v_fst_1787_; lean_object* v___x_1788_; lean_object* v___x_1790_; 
v_fst_1787_ = lean_ctor_get(v_a_1783_, 0);
lean_inc(v_fst_1787_);
lean_dec(v_a_1783_);
v___x_1788_ = l_Lean_Doc_joinBlocks(v_fst_1787_);
lean_dec(v_fst_1787_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1788_);
v___x_1790_ = v___x_1785_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v_a_1793_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1782_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1782_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_1805_; lean_object* v___f_1806_; size_t v_sz_1807_; size_t v___x_1808_; lean_object* v___x_2598__overap_1809_; lean_object* v___x_1810_; 
v_items_1805_ = lean_ctor_get(v_x_1703_, 0);
lean_inc_ref(v_items_1805_);
lean_dec_ref_known(v_x_1703_, 1);
lean_inc_ref(v___x_1724_);
v___f_1806_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 8, 3);
lean_closure_set(v___f_1806_, 0, v_inst_1701_);
lean_closure_set(v___f_1806_, 1, v_inst_1702_);
lean_closure_set(v___f_1806_, 2, v___x_1724_);
v_sz_1807_ = lean_array_size(v_items_1805_);
v___x_1808_ = ((size_t)0ULL);
v___x_2598__overap_1809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1724_, v___f_1806_, v_sz_1807_, v___x_1808_, v_items_1805_);
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
lean_inc(v_a_1704_);
v___x_1810_ = lean_apply_4(v___x_2598__overap_1809_, v_a_1704_, v_a_1705_, v_a_1706_, lean_box(0));
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1819_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = l_Lean_Doc_joinBlocks(v_a_1811_);
lean_dec(v_a_1811_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_a_1820_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1810_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1810_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
case 5:
{
lean_object* v_items_1828_; lean_object* v___x_1829_; size_t v_sz_1830_; size_t v___x_1831_; lean_object* v___x_2601__overap_1832_; lean_object* v___x_1833_; 
v_items_1828_ = lean_ctor_get(v_x_1703_, 0);
lean_inc_ref(v_items_1828_);
lean_dec_ref_known(v_x_1703_, 1);
v___x_1829_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1829_, 0, v_inst_1701_);
lean_closure_set(v___x_1829_, 1, v_inst_1702_);
v_sz_1830_ = lean_array_size(v_items_1828_);
v___x_1831_ = ((size_t)0ULL);
v___x_2601__overap_1832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1724_, v___x_1829_, v_sz_1830_, v___x_1831_, v_items_1828_);
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
lean_inc(v_a_1704_);
v___x_1833_ = lean_apply_4(v___x_2601__overap_1832_, v_a_1704_, v_a_1705_, v_a_1706_, lean_box(0));
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1844_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1844_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1844_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1838_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_1839_ = l_Lean_Doc_joinBlocks(v_a_1834_);
lean_dec(v_a_1834_);
v___x_1840_ = l_Lean_Doc_prefixLines(v___x_1838_, v___x_1839_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1840_);
v___x_1842_ = v___x_1836_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
v_a_1845_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1833_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1833_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
case 6:
{
lean_object* v_content_1853_; lean_object* v___x_1854_; size_t v_sz_1855_; size_t v___x_1856_; lean_object* v___x_2604__overap_1857_; lean_object* v___x_1858_; 
v_content_1853_ = lean_ctor_get(v_x_1703_, 0);
lean_inc_ref(v_content_1853_);
lean_dec_ref_known(v_x_1703_, 1);
v___x_1854_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1854_, 0, v_inst_1701_);
lean_closure_set(v___x_1854_, 1, v_inst_1702_);
v_sz_1855_ = lean_array_size(v_content_1853_);
v___x_1856_ = ((size_t)0ULL);
v___x_2604__overap_1857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1724_, v___x_1854_, v_sz_1855_, v___x_1856_, v_content_1853_);
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
lean_inc(v_a_1704_);
v___x_1858_ = lean_apply_4(v___x_2604__overap_1857_, v_a_1704_, v_a_1705_, v_a_1706_, lean_box(0));
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1867_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = l_Lean_Doc_joinBlocks(v_a_1859_);
lean_dec(v_a_1859_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1868_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1858_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1858_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
default: 
{
lean_object* v_container_1876_; lean_object* v_content_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_dec_ref(v___x_1724_);
v_container_1876_ = lean_ctor_get(v_x_1703_, 0);
lean_inc(v_container_1876_);
v_content_1877_ = lean_ctor_get(v_x_1703_, 1);
lean_inc_ref(v_content_1877_);
lean_dec_ref_known(v_x_1703_, 2);
v___x_1878_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc_ref(v_inst_1701_);
v___x_1879_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed), 8, 3);
lean_closure_set(v___x_1879_, 0, lean_box(0));
lean_closure_set(v___x_1879_, 1, v_inst_1701_);
lean_closure_set(v___x_1879_, 2, v___x_1878_);
lean_inc_ref(v_inst_1702_);
v___x_1880_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1880_, 0, v_inst_1701_);
lean_closure_set(v___x_1880_, 1, v_inst_1702_);
lean_inc(v_a_1706_);
lean_inc_ref(v_a_1705_);
lean_inc(v_a_1704_);
v___x_1881_ = lean_apply_8(v_inst_1702_, v___x_1879_, v___x_1880_, v_container_1876_, v_content_1877_, v_a_1704_, v_a_1705_, v_a_1706_, lean_box(0));
return v___x_1881_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed(lean_object* v_inst_1882_, lean_object* v_inst_1883_, lean_object* v_x_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1882_, v_inst_1883_, v_x_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v___x_1892_, lean_object* v_item_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; size_t v_sz_1899_; size_t v___x_1900_; lean_object* v___x_2631__overap_1901_; lean_object* v___x_1902_; 
v___x_1898_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1898_, 0, v_inst_1890_);
lean_closure_set(v___x_1898_, 1, v_inst_1891_);
v_sz_1899_ = lean_array_size(v_item_1893_);
v___x_1900_ = ((size_t)0ULL);
v___x_2631__overap_1901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1892_, v___x_1898_, v_sz_1899_, v___x_1900_, v_item_1893_);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
lean_inc(v___y_1894_);
v___x_1902_ = lean_apply_4(v___x_2631__overap_1901_, v___y_1894_, v___y_1895_, v___y_1896_, lean_box(0));
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1914_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1914_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1914_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1907_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1908_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1909_ = l_Lean_Doc_joinBlocks(v_a_1903_);
lean_dec(v_a_1903_);
v___x_1910_ = l_Lean_Doc_prefixListLines(v___x_1907_, v___x_1908_, v___x_1909_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1910_);
v___x_1912_ = v___x_1905_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1902_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1902_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1923_, lean_object* v_b_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_x_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1925_, v_inst_1926_, v_x_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object* v_i_1933_, lean_object* v_b_1934_, lean_object* v_inst_1935_, lean_object* v_inst_1936_, lean_object* v_x_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(v_i_1933_, v_b_1934_, v_inst_1935_, v_inst_1936_, v_x_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1943_, v_inst_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1951_, v_inst_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1959_, lean_object* v_b_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1961_, v_inst_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1969_, lean_object* v_b_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1969_, v_b_1970_, v_inst_1971_, v_inst_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1979_, lean_object* v_inst_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_1981_, 0, lean_box(0));
lean_closure_set(v___x_1981_, 1, lean_box(0));
lean_closure_set(v___x_1981_, 2, v_inst_1979_);
lean_closure_set(v___x_1981_, 3, v_inst_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1982_, lean_object* v_b_1983_, lean_object* v_inst_1984_, lean_object* v_inst_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_1986_, 0, lean_box(0));
lean_closure_set(v___x_1986_, 1, lean_box(0));
lean_closure_set(v___x_1986_, 2, v_inst_1984_);
lean_closure_set(v___x_1986_, 3, v_inst_1985_);
return v___x_1986_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = 35;
v___x_1988_ = lean_box_uint32(v___x_1987_);
return v___x_1988_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___f_1990_; 
v___x_1989_ = l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1990_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1990_, 0, v___x_1989_);
return v___f_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1991_, lean_object* v_inst_1992_, lean_object* v_level_1993_, lean_object* v_part_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_Doc_partMarkdown___redArg(v_inst_1991_, v_inst_1992_, v_level_1993_, v_part_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
lean_dec(v_a_1995_);
lean_dec(v_level_1993_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg(lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_level_2002_, lean_object* v_part_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___x_2008_; lean_object* v_toApplicative_2009_; lean_object* v_toFunctor_2010_; lean_object* v_toSeq_2011_; lean_object* v_toSeqLeft_2012_; lean_object* v_toSeqRight_2013_; lean_object* v___f_2014_; lean_object* v___f_2015_; lean_object* v___f_2016_; lean_object* v___f_2017_; lean_object* v___x_2018_; lean_object* v___f_2019_; lean_object* v___f_2020_; lean_object* v___f_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v_title_2025_; lean_object* v_content_2026_; lean_object* v_subParts_2027_; lean_object* v___x_2028_; size_t v_sz_2029_; size_t v___x_2030_; lean_object* v___x_680__overap_2031_; lean_object* v___x_2032_; 
v___x_2008_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2009_ = lean_ctor_get(v___x_2008_, 0);
v_toFunctor_2010_ = lean_ctor_get(v_toApplicative_2009_, 0);
v_toSeq_2011_ = lean_ctor_get(v_toApplicative_2009_, 2);
v_toSeqLeft_2012_ = lean_ctor_get(v_toApplicative_2009_, 3);
v_toSeqRight_2013_ = lean_ctor_get(v_toApplicative_2009_, 4);
v___f_2014_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2015_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2010_, 2);
v___f_2016_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2016_, 0, v_toFunctor_2010_);
v___f_2017_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2017_, 0, v_toFunctor_2010_);
v___x_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___f_2016_);
lean_ctor_set(v___x_2018_, 1, v___f_2017_);
lean_inc(v_toSeqRight_2013_);
v___f_2019_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2019_, 0, v_toSeqRight_2013_);
lean_inc(v_toSeqLeft_2012_);
v___f_2020_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2020_, 0, v_toSeqLeft_2012_);
lean_inc(v_toSeq_2011_);
v___f_2021_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2021_, 0, v_toSeq_2011_);
v___x_2022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2018_);
lean_ctor_set(v___x_2022_, 1, v___f_2014_);
lean_ctor_set(v___x_2022_, 2, v___f_2021_);
lean_ctor_set(v___x_2022_, 3, v___f_2020_);
lean_ctor_set(v___x_2022_, 4, v___f_2019_);
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v___f_2015_);
v___x_2024_ = l_StateRefT_x27_instMonad___redArg(v___x_2023_);
v_title_2025_ = lean_ctor_get(v_part_2003_, 0);
lean_inc_ref(v_title_2025_);
v_content_2026_ = lean_ctor_get(v_part_2003_, 3);
lean_inc_ref(v_content_2026_);
v_subParts_2027_ = lean_ctor_get(v_part_2003_, 4);
lean_inc_ref(v_subParts_2027_);
lean_dec_ref(v_part_2003_);
lean_inc_ref(v_inst_2000_);
v___x_2028_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_2028_, 0, lean_box(0));
lean_closure_set(v___x_2028_, 1, v_inst_2000_);
v_sz_2029_ = lean_array_size(v_title_2025_);
v___x_2030_ = ((size_t)0ULL);
lean_inc_ref(v___x_2024_);
v___x_680__overap_2031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2024_, v___x_2028_, v_sz_2029_, v___x_2030_, v_title_2025_);
lean_inc(v_a_2006_);
lean_inc_ref(v_a_2005_);
lean_inc(v_a_2004_);
v___x_2032_ = lean_apply_4(v___x_680__overap_2031_, v_a_2004_, v_a_2005_, v_a_2006_, lean_box(0));
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2034_; size_t v_sz_2035_; lean_object* v___x_683__overap_2036_; lean_object* v___x_2037_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
lean_inc_ref(v_inst_2001_);
lean_inc_ref(v_inst_2000_);
v___x_2034_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_2034_, 0, lean_box(0));
lean_closure_set(v___x_2034_, 1, lean_box(0));
lean_closure_set(v___x_2034_, 2, v_inst_2000_);
lean_closure_set(v___x_2034_, 3, v_inst_2001_);
v_sz_2035_ = lean_array_size(v_content_2026_);
lean_inc_ref(v___x_2024_);
v___x_683__overap_2036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2024_, v___x_2034_, v_sz_2035_, v___x_2030_, v_content_2026_);
lean_inc(v_a_2006_);
lean_inc_ref(v_a_2005_);
lean_inc(v_a_2004_);
v___x_2037_ = lean_apply_4(v___x_683__overap_2036_, v_a_2004_, v_a_2005_, v_a_2006_, lean_box(0));
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2039_; lean_object* v___f_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; size_t v_sz_2045_; lean_object* v___x_686__overap_2046_; lean_object* v___x_2047_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v___x_2039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_2040_ = lean_obj_once(&l_Lean_Doc_partMarkdown___redArg___closed__0, &l_Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_partMarkdown___redArg___closed__0);
v___x_2041_ = lean_unsigned_to_nat(1u);
v___x_2042_ = lean_nat_add(v_level_2002_, v___x_2041_);
lean_inc(v___x_2042_);
v___x_2043_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_2040_, v___x_2042_, v___x_2039_);
v___x_2044_ = lean_alloc_closure((void*)(l_Lean_Doc_partMarkdown___redArg___boxed), 8, 3);
lean_closure_set(v___x_2044_, 0, v_inst_2000_);
lean_closure_set(v___x_2044_, 1, v_inst_2001_);
lean_closure_set(v___x_2044_, 2, v___x_2042_);
v_sz_2045_ = lean_array_size(v_subParts_2027_);
v___x_686__overap_2046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2024_, v___x_2044_, v_sz_2045_, v___x_2030_, v_subParts_2027_);
lean_inc(v_a_2006_);
lean_inc_ref(v_a_2005_);
lean_inc(v_a_2004_);
v___x_2047_ = lean_apply_4(v___x_686__overap_2046_, v_a_2004_, v_a_2005_, v_a_2006_, lean_box(0));
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2066_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2066_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2066_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2052_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_2053_ = lean_string_append(v___x_2043_, v___x_2052_);
v___x_2054_ = lean_mk_empty_array_with_capacity(v___x_2041_);
lean_inc_ref_n(v___x_2054_, 2);
v___x_2055_ = lean_array_push(v___x_2054_, v___x_2053_);
v___x_2056_ = lean_array_push(v___x_2054_, v___x_2055_);
v___x_2057_ = l_Array_append___redArg(v___x_2056_, v_a_2033_);
lean_dec(v_a_2033_);
v___x_2058_ = l_Lean_Doc_joinInlines(v___x_2057_);
lean_dec_ref(v___x_2057_);
v___x_2059_ = lean_array_push(v___x_2054_, v___x_2058_);
v___x_2060_ = l_Array_append___redArg(v___x_2059_, v_a_2038_);
lean_dec(v_a_2038_);
v___x_2061_ = l_Array_append___redArg(v___x_2060_, v_a_2048_);
lean_dec(v_a_2048_);
v___x_2062_ = l_Lean_Doc_joinBlocks(v___x_2061_);
lean_dec_ref(v___x_2061_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v___x_2062_);
v___x_2064_ = v___x_2050_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v___x_2043_);
lean_dec(v_a_2038_);
lean_dec(v_a_2033_);
v_a_2067_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2047_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2047_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_a_2033_);
lean_dec_ref(v_subParts_2027_);
lean_dec_ref(v___x_2024_);
lean_dec_ref(v_inst_2001_);
lean_dec_ref(v_inst_2000_);
v_a_2075_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2037_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2037_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec_ref(v_subParts_2027_);
lean_dec_ref(v_content_2026_);
lean_dec_ref(v___x_2024_);
lean_dec_ref(v_inst_2001_);
lean_dec_ref(v_inst_2000_);
v_a_2083_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2032_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2032_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown(lean_object* v_i_2091_, lean_object* v_b_2092_, lean_object* v_p_2093_, lean_object* v_inst_2094_, lean_object* v_inst_2095_, lean_object* v_level_2096_, lean_object* v_part_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2094_, v_inst_2095_, v_level_2096_, v_part_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___boxed(lean_object* v_i_2103_, lean_object* v_b_2104_, lean_object* v_p_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_level_2108_, lean_object* v_part_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_Doc_partMarkdown(v_i_2103_, v_b_2104_, v_p_2105_, v_inst_2106_, v_inst_2107_, v_level_2108_, v_part_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
lean_dec(v_a_2112_);
lean_dec_ref(v_a_2111_);
lean_dec(v_a_2110_);
lean_dec(v_level_2108_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_part_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2115_, v_inst_2116_, v___x_2122_, v_part_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_2124_, lean_object* v_inst_2125_, lean_object* v_part_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_2124_, v_inst_2125_, v_part_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_2132_, lean_object* v_inst_2133_){
_start:
{
lean_object* v___f_2134_; 
v___f_2134_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2134_, 0, v_inst_2132_);
lean_closure_set(v___f_2134_, 1, v_inst_2133_);
return v___f_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_2135_, lean_object* v_b_2136_, lean_object* v_p_2137_, lean_object* v_inst_2138_, lean_object* v_inst_2139_){
_start:
{
lean_object* v___f_2140_; 
v___f_2140_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2140_, 0, v_inst_2138_);
lean_closure_set(v___f_2140_, 1, v_inst_2139_);
return v___f_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg(lean_object* v_inst_2141_, lean_object* v_f_2142_, lean_object* v_go_2143_, lean_object* v_val_2144_, lean_object* v_content_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v___x_2150_; lean_object* v_toApplicative_2151_; lean_object* v_toFunctor_2152_; lean_object* v_toSeq_2153_; lean_object* v_toSeqLeft_2154_; lean_object* v_toSeqRight_2155_; lean_object* v___f_2156_; lean_object* v___f_2157_; lean_object* v___f_2158_; lean_object* v___f_2159_; lean_object* v___x_2160_; lean_object* v___f_2161_; lean_object* v___f_2162_; lean_object* v___f_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2150_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2151_ = lean_ctor_get(v___x_2150_, 0);
v_toFunctor_2152_ = lean_ctor_get(v_toApplicative_2151_, 0);
v_toSeq_2153_ = lean_ctor_get(v_toApplicative_2151_, 2);
v_toSeqLeft_2154_ = lean_ctor_get(v_toApplicative_2151_, 3);
v_toSeqRight_2155_ = lean_ctor_get(v_toApplicative_2151_, 4);
v___f_2156_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2157_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2152_, 2);
v___f_2158_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2158_, 0, v_toFunctor_2152_);
v___f_2159_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2159_, 0, v_toFunctor_2152_);
v___x_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___f_2158_);
lean_ctor_set(v___x_2160_, 1, v___f_2159_);
lean_inc(v_toSeqRight_2155_);
v___f_2161_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2161_, 0, v_toSeqRight_2155_);
lean_inc(v_toSeqLeft_2154_);
v___f_2162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2162_, 0, v_toSeqLeft_2154_);
lean_inc(v_toSeq_2153_);
v___f_2163_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2163_, 0, v_toSeq_2153_);
v___x_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2160_);
lean_ctor_set(v___x_2164_, 1, v___f_2156_);
lean_ctor_set(v___x_2164_, 2, v___f_2163_);
lean_ctor_set(v___x_2164_, 3, v___f_2162_);
lean_ctor_set(v___x_2164_, 4, v___f_2161_);
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
lean_ctor_set(v___x_2165_, 1, v___f_2157_);
v___x_2166_ = l_StateRefT_x27_instMonad___redArg(v___x_2165_);
v___x_2167_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2144_, v_inst_2141_);
if (lean_obj_tag(v___x_2167_) == 0)
{
size_t v_sz_2168_; size_t v___x_2169_; lean_object* v___x_288__overap_2170_; lean_object* v___x_2171_; 
lean_dec_ref(v_f_2142_);
v_sz_2168_ = lean_array_size(v_content_2145_);
v___x_2169_ = ((size_t)0ULL);
v___x_288__overap_2170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2166_, v_go_2143_, v_sz_2168_, v___x_2169_, v_content_2145_);
lean_inc(v_a_2148_);
lean_inc_ref(v_a_2147_);
lean_inc(v_a_2146_);
v___x_2171_ = lean_apply_4(v___x_288__overap_2170_, v_a_2146_, v_a_2147_, v_a_2148_, lean_box(0));
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2180_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2180_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2180_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
v___x_2176_ = l_Lean_Doc_joinInlines(v_a_2172_);
lean_dec(v_a_2172_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2176_);
v___x_2178_ = v___x_2174_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
v_a_2181_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2171_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2171_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_val_2189_; lean_object* v___x_2190_; 
lean_dec_ref(v___x_2166_);
v_val_2189_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_val_2189_);
lean_dec_ref_known(v___x_2167_, 1);
lean_inc(v_a_2148_);
lean_inc_ref(v_a_2147_);
lean_inc(v_a_2146_);
v___x_2190_ = lean_apply_7(v_f_2142_, v_go_2143_, v_val_2189_, v_content_2145_, v_a_2146_, v_a_2147_, v_a_2148_, lean_box(0));
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg___boxed(lean_object* v_inst_2191_, lean_object* v_f_2192_, lean_object* v_go_2193_, lean_object* v_val_2194_, lean_object* v_content_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2191_, v_f_2192_, v_go_2193_, v_val_2194_, v_content_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec(v_val_2194_);
lean_dec(v_inst_2191_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer(lean_object* v_00_u03b1_2201_, lean_object* v_inst_2202_, lean_object* v_f_2203_, lean_object* v_go_2204_, lean_object* v_val_2205_, lean_object* v_content_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2202_, v_f_2203_, v_go_2204_, v_val_2205_, v_content_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___boxed(lean_object* v_00_u03b1_2212_, lean_object* v_inst_2213_, lean_object* v_f_2214_, lean_object* v_go_2215_, lean_object* v_val_2216_, lean_object* v_content_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Doc_mkInlineMdRenderer(v_00_u03b1_2212_, v_inst_2213_, v_f_2214_, v_go_2215_, v_val_2216_, v_content_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec(v_val_2216_);
lean_dec(v_inst_2213_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg(lean_object* v_inst_2223_, lean_object* v_f_2224_, lean_object* v_goI_2225_, lean_object* v_goB_2226_, lean_object* v_val_2227_, lean_object* v_content_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v___x_2233_; lean_object* v_toApplicative_2234_; lean_object* v_toFunctor_2235_; lean_object* v_toSeq_2236_; lean_object* v_toSeqLeft_2237_; lean_object* v_toSeqRight_2238_; lean_object* v___f_2239_; lean_object* v___f_2240_; lean_object* v___f_2241_; lean_object* v___f_2242_; lean_object* v___x_2243_; lean_object* v___f_2244_; lean_object* v___f_2245_; lean_object* v___f_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2233_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2234_ = lean_ctor_get(v___x_2233_, 0);
v_toFunctor_2235_ = lean_ctor_get(v_toApplicative_2234_, 0);
v_toSeq_2236_ = lean_ctor_get(v_toApplicative_2234_, 2);
v_toSeqLeft_2237_ = lean_ctor_get(v_toApplicative_2234_, 3);
v_toSeqRight_2238_ = lean_ctor_get(v_toApplicative_2234_, 4);
v___f_2239_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2240_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2235_, 2);
v___f_2241_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2241_, 0, v_toFunctor_2235_);
v___f_2242_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2242_, 0, v_toFunctor_2235_);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___f_2241_);
lean_ctor_set(v___x_2243_, 1, v___f_2242_);
lean_inc(v_toSeqRight_2238_);
v___f_2244_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2244_, 0, v_toSeqRight_2238_);
lean_inc(v_toSeqLeft_2237_);
v___f_2245_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2245_, 0, v_toSeqLeft_2237_);
lean_inc(v_toSeq_2236_);
v___f_2246_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2246_, 0, v_toSeq_2236_);
v___x_2247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2243_);
lean_ctor_set(v___x_2247_, 1, v___f_2239_);
lean_ctor_set(v___x_2247_, 2, v___f_2246_);
lean_ctor_set(v___x_2247_, 3, v___f_2245_);
lean_ctor_set(v___x_2247_, 4, v___f_2244_);
v___x_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v___f_2240_);
v___x_2249_ = l_StateRefT_x27_instMonad___redArg(v___x_2248_);
v___x_2250_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2227_, v_inst_2223_);
if (lean_obj_tag(v___x_2250_) == 0)
{
size_t v_sz_2251_; size_t v___x_2252_; lean_object* v___x_288__overap_2253_; lean_object* v___x_2254_; 
lean_dec_ref(v_goI_2225_);
lean_dec_ref(v_f_2224_);
v_sz_2251_ = lean_array_size(v_content_2228_);
v___x_2252_ = ((size_t)0ULL);
v___x_288__overap_2253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2249_, v_goB_2226_, v_sz_2251_, v___x_2252_, v_content_2228_);
lean_inc(v_a_2231_);
lean_inc_ref(v_a_2230_);
lean_inc(v_a_2229_);
v___x_2254_ = lean_apply_4(v___x_288__overap_2253_, v_a_2229_, v_a_2230_, v_a_2231_, lean_box(0));
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2263_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2263_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2263_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2259_ = l_Lean_Doc_joinBlocks(v_a_2255_);
lean_dec(v_a_2255_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v___x_2259_);
v___x_2261_ = v___x_2257_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
v_a_2264_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2254_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2254_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_object* v_val_2272_; lean_object* v___x_2273_; 
lean_dec_ref(v___x_2249_);
v_val_2272_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_val_2272_);
lean_dec_ref_known(v___x_2250_, 1);
lean_inc(v_a_2231_);
lean_inc_ref(v_a_2230_);
lean_inc(v_a_2229_);
v___x_2273_ = lean_apply_8(v_f_2224_, v_goI_2225_, v_goB_2226_, v_val_2272_, v_content_2228_, v_a_2229_, v_a_2230_, v_a_2231_, lean_box(0));
return v___x_2273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg___boxed(lean_object* v_inst_2274_, lean_object* v_f_2275_, lean_object* v_goI_2276_, lean_object* v_goB_2277_, lean_object* v_val_2278_, lean_object* v_content_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2274_, v_f_2275_, v_goI_2276_, v_goB_2277_, v_val_2278_, v_content_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
lean_dec(v_a_2280_);
lean_dec(v_val_2278_);
lean_dec(v_inst_2274_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer(lean_object* v_00_u03b1_2285_, lean_object* v_inst_2286_, lean_object* v_f_2287_, lean_object* v_goI_2288_, lean_object* v_goB_2289_, lean_object* v_val_2290_, lean_object* v_content_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2286_, v_f_2287_, v_goI_2288_, v_goB_2289_, v_val_2290_, v_content_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___boxed(lean_object* v_00_u03b1_2297_, lean_object* v_inst_2298_, lean_object* v_f_2299_, lean_object* v_goI_2300_, lean_object* v_goB_2301_, lean_object* v_val_2302_, lean_object* v_content_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_Doc_mkBlockMdRenderer(v_00_u03b1_2297_, v_inst_2298_, v_f_2299_, v_goI_2300_, v_goB_2301_, v_val_2302_, v_content_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
lean_dec(v_a_2304_);
lean_dec(v_val_2302_);
lean_dec(v_inst_2298_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(lean_object* v_as_2313_, size_t v_i_2314_, size_t v_stop_2315_, lean_object* v_b_2316_){
_start:
{
uint8_t v___x_2317_; 
v___x_2317_ = lean_usize_dec_eq(v_i_2314_, v_stop_2315_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; lean_object* v_fst_2319_; lean_object* v_snd_2320_; lean_object* v___x_2321_; size_t v___x_2322_; size_t v___x_2323_; 
v___x_2318_ = lean_array_uget_borrowed(v_as_2313_, v_i_2314_);
v_fst_2319_ = lean_ctor_get(v___x_2318_, 0);
v_snd_2320_ = lean_ctor_get(v___x_2318_, 1);
lean_inc(v_snd_2320_);
lean_inc(v_fst_2319_);
v___x_2321_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2319_, v_snd_2320_, v_b_2316_);
v___x_2322_ = ((size_t)1ULL);
v___x_2323_ = lean_usize_add(v_i_2314_, v___x_2322_);
v_i_2314_ = v___x_2323_;
v_b_2316_ = v___x_2321_;
goto _start;
}
else
{
return v_b_2316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0___boxed(lean_object* v_as_2325_, lean_object* v_i_2326_, lean_object* v_stop_2327_, lean_object* v_b_2328_){
_start:
{
size_t v_i_boxed_2329_; size_t v_stop_boxed_2330_; lean_object* v_res_2331_; 
v_i_boxed_2329_ = lean_unbox_usize(v_i_2326_);
lean_dec(v_i_2326_);
v_stop_boxed_2330_ = lean_unbox_usize(v_stop_2327_);
lean_dec(v_stop_2327_);
v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v_as_2325_, v_i_boxed_2329_, v_stop_boxed_2330_, v_b_2328_);
lean_dec_ref(v_as_2325_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(lean_object* v_as_2332_, size_t v_i_2333_, size_t v_stop_2334_, lean_object* v_b_2335_){
_start:
{
lean_object* v___y_2337_; uint8_t v___x_2341_; 
v___x_2341_ = lean_usize_dec_eq(v_i_2333_, v_stop_2334_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2342_ = lean_array_uget_borrowed(v_as_2332_, v_i_2333_);
v___x_2343_ = lean_unsigned_to_nat(0u);
v___x_2344_ = lean_array_get_size(v___x_2342_);
v___x_2345_ = lean_nat_dec_lt(v___x_2343_, v___x_2344_);
if (v___x_2345_ == 0)
{
v___y_2337_ = v_b_2335_;
goto v___jp_2336_;
}
else
{
uint8_t v___x_2346_; 
v___x_2346_ = lean_nat_dec_le(v___x_2344_, v___x_2344_);
if (v___x_2346_ == 0)
{
if (v___x_2345_ == 0)
{
v___y_2337_ = v_b_2335_;
goto v___jp_2336_;
}
else
{
size_t v___x_2347_; size_t v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = ((size_t)0ULL);
v___x_2348_ = lean_usize_of_nat(v___x_2344_);
v___x_2349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2342_, v___x_2347_, v___x_2348_, v_b_2335_);
v___y_2337_ = v___x_2349_;
goto v___jp_2336_;
}
}
else
{
size_t v___x_2350_; size_t v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = ((size_t)0ULL);
v___x_2351_ = lean_usize_of_nat(v___x_2344_);
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2342_, v___x_2350_, v___x_2351_, v_b_2335_);
v___y_2337_ = v___x_2352_;
goto v___jp_2336_;
}
}
}
else
{
return v_b_2335_;
}
v___jp_2336_:
{
size_t v___x_2338_; size_t v___x_2339_; 
v___x_2338_ = ((size_t)1ULL);
v___x_2339_ = lean_usize_add(v_i_2333_, v___x_2338_);
v_i_2333_ = v___x_2339_;
v_b_2335_ = v___y_2337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1___boxed(lean_object* v_as_2353_, lean_object* v_i_2354_, lean_object* v_stop_2355_, lean_object* v_b_2356_){
_start:
{
size_t v_i_boxed_2357_; size_t v_stop_boxed_2358_; lean_object* v_res_2359_; 
v_i_boxed_2357_ = lean_unbox_usize(v_i_2354_);
lean_dec(v_i_2354_);
v_stop_boxed_2358_ = lean_unbox_usize(v_stop_2355_);
lean_dec(v_stop_2355_);
v_res_2359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_as_2353_, v_i_boxed_2357_, v_stop_boxed_2358_, v_b_2356_);
lean_dec_ref(v_as_2353_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(lean_object* v_init_2360_, lean_object* v_es_2361_){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2362_ = lean_unsigned_to_nat(0u);
v___x_2363_ = lean_array_get_size(v_es_2361_);
v___x_2364_ = lean_nat_dec_lt(v___x_2362_, v___x_2363_);
if (v___x_2364_ == 0)
{
return v_init_2360_;
}
else
{
uint8_t v___x_2365_; 
v___x_2365_ = lean_nat_dec_le(v___x_2363_, v___x_2363_);
if (v___x_2365_ == 0)
{
if (v___x_2364_ == 0)
{
return v_init_2360_;
}
else
{
size_t v___x_2366_; size_t v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = ((size_t)0ULL);
v___x_2367_ = lean_usize_of_nat(v___x_2363_);
v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2361_, v___x_2366_, v___x_2367_, v_init_2360_);
return v___x_2368_;
}
}
else
{
size_t v___x_2369_; size_t v___x_2370_; lean_object* v___x_2371_; 
v___x_2369_ = ((size_t)0ULL);
v___x_2370_ = lean_usize_of_nat(v___x_2363_);
v___x_2371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2361_, v___x_2369_, v___x_2370_, v_init_2360_);
return v___x_2371_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries___boxed(lean_object* v_init_2372_, lean_object* v_es_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v_init_2372_, v_es_2373_);
lean_dec_ref(v_es_2373_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_2375_, lean_object* v_x_2376_){
_start:
{
if (lean_obj_tag(v_x_2376_) == 0)
{
lean_object* v_k_2377_; lean_object* v_v_2378_; lean_object* v_l_2379_; lean_object* v_r_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v_k_2377_ = lean_ctor_get(v_x_2376_, 1);
v_v_2378_ = lean_ctor_get(v_x_2376_, 2);
v_l_2379_ = lean_ctor_get(v_x_2376_, 3);
v_r_2380_ = lean_ctor_get(v_x_2376_, 4);
v___x_2381_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2375_, v_l_2379_);
lean_inc(v_v_2378_);
lean_inc(v_k_2377_);
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v_k_2377_);
lean_ctor_set(v___x_2382_, 1, v_v_2378_);
v___x_2383_ = lean_array_push(v___x_2381_, v___x_2382_);
v_init_2375_ = v___x_2383_;
v_x_2376_ = v_r_2380_;
goto _start;
}
else
{
return v_init_2375_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_2385_, lean_object* v_x_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2385_, v_x_2386_);
lean_dec(v_x_2386_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2390_){
_start:
{
lean_object* v_current_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_current_2391_ = lean_ctor_get(v_s_2390_, 1);
v___x_2392_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2393_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2392_, v_current_2391_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_s_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_s_2394_);
lean_dec_ref(v_s_2394_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_box(0);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2398_);
lean_dec_ref(v_x_2398_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2400_, lean_object* v_s_2401_){
_start:
{
lean_object* v_current_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_current_2402_ = lean_ctor_get(v_s_2401_, 1);
v___x_2403_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2404_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2403_, v_current_2402_);
lean_inc_ref_n(v___x_2404_, 2);
v___x_2405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
lean_ctor_set(v___x_2405_, 2, v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2406_, lean_object* v_s_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2406_, v_s_2407_);
lean_dec_ref(v_s_2407_);
lean_dec_ref(v_x_2406_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2409_, lean_object* v_x_2410_){
_start:
{
lean_object* v_fst_2411_; lean_object* v_snd_2412_; lean_object* v_imported_2413_; lean_object* v_current_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2422_; 
v_fst_2411_ = lean_ctor_get(v_x_2410_, 0);
lean_inc(v_fst_2411_);
v_snd_2412_ = lean_ctor_get(v_x_2410_, 1);
lean_inc(v_snd_2412_);
lean_dec_ref(v_x_2410_);
v_imported_2413_ = lean_ctor_get(v_s_2409_, 0);
v_current_2414_ = lean_ctor_get(v_s_2409_, 1);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_s_2409_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2416_ = v_s_2409_;
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_current_2414_);
lean_inc(v_imported_2413_);
lean_dec(v_s_2409_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2420_; 
v___x_2418_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2411_, v_snd_2412_, v_current_2414_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v___x_2418_);
v___x_2420_ = v___x_2416_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_imported_2413_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2423_, lean_object* v_es_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
lean_inc(v___x_2423_);
v___x_2427_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v___x_2423_, v_es_2424_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v___x_2423_);
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2430_, lean_object* v_es_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2430_, v_es_2431_, v___y_2432_);
lean_dec_ref(v___y_2432_);
lean_dec_ref(v_es_2431_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2435_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2438_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2470_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_();
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(lean_object* v_init_2473_, lean_object* v_t_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2473_, v_t_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_2476_, lean_object* v_t_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(v_init_2476_, v_t_2477_);
lean_dec(v_t_2477_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_));
v___x_2498_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2____boxed(lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_();
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = lean_box(1);
v___x_2503_ = lean_st_mk_ref(v___x_2502_);
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2____boxed(lean_object* v_a_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_();
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = lean_box(1);
v___x_2509_ = lean_st_mk_ref(v___x_2508_);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2____boxed(lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_();
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer(lean_object* v_type_2513_, lean_object* v_r_2514_){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2516_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2517_ = lean_st_ref_take(v___x_2516_);
v___x_2518_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2513_, v_r_2514_, v___x_2517_);
v___x_2519_ = lean_st_ref_set(v___x_2516_, v___x_2518_);
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer___boxed(lean_object* v_type_2521_, lean_object* v_r_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Doc_addBuiltinInlineMdRenderer(v_type_2521_, v_r_2522_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer(lean_object* v_type_2525_, lean_object* v_r_2526_){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2528_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2529_ = lean_st_ref_take(v___x_2528_);
v___x_2530_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2525_, v_r_2526_, v___x_2529_);
v___x_2531_ = lean_st_ref_set(v___x_2528_, v___x_2530_);
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer___boxed(lean_object* v_type_2533_, lean_object* v_r_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Doc_addBuiltinBlockMdRenderer(v_type_2533_, v_r_2534_);
return v_res_2536_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2537_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
return v___x_2539_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2541_ = lean_unsigned_to_nat(0u);
v___x_2542_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
lean_ctor_set(v___x_2542_, 2, v___x_2541_);
lean_ctor_set(v___x_2542_, 3, v___x_2541_);
lean_ctor_set(v___x_2542_, 4, v___x_2540_);
lean_ctor_set(v___x_2542_, 5, v___x_2540_);
lean_ctor_set(v___x_2542_, 6, v___x_2540_);
lean_ctor_set(v___x_2542_, 7, v___x_2540_);
lean_ctor_set(v___x_2542_, 8, v___x_2540_);
lean_ctor_set(v___x_2542_, 9, v___x_2540_);
return v___x_2542_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2543_ = lean_unsigned_to_nat(32u);
v___x_2544_ = lean_mk_empty_array_with_capacity(v___x_2543_);
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
return v___x_2545_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2546_ = ((size_t)5ULL);
v___x_2547_ = lean_unsigned_to_nat(0u);
v___x_2548_ = lean_unsigned_to_nat(32u);
v___x_2549_ = lean_mk_empty_array_with_capacity(v___x_2548_);
v___x_2550_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_2551_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
lean_ctor_set(v___x_2551_, 1, v___x_2549_);
lean_ctor_set(v___x_2551_, 2, v___x_2547_);
lean_ctor_set(v___x_2551_, 3, v___x_2547_);
lean_ctor_set_usize(v___x_2551_, 4, v___x_2546_);
return v___x_2551_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2552_ = lean_box(1);
v___x_2553_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_2554_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v___x_2553_);
lean_ctor_set(v___x_2555_, 2, v___x_2552_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; lean_object* v_env_2561_; lean_object* v_options_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2560_ = lean_st_ref_get(v___y_2558_);
v_env_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc_ref(v_env_2561_);
lean_dec(v___x_2560_);
v_options_2562_ = lean_ctor_get(v___y_2557_, 2);
v___x_2563_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_2564_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_2562_);
v___x_2565_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2565_, 0, v_env_2561_);
lean_ctor_set(v___x_2565_, 1, v___x_2563_);
lean_ctor_set(v___x_2565_, 2, v___x_2564_);
lean_ctor_set(v___x_2565_, 3, v_options_2562_);
v___x_2566_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v_msgData_2556_);
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_ref_2577_; lean_object* v___x_2578_; lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2587_; 
v_ref_2577_ = lean_ctor_get(v___y_2574_, 5);
v___x_2578_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_2573_, v___y_2574_, v___y_2575_);
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2587_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2587_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
lean_inc(v_ref_2577_);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v_ref_2577_);
lean_ctor_set(v___x_2583_, 1, v_a_2579_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 1);
lean_ctor_set(v___x_2581_, 0, v___x_2583_);
v___x_2585_ = v___x_2581_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(lean_object* v_x_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
if (lean_obj_tag(v_x_2593_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v_a_2597_ = lean_ctor_get(v_x_2593_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v_x_2593_, 1);
v___x_2598_ = l_Lean_stringToMessageData(v_a_2597_);
v___x_2599_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v___x_2598_, v___y_2594_, v___y_2595_);
return v___x_2599_;
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
v_a_2600_ = lean_ctor_get(v_x_2593_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_x_2593_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v_x_2593_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v_x_2593_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
lean_ctor_set_tag(v___x_2602_, 0);
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
return v_res_2612_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = lean_box(0);
v___x_2614_ = l_Lean_Elab_abortCommandExceptionId;
v___x_2615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
lean_ctor_set(v___x_2615_, 1, v___x_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(lean_object* v_constName_2621_, uint8_t v_checkMeta_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; lean_object* v_env_2627_; uint8_t v___x_2628_; 
v___x_2626_ = lean_st_ref_get(v___y_2624_);
v_env_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc_ref(v_env_2627_);
lean_dec(v___x_2626_);
lean_inc(v_constName_2621_);
v___x_2628_ = lean_has_compile_error(v_env_2627_, v_constName_2621_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v_env_2630_; lean_object* v_options_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2629_ = lean_st_ref_get(v___y_2624_);
v_env_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc_ref(v_env_2630_);
lean_dec(v___x_2629_);
v_options_2631_ = lean_ctor_get(v___y_2623_, 2);
v___x_2632_ = l_Lean_Environment_evalConst___redArg(v_env_2630_, v_options_2631_, v_constName_2621_, v_checkMeta_2622_);
lean_dec(v_constName_2621_);
lean_dec_ref(v_env_2630_);
v___x_2633_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2632_, v___y_2623_, v___y_2624_);
return v___x_2633_;
}
else
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v___x_2635_; lean_object* v_env_2636_; lean_object* v_options_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_dec_ref_known(v___x_2634_, 1);
v___x_2635_ = lean_st_ref_get(v___y_2624_);
v_env_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc_ref(v_env_2636_);
lean_dec(v___x_2635_);
v_options_2637_ = lean_ctor_get(v___y_2623_, 2);
v___x_2638_ = l_Lean_Environment_evalConst___redArg(v_env_2636_, v_options_2637_, v_constName_2621_, v_checkMeta_2622_);
lean_dec(v_constName_2621_);
lean_dec_ref(v_env_2636_);
v___x_2639_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2638_, v___y_2623_, v___y_2624_);
return v___x_2639_;
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec(v_constName_2621_);
v_a_2640_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2634_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2634_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg___boxed(lean_object* v_constName_2648_, lean_object* v_checkMeta_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
uint8_t v_checkMeta_boxed_2653_; lean_object* v_res_2654_; 
v_checkMeta_boxed_2653_ = lean_unbox(v_checkMeta_2649_);
v_res_2654_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2648_, v_checkMeta_boxed_2653_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(lean_object* v_type_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v___x_2659_; lean_object* v___y_2661_; lean_object* v_env_2692_; lean_object* v___x_2693_; lean_object* v_toEnvExtension_2694_; lean_object* v_asyncMode_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v_imported_2699_; lean_object* v_current_2700_; lean_object* v___x_2701_; 
v___x_2659_ = lean_st_ref_get(v_a_2657_);
v_env_2692_ = lean_ctor_get(v___x_2659_, 0);
lean_inc_ref(v_env_2692_);
lean_dec(v___x_2659_);
v___x_2693_ = l_Lean_Doc_docInlineMdExt;
v_toEnvExtension_2694_ = lean_ctor_get(v___x_2693_, 0);
v_asyncMode_2695_ = lean_ctor_get(v_toEnvExtension_2694_, 2);
v___x_2696_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2697_ = lean_box(0);
v___x_2698_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2696_, v___x_2693_, v_env_2692_, v_asyncMode_2695_, v___x_2697_);
v_imported_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_imported_2699_);
v_current_2700_ = lean_ctor_get(v___x_2698_, 1);
lean_inc(v_current_2700_);
lean_dec(v___x_2698_);
v___x_2701_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2700_, v_type_2655_);
lean_dec(v_current_2700_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2699_, v_type_2655_);
lean_dec(v_imported_2699_);
v___y_2661_ = v___x_2702_;
goto v___jp_2660_;
}
else
{
lean_dec(v_imported_2699_);
v___y_2661_ = v___x_2701_;
goto v___jp_2660_;
}
v___jp_2660_:
{
if (lean_obj_tag(v___y_2661_) == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2662_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2663_ = lean_st_ref_get(v___x_2662_);
v___x_2664_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2663_, v_type_2655_);
lean_dec(v___x_2663_);
v___x_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
return v___x_2665_;
}
else
{
lean_object* v_val_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2691_; 
v_val_2666_ = lean_ctor_get(v___y_2661_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___y_2661_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2668_ = v___y_2661_;
v_isShared_2669_ = v_isSharedCheck_2691_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_val_2666_);
lean_dec(v___y_2661_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2691_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
uint8_t v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = 1;
v___x_2671_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2666_, v___x_2670_, v_a_2656_, v_a_2657_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2682_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2682_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2682_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v_a_2672_);
v___x_2677_ = v___x_2668_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2679_; 
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2677_);
v___x_2679_ = v___x_2674_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_del_object(v___x_2668_);
v_a_2683_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2671_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2671_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe___boxed(lean_object* v_type_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v_type_2703_, v_a_2704_, v_a_2705_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
lean_dec(v_type_2703_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(v_00_u03b1_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(lean_object* v_00_u03b1_2718_, lean_object* v_constName_2719_, uint8_t v_checkMeta_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2719_, v_checkMeta_2720_, v___y_2721_, v___y_2722_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___boxed(lean_object* v_00_u03b1_2725_, lean_object* v_constName_2726_, lean_object* v_checkMeta_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
uint8_t v_checkMeta_boxed_2731_; lean_object* v_res_2732_; 
v_checkMeta_boxed_2731_ = lean_unbox(v_checkMeta_2727_);
v_res_2732_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(v_00_u03b1_2725_, v_constName_2726_, v_checkMeta_boxed_2731_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_2733_, lean_object* v_x_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2734_, v___y_2735_, v___y_2736_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2739_, lean_object* v_x_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(v_00_u03b1_2739_, v_x_2740_, v___y_2741_, v___y_2742_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2745_, lean_object* v_msg_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2746_, v___y_2747_, v___y_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2751_, lean_object* v_msg_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_2751_, v_msg_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(lean_object* v_typeName_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v___x_2761_; lean_object* v___y_2763_; lean_object* v_env_2794_; lean_object* v___x_2795_; lean_object* v_toEnvExtension_2796_; lean_object* v_asyncMode_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v_imported_2801_; lean_object* v_current_2802_; lean_object* v___x_2803_; 
v___x_2761_ = lean_st_ref_get(v_a_2759_);
v_env_2794_ = lean_ctor_get(v___x_2761_, 0);
lean_inc_ref(v_env_2794_);
lean_dec(v___x_2761_);
v___x_2795_ = l_Lean_Doc_docBlockMdExt;
v_toEnvExtension_2796_ = lean_ctor_get(v___x_2795_, 0);
v_asyncMode_2797_ = lean_ctor_get(v_toEnvExtension_2796_, 2);
v___x_2798_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2799_ = lean_box(0);
v___x_2800_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2798_, v___x_2795_, v_env_2794_, v_asyncMode_2797_, v___x_2799_);
v_imported_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_imported_2801_);
v_current_2802_ = lean_ctor_get(v___x_2800_, 1);
lean_inc(v_current_2802_);
lean_dec(v___x_2800_);
v___x_2803_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2802_, v_typeName_2757_);
lean_dec(v_current_2802_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v___x_2804_; 
v___x_2804_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2801_, v_typeName_2757_);
lean_dec(v_imported_2801_);
v___y_2763_ = v___x_2804_;
goto v___jp_2762_;
}
else
{
lean_dec(v_imported_2801_);
v___y_2763_ = v___x_2803_;
goto v___jp_2762_;
}
v___jp_2762_:
{
if (lean_obj_tag(v___y_2763_) == 0)
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2764_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2765_ = lean_st_ref_get(v___x_2764_);
v___x_2766_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2765_, v_typeName_2757_);
lean_dec(v___x_2765_);
v___x_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
return v___x_2767_;
}
else
{
lean_object* v_val_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2793_; 
v_val_2768_ = lean_ctor_get(v___y_2763_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___y_2763_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2770_ = v___y_2763_;
v_isShared_2771_ = v_isSharedCheck_2793_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_val_2768_);
lean_dec(v___y_2763_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2793_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
uint8_t v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = 1;
v___x_2773_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2768_, v___x_2772_, v_a_2758_, v_a_2759_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2784_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2784_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2784_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v_a_2774_);
v___x_2779_ = v___x_2770_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2781_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v___x_2779_);
v___x_2781_ = v___x_2776_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_del_object(v___x_2770_);
v_a_2785_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2773_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2773_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe___boxed(lean_object* v_typeName_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v_typeName_2805_, v_a_2806_, v_a_2807_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_typeName_2805_);
return v_res_2809_;
}
}
static lean_object* _init_l_Lean_Doc_mdRendererHeartbeats(void){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_unsigned_to_nat(200000u);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg(lean_object* v_x_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v___x_2816_; lean_object* v_fileName_2817_; lean_object* v_fileMap_2818_; lean_object* v_options_2819_; lean_object* v_currRecDepth_2820_; lean_object* v_maxRecDepth_2821_; lean_object* v_ref_2822_; lean_object* v_currNamespace_2823_; lean_object* v_openDecls_2824_; lean_object* v_quotContext_2825_; lean_object* v_currMacroScope_2826_; uint8_t v_diag_2827_; lean_object* v_cancelTk_x3f_2828_; uint8_t v_suppressElabErrors_2829_; lean_object* v_inheritedTraceOptions_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2816_ = lean_io_get_num_heartbeats();
v_fileName_2817_ = lean_ctor_get(v_a_2813_, 0);
v_fileMap_2818_ = lean_ctor_get(v_a_2813_, 1);
v_options_2819_ = lean_ctor_get(v_a_2813_, 2);
v_currRecDepth_2820_ = lean_ctor_get(v_a_2813_, 3);
v_maxRecDepth_2821_ = lean_ctor_get(v_a_2813_, 4);
v_ref_2822_ = lean_ctor_get(v_a_2813_, 5);
v_currNamespace_2823_ = lean_ctor_get(v_a_2813_, 6);
v_openDecls_2824_ = lean_ctor_get(v_a_2813_, 7);
v_quotContext_2825_ = lean_ctor_get(v_a_2813_, 10);
v_currMacroScope_2826_ = lean_ctor_get(v_a_2813_, 11);
v_diag_2827_ = lean_ctor_get_uint8(v_a_2813_, sizeof(void*)*14);
v_cancelTk_x3f_2828_ = lean_ctor_get(v_a_2813_, 12);
v_suppressElabErrors_2829_ = lean_ctor_get_uint8(v_a_2813_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2830_ = lean_ctor_get(v_a_2813_, 13);
v___x_2831_ = lean_unsigned_to_nat(200000u);
lean_inc_ref(v_inheritedTraceOptions_2830_);
lean_inc(v_cancelTk_x3f_2828_);
lean_inc(v_currMacroScope_2826_);
lean_inc(v_quotContext_2825_);
lean_inc(v_openDecls_2824_);
lean_inc(v_currNamespace_2823_);
lean_inc(v_ref_2822_);
lean_inc(v_maxRecDepth_2821_);
lean_inc(v_currRecDepth_2820_);
lean_inc_ref(v_options_2819_);
lean_inc_ref(v_fileMap_2818_);
lean_inc_ref(v_fileName_2817_);
v___x_2832_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2832_, 0, v_fileName_2817_);
lean_ctor_set(v___x_2832_, 1, v_fileMap_2818_);
lean_ctor_set(v___x_2832_, 2, v_options_2819_);
lean_ctor_set(v___x_2832_, 3, v_currRecDepth_2820_);
lean_ctor_set(v___x_2832_, 4, v_maxRecDepth_2821_);
lean_ctor_set(v___x_2832_, 5, v_ref_2822_);
lean_ctor_set(v___x_2832_, 6, v_currNamespace_2823_);
lean_ctor_set(v___x_2832_, 7, v_openDecls_2824_);
lean_ctor_set(v___x_2832_, 8, v___x_2816_);
lean_ctor_set(v___x_2832_, 9, v___x_2831_);
lean_ctor_set(v___x_2832_, 10, v_quotContext_2825_);
lean_ctor_set(v___x_2832_, 11, v_currMacroScope_2826_);
lean_ctor_set(v___x_2832_, 12, v_cancelTk_x3f_2828_);
lean_ctor_set(v___x_2832_, 13, v_inheritedTraceOptions_2830_);
lean_ctor_set_uint8(v___x_2832_, sizeof(void*)*14, v_diag_2827_);
lean_ctor_set_uint8(v___x_2832_, sizeof(void*)*14 + 1, v_suppressElabErrors_2829_);
lean_inc(v_a_2814_);
lean_inc(v_a_2812_);
v___x_2833_ = lean_apply_4(v_x_2811_, v_a_2812_, v___x_2832_, v_a_2814_, lean_box(0));
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg___boxed(lean_object* v_x_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget(lean_object* v_00_u03b1_2840_, lean_object* v_x_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___boxed(lean_object* v_00_u03b1_2847_, lean_object* v_x_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_Doc_withMdRendererBudget(v_00_u03b1_2847_, v_x_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback(lean_object* v_fallback_2854_, lean_object* v_act_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_st_ref_get(v_a_2856_);
v___x_2861_ = l_Lean_Doc_withMdRendererBudget___redArg(v_act_2855_, v_a_2856_, v_a_2857_, v_a_2858_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_dec(v___x_2860_);
lean_dec_ref(v_fallback_2854_);
return v___x_2861_;
}
else
{
lean_object* v_a_2862_; uint8_t v___x_2863_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
v___x_2863_ = l_Lean_Exception_isInterrupt(v_a_2862_);
lean_dec(v_a_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec_ref_known(v___x_2861_, 1);
v___x_2864_ = lean_st_ref_set(v_a_2856_, v___x_2860_);
lean_inc(v_a_2858_);
lean_inc_ref(v_a_2857_);
lean_inc(v_a_2856_);
v___x_2865_ = lean_apply_4(v_fallback_2854_, v_a_2856_, v_a_2857_, v_a_2858_, lean_box(0));
return v___x_2865_;
}
else
{
lean_dec(v___x_2860_);
lean_dec_ref(v_fallback_2854_);
return v___x_2861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback___boxed(lean_object* v_fallback_2866_, lean_object* v_act_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_Doc_withRendererFallback(v_fallback_2866_, v_act_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0(lean_object* v_____do__lift_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = l_Lean_Doc_joinInlines(v_____do__lift_2873_);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0___boxed(lean_object* v_____do__lift_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__0(v_____do__lift_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v_____do__lift_2880_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1(lean_object* v___x_2886_, lean_object* v___f_2887_, lean_object* v___x_2888_, lean_object* v_go_2889_, lean_object* v_container_2890_, lean_object* v_content_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
if (lean_obj_tag(v_container_2890_) == 0)
{
lean_object* v_val_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v_val_2896_ = lean_ctor_get(v_container_2890_, 0);
lean_inc(v_val_2896_);
lean_dec_ref_known(v_container_2890_, 1);
v___x_2897_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2896_);
v___x_2898_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_2897_, v___y_2893_, v___y_2894_);
lean_dec(v___x_2897_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2898_, 1);
if (lean_obj_tag(v_a_2899_) == 0)
{
size_t v_sz_2900_; size_t v___x_2901_; lean_object* v___x_541__overap_2902_; lean_object* v___x_2903_; 
lean_dec(v_val_2896_);
lean_dec_ref(v___x_2888_);
v_sz_2900_ = lean_array_size(v_content_2891_);
v___x_2901_ = ((size_t)0ULL);
v___x_541__overap_2902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2886_, v_go_2889_, v_sz_2900_, v___x_2901_, v_content_2891_);
lean_inc(v___y_2894_);
lean_inc_ref(v___y_2893_);
lean_inc(v___y_2892_);
v___x_2903_ = lean_apply_4(v___x_541__overap_2902_, v___y_2892_, v___y_2893_, v___y_2894_, lean_box(0));
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
lean_inc(v___y_2894_);
lean_inc_ref(v___y_2893_);
lean_inc(v___y_2892_);
v___x_2905_ = lean_apply_5(v___f_2887_, v_a_2904_, v___y_2892_, v___y_2893_, v___y_2894_, lean_box(0));
return v___x_2905_;
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref(v___f_2887_);
v_a_2906_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2903_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2903_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_val_2914_; size_t v_sz_2915_; size_t v___x_2916_; lean_object* v___x_2917_; lean_object* v_fallback_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_val_2914_ = lean_ctor_get(v_a_2899_, 0);
lean_inc(v_val_2914_);
lean_dec_ref_known(v_a_2899_, 1);
v_sz_2915_ = lean_array_size(v_content_2891_);
v___x_2916_ = ((size_t)0ULL);
lean_inc_ref(v_content_2891_);
lean_inc_ref(v_go_2889_);
v___x_2917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2886_, v_go_2889_, v_sz_2915_, v___x_2916_, v_content_2891_);
v_fallback_2918_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_2918_, 0, lean_box(0));
lean_closure_set(v_fallback_2918_, 1, lean_box(0));
lean_closure_set(v_fallback_2918_, 2, v___x_2888_);
lean_closure_set(v_fallback_2918_, 3, lean_box(0));
lean_closure_set(v_fallback_2918_, 4, lean_box(0));
lean_closure_set(v_fallback_2918_, 5, v___x_2917_);
lean_closure_set(v_fallback_2918_, 6, v___f_2887_);
v___x_2919_ = lean_apply_3(v_val_2914_, v_go_2889_, v_val_2896_, v_content_2891_);
v___x_2920_ = l_Lean_Doc_withRendererFallback(v_fallback_2918_, v___x_2919_, v___y_2892_, v___y_2893_, v___y_2894_);
return v___x_2920_;
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec(v_val_2896_);
lean_dec_ref(v_content_2891_);
lean_dec_ref(v_go_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___f_2887_);
lean_dec_ref(v___x_2886_);
v_a_2921_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2898_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2898_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
else
{
size_t v_sz_2929_; size_t v___x_2930_; lean_object* v___x_558__overap_2931_; lean_object* v___x_2932_; 
lean_dec_ref_known(v_container_2890_, 1);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___f_2887_);
v_sz_2929_ = lean_array_size(v_content_2891_);
v___x_2930_ = ((size_t)0ULL);
v___x_558__overap_2931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2886_, v_go_2889_, v_sz_2929_, v___x_2930_, v_content_2891_);
lean_inc(v___y_2894_);
lean_inc_ref(v___y_2893_);
lean_inc(v___y_2892_);
v___x_2932_ = lean_apply_4(v___x_558__overap_2931_, v___y_2892_, v___y_2893_, v___y_2894_, lean_box(0));
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2941_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_2941_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2941_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2937_ = l_Lean_Doc_joinInlines(v_a_2933_);
lean_dec(v_a_2933_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 0, v___x_2937_);
v___x_2939_ = v___x_2935_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
v_a_2942_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2932_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2932_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed(lean_object* v___x_2950_, lean_object* v___f_2951_, lean_object* v___x_2952_, lean_object* v_go_2953_, lean_object* v_container_2954_, lean_object* v_content_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__1(v___x_2950_, v___f_2951_, v___x_2952_, v_go_2953_, v_container_2954_, v_content_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
return v_res_2960_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownInlineElabInline(void){
_start:
{
lean_object* v___x_2962_; lean_object* v_toApplicative_2963_; lean_object* v_toFunctor_2964_; lean_object* v_toSeq_2965_; lean_object* v_toSeqLeft_2966_; lean_object* v_toSeqRight_2967_; lean_object* v___f_2968_; lean_object* v___f_2969_; lean_object* v___f_2970_; lean_object* v___f_2971_; lean_object* v___f_2972_; lean_object* v___x_2973_; lean_object* v___f_2974_; lean_object* v___f_2975_; lean_object* v___f_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___f_2980_; 
v___x_2962_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2963_ = lean_ctor_get(v___x_2962_, 0);
v_toFunctor_2964_ = lean_ctor_get(v_toApplicative_2963_, 0);
v_toSeq_2965_ = lean_ctor_get(v_toApplicative_2963_, 2);
v_toSeqLeft_2966_ = lean_ctor_get(v_toApplicative_2963_, 3);
v_toSeqRight_2967_ = lean_ctor_get(v_toApplicative_2963_, 4);
v___f_2968_ = ((lean_object*)(l_Lean_Doc_instMarkdownInlineElabInline___closed__0));
v___f_2969_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2970_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2964_, 2);
v___f_2971_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2971_, 0, v_toFunctor_2964_);
v___f_2972_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2972_, 0, v_toFunctor_2964_);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___f_2971_);
lean_ctor_set(v___x_2973_, 1, v___f_2972_);
lean_inc(v_toSeqRight_2967_);
v___f_2974_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2974_, 0, v_toSeqRight_2967_);
lean_inc(v_toSeqLeft_2966_);
v___f_2975_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2975_, 0, v_toSeqLeft_2966_);
lean_inc(v_toSeq_2965_);
v___f_2976_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2976_, 0, v_toSeq_2965_);
v___x_2977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2973_);
lean_ctor_set(v___x_2977_, 1, v___f_2969_);
lean_ctor_set(v___x_2977_, 2, v___f_2976_);
lean_ctor_set(v___x_2977_, 3, v___f_2975_);
lean_ctor_set(v___x_2977_, 4, v___f_2974_);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
lean_ctor_set(v___x_2978_, 1, v___f_2970_);
lean_inc_ref(v___x_2978_);
v___x_2979_ = l_StateRefT_x27_instMonad___redArg(v___x_2978_);
v___f_2980_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2980_, 0, v___x_2979_);
lean_closure_set(v___f_2980_, 1, v___f_2968_);
lean_closure_set(v___f_2980_, 2, v___x_2978_);
return v___f_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v_____do__lift_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = l_Lean_Doc_joinBlocks(v_____do__lift_2981_);
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object* v_____do__lift_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(v_____do__lift_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v_____do__lift_2988_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object* v___x_2994_, lean_object* v___f_2995_, lean_object* v___x_2996_, lean_object* v_goI_2997_, lean_object* v_goB_2998_, lean_object* v_container_2999_, lean_object* v_content_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
if (lean_obj_tag(v_container_2999_) == 0)
{
lean_object* v_val_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_val_3005_ = lean_ctor_get(v_container_2999_, 0);
lean_inc(v_val_3005_);
lean_dec_ref_known(v_container_2999_, 1);
v___x_3006_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3005_);
v___x_3007_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_3006_, v___y_3002_, v___y_3003_);
lean_dec(v___x_3006_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref_known(v___x_3007_, 1);
if (lean_obj_tag(v_a_3008_) == 0)
{
size_t v_sz_3009_; size_t v___x_3010_; lean_object* v___x_541__overap_3011_; lean_object* v___x_3012_; 
lean_dec(v_val_3005_);
lean_dec_ref(v_goI_2997_);
lean_dec_ref(v___x_2996_);
v_sz_3009_ = lean_array_size(v_content_3000_);
v___x_3010_ = ((size_t)0ULL);
v___x_541__overap_3011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2994_, v_goB_2998_, v_sz_3009_, v___x_3010_, v_content_3000_);
lean_inc(v___y_3003_);
lean_inc_ref(v___y_3002_);
lean_inc(v___y_3001_);
v___x_3012_ = lean_apply_4(v___x_541__overap_3011_, v___y_3001_, v___y_3002_, v___y_3003_, lean_box(0));
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
lean_inc(v___y_3003_);
lean_inc_ref(v___y_3002_);
lean_inc(v___y_3001_);
v___x_3014_ = lean_apply_5(v___f_2995_, v_a_3013_, v___y_3001_, v___y_3002_, v___y_3003_, lean_box(0));
return v___x_3014_;
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v___f_2995_);
v_a_3015_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3012_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3012_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
else
{
lean_object* v_val_3023_; size_t v_sz_3024_; size_t v___x_3025_; lean_object* v___x_3026_; lean_object* v_fallback_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v_val_3023_ = lean_ctor_get(v_a_3008_, 0);
lean_inc(v_val_3023_);
lean_dec_ref_known(v_a_3008_, 1);
v_sz_3024_ = lean_array_size(v_content_3000_);
v___x_3025_ = ((size_t)0ULL);
lean_inc_ref(v_content_3000_);
lean_inc_ref(v_goB_2998_);
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2994_, v_goB_2998_, v_sz_3024_, v___x_3025_, v_content_3000_);
v_fallback_3027_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_3027_, 0, lean_box(0));
lean_closure_set(v_fallback_3027_, 1, lean_box(0));
lean_closure_set(v_fallback_3027_, 2, v___x_2996_);
lean_closure_set(v_fallback_3027_, 3, lean_box(0));
lean_closure_set(v_fallback_3027_, 4, lean_box(0));
lean_closure_set(v_fallback_3027_, 5, v___x_3026_);
lean_closure_set(v_fallback_3027_, 6, v___f_2995_);
v___x_3028_ = lean_apply_4(v_val_3023_, v_goI_2997_, v_goB_2998_, v_val_3005_, v_content_3000_);
v___x_3029_ = l_Lean_Doc_withRendererFallback(v_fallback_3027_, v___x_3028_, v___y_3001_, v___y_3002_, v___y_3003_);
return v___x_3029_;
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec(v_val_3005_);
lean_dec_ref(v_content_3000_);
lean_dec_ref(v_goB_2998_);
lean_dec_ref(v_goI_2997_);
lean_dec_ref(v___x_2996_);
lean_dec_ref(v___f_2995_);
lean_dec_ref(v___x_2994_);
v_a_3030_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3007_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3007_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
size_t v_sz_3038_; size_t v___x_3039_; lean_object* v___x_558__overap_3040_; lean_object* v___x_3041_; 
lean_dec_ref_known(v_container_2999_, 1);
lean_dec_ref(v_goI_2997_);
lean_dec_ref(v___x_2996_);
lean_dec_ref(v___f_2995_);
v_sz_3038_ = lean_array_size(v_content_3000_);
v___x_3039_ = ((size_t)0ULL);
v___x_558__overap_3040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2994_, v_goB_2998_, v_sz_3038_, v___x_3039_, v_content_3000_);
lean_inc(v___y_3003_);
lean_inc_ref(v___y_3002_);
lean_inc(v___y_3001_);
v___x_3041_ = lean_apply_4(v___x_558__overap_3040_, v___y_3001_, v___y_3002_, v___y_3003_, lean_box(0));
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3050_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3044_ = v___x_3041_;
v_isShared_3045_ = v_isSharedCheck_3050_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3050_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3046_ = l_Lean_Doc_joinBlocks(v_a_3042_);
lean_dec(v_a_3042_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v___x_3046_);
v___x_3048_ = v___x_3044_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
v_a_3051_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3041_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3041_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object* v___x_3059_, lean_object* v___f_3060_, lean_object* v___x_3061_, lean_object* v_goI_3062_, lean_object* v_goB_3063_, lean_object* v_container_3064_, lean_object* v_content_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_3059_, v___f_3060_, v___x_3061_, v_goI_3062_, v_goB_3063_, v_container_3064_, v_content_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
return v_res_3070_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownBlockElabInlineElabBlock(void){
_start:
{
lean_object* v___x_3072_; lean_object* v_toApplicative_3073_; lean_object* v_toFunctor_3074_; lean_object* v_toSeq_3075_; lean_object* v_toSeqLeft_3076_; lean_object* v_toSeqRight_3077_; lean_object* v___f_3078_; lean_object* v___f_3079_; lean_object* v___f_3080_; lean_object* v___f_3081_; lean_object* v___f_3082_; lean_object* v___x_3083_; lean_object* v___f_3084_; lean_object* v___f_3085_; lean_object* v___f_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___f_3090_; 
v___x_3072_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3073_ = lean_ctor_get(v___x_3072_, 0);
v_toFunctor_3074_ = lean_ctor_get(v_toApplicative_3073_, 0);
v_toSeq_3075_ = lean_ctor_get(v_toApplicative_3073_, 2);
v_toSeqLeft_3076_ = lean_ctor_get(v_toApplicative_3073_, 3);
v_toSeqRight_3077_ = lean_ctor_get(v_toApplicative_3073_, 4);
v___f_3078_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___closed__0));
v___f_3079_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3080_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3074_, 2);
v___f_3081_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3081_, 0, v_toFunctor_3074_);
v___f_3082_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3082_, 0, v_toFunctor_3074_);
v___x_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___f_3081_);
lean_ctor_set(v___x_3083_, 1, v___f_3082_);
lean_inc(v_toSeqRight_3077_);
v___f_3084_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3084_, 0, v_toSeqRight_3077_);
lean_inc(v_toSeqLeft_3076_);
v___f_3085_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3085_, 0, v_toSeqLeft_3076_);
lean_inc(v_toSeq_3075_);
v___f_3086_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3086_, 0, v_toSeq_3075_);
v___x_3087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3083_);
lean_ctor_set(v___x_3087_, 1, v___f_3079_);
lean_ctor_set(v___x_3087_, 2, v___f_3086_);
lean_ctor_set(v___x_3087_, 3, v___f_3085_);
lean_ctor_set(v___x_3087_, 4, v___f_3084_);
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
lean_ctor_set(v___x_3088_, 1, v___f_3080_);
lean_inc_ref(v___x_3088_);
v___x_3089_ = l_StateRefT_x27_instMonad___redArg(v___x_3088_);
v___f_3090_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3090_, 0, v___x_3089_);
lean_closure_set(v___f_3090_, 1, v___f_3078_);
lean_closure_set(v___f_3090_, 2, v___x_3088_);
return v___f_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0(lean_object* v___x_3091_, lean_object* v___x_3092_, lean_object* v_part_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = lean_unsigned_to_nat(0u);
v___x_3099_ = l_Lean_Doc_partMarkdown___redArg(v___x_3091_, v___x_3092_, v___x_3098_, v_part_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed(lean_object* v___x_3100_, lean_object* v___x_3101_, lean_object* v_part_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__0(v___x_3100_, v___x_3101_, v_part_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1(lean_object* v___x_3108_, lean_object* v___x_3109_, lean_object* v___x_3110_, lean_object* v___f_3111_, lean_object* v_x_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_text_3117_; lean_object* v_subsections_3118_; lean_object* v___x_3119_; size_t v_sz_3120_; size_t v___x_3121_; lean_object* v___x_440__overap_3122_; lean_object* v___x_3123_; 
v_text_3117_ = lean_ctor_get(v_x_3112_, 0);
lean_inc_ref(v_text_3117_);
v_subsections_3118_ = lean_ctor_get(v_x_3112_, 1);
lean_inc_ref(v_subsections_3118_);
lean_dec_ref(v_x_3112_);
v___x_3119_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3119_, 0, lean_box(0));
lean_closure_set(v___x_3119_, 1, lean_box(0));
lean_closure_set(v___x_3119_, 2, v___x_3108_);
lean_closure_set(v___x_3119_, 3, v___x_3109_);
v_sz_3120_ = lean_array_size(v_text_3117_);
v___x_3121_ = ((size_t)0ULL);
lean_inc_ref(v___x_3110_);
v___x_440__overap_3122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3110_, v___x_3119_, v_sz_3120_, v___x_3121_, v_text_3117_);
lean_inc(v___y_3115_);
lean_inc_ref(v___y_3114_);
lean_inc(v___y_3113_);
v___x_3123_ = lean_apply_4(v___x_440__overap_3122_, v___y_3113_, v___y_3114_, v___y_3115_, lean_box(0));
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; size_t v_sz_3125_; lean_object* v___x_443__overap_3126_; lean_object* v___x_3127_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
v_sz_3125_ = lean_array_size(v_subsections_3118_);
v___x_443__overap_3126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3110_, v___f_3111_, v_sz_3125_, v___x_3121_, v_subsections_3118_);
lean_inc(v___y_3115_);
lean_inc_ref(v___y_3114_);
lean_inc(v___y_3113_);
v___x_3127_ = lean_apply_4(v___x_443__overap_3126_, v___y_3113_, v___y_3114_, v___y_3115_, lean_box(0));
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3137_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3137_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3137_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3132_ = l_Array_append___redArg(v_a_3124_, v_a_3128_);
lean_dec(v_a_3128_);
v___x_3133_ = l_Lean_Doc_joinBlocks(v___x_3132_);
lean_dec_ref(v___x_3132_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3133_);
v___x_3135_ = v___x_3130_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v_a_3124_);
v_a_3138_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3127_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3127_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec_ref(v_subsections_3118_);
lean_dec_ref(v___f_3111_);
lean_dec_ref(v___x_3110_);
v_a_3146_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3123_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3123_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed(lean_object* v___x_3154_, lean_object* v___x_3155_, lean_object* v___x_3156_, lean_object* v___f_3157_, lean_object* v_x_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__1(v___x_3154_, v___x_3155_, v___x_3156_, v___f_3157_, v_x_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
return v_res_3163_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0(void){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___f_3166_; 
v___x_3164_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3165_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3166_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3166_, 0, v___x_3165_);
lean_closure_set(v___f_3166_, 1, v___x_3164_);
return v___f_3166_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString(void){
_start:
{
lean_object* v___x_3167_; lean_object* v_toApplicative_3168_; lean_object* v_toFunctor_3169_; lean_object* v_toSeq_3170_; lean_object* v_toSeqLeft_3171_; lean_object* v_toSeqRight_3172_; lean_object* v___f_3173_; lean_object* v___f_3174_; lean_object* v___f_3175_; lean_object* v___f_3176_; lean_object* v___x_3177_; lean_object* v___f_3178_; lean_object* v___f_3179_; lean_object* v___f_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___f_3186_; lean_object* v___f_3187_; 
v___x_3167_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3168_ = lean_ctor_get(v___x_3167_, 0);
v_toFunctor_3169_ = lean_ctor_get(v_toApplicative_3168_, 0);
v_toSeq_3170_ = lean_ctor_get(v_toApplicative_3168_, 2);
v_toSeqLeft_3171_ = lean_ctor_get(v_toApplicative_3168_, 3);
v_toSeqRight_3172_ = lean_ctor_get(v_toApplicative_3168_, 4);
v___f_3173_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3174_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3169_, 2);
v___f_3175_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3175_, 0, v_toFunctor_3169_);
v___f_3176_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3176_, 0, v_toFunctor_3169_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___f_3175_);
lean_ctor_set(v___x_3177_, 1, v___f_3176_);
lean_inc(v_toSeqRight_3172_);
v___f_3178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3178_, 0, v_toSeqRight_3172_);
lean_inc(v_toSeqLeft_3171_);
v___f_3179_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3179_, 0, v_toSeqLeft_3171_);
lean_inc(v_toSeq_3170_);
v___f_3180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3180_, 0, v_toSeq_3170_);
v___x_3181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3177_);
lean_ctor_set(v___x_3181_, 1, v___f_3173_);
lean_ctor_set(v___x_3181_, 2, v___f_3180_);
lean_ctor_set(v___x_3181_, 3, v___f_3179_);
lean_ctor_set(v___x_3181_, 4, v___f_3178_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
lean_ctor_set(v___x_3182_, 1, v___f_3174_);
v___x_3183_ = l_StateRefT_x27_instMonad___redArg(v___x_3182_);
v___x_3184_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3185_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3186_ = lean_obj_once(&l_Lean_Doc_instToMarkdownVersoDocString___closed__0, &l_Lean_Doc_instToMarkdownVersoDocString___closed__0_once, _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0);
v___f_3187_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3187_, 0, v___x_3184_);
lean_closure_set(v___f_3187_, 1, v___x_3185_);
lean_closure_set(v___f_3187_, 2, v___x_3183_);
lean_closure_set(v___f_3187_, 3, v___f_3186_);
return v___f_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0(lean_object* v___x_3188_, lean_object* v___x_3189_, lean_object* v_x_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v_snd_3195_; lean_object* v_fst_3196_; lean_object* v_snd_3197_; lean_object* v___x_3198_; 
v_snd_3195_ = lean_ctor_get(v_x_3190_, 1);
lean_inc(v_snd_3195_);
v_fst_3196_ = lean_ctor_get(v_x_3190_, 0);
lean_inc(v_fst_3196_);
lean_dec_ref(v_x_3190_);
v_snd_3197_ = lean_ctor_get(v_snd_3195_, 1);
lean_inc(v_snd_3197_);
lean_dec(v_snd_3195_);
v___x_3198_ = l_Lean_Doc_partMarkdown___redArg(v___x_3188_, v___x_3189_, v_fst_3196_, v_snd_3197_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec(v_fst_3196_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_3199_, lean_object* v___x_3200_, lean_object* v_x_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Lean_Doc_instToMarkdownSnippet___lam__0(v___x_3199_, v___x_3200_, v_x_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1(lean_object* v___x_3207_, lean_object* v___x_3208_, lean_object* v___x_3209_, lean_object* v___f_3210_, lean_object* v_x_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_text_3216_; lean_object* v_sections_3217_; lean_object* v___x_3218_; size_t v_sz_3219_; size_t v___x_3220_; lean_object* v___x_487__overap_3221_; lean_object* v___x_3222_; 
v_text_3216_ = lean_ctor_get(v_x_3211_, 0);
lean_inc_ref(v_text_3216_);
v_sections_3217_ = lean_ctor_get(v_x_3211_, 1);
lean_inc_ref(v_sections_3217_);
lean_dec_ref(v_x_3211_);
v___x_3218_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3218_, 0, lean_box(0));
lean_closure_set(v___x_3218_, 1, lean_box(0));
lean_closure_set(v___x_3218_, 2, v___x_3207_);
lean_closure_set(v___x_3218_, 3, v___x_3208_);
v_sz_3219_ = lean_array_size(v_text_3216_);
v___x_3220_ = ((size_t)0ULL);
lean_inc_ref(v___x_3209_);
v___x_487__overap_3221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3209_, v___x_3218_, v_sz_3219_, v___x_3220_, v_text_3216_);
lean_inc(v___y_3214_);
lean_inc_ref(v___y_3213_);
lean_inc(v___y_3212_);
v___x_3222_ = lean_apply_4(v___x_487__overap_3221_, v___y_3212_, v___y_3213_, v___y_3214_, lean_box(0));
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; size_t v_sz_3224_; lean_object* v___x_490__overap_3225_; lean_object* v___x_3226_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_a_3223_);
lean_dec_ref_known(v___x_3222_, 1);
v_sz_3224_ = lean_array_size(v_sections_3217_);
v___x_490__overap_3225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3209_, v___f_3210_, v_sz_3224_, v___x_3220_, v_sections_3217_);
lean_inc(v___y_3214_);
lean_inc_ref(v___y_3213_);
lean_inc(v___y_3212_);
v___x_3226_ = lean_apply_4(v___x_490__overap_3225_, v___y_3212_, v___y_3213_, v___y_3214_, lean_box(0));
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3236_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3229_ = v___x_3226_;
v_isShared_3230_ = v_isSharedCheck_3236_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3226_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3236_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3234_; 
v___x_3231_ = l_Array_append___redArg(v_a_3223_, v_a_3227_);
lean_dec(v_a_3227_);
v___x_3232_ = l_Lean_Doc_joinBlocks(v___x_3231_);
lean_dec_ref(v___x_3231_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3232_);
v___x_3234_ = v___x_3229_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec(v_a_3223_);
v_a_3237_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3226_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3226_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref(v_sections_3217_);
lean_dec_ref(v___f_3210_);
lean_dec_ref(v___x_3209_);
v_a_3245_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3222_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3222_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_3253_, lean_object* v___x_3254_, lean_object* v___x_3255_, lean_object* v___f_3256_, lean_object* v_x_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_Doc_instToMarkdownSnippet___lam__1(v___x_3253_, v___x_3254_, v___x_3255_, v___f_3256_, v_x_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
return v_res_3262_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___f_3265_; 
v___x_3263_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3264_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3265_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3265_, 0, v___x_3264_);
lean_closure_set(v___f_3265_, 1, v___x_3263_);
return v___f_3265_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet(void){
_start:
{
lean_object* v___x_3266_; lean_object* v_toApplicative_3267_; lean_object* v_toFunctor_3268_; lean_object* v_toSeq_3269_; lean_object* v_toSeqLeft_3270_; lean_object* v_toSeqRight_3271_; lean_object* v___f_3272_; lean_object* v___f_3273_; lean_object* v___f_3274_; lean_object* v___f_3275_; lean_object* v___x_3276_; lean_object* v___f_3277_; lean_object* v___f_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___f_3285_; lean_object* v___f_3286_; 
v___x_3266_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3267_ = lean_ctor_get(v___x_3266_, 0);
v_toFunctor_3268_ = lean_ctor_get(v_toApplicative_3267_, 0);
v_toSeq_3269_ = lean_ctor_get(v_toApplicative_3267_, 2);
v_toSeqLeft_3270_ = lean_ctor_get(v_toApplicative_3267_, 3);
v_toSeqRight_3271_ = lean_ctor_get(v_toApplicative_3267_, 4);
v___f_3272_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3273_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3268_, 2);
v___f_3274_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3274_, 0, v_toFunctor_3268_);
v___f_3275_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3275_, 0, v_toFunctor_3268_);
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___f_3274_);
lean_ctor_set(v___x_3276_, 1, v___f_3275_);
lean_inc(v_toSeqRight_3271_);
v___f_3277_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3277_, 0, v_toSeqRight_3271_);
lean_inc(v_toSeqLeft_3270_);
v___f_3278_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3278_, 0, v_toSeqLeft_3270_);
lean_inc(v_toSeq_3269_);
v___f_3279_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3279_, 0, v_toSeq_3269_);
v___x_3280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3276_);
lean_ctor_set(v___x_3280_, 1, v___f_3272_);
lean_ctor_set(v___x_3280_, 2, v___f_3279_);
lean_ctor_set(v___x_3280_, 3, v___f_3278_);
lean_ctor_set(v___x_3280_, 4, v___f_3277_);
v___x_3281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
lean_ctor_set(v___x_3281_, 1, v___f_3273_);
v___x_3282_ = l_StateRefT_x27_instMonad___redArg(v___x_3281_);
v___x_3283_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3284_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3285_ = lean_obj_once(&l_Lean_Doc_instToMarkdownSnippet___closed__0, &l_Lean_Doc_instToMarkdownSnippet___closed__0_once, _init_l_Lean_Doc_instToMarkdownSnippet___closed__0);
v___f_3286_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3286_, 0, v___x_3283_);
lean_closure_set(v___f_3286_, 1, v___x_3284_);
lean_closure_set(v___f_3286_, 2, v___x_3282_);
lean_closure_set(v___f_3286_, 3, v___f_3285_);
return v___f_3286_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(lean_object* v_opts_3287_, lean_object* v_opt_3288_){
_start:
{
lean_object* v_name_3289_; lean_object* v_defValue_3290_; lean_object* v_map_3291_; lean_object* v___x_3292_; 
v_name_3289_ = lean_ctor_get(v_opt_3288_, 0);
v_defValue_3290_ = lean_ctor_get(v_opt_3288_, 1);
v_map_3291_ = lean_ctor_get(v_opts_3287_, 0);
v___x_3292_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3291_, v_name_3289_);
if (lean_obj_tag(v___x_3292_) == 0)
{
uint8_t v___x_3293_; 
v___x_3293_ = lean_unbox(v_defValue_3290_);
return v___x_3293_;
}
else
{
lean_object* v_val_3294_; 
v_val_3294_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_val_3294_);
lean_dec_ref_known(v___x_3292_, 1);
if (lean_obj_tag(v_val_3294_) == 1)
{
uint8_t v_v_3295_; 
v_v_3295_ = lean_ctor_get_uint8(v_val_3294_, 0);
lean_dec_ref_known(v_val_3294_, 0);
return v_v_3295_;
}
else
{
uint8_t v___x_3296_; 
lean_dec(v_val_3294_);
v___x_3296_ = lean_unbox(v_defValue_3290_);
return v___x_3296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0___boxed(lean_object* v_opts_3297_, lean_object* v_opt_3298_){
_start:
{
uint8_t v_res_3299_; lean_object* v_r_3300_; 
v_res_3299_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_opts_3297_, v_opt_3298_);
lean_dec_ref(v_opt_3298_);
lean_dec_ref(v_opts_3297_);
v_r_3300_ = lean_box(v_res_3299_);
return v_r_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(lean_object* v_opts_3301_, lean_object* v_opt_3302_){
_start:
{
lean_object* v_name_3303_; lean_object* v_defValue_3304_; lean_object* v_map_3305_; lean_object* v___x_3306_; 
v_name_3303_ = lean_ctor_get(v_opt_3302_, 0);
v_defValue_3304_ = lean_ctor_get(v_opt_3302_, 1);
v_map_3305_ = lean_ctor_get(v_opts_3301_, 0);
v___x_3306_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3305_, v_name_3303_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_inc(v_defValue_3304_);
return v_defValue_3304_;
}
else
{
lean_object* v_val_3307_; 
v_val_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_val_3307_);
lean_dec_ref_known(v___x_3306_, 1);
if (lean_obj_tag(v_val_3307_) == 3)
{
lean_object* v_v_3308_; 
v_v_3308_ = lean_ctor_get(v_val_3307_, 0);
lean_inc(v_v_3308_);
lean_dec_ref_known(v_val_3307_, 1);
return v_v_3308_;
}
else
{
lean_dec(v_val_3307_);
lean_inc(v_defValue_3304_);
return v_defValue_3304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1___boxed(lean_object* v_opts_3309_, lean_object* v_opt_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(v_opts_3309_, v_opt_3310_);
lean_dec_ref(v_opt_3310_);
lean_dec_ref(v_opts_3309_);
return v_res_3311_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3312_ = lean_unsigned_to_nat(32u);
v___x_3313_ = lean_mk_empty_array_with_capacity(v___x_3312_);
v___x_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
return v___x_3314_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__1(void){
_start:
{
size_t v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3315_ = ((size_t)5ULL);
v___x_3316_ = lean_unsigned_to_nat(0u);
v___x_3317_ = lean_unsigned_to_nat(32u);
v___x_3318_ = lean_mk_empty_array_with_capacity(v___x_3317_);
v___x_3319_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__0, &l_Lean_Doc_runMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__0);
v___x_3320_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
lean_ctor_set(v___x_3320_, 1, v___x_3318_);
lean_ctor_set(v___x_3320_, 2, v___x_3316_);
lean_ctor_set(v___x_3320_, 3, v___x_3316_);
lean_ctor_set_usize(v___x_3320_, 4, v___x_3315_);
return v___x_3320_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__2(void){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3321_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__3(void){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__2, &l_Lean_Doc_runMarkdown___redArg___closed__2_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__2);
v___x_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
return v___x_3323_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__4(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__3, &l_Lean_Doc_runMarkdown___redArg___closed__3_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__3);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
return v___x_3325_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__5(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3326_ = l_Lean_NameSet_empty;
v___x_3327_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
lean_ctor_set(v___x_3328_, 2, v___x_3326_);
return v___x_3328_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__6(void){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3329_ = lean_unsigned_to_nat(1u);
v___x_3330_ = l_Lean_firstFrontendMacroScope;
v___x_3331_ = lean_nat_add(v___x_3330_, v___x_3329_);
return v___x_3331_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__11(void){
_start:
{
lean_object* v___x_3342_; uint64_t v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3343_ = 0ULL;
v___x_3344_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set_uint64(v___x_3344_, sizeof(void*)*1, v___x_3343_);
return v___x_3344_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__12(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; 
v___x_3345_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3346_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__3, &l_Lean_Doc_runMarkdown___redArg___closed__3_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__3);
v___x_3347_ = 1;
v___x_3348_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3348_, 0, v___x_3346_);
lean_ctor_set(v___x_3348_, 1, v___x_3346_);
lean_ctor_set(v___x_3348_, 2, v___x_3345_);
lean_ctor_set_uint8(v___x_3348_, sizeof(void*)*3, v___x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg(lean_object* v_env_3355_, lean_object* v_act_3356_, lean_object* v_options_3357_, lean_object* v_currNamespace_3358_, lean_object* v_openDecls_3359_, lean_object* v_cancelTk_x3f_3360_){
_start:
{
lean_object* v_a_3363_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; uint8_t v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v_env_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; lean_object* v_fileName_3393_; lean_object* v_fileMap_3394_; lean_object* v_currRecDepth_3395_; lean_object* v_ref_3396_; lean_object* v_currNamespace_3397_; lean_object* v_openDecls_3398_; lean_object* v_initHeartbeats_3399_; lean_object* v_maxHeartbeats_3400_; lean_object* v_quotContext_3401_; lean_object* v_currMacroScope_3402_; lean_object* v_cancelTk_x3f_3403_; uint8_t v_suppressElabErrors_3404_; lean_object* v_inheritedTraceOptions_3405_; lean_object* v___y_3406_; uint8_t v___y_3443_; uint8_t v___x_3463_; 
v___x_3366_ = lean_unsigned_to_nat(0u);
v___x_3367_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__4, &l_Lean_Doc_runMarkdown___redArg___closed__4_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__4);
v___x_3368_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__5, &l_Lean_Doc_runMarkdown___redArg___closed__5_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__5);
v___x_3369_ = lean_io_get_num_heartbeats();
v___x_3370_ = l_Lean_firstFrontendMacroScope;
v___x_3371_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__6, &l_Lean_Doc_runMarkdown___redArg___closed__6_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__6);
v___x_3372_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__9));
v___x_3373_ = lean_box(0);
v___x_3374_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__10));
v___x_3375_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__11, &l_Lean_Doc_runMarkdown___redArg___closed__11_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__11);
v___x_3376_ = 1;
v___x_3377_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__12, &l_Lean_Doc_runMarkdown___redArg___closed__12_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__12);
v___x_3378_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__13));
v___x_3379_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3379_, 0, v_env_3355_);
lean_ctor_set(v___x_3379_, 1, v___x_3371_);
lean_ctor_set(v___x_3379_, 2, v___x_3372_);
lean_ctor_set(v___x_3379_, 3, v___x_3374_);
lean_ctor_set(v___x_3379_, 4, v___x_3375_);
lean_ctor_set(v___x_3379_, 5, v___x_3367_);
lean_ctor_set(v___x_3379_, 6, v___x_3368_);
lean_ctor_set(v___x_3379_, 7, v___x_3377_);
lean_ctor_set(v___x_3379_, 8, v___x_3378_);
v___x_3380_ = lean_st_mk_ref(v___x_3379_);
v___x_3381_ = l_Lean_inheritedTraceOptions;
v___x_3382_ = lean_st_ref_get(v___x_3381_);
v___x_3383_ = lean_st_ref_get(v___x_3380_);
v_env_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc_ref(v_env_3384_);
lean_dec(v___x_3383_);
v___x_3385_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__14));
v___x_3386_ = l_Lean_instInhabitedFileMap_default;
v___x_3387_ = lean_box(0);
v___x_3388_ = l_Lean_Core_getMaxHeartbeats(v_options_3357_);
v___x_3389_ = 0;
v___x_3390_ = l_Lean_diagnostics;
v___x_3391_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_options_3357_, v___x_3390_);
v___x_3463_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3384_);
lean_dec_ref(v_env_3384_);
if (v___x_3463_ == 0)
{
if (v___x_3391_ == 0)
{
lean_inc(v___x_3380_);
v_fileName_3393_ = v___x_3385_;
v_fileMap_3394_ = v___x_3386_;
v_currRecDepth_3395_ = v___x_3366_;
v_ref_3396_ = v___x_3387_;
v_currNamespace_3397_ = v_currNamespace_3358_;
v_openDecls_3398_ = v_openDecls_3359_;
v_initHeartbeats_3399_ = v___x_3369_;
v_maxHeartbeats_3400_ = v___x_3388_;
v_quotContext_3401_ = v___x_3373_;
v_currMacroScope_3402_ = v___x_3370_;
v_cancelTk_x3f_3403_ = v_cancelTk_x3f_3360_;
v_suppressElabErrors_3404_ = v___x_3389_;
v_inheritedTraceOptions_3405_ = v___x_3382_;
v___y_3406_ = v___x_3380_;
goto v___jp_3392_;
}
else
{
v___y_3443_ = v___x_3463_;
goto v___jp_3442_;
}
}
else
{
v___y_3443_ = v___x_3391_;
goto v___jp_3442_;
}
v___jp_3362_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = lean_mk_io_user_error(v_a_3363_);
v___x_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
return v___x_3365_;
}
v___jp_3392_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3407_ = l_Lean_maxRecDepth;
v___x_3408_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(v_options_3357_, v___x_3407_);
lean_inc(v_currMacroScope_3402_);
lean_inc(v_quotContext_3401_);
lean_inc(v_ref_3396_);
lean_inc_ref(v_fileMap_3394_);
lean_inc_ref(v_fileName_3393_);
v___x_3409_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3409_, 0, v_fileName_3393_);
lean_ctor_set(v___x_3409_, 1, v_fileMap_3394_);
lean_ctor_set(v___x_3409_, 2, v_options_3357_);
lean_ctor_set(v___x_3409_, 3, v_currRecDepth_3395_);
lean_ctor_set(v___x_3409_, 4, v___x_3408_);
lean_ctor_set(v___x_3409_, 5, v_ref_3396_);
lean_ctor_set(v___x_3409_, 6, v_currNamespace_3397_);
lean_ctor_set(v___x_3409_, 7, v_openDecls_3398_);
lean_ctor_set(v___x_3409_, 8, v_initHeartbeats_3399_);
lean_ctor_set(v___x_3409_, 9, v_maxHeartbeats_3400_);
lean_ctor_set(v___x_3409_, 10, v_quotContext_3401_);
lean_ctor_set(v___x_3409_, 11, v_currMacroScope_3402_);
lean_ctor_set(v___x_3409_, 12, v_cancelTk_x3f_3403_);
lean_ctor_set(v___x_3409_, 13, v_inheritedTraceOptions_3405_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*14, v___x_3391_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*14 + 1, v_suppressElabErrors_3404_);
v___x_3410_ = lean_apply_3(v_act_3356_, v___x_3409_, v___y_3406_, lean_box(0));
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3419_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3419_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3419_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3415_ = lean_st_ref_get(v___x_3380_);
lean_dec(v___x_3380_);
lean_dec(v___x_3415_);
if (v_isShared_3414_ == 0)
{
v___x_3417_ = v___x_3413_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3411_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3441_; 
lean_dec(v___x_3380_);
v_a_3420_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3422_ = v___x_3410_;
v_isShared_3423_ = v_isSharedCheck_3441_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3410_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3441_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
if (lean_obj_tag(v_a_3420_) == 0)
{
lean_object* v_msg_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3428_; 
v_msg_3424_ = lean_ctor_get(v_a_3420_, 1);
lean_inc_ref(v_msg_3424_);
lean_dec_ref_known(v_a_3420_, 2);
v___x_3425_ = l_Lean_MessageData_toString(v_msg_3424_);
v___x_3426_ = lean_mk_io_user_error(v___x_3425_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3426_);
v___x_3428_ = v___x_3422_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
else
{
lean_object* v_id_3430_; lean_object* v___x_3431_; 
lean_del_object(v___x_3422_);
v_id_3430_ = lean_ctor_get(v_a_3420_, 0);
lean_inc(v_id_3430_);
lean_dec_ref_known(v_a_3420_, 2);
v___x_3431_ = l_Lean_InternalExceptionId_getName(v_id_3430_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
lean_dec(v_id_3430_);
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3431_, 1);
v___x_3433_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__15));
v___x_3434_ = l_Lean_Name_toString(v_a_3432_, v___x_3376_);
v___x_3435_ = lean_string_append(v___x_3433_, v___x_3434_);
lean_dec_ref(v___x_3434_);
v_a_3363_ = v___x_3435_;
goto v___jp_3362_;
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
lean_dec_ref_known(v___x_3431_, 1);
v___x_3436_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__16));
v___x_3437_ = l_Nat_reprFast(v_id_3430_);
v___x_3438_ = lean_string_append(v___x_3436_, v___x_3437_);
lean_dec_ref(v___x_3437_);
v___x_3439_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__17));
v___x_3440_ = lean_string_append(v___x_3438_, v___x_3439_);
v_a_3363_ = v___x_3440_;
goto v___jp_3362_;
}
}
}
}
}
v___jp_3442_:
{
if (v___y_3443_ == 0)
{
lean_object* v___x_3444_; lean_object* v_env_3445_; lean_object* v_nextMacroScope_3446_; lean_object* v_ngen_3447_; lean_object* v_auxDeclNGen_3448_; lean_object* v_traceState_3449_; lean_object* v_messages_3450_; lean_object* v_infoState_3451_; lean_object* v_snapshotTasks_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3461_; 
v___x_3444_ = lean_st_ref_take(v___x_3380_);
v_env_3445_ = lean_ctor_get(v___x_3444_, 0);
v_nextMacroScope_3446_ = lean_ctor_get(v___x_3444_, 1);
v_ngen_3447_ = lean_ctor_get(v___x_3444_, 2);
v_auxDeclNGen_3448_ = lean_ctor_get(v___x_3444_, 3);
v_traceState_3449_ = lean_ctor_get(v___x_3444_, 4);
v_messages_3450_ = lean_ctor_get(v___x_3444_, 6);
v_infoState_3451_ = lean_ctor_get(v___x_3444_, 7);
v_snapshotTasks_3452_ = lean_ctor_get(v___x_3444_, 8);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3461_ == 0)
{
lean_object* v_unused_3462_; 
v_unused_3462_ = lean_ctor_get(v___x_3444_, 5);
lean_dec(v_unused_3462_);
v___x_3454_ = v___x_3444_;
v_isShared_3455_ = v_isSharedCheck_3461_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_snapshotTasks_3452_);
lean_inc(v_infoState_3451_);
lean_inc(v_messages_3450_);
lean_inc(v_traceState_3449_);
lean_inc(v_auxDeclNGen_3448_);
lean_inc(v_ngen_3447_);
lean_inc(v_nextMacroScope_3446_);
lean_inc(v_env_3445_);
lean_dec(v___x_3444_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3461_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3458_; 
v___x_3456_ = l_Lean_Kernel_enableDiag(v_env_3445_, v___x_3391_);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 5, v___x_3367_);
lean_ctor_set(v___x_3454_, 0, v___x_3456_);
v___x_3458_ = v___x_3454_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_nextMacroScope_3446_);
lean_ctor_set(v_reuseFailAlloc_3460_, 2, v_ngen_3447_);
lean_ctor_set(v_reuseFailAlloc_3460_, 3, v_auxDeclNGen_3448_);
lean_ctor_set(v_reuseFailAlloc_3460_, 4, v_traceState_3449_);
lean_ctor_set(v_reuseFailAlloc_3460_, 5, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3460_, 6, v_messages_3450_);
lean_ctor_set(v_reuseFailAlloc_3460_, 7, v_infoState_3451_);
lean_ctor_set(v_reuseFailAlloc_3460_, 8, v_snapshotTasks_3452_);
v___x_3458_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3459_; 
v___x_3459_ = lean_st_ref_set(v___x_3380_, v___x_3458_);
lean_inc(v___x_3380_);
v_fileName_3393_ = v___x_3385_;
v_fileMap_3394_ = v___x_3386_;
v_currRecDepth_3395_ = v___x_3366_;
v_ref_3396_ = v___x_3387_;
v_currNamespace_3397_ = v_currNamespace_3358_;
v_openDecls_3398_ = v_openDecls_3359_;
v_initHeartbeats_3399_ = v___x_3369_;
v_maxHeartbeats_3400_ = v___x_3388_;
v_quotContext_3401_ = v___x_3373_;
v_currMacroScope_3402_ = v___x_3370_;
v_cancelTk_x3f_3403_ = v_cancelTk_x3f_3360_;
v_suppressElabErrors_3404_ = v___x_3389_;
v_inheritedTraceOptions_3405_ = v___x_3382_;
v___y_3406_ = v___x_3380_;
goto v___jp_3392_;
}
}
}
else
{
lean_inc(v___x_3380_);
v_fileName_3393_ = v___x_3385_;
v_fileMap_3394_ = v___x_3386_;
v_currRecDepth_3395_ = v___x_3366_;
v_ref_3396_ = v___x_3387_;
v_currNamespace_3397_ = v_currNamespace_3358_;
v_openDecls_3398_ = v_openDecls_3359_;
v_initHeartbeats_3399_ = v___x_3369_;
v_maxHeartbeats_3400_ = v___x_3388_;
v_quotContext_3401_ = v___x_3373_;
v_currMacroScope_3402_ = v___x_3370_;
v_cancelTk_x3f_3403_ = v_cancelTk_x3f_3360_;
v_suppressElabErrors_3404_ = v___x_3389_;
v_inheritedTraceOptions_3405_ = v___x_3382_;
v___y_3406_ = v___x_3380_;
goto v___jp_3392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg___boxed(lean_object* v_env_3464_, lean_object* v_act_3465_, lean_object* v_options_3466_, lean_object* v_currNamespace_3467_, lean_object* v_openDecls_3468_, lean_object* v_cancelTk_x3f_3469_, lean_object* v_a_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_Lean_Doc_runMarkdown___redArg(v_env_3464_, v_act_3465_, v_options_3466_, v_currNamespace_3467_, v_openDecls_3468_, v_cancelTk_x3f_3469_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown(lean_object* v_00_u03b1_3472_, lean_object* v_env_3473_, lean_object* v_act_3474_, lean_object* v_options_3475_, lean_object* v_currNamespace_3476_, lean_object* v_openDecls_3477_, lean_object* v_cancelTk_x3f_3478_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Lean_Doc_runMarkdown___redArg(v_env_3473_, v_act_3474_, v_options_3475_, v_currNamespace_3476_, v_openDecls_3477_, v_cancelTk_x3f_3478_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___boxed(lean_object* v_00_u03b1_3481_, lean_object* v_env_3482_, lean_object* v_act_3483_, lean_object* v_options_3484_, lean_object* v_currNamespace_3485_, lean_object* v_openDecls_3486_, lean_object* v_cancelTk_x3f_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_Doc_runMarkdown(v_00_u03b1_3481_, v_env_3482_, v_act_3483_, v_options_3484_, v_currNamespace_3485_, v_openDecls_3486_, v_cancelTk_x3f_3487_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(lean_object* v_x_3490_, size_t v_sz_3491_, size_t v_i_3492_, lean_object* v_bs_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
uint8_t v___x_3498_; 
v___x_3498_ = lean_usize_dec_lt(v_i_3492_, v_sz_3491_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
lean_dec_ref(v_x_3490_);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v_bs_3493_);
return v___x_3499_;
}
else
{
lean_object* v_v_3500_; lean_object* v___x_3501_; 
v_v_3500_ = lean_array_uget_borrowed(v_bs_3493_, v_i_3492_);
lean_inc(v_v_3500_);
lean_inc_ref(v_x_3490_);
v___x_3501_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3490_, v_v_3500_, v___y_3494_, v___y_3495_, v___y_3496_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; lean_object* v_bs_x27_3504_; size_t v___x_3505_; size_t v___x_3506_; lean_object* v___x_3507_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___x_3503_ = lean_unsigned_to_nat(0u);
v_bs_x27_3504_ = lean_array_uset(v_bs_3493_, v_i_3492_, v___x_3503_);
v___x_3505_ = ((size_t)1ULL);
v___x_3506_ = lean_usize_add(v_i_3492_, v___x_3505_);
v___x_3507_ = lean_array_uset(v_bs_x27_3504_, v_i_3492_, v_a_3502_);
v_i_3492_ = v___x_3506_;
v_bs_3493_ = v___x_3507_;
goto _start;
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_dec_ref(v_bs_3493_);
lean_dec_ref(v_x_3490_);
v_a_3509_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3501_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3501_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed(lean_object* v_x_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(v_x_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(lean_object* v_x_3526_, size_t v_sz_3527_, size_t v___x_3528_, lean_object* v_content_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3526_, v_sz_3527_, v___x_3528_, v_content_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3543_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3537_ = v___x_3534_;
v_isShared_3538_ = v_isSharedCheck_3543_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3543_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3541_; 
v___x_3539_ = l_Lean_Doc_joinInlines(v_a_3535_);
lean_dec(v_a_3535_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3539_);
v___x_3541_ = v___x_3537_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
v_a_3544_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3534_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3534_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed(lean_object* v_x_3552_, lean_object* v_sz_3553_, lean_object* v___x_3554_, lean_object* v_content_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
size_t v_sz_boxed_3560_; size_t v___x_3961__boxed_3561_; lean_object* v_res_3562_; 
v_sz_boxed_3560_ = lean_unbox_usize(v_sz_3553_);
lean_dec(v_sz_3553_);
v___x_3961__boxed_3561_ = lean_unbox_usize(v___x_3554_);
lean_dec(v___x_3554_);
v_res_3562_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(v_x_3552_, v_sz_boxed_3560_, v___x_3961__boxed_3561_, v_content_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(lean_object* v_x_3563_, lean_object* v_x_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
lean_object* v_pieces_3570_; lean_object* v_pieces_3574_; 
switch(lean_obj_tag(v_x_3564_))
{
case 0:
{
lean_object* v_string_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
lean_dec_ref(v_x_3563_);
v_string_3577_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_string_3577_);
lean_dec_ref_known(v_x_3564_, 1);
v___x_3578_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_3577_);
lean_dec_ref(v_string_3577_);
v___x_3579_ = lean_unsigned_to_nat(1u);
v___x_3580_ = lean_mk_empty_array_with_capacity(v___x_3579_);
v___x_3581_ = lean_array_push(v___x_3580_, v___x_3578_);
v___x_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
return v___x_3582_;
}
case 1:
{
lean_object* v_content_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3638_; 
v_content_3583_ = lean_ctor_get(v_x_3564_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_x_3564_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3585_ = v_x_3564_;
v_isShared_3586_ = v_isSharedCheck_3638_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_content_3583_);
lean_dec(v_x_3564_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3638_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
lean_ctor_set_tag(v___x_3585_, 9);
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_content_3583_);
v___x_3588_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3589_; lean_object* v_snd_3590_; lean_object* v_fst_3591_; lean_object* v_fst_3592_; lean_object* v_snd_3593_; lean_object* v_pieces_3595_; uint8_t v_inEmph_3603_; uint8_t v_inBold_3604_; uint8_t v_inLink_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3636_; 
v___x_3589_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3588_);
v_snd_3590_ = lean_ctor_get(v___x_3589_, 1);
lean_inc(v_snd_3590_);
v_fst_3591_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_fst_3591_);
lean_dec_ref(v___x_3589_);
v_fst_3592_ = lean_ctor_get(v_snd_3590_, 0);
lean_inc(v_fst_3592_);
v_snd_3593_ = lean_ctor_get(v_snd_3590_, 1);
lean_inc(v_snd_3593_);
lean_dec(v_snd_3590_);
v_inEmph_3603_ = lean_ctor_get_uint8(v_x_3563_, 0);
v_inBold_3604_ = lean_ctor_get_uint8(v_x_3563_, 1);
v_inLink_3605_ = lean_ctor_get_uint8(v_x_3563_, 2);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_x_3563_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3607_ = v_x_3563_;
v_isShared_3608_ = v_isSharedCheck_3636_;
goto v_resetjp_3606_;
}
else
{
lean_dec(v_x_3563_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3636_;
goto v_resetjp_3606_;
}
v___jp_3594_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3596_ = lean_string_utf8_byte_size(v_snd_3593_);
v___x_3597_ = lean_unsigned_to_nat(0u);
v___x_3598_ = lean_nat_dec_eq(v___x_3596_, v___x_3597_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3599_ = lean_unsigned_to_nat(1u);
v___x_3600_ = lean_mk_empty_array_with_capacity(v___x_3599_);
v___x_3601_ = lean_array_push(v___x_3600_, v_snd_3593_);
v___x_3602_ = lean_array_push(v_pieces_3595_, v___x_3601_);
v_pieces_3574_ = v___x_3602_;
goto v___jp_3573_;
}
else
{
lean_dec(v_snd_3593_);
v_pieces_3574_ = v_pieces_3595_;
goto v___jp_3573_;
}
}
v_resetjp_3606_:
{
uint8_t v___x_3609_; lean_object* v___x_3611_; 
v___x_3609_ = 1;
if (v_isShared_3608_ == 0)
{
v___x_3611_ = v___x_3607_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, 1, v_inBold_3604_);
lean_ctor_set_uint8(v_reuseFailAlloc_3635_, 2, v_inLink_3605_);
v___x_3611_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3612_; 
lean_ctor_set_uint8(v___x_3611_, 0, v___x_3609_);
v___x_3612_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3611_, v_fst_3592_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v_pieces_3615_; lean_object* v_pieces_3622_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
v___x_3627_ = lean_unsigned_to_nat(0u);
v___x_3628_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3629_ = lean_string_utf8_byte_size(v_fst_3591_);
v___x_3630_ = lean_nat_dec_eq(v___x_3629_, v___x_3627_);
if (v___x_3630_ == 0)
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3631_ = lean_unsigned_to_nat(1u);
v___x_3632_ = lean_mk_empty_array_with_capacity(v___x_3631_);
v___x_3633_ = lean_array_push(v___x_3632_, v_fst_3591_);
v___x_3634_ = lean_array_push(v___x_3628_, v___x_3633_);
v_pieces_3622_ = v___x_3634_;
goto v___jp_3621_;
}
else
{
lean_dec(v_fst_3591_);
v_pieces_3622_ = v___x_3628_;
goto v___jp_3621_;
}
v___jp_3614_:
{
lean_object* v___x_3616_; 
v___x_3616_ = lean_array_push(v_pieces_3615_, v_a_3613_);
if (v_inEmph_3603_ == 0)
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3617_ = lean_unsigned_to_nat(1u);
v___x_3618_ = lean_mk_empty_array_with_capacity(v___x_3617_);
lean_dec_ref(v___x_3618_);
v___x_3619_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3620_ = lean_array_push(v___x_3616_, v___x_3619_);
v_pieces_3595_ = v___x_3620_;
goto v___jp_3594_;
}
else
{
v_pieces_3595_ = v___x_3616_;
goto v___jp_3594_;
}
}
v___jp_3621_:
{
if (v_inEmph_3603_ == 0)
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3623_ = lean_unsigned_to_nat(1u);
v___x_3624_ = lean_mk_empty_array_with_capacity(v___x_3623_);
lean_dec_ref(v___x_3624_);
v___x_3625_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3626_ = lean_array_push(v_pieces_3622_, v___x_3625_);
v_pieces_3615_ = v___x_3626_;
goto v___jp_3614_;
}
else
{
v_pieces_3615_ = v_pieces_3622_;
goto v___jp_3614_;
}
}
}
else
{
lean_dec(v_snd_3593_);
lean_dec(v_fst_3591_);
return v___x_3612_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3694_; 
v_content_3639_ = lean_ctor_get(v_x_3564_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_x_3564_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3641_ = v_x_3564_;
v_isShared_3642_ = v_isSharedCheck_3694_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_content_3639_);
lean_dec(v_x_3564_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3694_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
lean_ctor_set_tag(v___x_3641_, 9);
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_content_3639_);
v___x_3644_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3645_; lean_object* v_snd_3646_; lean_object* v_fst_3647_; lean_object* v_fst_3648_; lean_object* v_snd_3649_; lean_object* v_pieces_3651_; uint8_t v_inEmph_3659_; uint8_t v_inBold_3660_; uint8_t v_inLink_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3692_; 
v___x_3645_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3644_);
v_snd_3646_ = lean_ctor_get(v___x_3645_, 1);
lean_inc(v_snd_3646_);
v_fst_3647_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_fst_3647_);
lean_dec_ref(v___x_3645_);
v_fst_3648_ = lean_ctor_get(v_snd_3646_, 0);
lean_inc(v_fst_3648_);
v_snd_3649_ = lean_ctor_get(v_snd_3646_, 1);
lean_inc(v_snd_3649_);
lean_dec(v_snd_3646_);
v_inEmph_3659_ = lean_ctor_get_uint8(v_x_3563_, 0);
v_inBold_3660_ = lean_ctor_get_uint8(v_x_3563_, 1);
v_inLink_3661_ = lean_ctor_get_uint8(v_x_3563_, 2);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_x_3563_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3663_ = v_x_3563_;
v_isShared_3664_ = v_isSharedCheck_3692_;
goto v_resetjp_3662_;
}
else
{
lean_dec(v_x_3563_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3692_;
goto v_resetjp_3662_;
}
v___jp_3650_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
v___x_3652_ = lean_string_utf8_byte_size(v_snd_3649_);
v___x_3653_ = lean_unsigned_to_nat(0u);
v___x_3654_ = lean_nat_dec_eq(v___x_3652_, v___x_3653_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3655_ = lean_unsigned_to_nat(1u);
v___x_3656_ = lean_mk_empty_array_with_capacity(v___x_3655_);
v___x_3657_ = lean_array_push(v___x_3656_, v_snd_3649_);
v___x_3658_ = lean_array_push(v_pieces_3651_, v___x_3657_);
v_pieces_3570_ = v___x_3658_;
goto v___jp_3569_;
}
else
{
lean_dec(v_snd_3649_);
v_pieces_3570_ = v_pieces_3651_;
goto v___jp_3569_;
}
}
v_resetjp_3662_:
{
uint8_t v___x_3665_; lean_object* v___x_3667_; 
v___x_3665_ = 1;
if (v_isShared_3664_ == 0)
{
v___x_3667_ = v___x_3663_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3691_, 0, v_inEmph_3659_);
lean_ctor_set_uint8(v_reuseFailAlloc_3691_, 2, v_inLink_3661_);
v___x_3667_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3668_; 
lean_ctor_set_uint8(v___x_3667_, 1, v___x_3665_);
v___x_3668_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3667_, v_fst_3648_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v_pieces_3671_; lean_object* v_pieces_3678_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
lean_dec_ref_known(v___x_3668_, 1);
v___x_3683_ = lean_unsigned_to_nat(0u);
v___x_3684_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3685_ = lean_string_utf8_byte_size(v_fst_3647_);
v___x_3686_ = lean_nat_dec_eq(v___x_3685_, v___x_3683_);
if (v___x_3686_ == 0)
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3687_ = lean_unsigned_to_nat(1u);
v___x_3688_ = lean_mk_empty_array_with_capacity(v___x_3687_);
v___x_3689_ = lean_array_push(v___x_3688_, v_fst_3647_);
v___x_3690_ = lean_array_push(v___x_3684_, v___x_3689_);
v_pieces_3678_ = v___x_3690_;
goto v___jp_3677_;
}
else
{
lean_dec(v_fst_3647_);
v_pieces_3678_ = v___x_3684_;
goto v___jp_3677_;
}
v___jp_3670_:
{
lean_object* v___x_3672_; 
v___x_3672_ = lean_array_push(v_pieces_3671_, v_a_3669_);
if (v_inBold_3660_ == 0)
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3673_ = lean_unsigned_to_nat(1u);
v___x_3674_ = lean_mk_empty_array_with_capacity(v___x_3673_);
lean_dec_ref(v___x_3674_);
v___x_3675_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3676_ = lean_array_push(v___x_3672_, v___x_3675_);
v_pieces_3651_ = v___x_3676_;
goto v___jp_3650_;
}
else
{
v_pieces_3651_ = v___x_3672_;
goto v___jp_3650_;
}
}
v___jp_3677_:
{
if (v_inBold_3660_ == 0)
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3679_ = lean_unsigned_to_nat(1u);
v___x_3680_ = lean_mk_empty_array_with_capacity(v___x_3679_);
lean_dec_ref(v___x_3680_);
v___x_3681_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3682_ = lean_array_push(v_pieces_3678_, v___x_3681_);
v_pieces_3671_ = v___x_3682_;
goto v___jp_3670_;
}
else
{
v_pieces_3671_ = v_pieces_3678_;
goto v___jp_3670_;
}
}
}
else
{
lean_dec(v_snd_3649_);
lean_dec(v_fst_3647_);
return v___x_3668_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
lean_dec_ref(v_x_3563_);
v_string_3695_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_string_3695_);
lean_dec_ref_known(v_x_3564_, 1);
v___x_3696_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_3695_);
v___x_3697_ = lean_unsigned_to_nat(1u);
v___x_3698_ = lean_mk_empty_array_with_capacity(v___x_3697_);
v___x_3699_ = lean_array_push(v___x_3698_, v___x_3696_);
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
return v___x_3700_;
}
case 4:
{
uint8_t v_mode_3701_; 
lean_dec_ref(v_x_3563_);
v_mode_3701_ = lean_ctor_get_uint8(v_x_3564_, sizeof(void*)*1);
if (v_mode_3701_ == 0)
{
lean_object* v_string_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v_string_3702_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_string_3702_);
lean_dec_ref_known(v_x_3564_, 1);
v___x_3703_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_3704_ = lean_string_append(v___x_3703_, v_string_3702_);
lean_dec_ref(v_string_3702_);
v___x_3705_ = lean_string_append(v___x_3704_, v___x_3703_);
v___x_3706_ = lean_unsigned_to_nat(1u);
v___x_3707_ = lean_mk_empty_array_with_capacity(v___x_3706_);
v___x_3708_ = lean_array_push(v___x_3707_, v___x_3705_);
v___x_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
return v___x_3709_;
}
else
{
lean_object* v_string_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v_string_3710_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_string_3710_);
lean_dec_ref_known(v_x_3564_, 1);
v___x_3711_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_3712_ = lean_string_append(v___x_3711_, v_string_3710_);
lean_dec_ref(v_string_3710_);
v___x_3713_ = lean_string_append(v___x_3712_, v___x_3711_);
v___x_3714_ = lean_unsigned_to_nat(1u);
v___x_3715_ = lean_mk_empty_array_with_capacity(v___x_3714_);
v___x_3716_ = lean_array_push(v___x_3715_, v___x_3713_);
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
return v___x_3717_;
}
}
case 5:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
lean_dec_ref_known(v_x_3564_, 1);
lean_dec_ref(v_x_3563_);
v___x_3718_ = lean_unsigned_to_nat(2u);
v___x_3719_ = lean_mk_empty_array_with_capacity(v___x_3718_);
lean_dec_ref(v___x_3719_);
v___x_3720_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
return v___x_3721_;
}
case 6:
{
uint8_t v_inLink_3722_; 
v_inLink_3722_ = lean_ctor_get_uint8(v_x_3563_, 2);
if (v_inLink_3722_ == 0)
{
lean_object* v_content_3723_; lean_object* v_url_3724_; uint8_t v_inEmph_3725_; uint8_t v_inBold_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3757_; 
v_content_3723_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_content_3723_);
v_url_3724_ = lean_ctor_get(v_x_3564_, 1);
lean_inc_ref(v_url_3724_);
lean_dec_ref_known(v_x_3564_, 2);
v_inEmph_3725_ = lean_ctor_get_uint8(v_x_3563_, 0);
v_inBold_3726_ = lean_ctor_get_uint8(v_x_3563_, 1);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_x_3563_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3728_ = v_x_3563_;
v_isShared_3729_ = v_isSharedCheck_3757_;
goto v_resetjp_3727_;
}
else
{
lean_dec(v_x_3563_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3757_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
uint8_t v___x_3730_; lean_object* v___x_3732_; 
v___x_3730_ = 1;
if (v_isShared_3729_ == 0)
{
v___x_3732_ = v___x_3728_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 0, v_inEmph_3725_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 1, v_inBold_3726_);
v___x_3732_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_ctor_set_uint8(v___x_3732_, 2, v___x_3730_);
v___x_3733_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3733_, 0, v_content_3723_);
v___x_3734_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3732_, v___x_3733_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3755_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3755_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3755_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3753_; 
v___x_3739_ = lean_unsigned_to_nat(1u);
v___x_3740_ = lean_mk_empty_array_with_capacity(v___x_3739_);
v___x_3741_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3742_ = lean_string_append(v___x_3741_, v_url_3724_);
lean_dec_ref(v_url_3724_);
v___x_3743_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3744_ = lean_string_append(v___x_3742_, v___x_3743_);
v___x_3745_ = lean_array_push(v___x_3740_, v___x_3744_);
v___x_3746_ = lean_unsigned_to_nat(3u);
v___x_3747_ = lean_mk_empty_array_with_capacity(v___x_3746_);
lean_dec_ref(v___x_3747_);
v___x_3748_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_3749_ = lean_array_push(v___x_3748_, v_a_3735_);
v___x_3750_ = lean_array_push(v___x_3749_, v___x_3745_);
v___x_3751_ = l_Lean_Doc_joinInlines(v___x_3750_);
lean_dec_ref(v___x_3750_);
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v___x_3751_);
v___x_3753_ = v___x_3737_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3751_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
else
{
lean_dec_ref(v_url_3724_);
return v___x_3734_;
}
}
}
}
else
{
lean_object* v_content_3758_; size_t v_sz_3759_; size_t v___x_3760_; lean_object* v___x_3761_; 
v_content_3758_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_content_3758_);
lean_dec_ref_known(v_x_3564_, 2);
v_sz_3759_ = lean_array_size(v_content_3758_);
v___x_3760_ = ((size_t)0ULL);
v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3563_, v_sz_3759_, v___x_3760_, v_content_3758_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3770_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3764_ = v___x_3761_;
v_isShared_3765_ = v_isSharedCheck_3770_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3761_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3770_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3766_ = l_Lean_Doc_joinInlines(v_a_3762_);
lean_dec(v_a_3762_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 0, v___x_3766_);
v___x_3768_ = v___x_3764_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
v_a_3771_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3761_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3761_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
}
case 7:
{
lean_object* v_name_3779_; lean_object* v_content_3780_; size_t v_sz_3781_; size_t v___x_3782_; lean_object* v___x_3783_; 
v_name_3779_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_name_3779_);
v_content_3780_ = lean_ctor_get(v_x_3564_, 1);
lean_inc_ref(v_content_3780_);
lean_dec_ref_known(v_x_3564_, 2);
v_sz_3781_ = lean_array_size(v_content_3780_);
v___x_3782_ = ((size_t)0ULL);
v___x_3783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3563_, v_sz_3781_, v___x_3782_, v_content_3780_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v___x_3783_, 1);
v___x_3785_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_3786_ = l_Lean_Doc_joinInlines(v_a_3784_);
lean_dec(v_a_3784_);
v___x_3787_ = lean_array_to_list(v___x_3786_);
v___x_3788_ = l_String_intercalate(v___x_3785_, v___x_3787_);
lean_inc_ref(v_name_3779_);
v___x_3789_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_3779_, v___x_3788_, v_a_3565_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3803_; 
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3803_ == 0)
{
lean_object* v_unused_3804_; 
v_unused_3804_ = lean_ctor_get(v___x_3789_, 0);
lean_dec(v_unused_3804_);
v___x_3791_ = v___x_3789_;
v_isShared_3792_ = v_isSharedCheck_3803_;
goto v_resetjp_3790_;
}
else
{
lean_dec(v___x_3789_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3803_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3801_; 
v___x_3793_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_3794_ = lean_string_append(v___x_3793_, v_name_3779_);
lean_dec_ref(v_name_3779_);
v___x_3795_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_3796_ = lean_string_append(v___x_3794_, v___x_3795_);
v___x_3797_ = lean_unsigned_to_nat(1u);
v___x_3798_ = lean_mk_empty_array_with_capacity(v___x_3797_);
v___x_3799_ = lean_array_push(v___x_3798_, v___x_3796_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3799_);
v___x_3801_ = v___x_3791_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec_ref(v_name_3779_);
v_a_3805_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3789_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3789_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec_ref(v_name_3779_);
v_a_3813_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3783_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3783_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
case 8:
{
lean_object* v_alt_3821_; lean_object* v_url_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_dec_ref(v_x_3563_);
v_alt_3821_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_alt_3821_);
v_url_3822_ = lean_ctor_get(v_x_3564_, 1);
lean_inc_ref(v_url_3822_);
lean_dec_ref_known(v_x_3564_, 2);
v___x_3823_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_3824_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_3821_);
lean_dec_ref(v_alt_3821_);
v___x_3825_ = lean_string_append(v___x_3823_, v___x_3824_);
lean_dec_ref(v___x_3824_);
v___x_3826_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3827_ = lean_string_append(v___x_3825_, v___x_3826_);
v___x_3828_ = lean_string_append(v___x_3827_, v_url_3822_);
lean_dec_ref(v_url_3822_);
v___x_3829_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3830_ = lean_string_append(v___x_3828_, v___x_3829_);
v___x_3831_ = lean_unsigned_to_nat(1u);
v___x_3832_ = lean_mk_empty_array_with_capacity(v___x_3831_);
v___x_3833_ = lean_array_push(v___x_3832_, v___x_3830_);
v___x_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
return v___x_3834_;
}
case 9:
{
lean_object* v_content_3835_; size_t v_sz_3836_; size_t v___x_3837_; lean_object* v___x_3838_; 
v_content_3835_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_content_3835_);
lean_dec_ref_known(v_x_3564_, 1);
v_sz_3836_ = lean_array_size(v_content_3835_);
v___x_3837_ = ((size_t)0ULL);
v___x_3838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3563_, v_sz_3836_, v___x_3837_, v_content_3835_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3847_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3841_ = v___x_3838_;
v_isShared_3842_ = v_isSharedCheck_3847_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3838_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3847_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3843_ = l_Lean_Doc_joinInlines(v_a_3839_);
lean_dec(v_a_3839_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 0, v___x_3843_);
v___x_3845_ = v___x_3841_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
v_a_3848_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3838_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3838_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
default: 
{
lean_object* v_container_3856_; 
v_container_3856_ = lean_ctor_get(v_x_3564_, 0);
if (lean_obj_tag(v_container_3856_) == 0)
{
lean_object* v_content_3857_; lean_object* v_val_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
lean_inc_ref(v_container_3856_);
v_content_3857_ = lean_ctor_get(v_x_3564_, 1);
lean_inc_ref(v_content_3857_);
lean_dec_ref_known(v_x_3564_, 2);
v_val_3858_ = lean_ctor_get(v_container_3856_, 0);
lean_inc(v_val_3858_);
lean_dec_ref_known(v_container_3856_, 1);
v___x_3859_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3858_);
v___x_3860_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_3859_, v_a_3566_, v_a_3567_);
lean_dec(v___x_3859_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
if (lean_obj_tag(v_a_3861_) == 0)
{
size_t v_sz_3862_; size_t v___x_3863_; lean_object* v___x_3864_; 
lean_dec(v_val_3858_);
v_sz_3862_ = lean_array_size(v_content_3857_);
v___x_3863_ = ((size_t)0ULL);
v___x_3864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3563_, v_sz_3862_, v___x_3863_, v_content_3857_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3873_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3867_ = v___x_3864_;
v_isShared_3868_ = v_isSharedCheck_3873_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3864_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3873_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3869_; lean_object* v___x_3871_; 
v___x_3869_ = l_Lean_Doc_joinInlines(v_a_3865_);
lean_dec(v_a_3865_);
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 0, v___x_3869_);
v___x_3871_ = v___x_3867_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
v_a_3874_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3864_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3864_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
lean_object* v_val_3882_; lean_object* v___f_3883_; size_t v_sz_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v_fallback_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v_val_3882_ = lean_ctor_get(v_a_3861_, 0);
lean_inc(v_val_3882_);
lean_dec_ref_known(v_a_3861_, 1);
lean_inc_ref(v_x_3563_);
v___f_3883_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3883_, 0, v_x_3563_);
v_sz_3884_ = lean_array_size(v_content_3857_);
v___x_3885_ = lean_box_usize(v_sz_3884_);
v___x_3886_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
lean_inc_ref(v_content_3857_);
v_fallback_3887_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v_fallback_3887_, 0, v_x_3563_);
lean_closure_set(v_fallback_3887_, 1, v___x_3885_);
lean_closure_set(v_fallback_3887_, 2, v___x_3886_);
lean_closure_set(v_fallback_3887_, 3, v_content_3857_);
v___x_3888_ = lean_apply_3(v_val_3882_, v___f_3883_, v_val_3858_, v_content_3857_);
v___x_3889_ = l_Lean_Doc_withRendererFallback(v_fallback_3887_, v___x_3888_, v_a_3565_, v_a_3566_, v_a_3567_);
return v___x_3889_;
}
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
lean_dec(v_val_3858_);
lean_dec_ref(v_content_3857_);
lean_dec_ref(v_x_3563_);
v_a_3890_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3860_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3860_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3895_; 
if (v_isShared_3893_ == 0)
{
v___x_3895_ = v___x_3892_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
else
{
lean_object* v_content_3898_; size_t v_sz_3899_; size_t v___x_3900_; lean_object* v___x_3901_; 
v_content_3898_ = lean_ctor_get(v_x_3564_, 1);
lean_inc_ref(v_content_3898_);
lean_dec_ref_known(v_x_3564_, 2);
v_sz_3899_ = lean_array_size(v_content_3898_);
v___x_3900_ = ((size_t)0ULL);
v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3563_, v_sz_3899_, v___x_3900_, v_content_3898_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3910_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3904_ = v___x_3901_;
v_isShared_3905_ = v_isSharedCheck_3910_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3901_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3910_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3906_ = l_Lean_Doc_joinInlines(v_a_3902_);
lean_dec(v_a_3902_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3906_);
v___x_3908_ = v___x_3904_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
v_a_3911_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3901_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3901_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
}
}
v___jp_3569_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = l_Lean_Doc_joinInlines(v_pieces_3570_);
lean_dec_ref(v_pieces_3570_);
v___x_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
return v___x_3572_;
}
v___jp_3573_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = l_Lean_Doc_joinInlines(v_pieces_3574_);
lean_dec_ref(v_pieces_3574_);
v___x_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
return v___x_3576_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(lean_object* v_x_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3926_, lean_object* v_sz_3927_, lean_object* v_i_3928_, lean_object* v_bs_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
size_t v_sz_boxed_3934_; size_t v_i_boxed_3935_; lean_object* v_res_3936_; 
v_sz_boxed_3934_ = lean_unbox_usize(v_sz_3927_);
lean_dec(v_sz_3927_);
v_i_boxed_3935_ = lean_unbox_usize(v_i_3928_);
lean_dec(v_i_3928_);
v_res_3936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3926_, v_sz_boxed_3934_, v_i_boxed_3935_, v_bs_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed(lean_object* v_x_3937_, lean_object* v_x_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3937_, v_x_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(lean_object* v___x_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0___boxed(lean_object* v___x_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(v___x_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(lean_object* v_x_3958_, lean_object* v_x_3959_){
_start:
{
lean_object* v_zero_3960_; uint8_t v_isZero_3961_; 
v_zero_3960_ = lean_unsigned_to_nat(0u);
v_isZero_3961_ = lean_nat_dec_eq(v_x_3958_, v_zero_3960_);
if (v_isZero_3961_ == 1)
{
lean_dec(v_x_3958_);
return v_x_3959_;
}
else
{
uint32_t v___x_3962_; lean_object* v_one_3963_; lean_object* v_n_3964_; lean_object* v___x_3965_; 
v___x_3962_ = 32;
v_one_3963_ = lean_unsigned_to_nat(1u);
v_n_3964_ = lean_nat_sub(v_x_3958_, v_one_3963_);
lean_dec(v_x_3958_);
v___x_3965_ = lean_string_push(v_x_3959_, v___x_3962_);
v_x_3958_ = v_n_3964_;
v_x_3959_ = v___x_3965_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(size_t v_sz_3967_, size_t v_i_3968_, lean_object* v_bs_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
uint8_t v___x_3974_; 
v___x_3974_ = lean_usize_dec_lt(v_i_3968_, v_sz_3967_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; 
v___x_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3975_, 0, v_bs_3969_);
return v___x_3975_;
}
else
{
lean_object* v_v_3976_; size_t v_sz_3977_; size_t v___x_3978_; lean_object* v___x_3979_; 
v_v_3976_ = lean_array_uget_borrowed(v_bs_3969_, v_i_3968_);
v_sz_3977_ = lean_array_size(v_v_3976_);
v___x_3978_ = ((size_t)0ULL);
lean_inc(v_v_3976_);
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_3977_, v___x_3978_, v_v_3976_, v___y_3970_, v___y_3971_, v___y_3972_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3981_; lean_object* v_bs_x27_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; size_t v___x_3987_; size_t v___x_3988_; lean_object* v___x_3989_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref_known(v___x_3979_, 1);
v___x_3981_ = lean_unsigned_to_nat(0u);
v_bs_x27_3982_ = lean_array_uset(v_bs_3969_, v_i_3968_, v___x_3981_);
v___x_3983_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_3984_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_3985_ = l_Lean_Doc_joinBlocks(v_a_3980_);
lean_dec(v_a_3980_);
v___x_3986_ = l_Lean_Doc_prefixListLines(v___x_3983_, v___x_3984_, v___x_3985_);
v___x_3987_ = ((size_t)1ULL);
v___x_3988_ = lean_usize_add(v_i_3968_, v___x_3987_);
v___x_3989_ = lean_array_uset(v_bs_x27_3982_, v_i_3968_, v___x_3986_);
v_i_3968_ = v___x_3988_;
v_bs_3969_ = v___x_3989_;
goto _start;
}
else
{
lean_dec_ref(v_bs_3969_);
return v___x_3979_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(lean_object* v_as_3991_, size_t v_sz_3992_, size_t v_i_3993_, lean_object* v_b_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
uint8_t v___x_3999_; 
v___x_3999_ = lean_usize_dec_lt(v_i_3993_, v_sz_3992_);
if (v___x_3999_ == 0)
{
lean_object* v___x_4000_; 
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v_b_3994_);
return v___x_4000_;
}
else
{
lean_object* v_a_4001_; size_t v_sz_4002_; size_t v___x_4003_; lean_object* v___x_4004_; 
v_a_4001_ = lean_array_uget_borrowed(v_as_3991_, v_i_3993_);
v_sz_4002_ = lean_array_size(v_a_4001_);
v___x_4003_ = ((size_t)0ULL);
lean_inc(v_a_4001_);
v___x_4004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4002_, v___x_4003_, v_a_4001_, v___y_3995_, v___y_3996_, v___y_3997_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v_fst_4006_; lean_object* v_snd_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4028_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
v_fst_4006_ = lean_ctor_get(v_b_3994_, 0);
v_snd_4007_ = lean_ctor_get(v_b_3994_, 1);
v_isSharedCheck_4028_ = !lean_is_exclusive(v_b_3994_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4009_ = v_b_3994_;
v_isShared_4010_ = v_isSharedCheck_4028_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_snd_4007_);
lean_inc(v_fst_4006_);
lean_dec(v_b_3994_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4028_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4023_; 
v___x_4011_ = lean_unsigned_to_nat(1u);
lean_inc(v_snd_4007_);
v___x_4012_ = l_Nat_reprFast(v_snd_4007_);
v___x_4013_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_4014_ = lean_string_append(v___x_4012_, v___x_4013_);
v___x_4015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4016_ = lean_string_utf8_byte_size(v___x_4014_);
v___x_4017_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(v___x_4016_, v___x_4015_);
v___x_4018_ = l_Lean_Doc_joinBlocks(v_a_4005_);
lean_dec(v_a_4005_);
v___x_4019_ = l_Lean_Doc_prefixListLines(v___x_4014_, v___x_4017_, v___x_4018_);
v___x_4020_ = lean_array_push(v_fst_4006_, v___x_4019_);
v___x_4021_ = lean_nat_add(v_snd_4007_, v___x_4011_);
lean_dec(v_snd_4007_);
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 1, v___x_4021_);
lean_ctor_set(v___x_4009_, 0, v___x_4020_);
v___x_4023_ = v___x_4009_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4020_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v___x_4021_);
v___x_4023_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
size_t v___x_4024_; size_t v___x_4025_; 
v___x_4024_ = ((size_t)1ULL);
v___x_4025_ = lean_usize_add(v_i_3993_, v___x_4024_);
v_i_3993_ = v___x_4025_;
v_b_3994_ = v___x_4023_;
goto _start;
}
}
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec_ref(v_b_3994_);
v_a_4029_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4004_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4004_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(size_t v_sz_4037_, size_t v_i_4038_, lean_object* v_bs_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
uint8_t v___x_4044_; 
v___x_4044_ = lean_usize_dec_lt(v_i_4038_, v_sz_4037_);
if (v___x_4044_ == 0)
{
lean_object* v___x_4045_; 
v___x_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4045_, 0, v_bs_4039_);
return v___x_4045_;
}
else
{
lean_object* v_v_4046_; lean_object* v___x_4047_; lean_object* v_term_4048_; lean_object* v_desc_4049_; lean_object* v___x_4050_; lean_object* v_bs_x27_4051_; lean_object* v_a_4053_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v_v_4046_ = lean_array_uget_borrowed(v_bs_4039_, v_i_4038_);
v___x_4047_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_4048_ = lean_ctor_get(v_v_4046_, 0);
lean_inc_ref(v_term_4048_);
v_desc_4049_ = lean_ctor_get(v_v_4046_, 1);
lean_inc_ref(v_desc_4049_);
v___x_4050_ = lean_unsigned_to_nat(0u);
v_bs_x27_4051_ = lean_array_uset(v_bs_4039_, v_i_4038_, v___x_4050_);
v___x_4058_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4058_, 0, v_term_4048_);
v___x_4059_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4047_, v___x_4058_, v___y_4040_, v___y_4041_, v___y_4042_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; size_t v_sz_4061_; size_t v___x_4062_; lean_object* v___x_4063_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_a_4060_);
lean_dec_ref_known(v___x_4059_, 1);
v_sz_4061_ = lean_array_size(v_desc_4049_);
v___x_4062_ = ((size_t)0ULL);
lean_inc_ref(v_desc_4049_);
v___x_4063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4061_, v___x_4062_, v_desc_4049_, v___y_4040_, v___y_4041_, v___y_4042_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___y_4066_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; uint8_t v___x_4079_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4063_, 1);
v___x_4070_ = lean_unsigned_to_nat(1u);
v___x_4071_ = lean_mk_empty_array_with_capacity(v___x_4070_);
v___x_4072_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_4073_ = lean_unsigned_to_nat(2u);
v___x_4074_ = lean_mk_empty_array_with_capacity(v___x_4073_);
v___x_4075_ = lean_array_push(v___x_4074_, v_a_4060_);
v___x_4076_ = lean_array_push(v___x_4075_, v___x_4072_);
v___x_4077_ = l_Lean_Doc_joinInlines(v___x_4076_);
lean_dec_ref(v___x_4076_);
v___x_4078_ = lean_array_get_size(v_desc_4049_);
lean_dec_ref(v_desc_4049_);
v___x_4079_ = lean_nat_dec_le(v___x_4078_, v___x_4070_);
if (v___x_4079_ == 0)
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4080_ = lean_array_push(v___x_4071_, v___x_4077_);
v___x_4081_ = l_Array_append___redArg(v___x_4080_, v_a_4064_);
lean_dec(v_a_4064_);
v___x_4082_ = l_Lean_Doc_joinBlocks(v___x_4081_);
lean_dec_ref(v___x_4081_);
v___y_4066_ = v___x_4082_;
goto v___jp_4065_;
}
else
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
lean_dec_ref(v___x_4071_);
v___x_4083_ = l_Lean_Doc_joinBlocks(v_a_4064_);
lean_dec(v_a_4064_);
v___x_4084_ = l_Array_append___redArg(v___x_4077_, v___x_4083_);
lean_dec_ref(v___x_4083_);
v___y_4066_ = v___x_4084_;
goto v___jp_4065_;
}
v___jp_4065_:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4067_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_4068_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_4069_ = l_Lean_Doc_prefixListLines(v___x_4067_, v___x_4068_, v___y_4066_);
v_a_4053_ = v___x_4069_;
goto v___jp_4052_;
}
}
else
{
lean_dec(v_a_4060_);
lean_dec_ref(v_bs_x27_4051_);
lean_dec_ref(v_desc_4049_);
return v___x_4063_;
}
}
else
{
lean_dec_ref(v_desc_4049_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4085_; 
v_a_4085_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v___x_4059_, 1);
v_a_4053_ = v_a_4085_;
goto v___jp_4052_;
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec_ref(v_bs_x27_4051_);
v_a_4086_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4059_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4059_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
v___jp_4052_:
{
size_t v___x_4054_; size_t v___x_4055_; lean_object* v___x_4056_; 
v___x_4054_ = ((size_t)1ULL);
v___x_4055_ = lean_usize_add(v_i_4038_, v___x_4054_);
v___x_4056_ = lean_array_uset(v_bs_x27_4051_, v_i_4038_, v_a_4053_);
v_i_4038_ = v___x_4055_;
v_bs_4039_ = v___x_4056_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed(lean_object* v_x_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_x_4094_, v_a_4095_, v_a_4096_, v_a_4097_);
lean_dec(v_a_4097_);
lean_dec_ref(v_a_4096_);
lean_dec(v_a_4095_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed(lean_object* v_sz_4102_, lean_object* v___x_4103_, lean_object* v_content_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
size_t v_sz_boxed_4109_; size_t v___x_4817__boxed_4110_; lean_object* v_res_4111_; 
v_sz_boxed_4109_ = lean_unbox_usize(v_sz_4102_);
lean_dec(v_sz_4102_);
v___x_4817__boxed_4110_ = lean_unbox_usize(v___x_4103_);
lean_dec(v___x_4103_);
v_res_4111_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(v_sz_boxed_4109_, v___x_4817__boxed_4110_, v_content_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(lean_object* v_x_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
switch(lean_obj_tag(v_x_4112_))
{
case 0:
{
lean_object* v_contents_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4126_; 
v_contents_4117_ = lean_ctor_get(v_x_4112_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v_x_4112_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4119_ = v_x_4112_;
v_isShared_4120_ = v_isSharedCheck_4126_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_contents_4117_);
lean_dec(v_x_4112_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4126_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4121_; lean_object* v___x_4123_; 
v___x_4121_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_4120_ == 0)
{
lean_ctor_set_tag(v___x_4119_, 9);
v___x_4123_ = v___x_4119_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_contents_4117_);
v___x_4123_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4124_; 
v___x_4124_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4121_, v___x_4123_, v_a_4113_, v_a_4114_, v_a_4115_);
return v___x_4124_;
}
}
}
case 1:
{
lean_object* v_content_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4135_; 
v_content_4127_ = lean_ctor_get(v_x_4112_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_x_4112_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4129_ = v_x_4112_;
v_isShared_4130_ = v_isSharedCheck_4135_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_content_4127_);
lean_dec(v_x_4112_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4135_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4131_; lean_object* v___x_4133_; 
v___x_4131_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_4127_);
if (v_isShared_4130_ == 0)
{
lean_ctor_set_tag(v___x_4129_, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4131_);
v___x_4133_ = v___x_4129_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
case 2:
{
lean_object* v_items_4136_; size_t v_sz_4137_; size_t v___x_4138_; lean_object* v___x_4139_; 
v_items_4136_ = lean_ctor_get(v_x_4112_, 0);
lean_inc_ref(v_items_4136_);
lean_dec_ref_known(v_x_4112_, 1);
v_sz_4137_ = lean_array_size(v_items_4136_);
v___x_4138_ = ((size_t)0ULL);
v___x_4139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_4137_, v___x_4138_, v_items_4136_, v_a_4113_, v_a_4114_, v_a_4115_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4148_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4142_ = v___x_4139_;
v_isShared_4143_ = v_isSharedCheck_4148_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4139_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4148_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4144_; lean_object* v___x_4146_; 
v___x_4144_ = l_Lean_Doc_joinBlocks(v_a_4140_);
lean_dec(v_a_4140_);
if (v_isShared_4143_ == 0)
{
lean_ctor_set(v___x_4142_, 0, v___x_4144_);
v___x_4146_ = v___x_4142_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4144_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
v_a_4149_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4139_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4139_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
case 3:
{
lean_object* v_start_4157_; lean_object* v_items_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4192_; 
v_start_4157_ = lean_ctor_get(v_x_4112_, 0);
v_items_4158_ = lean_ctor_get(v_x_4112_, 1);
v_isSharedCheck_4192_ = !lean_is_exclusive(v_x_4112_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4160_ = v_x_4112_;
v_isShared_4161_ = v_isSharedCheck_4192_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_items_4158_);
lean_inc(v_start_4157_);
lean_dec(v_x_4112_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4192_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v_out_4162_; lean_object* v___y_4164_; lean_object* v___x_4189_; lean_object* v___x_4190_; uint8_t v___x_4191_; 
v_out_4162_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_4189_ = lean_unsigned_to_nat(1u);
v___x_4190_ = l_Int_toNat(v_start_4157_);
lean_dec(v_start_4157_);
v___x_4191_ = lean_nat_dec_le(v___x_4189_, v___x_4190_);
if (v___x_4191_ == 0)
{
lean_dec(v___x_4190_);
v___y_4164_ = v___x_4189_;
goto v___jp_4163_;
}
else
{
v___y_4164_ = v___x_4190_;
goto v___jp_4163_;
}
v___jp_4163_:
{
lean_object* v___x_4166_; 
if (v_isShared_4161_ == 0)
{
lean_ctor_set_tag(v___x_4160_, 0);
lean_ctor_set(v___x_4160_, 1, v___y_4164_);
lean_ctor_set(v___x_4160_, 0, v_out_4162_);
v___x_4166_ = v___x_4160_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_out_4162_);
lean_ctor_set(v_reuseFailAlloc_4188_, 1, v___y_4164_);
v___x_4166_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
size_t v_sz_4167_; size_t v___x_4168_; lean_object* v___x_4169_; 
v_sz_4167_ = lean_array_size(v_items_4158_);
v___x_4168_ = ((size_t)0ULL);
v___x_4169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_items_4158_, v_sz_4167_, v___x_4168_, v___x_4166_, v_a_4113_, v_a_4114_, v_a_4115_);
lean_dec_ref(v_items_4158_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4179_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4172_ = v___x_4169_;
v_isShared_4173_ = v_isSharedCheck_4179_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4169_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4179_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v_fst_4174_; lean_object* v___x_4175_; lean_object* v___x_4177_; 
v_fst_4174_ = lean_ctor_get(v_a_4170_, 0);
lean_inc(v_fst_4174_);
lean_dec(v_a_4170_);
v___x_4175_ = l_Lean_Doc_joinBlocks(v_fst_4174_);
lean_dec(v_fst_4174_);
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 0, v___x_4175_);
v___x_4177_ = v___x_4172_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4175_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
v_a_4180_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4169_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4169_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_4193_; size_t v_sz_4194_; size_t v___x_4195_; lean_object* v___x_4196_; 
v_items_4193_ = lean_ctor_get(v_x_4112_, 0);
lean_inc_ref(v_items_4193_);
lean_dec_ref_known(v_x_4112_, 1);
v_sz_4194_ = lean_array_size(v_items_4193_);
v___x_4195_ = ((size_t)0ULL);
v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_4194_, v___x_4195_, v_items_4193_, v_a_4113_, v_a_4114_, v_a_4115_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4205_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4199_ = v___x_4196_;
v_isShared_4200_ = v_isSharedCheck_4205_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4196_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4205_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4201_; lean_object* v___x_4203_; 
v___x_4201_ = l_Lean_Doc_joinBlocks(v_a_4197_);
lean_dec(v_a_4197_);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v___x_4201_);
v___x_4203_ = v___x_4199_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v___x_4201_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
v_a_4206_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4196_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4196_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
case 5:
{
lean_object* v_items_4214_; size_t v_sz_4215_; size_t v___x_4216_; lean_object* v___x_4217_; 
v_items_4214_ = lean_ctor_get(v_x_4112_, 0);
lean_inc_ref(v_items_4214_);
lean_dec_ref_known(v_x_4112_, 1);
v_sz_4215_ = lean_array_size(v_items_4214_);
v___x_4216_ = ((size_t)0ULL);
v___x_4217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4215_, v___x_4216_, v_items_4214_, v_a_4113_, v_a_4114_, v_a_4115_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4228_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4220_ = v___x_4217_;
v_isShared_4221_ = v_isSharedCheck_4228_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4217_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4228_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4226_; 
v___x_4222_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_4223_ = l_Lean_Doc_joinBlocks(v_a_4218_);
lean_dec(v_a_4218_);
v___x_4224_ = l_Lean_Doc_prefixLines(v___x_4222_, v___x_4223_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v___x_4224_);
v___x_4226_ = v___x_4220_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4224_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
v_a_4229_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4217_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4217_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
case 6:
{
lean_object* v_content_4237_; size_t v_sz_4238_; size_t v___x_4239_; lean_object* v___x_4240_; 
v_content_4237_ = lean_ctor_get(v_x_4112_, 0);
lean_inc_ref(v_content_4237_);
lean_dec_ref_known(v_x_4112_, 1);
v_sz_4238_ = lean_array_size(v_content_4237_);
v___x_4239_ = ((size_t)0ULL);
v___x_4240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4238_, v___x_4239_, v_content_4237_, v_a_4113_, v_a_4114_, v_a_4115_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4249_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4243_ = v___x_4240_;
v_isShared_4244_ = v_isSharedCheck_4249_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4240_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4249_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4245_; lean_object* v___x_4247_; 
v___x_4245_ = l_Lean_Doc_joinBlocks(v_a_4241_);
lean_dec(v_a_4241_);
if (v_isShared_4244_ == 0)
{
lean_ctor_set(v___x_4243_, 0, v___x_4245_);
v___x_4247_ = v___x_4243_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4245_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
v_a_4250_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4240_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4240_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
default: 
{
lean_object* v_container_4258_; 
v_container_4258_ = lean_ctor_get(v_x_4112_, 0);
if (lean_obj_tag(v_container_4258_) == 0)
{
lean_object* v_content_4259_; lean_object* v_val_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
lean_inc_ref(v_container_4258_);
v_content_4259_ = lean_ctor_get(v_x_4112_, 1);
lean_inc_ref(v_content_4259_);
lean_dec_ref_known(v_x_4112_, 2);
v_val_4260_ = lean_ctor_get(v_container_4258_, 0);
lean_inc(v_val_4260_);
lean_dec_ref_known(v_container_4258_, 1);
v___x_4261_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_4260_);
v___x_4262_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_4261_, v_a_4114_, v_a_4115_);
lean_dec(v___x_4261_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
if (lean_obj_tag(v_a_4263_) == 0)
{
size_t v_sz_4264_; size_t v___x_4265_; lean_object* v___x_4266_; 
lean_dec(v_val_4260_);
v_sz_4264_ = lean_array_size(v_content_4259_);
v___x_4265_ = ((size_t)0ULL);
v___x_4266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4264_, v___x_4265_, v_content_4259_, v_a_4113_, v_a_4114_, v_a_4115_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4275_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4269_ = v___x_4266_;
v_isShared_4270_ = v_isSharedCheck_4275_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4266_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4275_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4271_; lean_object* v___x_4273_; 
v___x_4271_ = l_Lean_Doc_joinBlocks(v_a_4267_);
lean_dec(v_a_4267_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 0, v___x_4271_);
v___x_4273_ = v___x_4269_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4271_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
else
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
v_a_4276_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4266_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4266_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
else
{
lean_object* v_val_4284_; lean_object* v___f_4285_; lean_object* v___f_4286_; size_t v_sz_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v_fallback_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v_val_4284_ = lean_ctor_get(v_a_4263_, 0);
lean_inc(v_val_4284_);
lean_dec_ref_known(v_a_4263_, 1);
v___f_4285_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed), 5, 0);
v___f_4286_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___closed__0));
v_sz_4287_ = lean_array_size(v_content_4259_);
v___x_4288_ = lean_box_usize(v_sz_4287_);
v___x_4289_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
lean_inc_ref(v_content_4259_);
v_fallback_4290_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_fallback_4290_, 0, v___x_4288_);
lean_closure_set(v_fallback_4290_, 1, v___x_4289_);
lean_closure_set(v_fallback_4290_, 2, v_content_4259_);
v___x_4291_ = lean_apply_4(v_val_4284_, v___f_4286_, v___f_4285_, v_val_4260_, v_content_4259_);
v___x_4292_ = l_Lean_Doc_withRendererFallback(v_fallback_4290_, v___x_4291_, v_a_4113_, v_a_4114_, v_a_4115_);
return v___x_4292_;
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec(v_val_4260_);
lean_dec_ref(v_content_4259_);
v_a_4293_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4262_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4262_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
else
{
lean_object* v_content_4301_; size_t v_sz_4302_; size_t v___x_4303_; lean_object* v___x_4304_; 
v_content_4301_ = lean_ctor_get(v_x_4112_, 1);
lean_inc_ref(v_content_4301_);
lean_dec_ref_known(v_x_4112_, 2);
v_sz_4302_ = lean_array_size(v_content_4301_);
v___x_4303_ = ((size_t)0ULL);
v___x_4304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4302_, v___x_4303_, v_content_4301_, v_a_4113_, v_a_4114_, v_a_4115_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4313_; 
v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4307_ = v___x_4304_;
v_isShared_4308_ = v_isSharedCheck_4313_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4304_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4313_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4309_; lean_object* v___x_4311_; 
v___x_4309_ = l_Lean_Doc_joinBlocks(v_a_4305_);
lean_dec(v_a_4305_);
if (v_isShared_4308_ == 0)
{
lean_ctor_set(v___x_4307_, 0, v___x_4309_);
v___x_4311_ = v___x_4307_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4309_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
v_a_4314_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4304_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4304_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(size_t v_sz_4322_, size_t v_i_4323_, lean_object* v_bs_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
uint8_t v___x_4329_; 
v___x_4329_ = lean_usize_dec_lt(v_i_4323_, v_sz_4322_);
if (v___x_4329_ == 0)
{
lean_object* v___x_4330_; 
v___x_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4330_, 0, v_bs_4324_);
return v___x_4330_;
}
else
{
lean_object* v_v_4331_; lean_object* v___x_4332_; 
v_v_4331_ = lean_array_uget_borrowed(v_bs_4324_, v_i_4323_);
lean_inc(v_v_4331_);
v___x_4332_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_v_4331_, v___y_4325_, v___y_4326_, v___y_4327_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v___x_4334_; lean_object* v_bs_x27_4335_; size_t v___x_4336_; size_t v___x_4337_; lean_object* v___x_4338_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_a_4333_);
lean_dec_ref_known(v___x_4332_, 1);
v___x_4334_ = lean_unsigned_to_nat(0u);
v_bs_x27_4335_ = lean_array_uset(v_bs_4324_, v_i_4323_, v___x_4334_);
v___x_4336_ = ((size_t)1ULL);
v___x_4337_ = lean_usize_add(v_i_4323_, v___x_4336_);
v___x_4338_ = lean_array_uset(v_bs_x27_4335_, v_i_4323_, v_a_4333_);
v_i_4323_ = v___x_4337_;
v_bs_4324_ = v___x_4338_;
goto _start;
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
lean_dec_ref(v_bs_4324_);
v_a_4340_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4332_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4332_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(size_t v_sz_4348_, size_t v___x_4349_, lean_object* v_content_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
lean_object* v___x_4355_; 
v___x_4355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4348_, v___x_4349_, v_content_4350_, v___y_4351_, v___y_4352_, v___y_4353_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4364_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4358_ = v___x_4355_;
v_isShared_4359_ = v_isSharedCheck_4364_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4355_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4364_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4360_; lean_object* v___x_4362_; 
v___x_4360_ = l_Lean_Doc_joinBlocks(v_a_4356_);
lean_dec(v_a_4356_);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 0, v___x_4360_);
v___x_4362_ = v___x_4358_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4360_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
v_a_4365_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4355_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4355_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2___boxed(lean_object* v_sz_4373_, lean_object* v_i_4374_, lean_object* v_bs_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_){
_start:
{
size_t v_sz_boxed_4380_; size_t v_i_boxed_4381_; lean_object* v_res_4382_; 
v_sz_boxed_4380_ = lean_unbox_usize(v_sz_4373_);
lean_dec(v_sz_4373_);
v_i_boxed_4381_ = lean_unbox_usize(v_i_4374_);
lean_dec(v_i_4374_);
v_res_4382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_boxed_4380_, v_i_boxed_4381_, v_bs_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4376_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5___boxed(lean_object* v_sz_4383_, lean_object* v_i_4384_, lean_object* v_bs_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
size_t v_sz_boxed_4390_; size_t v_i_boxed_4391_; lean_object* v_res_4392_; 
v_sz_boxed_4390_ = lean_unbox_usize(v_sz_4383_);
lean_dec(v_sz_4383_);
v_i_boxed_4391_ = lean_unbox_usize(v_i_4384_);
lean_dec(v_i_4384_);
v_res_4392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_boxed_4390_, v_i_boxed_4391_, v_bs_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
lean_dec(v___y_4386_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7___boxed(lean_object* v_as_4393_, lean_object* v_sz_4394_, lean_object* v_i_4395_, lean_object* v_b_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
size_t v_sz_boxed_4401_; size_t v_i_boxed_4402_; lean_object* v_res_4403_; 
v_sz_boxed_4401_ = lean_unbox_usize(v_sz_4394_);
lean_dec(v_sz_4394_);
v_i_boxed_4402_ = lean_unbox_usize(v_i_4395_);
lean_dec(v_i_4395_);
v_res_4403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_as_4393_, v_sz_boxed_4401_, v_i_boxed_4402_, v_b_4396_, v___y_4397_, v___y_4398_, v___y_4399_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
lean_dec(v___y_4397_);
lean_dec_ref(v_as_4393_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8___boxed(lean_object* v_sz_4404_, lean_object* v_i_4405_, lean_object* v_bs_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
size_t v_sz_boxed_4411_; size_t v_i_boxed_4412_; lean_object* v_res_4413_; 
v_sz_boxed_4411_ = lean_unbox_usize(v_sz_4404_);
lean_dec(v_sz_4404_);
v_i_boxed_4412_ = lean_unbox_usize(v_i_4405_);
lean_dec(v_i_4405_);
v_res_4413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_boxed_4411_, v_i_boxed_4412_, v_bs_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(size_t v_sz_4414_, size_t v_i_4415_, lean_object* v_bs_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
uint8_t v___x_4421_; 
v___x_4421_ = lean_usize_dec_lt(v_i_4415_, v_sz_4414_);
if (v___x_4421_ == 0)
{
lean_object* v___x_4422_; 
v___x_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4422_, 0, v_bs_4416_);
return v___x_4422_;
}
else
{
lean_object* v_v_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v_v_4423_ = lean_array_uget_borrowed(v_bs_4416_, v_i_4415_);
v___x_4424_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc(v_v_4423_);
v___x_4425_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4424_, v_v_4423_, v___y_4417_, v___y_4418_, v___y_4419_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4427_; lean_object* v_bs_x27_4428_; size_t v___x_4429_; size_t v___x_4430_; lean_object* v___x_4431_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4426_);
lean_dec_ref_known(v___x_4425_, 1);
v___x_4427_ = lean_unsigned_to_nat(0u);
v_bs_x27_4428_ = lean_array_uset(v_bs_4416_, v_i_4415_, v___x_4427_);
v___x_4429_ = ((size_t)1ULL);
v___x_4430_ = lean_usize_add(v_i_4415_, v___x_4429_);
v___x_4431_ = lean_array_uset(v_bs_x27_4428_, v_i_4415_, v_a_4426_);
v_i_4415_ = v___x_4430_;
v_bs_4416_ = v___x_4431_;
goto _start;
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec_ref(v_bs_4416_);
v_a_4433_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4425_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4425_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1___boxed(lean_object* v_sz_4441_, lean_object* v_i_4442_, lean_object* v_bs_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
size_t v_sz_boxed_4448_; size_t v_i_boxed_4449_; lean_object* v_res_4450_; 
v_sz_boxed_4448_ = lean_unbox_usize(v_sz_4441_);
lean_dec(v_sz_4441_);
v_i_boxed_4449_ = lean_unbox_usize(v_i_4442_);
lean_dec(v_i_4442_);
v_res_4450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_boxed_4448_, v_i_boxed_4449_, v_bs_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(lean_object* v_x_4451_, lean_object* v_x_4452_){
_start:
{
lean_object* v_zero_4453_; uint8_t v_isZero_4454_; 
v_zero_4453_ = lean_unsigned_to_nat(0u);
v_isZero_4454_ = lean_nat_dec_eq(v_x_4451_, v_zero_4453_);
if (v_isZero_4454_ == 1)
{
lean_dec(v_x_4451_);
return v_x_4452_;
}
else
{
uint32_t v___x_4455_; lean_object* v_one_4456_; lean_object* v_n_4457_; lean_object* v___x_4458_; 
v___x_4455_ = 35;
v_one_4456_ = lean_unsigned_to_nat(1u);
v_n_4457_ = lean_nat_sub(v_x_4451_, v_one_4456_);
lean_dec(v_x_4451_);
v___x_4458_ = lean_string_push(v_x_4452_, v___x_4455_);
v_x_4451_ = v_n_4457_;
v_x_4452_ = v___x_4458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(lean_object* v_level_4460_, lean_object* v_part_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v_title_4466_; lean_object* v_content_4467_; lean_object* v_subParts_4468_; size_t v_sz_4469_; size_t v___x_4470_; lean_object* v___x_4471_; 
v_title_4466_ = lean_ctor_get(v_part_4461_, 0);
lean_inc_ref(v_title_4466_);
v_content_4467_ = lean_ctor_get(v_part_4461_, 3);
lean_inc_ref(v_content_4467_);
v_subParts_4468_ = lean_ctor_get(v_part_4461_, 4);
lean_inc_ref(v_subParts_4468_);
lean_dec_ref(v_part_4461_);
v_sz_4469_ = lean_array_size(v_title_4466_);
v___x_4470_ = ((size_t)0ULL);
v___x_4471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_4469_, v___x_4470_, v_title_4466_, v_a_4462_, v_a_4463_, v_a_4464_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v_a_4472_; size_t v_sz_4473_; lean_object* v___x_4474_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
lean_inc(v_a_4472_);
lean_dec_ref_known(v___x_4471_, 1);
v_sz_4473_ = lean_array_size(v_content_4467_);
v___x_4474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4473_, v___x_4470_, v_content_4467_, v_a_4462_, v_a_4463_, v_a_4464_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_a_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; size_t v_sz_4480_; lean_object* v___x_4481_; 
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
lean_dec_ref_known(v___x_4474_, 1);
v___x_4476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4477_ = lean_unsigned_to_nat(1u);
v___x_4478_ = lean_nat_add(v_level_4460_, v___x_4477_);
lean_inc(v___x_4478_);
v___x_4479_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(v___x_4478_, v___x_4476_);
v_sz_4480_ = lean_array_size(v_subParts_4468_);
v___x_4481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4478_, v_sz_4480_, v___x_4470_, v_subParts_4468_, v_a_4462_, v_a_4463_, v_a_4464_);
lean_dec(v___x_4478_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4500_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4484_ = v___x_4481_;
v_isShared_4485_ = v_isSharedCheck_4500_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4481_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4500_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4498_; 
v___x_4486_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_4487_ = lean_string_append(v___x_4479_, v___x_4486_);
v___x_4488_ = lean_mk_empty_array_with_capacity(v___x_4477_);
lean_inc_ref_n(v___x_4488_, 2);
v___x_4489_ = lean_array_push(v___x_4488_, v___x_4487_);
v___x_4490_ = lean_array_push(v___x_4488_, v___x_4489_);
v___x_4491_ = l_Array_append___redArg(v___x_4490_, v_a_4472_);
lean_dec(v_a_4472_);
v___x_4492_ = l_Lean_Doc_joinInlines(v___x_4491_);
lean_dec_ref(v___x_4491_);
v___x_4493_ = lean_array_push(v___x_4488_, v___x_4492_);
v___x_4494_ = l_Array_append___redArg(v___x_4493_, v_a_4475_);
lean_dec(v_a_4475_);
v___x_4495_ = l_Array_append___redArg(v___x_4494_, v_a_4482_);
lean_dec(v_a_4482_);
v___x_4496_ = l_Lean_Doc_joinBlocks(v___x_4495_);
lean_dec_ref(v___x_4495_);
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v___x_4496_);
v___x_4498_ = v___x_4484_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
lean_dec_ref(v___x_4479_);
lean_dec(v_a_4475_);
lean_dec(v_a_4472_);
v_a_4501_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4481_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4481_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
else
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
lean_dec(v_a_4472_);
lean_dec_ref(v_subParts_4468_);
v_a_4509_ = lean_ctor_get(v___x_4474_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4474_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4474_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4509_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4524_; 
lean_dec_ref(v_subParts_4468_);
lean_dec_ref(v_content_4467_);
v_a_4517_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4519_ = v___x_4471_;
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4471_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4522_; 
if (v_isShared_4520_ == 0)
{
v___x_4522_ = v___x_4519_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(lean_object* v___x_4525_, size_t v_sz_4526_, size_t v_i_4527_, lean_object* v_bs_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
uint8_t v___x_4533_; 
v___x_4533_ = lean_usize_dec_lt(v_i_4527_, v_sz_4526_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4534_; 
v___x_4534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4534_, 0, v_bs_4528_);
return v___x_4534_;
}
else
{
lean_object* v_v_4535_; lean_object* v___x_4536_; 
v_v_4535_ = lean_array_uget_borrowed(v_bs_4528_, v_i_4527_);
lean_inc(v_v_4535_);
v___x_4536_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4525_, v_v_4535_, v___y_4529_, v___y_4530_, v___y_4531_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4538_; lean_object* v_bs_x27_4539_; size_t v___x_4540_; size_t v___x_4541_; lean_object* v___x_4542_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref_known(v___x_4536_, 1);
v___x_4538_ = lean_unsigned_to_nat(0u);
v_bs_x27_4539_ = lean_array_uset(v_bs_4528_, v_i_4527_, v___x_4538_);
v___x_4540_ = ((size_t)1ULL);
v___x_4541_ = lean_usize_add(v_i_4527_, v___x_4540_);
v___x_4542_ = lean_array_uset(v_bs_x27_4539_, v_i_4527_, v_a_4537_);
v_i_4527_ = v___x_4541_;
v_bs_4528_ = v___x_4542_;
goto _start;
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
lean_dec_ref(v_bs_4528_);
v_a_4544_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4536_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4536_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg___boxed(lean_object* v___x_4552_, lean_object* v_sz_4553_, lean_object* v_i_4554_, lean_object* v_bs_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
size_t v_sz_boxed_4560_; size_t v_i_boxed_4561_; lean_object* v_res_4562_; 
v_sz_boxed_4560_ = lean_unbox_usize(v_sz_4553_);
lean_dec(v_sz_4553_);
v_i_boxed_4561_ = lean_unbox_usize(v_i_4554_);
lean_dec(v_i_4554_);
v_res_4562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4552_, v_sz_boxed_4560_, v_i_boxed_4561_, v_bs_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec(v___x_4552_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg___boxed(lean_object* v_level_4563_, lean_object* v_part_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4563_, v_part_4564_, v_a_4565_, v_a_4566_, v_a_4567_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec(v_level_4563_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(size_t v_sz_4570_, size_t v_i_4571_, lean_object* v_bs_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
uint8_t v___x_4577_; 
v___x_4577_ = lean_usize_dec_lt(v_i_4571_, v_sz_4570_);
if (v___x_4577_ == 0)
{
lean_object* v___x_4578_; 
v___x_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4578_, 0, v_bs_4572_);
return v___x_4578_;
}
else
{
lean_object* v_v_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v_v_4579_ = lean_array_uget_borrowed(v_bs_4572_, v_i_4571_);
v___x_4580_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_4579_);
v___x_4581_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4580_, v_v_4579_, v___y_4573_, v___y_4574_, v___y_4575_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v_bs_x27_4583_; size_t v___x_4584_; size_t v___x_4585_; lean_object* v___x_4586_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
lean_inc(v_a_4582_);
lean_dec_ref_known(v___x_4581_, 1);
v_bs_x27_4583_ = lean_array_uset(v_bs_4572_, v_i_4571_, v___x_4580_);
v___x_4584_ = ((size_t)1ULL);
v___x_4585_ = lean_usize_add(v_i_4571_, v___x_4584_);
v___x_4586_ = lean_array_uset(v_bs_x27_4583_, v_i_4571_, v_a_4582_);
v_i_4571_ = v___x_4585_;
v_bs_4572_ = v___x_4586_;
goto _start;
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4595_; 
lean_dec_ref(v_bs_4572_);
v_a_4588_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v___x_4581_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4581_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4593_; 
if (v_isShared_4591_ == 0)
{
v___x_4593_ = v___x_4590_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3___boxed(lean_object* v_sz_4596_, lean_object* v_i_4597_, lean_object* v_bs_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
size_t v_sz_boxed_4603_; size_t v_i_boxed_4604_; lean_object* v_res_4605_; 
v_sz_boxed_4603_ = lean_unbox_usize(v_sz_4596_);
lean_dec(v_sz_4596_);
v_i_boxed_4604_ = lean_unbox_usize(v_i_4597_);
lean_dec(v_i_4597_);
v_res_4605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_boxed_4603_, v_i_boxed_4604_, v_bs_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec(v___y_4599_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0(lean_object* v_val_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v_text_4611_; lean_object* v_subsections_4612_; size_t v_sz_4613_; size_t v___x_4614_; lean_object* v___x_4615_; 
v_text_4611_ = lean_ctor_get(v_val_4606_, 0);
lean_inc_ref(v_text_4611_);
v_subsections_4612_ = lean_ctor_get(v_val_4606_, 1);
lean_inc_ref(v_subsections_4612_);
lean_dec_ref(v_val_4606_);
v_sz_4613_ = lean_array_size(v_text_4611_);
v___x_4614_ = ((size_t)0ULL);
v___x_4615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4613_, v___x_4614_, v_text_4611_, v___y_4607_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; size_t v_sz_4617_; lean_object* v___x_4618_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
lean_inc(v_a_4616_);
lean_dec_ref_known(v___x_4615_, 1);
v_sz_4617_ = lean_array_size(v_subsections_4612_);
v___x_4618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_4617_, v___x_4614_, v_subsections_4612_, v___y_4607_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4628_; 
v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4621_ = v___x_4618_;
v_isShared_4622_ = v_isSharedCheck_4628_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v___x_4618_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4628_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4626_; 
v___x_4623_ = l_Array_append___redArg(v_a_4616_, v_a_4619_);
lean_dec(v_a_4619_);
v___x_4624_ = l_Lean_Doc_joinBlocks(v___x_4623_);
lean_dec_ref(v___x_4623_);
if (v_isShared_4622_ == 0)
{
lean_ctor_set(v___x_4621_, 0, v___x_4624_);
v___x_4626_ = v___x_4621_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4624_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4636_; 
lean_dec(v_a_4616_);
v_a_4629_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4631_ = v___x_4618_;
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4618_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4634_; 
if (v_isShared_4632_ == 0)
{
v___x_4634_ = v___x_4631_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
lean_dec_ref(v_subsections_4612_);
v_a_4637_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4615_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4615_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0___boxed(lean_object* v_val_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l_Lean_findSimpleDocString_x3f___lam__0(v_val_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
lean_dec(v___y_4646_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_4651_, lean_object* v_declName_4652_, uint8_t v_includeBuiltin_4653_, lean_object* v_options_4654_, lean_object* v_currNamespace_4655_, lean_object* v_openDecls_4656_, lean_object* v_cancelTk_x3f_4657_){
_start:
{
lean_object* v___x_4659_; 
lean_inc_ref(v_env_4651_);
v___x_4659_ = l_Lean_findInternalDocString_x3f(v_env_4651_, v_declName_4652_, v_includeBuiltin_4653_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4703_; 
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4662_ = v___x_4659_;
v_isShared_4663_ = v_isSharedCheck_4703_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4659_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4703_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
if (lean_obj_tag(v_a_4660_) == 0)
{
lean_object* v___x_4664_; lean_object* v___x_4666_; 
lean_dec(v_cancelTk_x3f_4657_);
lean_dec(v_openDecls_4656_);
lean_dec(v_currNamespace_4655_);
lean_dec_ref(v_options_4654_);
lean_dec_ref(v_env_4651_);
v___x_4664_ = lean_box(0);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 0, v___x_4664_);
v___x_4666_ = v___x_4662_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v___x_4664_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
return v___x_4666_;
}
}
else
{
lean_object* v_val_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4702_; 
v_val_4668_ = lean_ctor_get(v_a_4660_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v_a_4660_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4670_ = v_a_4660_;
v_isShared_4671_ = v_isSharedCheck_4702_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_val_4668_);
lean_dec(v_a_4660_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4702_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
if (lean_obj_tag(v_val_4668_) == 0)
{
lean_object* v_val_4672_; lean_object* v___x_4674_; 
lean_dec(v_cancelTk_x3f_4657_);
lean_dec(v_openDecls_4656_);
lean_dec(v_currNamespace_4655_);
lean_dec_ref(v_options_4654_);
lean_dec_ref(v_env_4651_);
v_val_4672_ = lean_ctor_get(v_val_4668_, 0);
lean_inc(v_val_4672_);
lean_dec_ref_known(v_val_4668_, 1);
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 0, v_val_4672_);
v___x_4674_ = v___x_4670_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_val_4672_);
v___x_4674_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
lean_object* v___x_4676_; 
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 0, v___x_4674_);
v___x_4676_ = v___x_4662_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v___x_4674_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
else
{
lean_object* v_val_4679_; lean_object* v___f_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; 
lean_del_object(v___x_4662_);
v_val_4679_ = lean_ctor_get(v_val_4668_, 0);
lean_inc(v_val_4679_);
lean_dec_ref_known(v_val_4668_, 1);
v___f_4680_ = lean_alloc_closure((void*)(l_Lean_findSimpleDocString_x3f___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4680_, 0, v_val_4679_);
v___x_4681_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_4681_, 0, v___f_4680_);
v___x_4682_ = l_Lean_Doc_runMarkdown___redArg(v_env_4651_, v___x_4681_, v_options_4654_, v_currNamespace_4655_, v_openDecls_4656_, v_cancelTk_x3f_4657_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4693_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4685_ = v___x_4682_;
v_isShared_4686_ = v_isSharedCheck_4693_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4682_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4693_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 0, v_a_4683_);
v___x_4688_ = v___x_4670_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
lean_object* v___x_4690_; 
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 0, v___x_4688_);
v___x_4690_ = v___x_4685_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4688_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
}
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_del_object(v___x_4670_);
v_a_4694_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4682_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4682_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
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
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4711_; 
lean_dec(v_cancelTk_x3f_4657_);
lean_dec(v_openDecls_4656_);
lean_dec(v_currNamespace_4655_);
lean_dec_ref(v_options_4654_);
lean_dec_ref(v_env_4651_);
v_a_4704_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4706_ = v___x_4659_;
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4659_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4707_ == 0)
{
v___x_4709_ = v___x_4706_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_a_4704_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_4712_, lean_object* v_declName_4713_, lean_object* v_includeBuiltin_4714_, lean_object* v_options_4715_, lean_object* v_currNamespace_4716_, lean_object* v_openDecls_4717_, lean_object* v_cancelTk_x3f_4718_, lean_object* v_a_4719_){
_start:
{
uint8_t v_includeBuiltin_boxed_4720_; lean_object* v_res_4721_; 
v_includeBuiltin_boxed_4720_ = lean_unbox(v_includeBuiltin_4714_);
v_res_4721_ = l_Lean_findSimpleDocString_x3f(v_env_4712_, v_declName_4713_, v_includeBuiltin_boxed_4720_, v_options_4715_, v_currNamespace_4716_, v_openDecls_4717_, v_cancelTk_x3f_4718_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(lean_object* v_p_4722_, lean_object* v_level_4723_, lean_object* v_part_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_){
_start:
{
lean_object* v___x_4729_; 
v___x_4729_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4723_, v_part_4724_, v_a_4725_, v_a_4726_, v_a_4727_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___boxed(lean_object* v_p_4730_, lean_object* v_level_4731_, lean_object* v_part_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(v_p_4730_, v_level_4731_, v_part_4732_, v_a_4733_, v_a_4734_, v_a_4735_);
lean_dec(v_a_4735_);
lean_dec_ref(v_a_4734_);
lean_dec(v_a_4733_);
lean_dec(v_level_4731_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(lean_object* v_p_4738_, lean_object* v___x_4739_, size_t v_sz_4740_, size_t v_i_4741_, lean_object* v_bs_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_){
_start:
{
lean_object* v___x_4747_; 
v___x_4747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4739_, v_sz_4740_, v_i_4741_, v_bs_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___boxed(lean_object* v_p_4748_, lean_object* v___x_4749_, lean_object* v_sz_4750_, lean_object* v_i_4751_, lean_object* v_bs_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_){
_start:
{
size_t v_sz_boxed_4757_; size_t v_i_boxed_4758_; lean_object* v_res_4759_; 
v_sz_boxed_4757_ = lean_unbox_usize(v_sz_4750_);
lean_dec(v_sz_4750_);
v_i_boxed_4758_ = lean_unbox_usize(v_i_4751_);
lean_dec(v_i_4751_);
v_res_4759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(v_p_4748_, v___x_4749_, v_sz_boxed_4757_, v_i_boxed_4758_, v_bs_4752_, v___y_4753_, v___y_4754_, v___y_4755_);
lean_dec(v___y_4755_);
lean_dec_ref(v___y_4754_);
lean_dec(v___y_4753_);
lean_dec(v___x_4749_);
return v_res_4759_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Markdown(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
