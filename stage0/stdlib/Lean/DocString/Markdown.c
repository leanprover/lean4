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
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(lean_object* v_rest_164_, lean_object* v_restTrim_165_, lean_object* v_head_166_, lean_object* v_headTrim_167_, lean_object* v_as_168_, lean_object* v_i_169_, lean_object* v_j_170_, lean_object* v_bs_171_){
_start:
{
lean_object* v_zero_172_; uint8_t v_isZero_173_; 
v_zero_172_ = lean_unsigned_to_nat(0u);
v_isZero_173_ = lean_nat_dec_eq(v_i_169_, v_zero_172_);
if (v_isZero_173_ == 1)
{
lean_dec(v_j_170_);
lean_dec(v_i_169_);
lean_dec_ref(v_headTrim_167_);
lean_dec_ref(v_head_166_);
lean_dec_ref(v_restTrim_165_);
lean_dec_ref(v_rest_164_);
return v_bs_171_;
}
else
{
lean_object* v_one_174_; lean_object* v_n_175_; lean_object* v___y_177_; lean_object* v___x_181_; lean_object* v_fst_183_; lean_object* v_snd_184_; uint8_t v___x_188_; 
v_one_174_ = lean_unsigned_to_nat(1u);
v_n_175_ = lean_nat_sub(v_i_169_, v_one_174_);
lean_dec(v_i_169_);
v___x_181_ = lean_array_fget_borrowed(v_as_168_, v_j_170_);
v___x_188_ = lean_nat_dec_eq(v_j_170_, v_zero_172_);
if (v___x_188_ == 0)
{
lean_inc_ref(v_restTrim_165_);
lean_inc_ref(v_rest_164_);
v_fst_183_ = v_rest_164_;
v_snd_184_ = v_restTrim_165_;
goto v___jp_182_;
}
else
{
lean_inc_ref(v_headTrim_167_);
lean_inc_ref(v_head_166_);
v_fst_183_ = v_head_166_;
v_snd_184_ = v_headTrim_167_;
goto v___jp_182_;
}
v___jp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_nat_add(v_j_170_, v_one_174_);
lean_dec(v_j_170_);
v___x_179_ = lean_array_push(v_bs_171_, v___y_177_);
v_i_169_ = v_n_175_;
v_j_170_ = v___x_178_;
v_bs_171_ = v___x_179_;
goto _start;
}
v___jp_182_:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = lean_string_utf8_byte_size(v___x_181_);
v___x_186_ = lean_nat_dec_eq(v___x_185_, v_zero_172_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_dec_ref(v_snd_184_);
v___x_187_ = lean_string_append(v_fst_183_, v___x_181_);
v___y_177_ = v___x_187_;
goto v___jp_176_;
}
else
{
lean_dec_ref(v_fst_183_);
v___y_177_ = v_snd_184_;
goto v___jp_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg___boxed(lean_object* v_rest_189_, lean_object* v_restTrim_190_, lean_object* v_head_191_, lean_object* v_headTrim_192_, lean_object* v_as_193_, lean_object* v_i_194_, lean_object* v_j_195_, lean_object* v_bs_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_189_, v_restTrim_190_, v_head_191_, v_headTrim_192_, v_as_193_, v_i_194_, v_j_195_, v_bs_196_);
lean_dec_ref(v_as_193_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_prefixListLines(lean_object* v_head_198_, lean_object* v_rest_199_, lean_object* v_lines_200_){
_start:
{
lean_object* v_headTrim_201_; lean_object* v_restTrim_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
lean_inc_ref(v_head_198_);
v_headTrim_201_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_head_198_);
lean_inc_ref(v_rest_199_);
v_restTrim_202_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_rest_199_);
v___x_203_ = lean_array_get_size(v_lines_200_);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_mk_empty_array_with_capacity(v___x_203_);
v___x_206_ = l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_199_, v_restTrim_202_, v_head_198_, v_headTrim_201_, v_lines_200_, v___x_203_, v___x_204_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_prefixListLines___boxed(lean_object* v_head_207_, lean_object* v_rest_208_, lean_object* v_lines_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Doc_prefixListLines(v_head_207_, v_rest_208_, v_lines_209_);
lean_dec_ref(v_lines_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0(lean_object* v_rest_211_, lean_object* v_restTrim_212_, lean_object* v_head_213_, lean_object* v_headTrim_214_, lean_object* v_as_215_, lean_object* v_i_216_, lean_object* v_j_217_, lean_object* v_inv_218_, lean_object* v_bs_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_211_, v_restTrim_212_, v_head_213_, v_headTrim_214_, v_as_215_, v_i_216_, v_j_217_, v_bs_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___boxed(lean_object* v_rest_221_, lean_object* v_restTrim_222_, lean_object* v_head_223_, lean_object* v_headTrim_224_, lean_object* v_as_225_, lean_object* v_i_226_, lean_object* v_j_227_, lean_object* v_inv_228_, lean_object* v_bs_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0(v_rest_221_, v_restTrim_222_, v_head_223_, v_headTrim_224_, v_as_225_, v_i_226_, v_j_227_, v_inv_228_, v_bs_229_);
lean_dec_ref(v_as_225_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(lean_object* v_as_232_, size_t v_i_233_, size_t v_stop_234_, lean_object* v_b_235_){
_start:
{
lean_object* v___y_237_; uint8_t v___x_241_; 
v___x_241_ = lean_usize_dec_eq(v_i_233_, v_stop_234_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_242_ = lean_array_uget_borrowed(v_as_232_, v_i_233_);
v___x_243_ = lean_array_get_size(v___x_242_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_dec_eq(v___x_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = lean_array_get_size(v_b_235_);
v___x_247_ = lean_nat_dec_eq(v___x_246_, v___x_244_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_249_ = lean_array_push(v_b_235_, v___x_248_);
v___x_250_ = l_Array_append___redArg(v___x_249_, v___x_242_);
v___y_237_ = v___x_250_;
goto v___jp_236_;
}
else
{
lean_dec_ref(v_b_235_);
lean_inc(v___x_242_);
v___y_237_ = v___x_242_;
goto v___jp_236_;
}
}
else
{
v___y_237_ = v_b_235_;
goto v___jp_236_;
}
}
else
{
return v_b_235_;
}
v___jp_236_:
{
size_t v___x_238_; size_t v___x_239_; 
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_add(v_i_233_, v___x_238_);
v_i_233_ = v___x_239_;
v_b_235_ = v___y_237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___boxed(lean_object* v_as_251_, lean_object* v_i_252_, lean_object* v_stop_253_, lean_object* v_b_254_){
_start:
{
size_t v_i_boxed_255_; size_t v_stop_boxed_256_; lean_object* v_res_257_; 
v_i_boxed_255_ = lean_unbox_usize(v_i_252_);
lean_dec(v_i_252_);
v_stop_boxed_256_ = lean_unbox_usize(v_stop_253_);
lean_dec(v_stop_253_);
v_res_257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_as_251_, v_i_boxed_255_, v_stop_boxed_256_, v_b_254_);
lean_dec_ref(v_as_251_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks(lean_object* v_blocks_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_263_ = lean_array_get_size(v_blocks_260_);
v___x_264_ = lean_nat_dec_lt(v___x_261_, v___x_263_);
if (v___x_264_ == 0)
{
return v___x_262_;
}
else
{
uint8_t v___x_265_; 
v___x_265_ = lean_nat_dec_le(v___x_263_, v___x_263_);
if (v___x_265_ == 0)
{
if (v___x_264_ == 0)
{
return v___x_262_;
}
else
{
size_t v___x_266_; size_t v___x_267_; lean_object* v___x_268_; 
v___x_266_ = ((size_t)0ULL);
v___x_267_ = lean_usize_of_nat(v___x_263_);
v___x_268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_260_, v___x_266_, v___x_267_, v___x_262_);
return v___x_268_;
}
}
else
{
size_t v___x_269_; size_t v___x_270_; lean_object* v___x_271_; 
v___x_269_ = ((size_t)0ULL);
v___x_270_ = lean_usize_of_nat(v___x_263_);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_260_, v___x_269_, v___x_270_, v___x_262_);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks___boxed(lean_object* v_blocks_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Doc_joinBlocks(v_blocks_272_);
lean_dec_ref(v_blocks_272_);
return v_res_273_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_276_ = lean_string_utf8_byte_size(v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(lean_object* v_l_278_, lean_object* v_r_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_280_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_281_ = lean_string_utf8_byte_size(v_l_278_);
v___x_282_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1);
v___x_283_ = lean_nat_dec_le(v___x_282_, v___x_281_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_string_append(v_l_278_, v_r_279_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_nat_sub(v___x_281_, v___x_282_);
v___x_287_ = lean_string_memcmp(v_l_278_, v___x_280_, v___x_286_, v___x_285_, v___x_282_);
lean_dec(v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; 
v___x_288_ = lean_string_append(v_l_278_, v_r_279_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_string_utf8_byte_size(v_r_279_);
v___x_290_ = lean_nat_dec_le(v___x_282_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
v___x_291_ = lean_string_append(v_l_278_, v_r_279_);
return v___x_291_;
}
else
{
uint8_t v___x_292_; 
v___x_292_ = lean_string_memcmp(v_r_279_, v___x_280_, v___x_285_, v___x_285_, v___x_282_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
v___x_293_ = lean_string_append(v_l_278_, v_r_279_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2));
v___x_295_ = lean_string_append(v_l_278_, v___x_294_);
v___x_296_ = lean_string_append(v___x_295_, v_r_279_);
return v___x_296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___boxed(lean_object* v_l_297_, lean_object* v_r_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v_l_297_, v_r_298_);
lean_dec_ref(v_r_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(lean_object* v_as_300_, size_t v_i_301_, size_t v_stop_302_, lean_object* v_b_303_){
_start:
{
lean_object* v___y_305_; uint8_t v___x_309_; 
v___x_309_ = lean_usize_dec_eq(v_i_301_, v_stop_302_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_310_ = lean_array_uget_borrowed(v_as_300_, v_i_301_);
v___x_311_ = lean_array_get_size(v___x_310_);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_nat_dec_eq(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = lean_array_get_size(v_b_303_);
v___x_315_ = lean_nat_dec_eq(v___x_314_, v___x_312_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v_lastIdx_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_glued_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_316_ = lean_unsigned_to_nat(1u);
v_lastIdx_317_ = lean_nat_sub(v___x_314_, v___x_316_);
v___x_318_ = lean_array_fget_borrowed(v_b_303_, v_lastIdx_317_);
v___x_319_ = lean_array_fget_borrowed(v___x_310_, v___x_312_);
lean_inc(v___x_318_);
v_glued_320_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v___x_318_, v___x_319_);
v___x_321_ = lean_array_fset(v_b_303_, v_lastIdx_317_, v_glued_320_);
lean_dec(v_lastIdx_317_);
v___x_322_ = l_Array_extract___redArg(v___x_310_, v___x_316_, v___x_311_);
v___x_323_ = l_Array_append___redArg(v___x_321_, v___x_322_);
lean_dec_ref(v___x_322_);
v___y_305_ = v___x_323_;
goto v___jp_304_;
}
else
{
lean_dec_ref(v_b_303_);
lean_inc(v___x_310_);
v___y_305_ = v___x_310_;
goto v___jp_304_;
}
}
else
{
v___y_305_ = v_b_303_;
goto v___jp_304_;
}
}
else
{
return v_b_303_;
}
v___jp_304_:
{
size_t v___x_306_; size_t v___x_307_; 
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_add(v_i_301_, v___x_306_);
v_i_301_ = v___x_307_;
v_b_303_ = v___y_305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0___boxed(lean_object* v_as_324_, lean_object* v_i_325_, lean_object* v_stop_326_, lean_object* v_b_327_){
_start:
{
size_t v_i_boxed_328_; size_t v_stop_boxed_329_; lean_object* v_res_330_; 
v_i_boxed_328_ = lean_unbox_usize(v_i_325_);
lean_dec(v_i_325_);
v_stop_boxed_329_ = lean_unbox_usize(v_stop_326_);
lean_dec(v_stop_326_);
v_res_330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_as_324_, v_i_boxed_328_, v_stop_boxed_329_, v_b_327_);
lean_dec_ref(v_as_324_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines(lean_object* v_parts_331_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_334_ = lean_array_get_size(v_parts_331_);
v___x_335_ = lean_nat_dec_lt(v___x_332_, v___x_334_);
if (v___x_335_ == 0)
{
return v___x_333_;
}
else
{
uint8_t v___x_336_; 
v___x_336_ = lean_nat_dec_le(v___x_334_, v___x_334_);
if (v___x_336_ == 0)
{
if (v___x_335_ == 0)
{
return v___x_333_;
}
else
{
size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((size_t)0ULL);
v___x_338_ = lean_usize_of_nat(v___x_334_);
v___x_339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_331_, v___x_337_, v___x_338_, v___x_333_);
return v___x_339_;
}
}
else
{
size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((size_t)0ULL);
v___x_341_ = lean_usize_of_nat(v___x_334_);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_331_, v___x_340_, v___x_341_, v___x_333_);
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines___boxed(lean_object* v_parts_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Doc_joinInlines(v_parts_343_);
lean_dec_ref(v_parts_343_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object* v_a_345_, uint8_t v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
uint8_t v_a_19__boxed_359_; lean_object* v_res_360_; 
v_a_19__boxed_359_ = lean_unbox(v_a_353_);
v_res_360_ = l_Lean_Doc_instMarkdownInlineEmpty___lam__0(v_a_352_, v_a_19__boxed_359_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_a_352_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0(lean_object* v_a_363_, lean_object* v_a_364_, uint8_t v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed(lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
uint8_t v_a_23__boxed_379_; lean_object* v_res_380_; 
v_a_23__boxed_379_ = lean_unbox(v_a_373_);
v_res_380_ = l_Lean_Doc_instMarkdownBlockEmpty___lam__0(v_a_371_, v_a_372_, v_a_23__boxed_379_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec_ref(v_a_372_);
lean_dec_ref(v_a_371_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object* v_i_382_){
_start:
{
lean_object* v___f_383_; 
v___f_383_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___closed__0));
return v___f_383_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
if (lean_obj_tag(v_x_385_) == 0)
{
uint8_t v___x_386_; 
v___x_386_ = 1;
return v___x_386_;
}
else
{
uint8_t v___x_387_; 
v___x_387_ = 0;
return v___x_387_;
}
}
else
{
if (lean_obj_tag(v_x_385_) == 0)
{
uint8_t v___x_388_; 
v___x_388_ = 0;
return v___x_388_;
}
else
{
lean_object* v_val_389_; lean_object* v_val_390_; uint32_t v___x_391_; uint32_t v___x_392_; uint8_t v___x_393_; 
v_val_389_ = lean_ctor_get(v_x_384_, 0);
v_val_390_ = lean_ctor_get(v_x_385_, 0);
v___x_391_ = lean_unbox_uint32(v_val_389_);
v___x_392_ = lean_unbox_uint32(v_val_390_);
v___x_393_ = lean_uint32_dec_eq(v___x_391_, v___x_392_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1___boxed(lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_x_394_, v_x_395_);
lean_dec(v_x_395_);
lean_dec(v_x_394_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(lean_object* v_s_398_, uint32_t v_c_399_, lean_object* v_a_400_, uint8_t v_b_401_){
_start:
{
lean_object* v_str_402_; lean_object* v_startInclusive_403_; lean_object* v_endExclusive_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v_str_402_ = lean_ctor_get(v_s_398_, 0);
v_startInclusive_403_ = lean_ctor_get(v_s_398_, 1);
v_endExclusive_404_ = lean_ctor_get(v_s_398_, 2);
v___x_405_ = lean_nat_sub(v_endExclusive_404_, v_startInclusive_403_);
v___x_406_ = lean_nat_dec_eq(v_a_400_, v___x_405_);
lean_dec(v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; uint32_t v___x_408_; uint8_t v___x_409_; 
v___x_407_ = lean_nat_add(v_startInclusive_403_, v_a_400_);
lean_dec(v_a_400_);
v___x_408_ = lean_string_utf8_get_fast(v_str_402_, v___x_407_);
v___x_409_ = lean_uint32_dec_eq(v___x_408_, v_c_399_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_string_utf8_next_fast(v_str_402_, v___x_407_);
lean_dec(v___x_407_);
v___x_411_ = lean_nat_sub(v___x_410_, v_startInclusive_403_);
v_a_400_ = v___x_411_;
v_b_401_ = v___x_409_;
goto _start;
}
else
{
lean_dec(v___x_407_);
return v___x_409_;
}
}
else
{
lean_dec(v_a_400_);
return v_b_401_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg___boxed(lean_object* v_s_413_, lean_object* v_c_414_, lean_object* v_a_415_, lean_object* v_b_416_){
_start:
{
uint32_t v_c_boxed_417_; uint8_t v_b_boxed_418_; uint8_t v_res_419_; lean_object* v_r_420_; 
v_c_boxed_417_ = lean_unbox_uint32(v_c_414_);
lean_dec(v_c_414_);
v_b_boxed_418_ = lean_unbox(v_b_416_);
v_res_419_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_413_, v_c_boxed_417_, v_a_415_, v_b_boxed_418_);
lean_dec_ref(v_s_413_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(uint32_t v_c_421_, lean_object* v_s_422_){
_start:
{
lean_object* v_searcher_423_; uint8_t v___x_424_; uint8_t v___x_425_; 
v_searcher_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = 0;
v___x_425_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_422_, v_c_421_, v_searcher_423_, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0___boxed(lean_object* v_c_426_, lean_object* v_s_427_){
_start:
{
uint32_t v_c_boxed_428_; uint8_t v_res_429_; lean_object* v_r_430_; 
v_c_boxed_428_ = lean_unbox_uint32(v_c_426_);
lean_dec(v_c_426_);
v_res_429_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_boxed_428_, v_s_427_);
lean_dec_ref(v_s_427_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0));
v___x_433_ = lean_string_utf8_byte_size(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0));
v___x_437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_434_);
return v___x_437_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_438_; lean_object* v___x_439_; 
v___x_438_ = 91;
v___x_439_ = lean_box_uint32(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1;
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(uint32_t v_c_442_, lean_object* v_next_x3f_443_){
_start:
{
uint32_t v___x_444_; uint8_t v___x_445_; 
v___x_444_ = 33;
v___x_445_ = lean_uint32_dec_eq(v_c_442_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2);
v___x_447_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_442_, v___x_446_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3);
v___x_449_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_443_, v___x_448_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___boxed(lean_object* v_c_450_, lean_object* v_next_x3f_451_){
_start:
{
uint32_t v_c_boxed_452_; uint8_t v_res_453_; lean_object* v_r_454_; 
v_c_boxed_452_ = lean_unbox_uint32(v_c_450_);
lean_dec(v_c_450_);
v_res_453_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_boxed_452_, v_next_x3f_451_);
lean_dec(v_next_x3f_451_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(lean_object* v_s_455_, uint32_t v_c_456_, lean_object* v_inst_457_, lean_object* v_R_458_, lean_object* v_a_459_, uint8_t v_b_460_, lean_object* v_c_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_455_, v_c_456_, v_a_459_, v_b_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___boxed(lean_object* v_s_463_, lean_object* v_c_464_, lean_object* v_inst_465_, lean_object* v_R_466_, lean_object* v_a_467_, lean_object* v_b_468_, lean_object* v_c_469_){
_start:
{
uint32_t v_c_boxed_470_; uint8_t v_b_boxed_471_; uint8_t v_res_472_; lean_object* v_r_473_; 
v_c_boxed_470_ = lean_unbox_uint32(v_c_464_);
lean_dec(v_c_464_);
v_b_boxed_471_ = lean_unbox(v_b_468_);
v_res_472_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(v_s_463_, v_c_boxed_470_, v_inst_465_, v_R_466_, v_a_467_, v_b_boxed_471_, v_c_469_);
lean_dec_ref(v_s_463_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_474_; lean_object* v___x_475_; 
v___x_474_ = 32;
v___x_475_ = lean_box_uint32(v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(lean_object* v_prev_x3f_478_, uint32_t v_c_479_, lean_object* v_next_x3f_480_){
_start:
{
uint8_t v___y_482_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0);
v___x_500_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_480_, v___x_499_);
if (v___x_500_ == 0)
{
if (lean_obj_tag(v_next_x3f_480_) == 0)
{
uint8_t v___x_501_; 
v___x_501_ = 1;
v___y_482_ = v___x_501_;
goto v___jp_481_;
}
else
{
v___y_482_ = v___x_500_;
goto v___jp_481_;
}
}
else
{
v___y_482_ = v___x_500_;
goto v___jp_481_;
}
v___jp_481_:
{
uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 62;
v___x_484_ = lean_uint32_dec_eq(v_c_479_, v___x_483_);
if (v___x_484_ == 0)
{
uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 45;
v___x_486_ = lean_uint32_dec_eq(v_c_479_, v___x_485_);
if (v___x_486_ == 0)
{
uint32_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = 43;
v___x_488_ = lean_uint32_dec_eq(v_c_479_, v___x_487_);
if (v___x_488_ == 0)
{
uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 46;
v___x_490_ = lean_uint32_dec_eq(v_c_479_, v___x_489_);
if (v___x_490_ == 0)
{
uint8_t v___x_491_; 
v___x_491_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_479_, v_next_x3f_480_);
return v___x_491_;
}
else
{
if (lean_obj_tag(v_prev_x3f_478_) == 0)
{
return v___x_488_;
}
else
{
lean_object* v_val_492_; uint32_t v___x_493_; uint32_t v___x_494_; uint8_t v___x_495_; 
v_val_492_ = lean_ctor_get(v_prev_x3f_478_, 0);
v___x_493_ = 48;
v___x_494_ = lean_unbox_uint32(v_val_492_);
v___x_495_ = lean_uint32_dec_le(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
if (v___x_495_ == 0)
{
return v___x_495_;
}
else
{
return v___y_482_;
}
}
else
{
uint32_t v___x_496_; uint32_t v___x_497_; uint8_t v___x_498_; 
v___x_496_ = 57;
v___x_497_ = lean_unbox_uint32(v_val_492_);
v___x_498_ = lean_uint32_dec_le(v___x_497_, v___x_496_);
if (v___x_498_ == 0)
{
return v___x_498_;
}
else
{
return v___y_482_;
}
}
}
}
}
else
{
return v___y_482_;
}
}
else
{
return v___y_482_;
}
}
else
{
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___boxed(lean_object* v_prev_x3f_502_, lean_object* v_c_503_, lean_object* v_next_x3f_504_){
_start:
{
uint32_t v_c_boxed_505_; uint8_t v_res_506_; lean_object* v_r_507_; 
v_c_boxed_505_ = lean_unbox_uint32(v_c_503_);
lean_dec(v_c_503_);
v_res_506_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_prev_x3f_502_, v_c_boxed_505_, v_next_x3f_504_);
lean_dec(v_next_x3f_504_);
lean_dec(v_prev_x3f_502_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0));
v___x_510_ = lean_string_utf8_byte_size(v___x_509_);
return v___x_510_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_511_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0));
v___x_514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v___x_512_);
lean_ctor_set(v___x_514_, 2, v___x_511_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(uint32_t v___x_515_, lean_object* v___x_516_, lean_object* v_____r_517_, lean_object* v_s_x27_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___y_527_; uint32_t v___x_533_; uint8_t v___x_534_; 
v___x_519_ = lean_string_push(v_s_x27_518_, v___x_515_);
v___x_520_ = lean_box_uint32(v___x_515_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
v___x_533_ = 48;
v___x_534_ = lean_uint32_dec_le(v___x_533_, v___x_515_);
if (v___x_534_ == 0)
{
v___y_527_ = v___x_534_;
goto v___jp_526_;
}
else
{
uint32_t v___x_535_; uint8_t v___x_536_; 
v___x_535_ = 57;
v___x_536_ = lean_uint32_dec_le(v___x_515_, v___x_535_);
v___y_527_ = v___x_536_;
goto v___jp_526_;
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_516_);
lean_ctor_set(v___x_523_, 1, v___x_521_);
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_519_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
v___jp_526_:
{
if (v___y_527_ == 0)
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2);
v___x_529_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v___x_515_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_516_);
lean_ctor_set(v___x_530_, 1, v___x_521_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_519_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
else
{
goto v___jp_522_;
}
}
else
{
goto v___jp_522_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed(lean_object* v___x_537_, lean_object* v___x_538_, lean_object* v_____r_539_, lean_object* v_s_x27_540_){
_start:
{
uint32_t v___x_1753__boxed_541_; lean_object* v_res_542_; 
v___x_1753__boxed_541_ = lean_unbox_uint32(v___x_537_);
lean_dec(v___x_537_);
v_res_542_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_1753__boxed_541_, v___x_538_, v_____r_539_, v_s_x27_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(lean_object* v_s_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___y_546_; lean_object* v_snd_550_; lean_object* v_fst_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_585_; 
v_snd_550_ = lean_ctor_get(v_a_544_, 1);
v_fst_551_ = lean_ctor_get(v_a_544_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v_a_544_);
if (v_isSharedCheck_585_ == 0)
{
v___x_553_ = v_a_544_;
v_isShared_554_ = v_isSharedCheck_585_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_snd_550_);
lean_inc(v_fst_551_);
lean_dec(v_a_544_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_585_;
goto v_resetjp_552_;
}
v___jp_545_:
{
if (lean_obj_tag(v___y_546_) == 0)
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v___y_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___y_546_, 1);
return v_a_547_;
}
else
{
lean_object* v_a_548_; 
v_a_548_ = lean_ctor_get(v___y_546_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___y_546_, 1);
v_a_544_ = v_a_548_;
goto _start;
}
}
v_resetjp_552_:
{
lean_object* v_fst_555_; lean_object* v_snd_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_584_; 
v_fst_555_ = lean_ctor_get(v_snd_550_, 0);
v_snd_556_ = lean_ctor_get(v_snd_550_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_snd_550_);
if (v_isSharedCheck_584_ == 0)
{
v___x_558_ = v_snd_550_;
v_isShared_559_ = v_isSharedCheck_584_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snd_556_);
lean_inc(v_fst_555_);
lean_dec(v_snd_550_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_584_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_string_utf8_byte_size(v_s_543_);
v___x_561_ = lean_nat_dec_eq(v_fst_555_, v___x_560_);
if (v___x_561_ == 0)
{
uint32_t v___x_562_; lean_object* v___x_563_; lean_object* v___y_565_; uint8_t v___x_573_; 
lean_del_object(v___x_558_);
lean_del_object(v___x_553_);
v___x_562_ = lean_string_utf8_get_fast(v_s_543_, v_fst_555_);
v___x_563_ = lean_string_utf8_next_fast(v_s_543_, v_fst_555_);
lean_dec(v_fst_555_);
v___x_573_ = lean_nat_dec_eq(v___x_563_, v___x_560_);
if (v___x_573_ == 0)
{
uint32_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_string_utf8_get_fast(v_s_543_, v___x_563_);
v___x_575_ = lean_box_uint32(v___x_574_);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
v___y_565_ = v___x_576_;
goto v___jp_564_;
}
else
{
lean_object* v_prev_x3f_577_; 
v_prev_x3f_577_ = lean_box(0);
v___y_565_ = v_prev_x3f_577_;
goto v___jp_564_;
}
v___jp_564_:
{
uint8_t v___x_566_; 
v___x_566_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_snd_556_, v___x_562_, v___y_565_);
lean_dec(v___y_565_);
lean_dec(v_snd_556_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_box(0);
v___x_568_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_562_, v___x_563_, v___x_567_, v_fst_551_);
v___y_546_ = v___x_568_;
goto v___jp_545_;
}
else
{
uint32_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_569_ = 92;
v___x_570_ = lean_string_push(v_fst_551_, v___x_569_);
v___x_571_ = lean_box(0);
v___x_572_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_562_, v___x_563_, v___x_571_, v___x_570_);
v___y_546_ = v___x_572_;
goto v___jp_545_;
}
}
}
else
{
lean_object* v___x_579_; 
if (v_isShared_559_ == 0)
{
v___x_579_ = v___x_558_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_fst_555_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_snd_556_);
v___x_579_ = v_reuseFailAlloc_583_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v___x_579_);
v___x_581_ = v___x_553_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_fst_551_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___boxed(lean_object* v_s_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_586_, v_a_587_);
lean_dec_ref(v_s_586_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(uint32_t v___x_589_, lean_object* v___x_590_, lean_object* v_____r_591_, lean_object* v_s_x27_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = lean_string_push(v_s_x27_592_, v___x_589_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_590_);
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0___boxed(lean_object* v___x_596_, lean_object* v___x_597_, lean_object* v_____r_598_, lean_object* v_s_x27_599_){
_start:
{
uint32_t v___x_1877__boxed_600_; lean_object* v_res_601_; 
v___x_1877__boxed_600_ = lean_unbox_uint32(v___x_596_);
lean_dec(v___x_596_);
v_res_601_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_1877__boxed_600_, v___x_597_, v_____r_598_, v_s_x27_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(lean_object* v_s_602_, lean_object* v_a_603_){
_start:
{
lean_object* v___y_605_; lean_object* v_fst_609_; lean_object* v_snd_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_635_; 
v_fst_609_ = lean_ctor_get(v_a_603_, 0);
v_snd_610_ = lean_ctor_get(v_a_603_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_a_603_);
if (v_isSharedCheck_635_ == 0)
{
v___x_612_ = v_a_603_;
v_isShared_613_ = v_isSharedCheck_635_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_snd_610_);
lean_inc(v_fst_609_);
lean_dec(v_a_603_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_635_;
goto v_resetjp_611_;
}
v___jp_604_:
{
if (lean_obj_tag(v___y_605_) == 0)
{
lean_object* v_a_606_; 
v_a_606_ = lean_ctor_get(v___y_605_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v___y_605_, 1);
return v_a_606_;
}
else
{
lean_object* v_a_607_; 
v_a_607_ = lean_ctor_get(v___y_605_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___y_605_, 1);
v_a_603_ = v_a_607_;
goto _start;
}
}
v_resetjp_611_:
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_string_utf8_byte_size(v_s_602_);
v___x_615_ = lean_nat_dec_eq(v_snd_610_, v___x_614_);
if (v___x_615_ == 0)
{
uint32_t v___x_616_; lean_object* v___x_617_; lean_object* v___y_619_; uint8_t v___x_627_; 
lean_del_object(v___x_612_);
v___x_616_ = lean_string_utf8_get_fast(v_s_602_, v_snd_610_);
v___x_617_ = lean_string_utf8_next_fast(v_s_602_, v_snd_610_);
lean_dec(v_snd_610_);
v___x_627_ = lean_nat_dec_eq(v___x_617_, v___x_614_);
if (v___x_627_ == 0)
{
uint32_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_string_utf8_get_fast(v_s_602_, v___x_617_);
v___x_629_ = lean_box_uint32(v___x_628_);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
v___y_619_ = v___x_630_;
goto v___jp_618_;
}
else
{
lean_object* v_prev_x3f_631_; 
v_prev_x3f_631_ = lean_box(0);
v___y_619_ = v_prev_x3f_631_;
goto v___jp_618_;
}
v___jp_618_:
{
uint8_t v___x_620_; 
v___x_620_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v___x_616_, v___y_619_);
lean_dec(v___y_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_box(0);
v___x_622_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_616_, v___x_617_, v___x_621_, v_fst_609_);
v___y_605_ = v___x_622_;
goto v___jp_604_;
}
else
{
uint32_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = 92;
v___x_624_ = lean_string_push(v_fst_609_, v___x_623_);
v___x_625_ = lean_box(0);
v___x_626_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_616_, v___x_617_, v___x_625_, v___x_624_);
v___y_605_ = v___x_626_;
goto v___jp_604_;
}
}
}
else
{
lean_object* v___x_633_; 
if (v_isShared_613_ == 0)
{
v___x_633_ = v___x_612_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_fst_609_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_snd_610_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___boxed(lean_object* v_s_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_636_, v_a_637_);
lean_dec_ref(v_s_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object* v_s_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_snd_648_; lean_object* v_fst_649_; lean_object* v_fst_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_659_; 
v___x_646_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1));
v___x_647_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_645_, v___x_646_);
v_snd_648_ = lean_ctor_get(v___x_647_, 1);
lean_inc(v_snd_648_);
v_fst_649_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_fst_649_);
lean_dec_ref(v___x_647_);
v_fst_650_ = lean_ctor_get(v_snd_648_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_snd_648_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v_snd_648_, 1);
lean_dec(v_unused_660_);
v___x_652_ = v_snd_648_;
v_isShared_653_ = v_isSharedCheck_659_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_fst_650_);
lean_dec(v_snd_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_659_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v_fst_650_);
lean_ctor_set(v___x_652_, 0, v_fst_649_);
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_fst_649_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_fst_650_);
v___x_655_ = v_reuseFailAlloc_658_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v_fst_657_; 
v___x_656_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_645_, v___x_655_);
v_fst_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_fst_657_);
lean_dec_ref(v___x_656_);
return v_fst_657_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object* v_s_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_661_);
lean_dec_ref(v_s_661_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object* v_s_663_, lean_object* v_inst_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_663_, v_a_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object* v_s_667_, lean_object* v_inst_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_667_, v_inst_668_, v_a_669_);
lean_dec_ref(v_s_667_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(lean_object* v_s_671_, lean_object* v_inst_672_, lean_object* v_a_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_671_, v_a_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___boxed(lean_object* v_s_675_, lean_object* v_inst_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(v_s_675_, v_inst_676_, v_a_677_);
lean_dec_ref(v_s_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v_str_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_snd_681_; lean_object* v_fst_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_724_; 
v_snd_681_ = lean_ctor_get(v_a_680_, 1);
v_fst_682_ = lean_ctor_get(v_a_680_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_a_680_);
if (v_isSharedCheck_724_ == 0)
{
v___x_684_ = v_a_680_;
v_isShared_685_ = v_isSharedCheck_724_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_snd_681_);
lean_inc(v_fst_682_);
lean_dec(v_a_680_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_724_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_fst_686_; lean_object* v_snd_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_723_; 
v_fst_686_ = lean_ctor_get(v_snd_681_, 0);
v_snd_687_ = lean_ctor_get(v_snd_681_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_snd_681_);
if (v_isSharedCheck_723_ == 0)
{
v___x_689_ = v_snd_681_;
v_isShared_690_ = v_isSharedCheck_723_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_snd_687_);
lean_inc(v_fst_686_);
lean_dec(v_snd_681_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_723_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_string_utf8_byte_size(v_str_679_);
v___x_692_ = lean_nat_dec_eq(v_snd_687_, v___x_691_);
if (v___x_692_ == 0)
{
uint32_t v___x_693_; lean_object* v___x_694_; uint32_t v___x_695_; uint8_t v___x_696_; 
v___x_693_ = lean_string_utf8_get_fast(v_str_679_, v_snd_687_);
v___x_694_ = lean_string_utf8_next_fast(v_str_679_, v_snd_687_);
lean_dec(v_snd_687_);
v___x_695_ = 96;
v___x_696_ = lean_uint32_dec_eq(v___x_693_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v_longest_697_; lean_object* v___y_699_; uint8_t v___x_707_; 
v_longest_697_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_nat_dec_le(v_fst_682_, v_fst_686_);
if (v___x_707_ == 0)
{
lean_dec(v_fst_686_);
v___y_699_ = v_fst_682_;
goto v___jp_698_;
}
else
{
lean_dec(v_fst_682_);
v___y_699_ = v_fst_686_;
goto v___jp_698_;
}
v___jp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_694_);
lean_ctor_set(v___x_689_, 0, v_longest_697_);
v___x_701_ = v___x_689_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_longest_697_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_694_);
v___x_701_ = v_reuseFailAlloc_706_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_703_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_701_);
lean_ctor_set(v___x_684_, 0, v___y_699_);
v___x_703_ = v___x_684_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___y_699_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_701_);
v___x_703_ = v_reuseFailAlloc_705_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v_a_680_ = v___x_703_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_nat_add(v_fst_686_, v___x_708_);
lean_dec(v_fst_686_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_694_);
lean_ctor_set(v___x_689_, 0, v___x_709_);
v___x_711_ = v___x_689_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v___x_694_);
v___x_711_ = v_reuseFailAlloc_716_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_711_);
v___x_713_ = v___x_684_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_fst_682_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_715_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
v_a_680_ = v___x_713_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_718_; 
if (v_isShared_690_ == 0)
{
v___x_718_ = v___x_689_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_fst_686_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_snd_687_);
v___x_718_ = v_reuseFailAlloc_722_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_718_);
v___x_720_ = v___x_684_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_fst_682_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v_str_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_725_, v_a_726_);
lean_dec_ref(v_str_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(lean_object* v_str_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_snd_736_; lean_object* v_fst_737_; lean_object* v_fst_738_; uint8_t v___x_739_; 
v___x_734_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1));
v___x_735_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_733_, v___x_734_);
v_snd_736_ = lean_ctor_get(v___x_735_, 1);
lean_inc(v_snd_736_);
v_fst_737_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_fst_737_);
lean_dec_ref(v___x_735_);
v_fst_738_ = lean_ctor_get(v_snd_736_, 0);
lean_inc(v_fst_738_);
lean_dec(v_snd_736_);
v___x_739_ = lean_nat_dec_le(v_fst_737_, v_fst_738_);
if (v___x_739_ == 0)
{
lean_dec(v_fst_738_);
return v_fst_737_;
}
else
{
lean_dec(v_fst_737_);
return v_fst_738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___boxed(lean_object* v_str_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_740_);
lean_dec_ref(v_str_740_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(lean_object* v_str_742_, lean_object* v_inst_743_, lean_object* v_a_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_742_, v_a_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v_str_746_, lean_object* v_inst_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(v_str_746_, v_inst_747_, v_a_748_);
lean_dec_ref(v_str_746_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
lean_object* v_zero_752_; uint8_t v_isZero_753_; 
v_zero_752_ = lean_unsigned_to_nat(0u);
v_isZero_753_ = lean_nat_dec_eq(v_x_750_, v_zero_752_);
if (v_isZero_753_ == 1)
{
lean_dec(v_x_750_);
return v_x_751_;
}
else
{
uint32_t v___x_754_; lean_object* v_one_755_; lean_object* v_n_756_; lean_object* v___x_757_; 
v___x_754_ = 96;
v_one_755_ = lean_unsigned_to_nat(1u);
v_n_756_ = lean_nat_sub(v_x_750_, v_one_755_);
lean_dec(v_x_750_);
v___x_757_ = lean_string_push(v_x_751_, v___x_754_);
v_x_750_ = v_n_756_;
v_x_751_ = v___x_757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(lean_object* v_atLeast_759_, lean_object* v_str_760_){
_start:
{
lean_object* v___x_761_; lean_object* v___y_763_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_767_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_760_);
v___x_768_ = lean_nat_dec_le(v_atLeast_759_, v___x_767_);
if (v___x_768_ == 0)
{
lean_dec(v___x_767_);
v___y_763_ = v_atLeast_759_;
goto v___jp_762_;
}
else
{
lean_dec(v_atLeast_759_);
v___y_763_ = v___x_767_;
goto v___jp_762_;
}
v___jp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_unsigned_to_nat(1u);
v___x_765_ = lean_nat_add(v___y_763_, v___x_764_);
lean_dec(v___y_763_);
v___x_766_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(v___x_765_, v___x_761_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor___boxed(lean_object* v_atLeast_769_, lean_object* v_str_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v_atLeast_769_, v_str_770_);
lean_dec_ref(v_str_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object* v_str_773_){
_start:
{
lean_object* v___x_774_; lean_object* v_backticks_775_; lean_object* v___y_777_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v_backticks_775_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_774_, v_str_773_);
v___x_791_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_792_ = lean_string_utf8_byte_size(v_str_773_);
v___x_793_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1);
v___x_794_ = lean_nat_dec_le(v___x_793_, v___x_792_);
if (v___x_794_ == 0)
{
goto v___jp_784_;
}
else
{
uint8_t v___x_795_; 
v___x_795_ = lean_string_memcmp(v_str_773_, v___x_791_, v___x_774_, v___x_774_, v___x_793_);
if (v___x_795_ == 0)
{
goto v___jp_784_;
}
else
{
goto v___jp_780_;
}
}
v___jp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_inc_ref(v_backticks_775_);
v___x_778_ = lean_string_append(v_backticks_775_, v___y_777_);
lean_dec_ref(v___y_777_);
v___x_779_ = lean_string_append(v___x_778_, v_backticks_775_);
lean_dec_ref(v_backticks_775_);
return v___x_779_;
}
v___jp_780_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_782_ = lean_string_append(v___x_781_, v_str_773_);
lean_dec_ref(v_str_773_);
v___x_783_ = lean_string_append(v___x_782_, v___x_781_);
v___y_777_ = v___x_783_;
goto v___jp_776_;
}
v___jp_784_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_785_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_786_ = lean_string_utf8_byte_size(v_str_773_);
v___x_787_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1);
v___x_788_ = lean_nat_dec_le(v___x_787_, v___x_786_);
if (v___x_788_ == 0)
{
v___y_777_ = v_str_773_;
goto v___jp_776_;
}
else
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = lean_nat_sub(v___x_786_, v___x_787_);
v___x_790_ = lean_string_memcmp(v_str_773_, v___x_785_, v___x_789_, v___x_774_, v___x_787_);
lean_dec(v___x_789_);
if (v___x_790_ == 0)
{
v___y_777_ = v_str_773_;
goto v___jp_776_;
}
else
{
goto v___jp_780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(lean_object* v_s_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0));
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___boxed(lean_object* v_s_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v_s_800_);
lean_dec_ref(v_s_800_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(lean_object* v_str_802_, lean_object* v___x_803_, lean_object* v___x_804_, lean_object* v_a_805_, lean_object* v_b_806_){
_start:
{
lean_object* v_it_808_; lean_object* v_startInclusive_809_; lean_object* v_endExclusive_810_; 
if (lean_obj_tag(v_a_805_) == 0)
{
lean_object* v_currPos_814_; lean_object* v_searcher_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_841_; 
v_currPos_814_ = lean_ctor_get(v_a_805_, 0);
v_searcher_815_ = lean_ctor_get(v_a_805_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_a_805_);
if (v_isSharedCheck_841_ == 0)
{
v___x_817_ = v_a_805_;
v_isShared_818_ = v_isSharedCheck_841_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_searcher_815_);
lean_inc(v_currPos_814_);
lean_dec(v_a_805_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_841_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_startInclusive_819_; lean_object* v_endExclusive_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_startInclusive_819_ = lean_ctor_get(v___x_803_, 1);
v_endExclusive_820_ = lean_ctor_get(v___x_803_, 2);
v___x_821_ = lean_nat_sub(v_endExclusive_820_, v_startInclusive_819_);
v___x_822_ = lean_nat_dec_eq(v_searcher_815_, v___x_821_);
lean_dec(v___x_821_);
if (v___x_822_ == 0)
{
uint32_t v___x_823_; uint32_t v___x_824_; uint8_t v___x_825_; 
v___x_823_ = 10;
v___x_824_ = lean_string_utf8_get_fast(v_str_802_, v_searcher_815_);
v___x_825_ = lean_uint32_dec_eq(v___x_824_, v___x_823_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = lean_string_utf8_next_fast(v_str_802_, v_searcher_815_);
lean_dec(v_searcher_815_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___x_826_);
v___x_828_ = v___x_817_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_currPos_814_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_826_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v_a_805_ = v___x_828_;
goto _start;
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_slice_834_; lean_object* v_nextIt_836_; 
v___x_831_ = lean_string_utf8_next_fast(v_str_802_, v_searcher_815_);
v___x_832_ = lean_nat_sub(v___x_831_, v_searcher_815_);
v___x_833_ = lean_nat_add(v_searcher_815_, v___x_832_);
lean_dec(v___x_832_);
v_slice_834_ = l_String_Slice_subslice_x21(v___x_803_, v_currPos_814_, v_searcher_815_);
lean_inc(v___x_833_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___x_833_);
lean_ctor_set(v___x_817_, 0, v___x_833_);
v_nextIt_836_ = v___x_817_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_833_);
v_nextIt_836_ = v_reuseFailAlloc_839_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v_startInclusive_837_; lean_object* v_endExclusive_838_; 
v_startInclusive_837_ = lean_ctor_get(v_slice_834_, 0);
lean_inc(v_startInclusive_837_);
v_endExclusive_838_ = lean_ctor_get(v_slice_834_, 1);
lean_inc(v_endExclusive_838_);
lean_dec_ref(v_slice_834_);
v_it_808_ = v_nextIt_836_;
v_startInclusive_809_ = v_startInclusive_837_;
v_endExclusive_810_ = v_endExclusive_838_;
goto v___jp_807_;
}
}
}
else
{
lean_object* v___x_840_; 
lean_del_object(v___x_817_);
lean_dec(v_searcher_815_);
v___x_840_ = lean_box(1);
lean_inc(v___x_804_);
v_it_808_ = v___x_840_;
v_startInclusive_809_ = v_currPos_814_;
v_endExclusive_810_ = v___x_804_;
goto v___jp_807_;
}
}
}
else
{
lean_dec(v___x_804_);
return v_b_806_;
}
v___jp_807_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_string_utf8_extract(v_str_802_, v_startInclusive_809_, v_endExclusive_810_);
lean_dec(v_endExclusive_810_);
lean_dec(v_startInclusive_809_);
v___x_812_ = lean_array_push(v_b_806_, v___x_811_);
v_a_805_ = v_it_808_;
v_b_806_ = v___x_812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg___boxed(lean_object* v_str_842_, lean_object* v___x_843_, lean_object* v___x_844_, lean_object* v_a_845_, lean_object* v_b_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_842_, v___x_843_, v___x_844_, v_a_845_, v_b_846_);
lean_dec_ref(v___x_843_);
lean_dec_ref(v_str_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(lean_object* v_str_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_string_utf8_byte_size(v_str_848_);
lean_inc_ref(v_str_848_);
v___x_851_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_851_, 0, v_str_848_);
lean_ctor_set(v___x_851_, 1, v___x_849_);
lean_ctor_set(v___x_851_, 2, v___x_850_);
v___x_852_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v___x_851_);
v___x_853_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_854_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_848_, v___x_851_, v___x_850_, v___x_852_, v___x_853_);
lean_dec_ref_known(v___x_851_, 3);
lean_dec_ref(v_str_848_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(lean_object* v_str_855_, lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v_inst_858_, lean_object* v_R_859_, lean_object* v_a_860_, lean_object* v_b_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_855_, v___x_856_, v___x_857_, v_a_860_, v_b_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___boxed(lean_object* v_str_863_, lean_object* v___x_864_, lean_object* v___x_865_, lean_object* v_inst_866_, lean_object* v_R_867_, lean_object* v_a_868_, lean_object* v_b_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(v_str_863_, v___x_864_, v___x_865_, v_inst_866_, v_R_867_, v_a_868_, v_b_869_);
lean_dec_ref(v___x_864_);
lean_dec_ref(v_str_863_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(lean_object* v_str_871_){
_start:
{
lean_object* v___x_872_; lean_object* v_fence_873_; lean_object* v___y_875_; lean_object* v_body_881_; uint8_t v___y_883_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_872_ = lean_unsigned_to_nat(2u);
v_fence_873_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_872_, v_str_871_);
v_body_881_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(v_str_871_);
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = lean_array_get_size(v_body_881_);
v___x_887_ = lean_nat_dec_lt(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
v___y_883_ = v___x_887_;
goto v___jp_882_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = lean_nat_sub(v___x_886_, v___x_889_);
v___x_891_ = lean_array_get(v___x_888_, v_body_881_, v___x_890_);
lean_dec(v___x_890_);
v___x_892_ = lean_string_utf8_byte_size(v___x_891_);
lean_dec(v___x_891_);
v___x_893_ = lean_nat_dec_eq(v___x_892_, v___x_885_);
v___y_883_ = v___x_893_;
goto v___jp_882_;
}
v___jp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_876_ = lean_unsigned_to_nat(1u);
v___x_877_ = lean_mk_empty_array_with_capacity(v___x_876_);
v___x_878_ = lean_array_push(v___x_877_, v_fence_873_);
lean_inc_ref(v___x_878_);
v___x_879_ = l_Array_append___redArg(v___x_878_, v___y_875_);
lean_dec_ref(v___y_875_);
v___x_880_ = l_Array_append___redArg(v___x_879_, v___x_878_);
lean_dec_ref(v___x_878_);
return v___x_880_;
}
v___jp_882_:
{
if (v___y_883_ == 0)
{
v___y_875_ = v_body_881_;
goto v___jp_874_;
}
else
{
lean_object* v___x_884_; 
v___x_884_ = lean_array_pop(v_body_881_);
v___y_875_ = v___x_884_;
goto v___jp_874_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_894_, lean_object* v_pos_895_){
_start:
{
lean_object* v_str_896_; lean_object* v_startInclusive_897_; lean_object* v_endExclusive_898_; lean_object* v___x_899_; uint8_t v___y_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_str_896_ = lean_ctor_get(v_s_894_, 0);
v_startInclusive_897_ = lean_ctor_get(v_s_894_, 1);
v_endExclusive_898_ = lean_ctor_get(v_s_894_, 2);
v___x_899_ = lean_nat_add(v_startInclusive_897_, v_pos_895_);
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_nat_sub(v_endExclusive_898_, v___x_899_);
v___x_910_ = lean_nat_dec_eq(v___x_908_, v___x_909_);
lean_dec(v___x_909_);
if (v___x_910_ == 0)
{
uint32_t v___x_911_; uint8_t v___y_913_; uint32_t v___x_918_; uint8_t v___x_919_; 
v___x_911_ = lean_string_utf8_get_fast(v_str_896_, v___x_899_);
v___x_918_ = 32;
v___x_919_ = lean_uint32_dec_eq(v___x_911_, v___x_918_);
if (v___x_919_ == 0)
{
uint32_t v___x_920_; uint8_t v___x_921_; 
v___x_920_ = 9;
v___x_921_ = lean_uint32_dec_eq(v___x_911_, v___x_920_);
v___y_913_ = v___x_921_;
goto v___jp_912_;
}
else
{
v___y_913_ = v___x_919_;
goto v___jp_912_;
}
v___jp_912_:
{
if (v___y_913_ == 0)
{
uint32_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = 13;
v___x_915_ = lean_uint32_dec_eq(v___x_911_, v___x_914_);
if (v___x_915_ == 0)
{
uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 10;
v___x_917_ = lean_uint32_dec_eq(v___x_911_, v___x_916_);
v___y_907_ = v___x_917_;
goto v___jp_906_;
}
else
{
v___y_907_ = v___x_915_;
goto v___jp_906_;
}
}
else
{
goto v___jp_900_;
}
}
}
else
{
lean_dec(v___x_899_);
return v_pos_895_;
}
v___jp_900_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_901_ = lean_string_utf8_next_fast(v_str_896_, v___x_899_);
v___x_902_ = lean_nat_sub(v___x_901_, v___x_899_);
lean_dec(v___x_899_);
v___x_903_ = lean_nat_add(v_pos_895_, v___x_902_);
lean_dec(v___x_902_);
v___x_904_ = lean_nat_dec_lt(v_pos_895_, v___x_903_);
if (v___x_904_ == 0)
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
v___jp_906_:
{
if (v___y_907_ == 0)
{
lean_dec(v___x_899_);
return v_pos_895_;
}
else
{
goto v___jp_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object* v_s_922_, lean_object* v_pos_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_922_, v_pos_923_);
lean_dec_ref(v_s_922_);
return v_res_924_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_Doc_Inline_empty(lean_box(0));
return v___x_925_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_927_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___x_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object* v_a_929_){
_start:
{
if (lean_obj_tag(v_a_929_) == 0)
{
lean_object* v___x_930_; 
v___x_930_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
return v___x_930_;
}
else
{
lean_object* v_head_931_; 
v_head_931_ = lean_ctor_get(v_a_929_, 0);
lean_inc(v_head_931_);
switch(lean_obj_tag(v_head_931_))
{
case 0:
{
lean_object* v_tail_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_976_; 
v_tail_932_ = lean_ctor_get(v_a_929_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v_a_929_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v_a_929_, 0);
lean_dec(v_unused_977_);
v___x_934_ = v_a_929_;
v_isShared_935_ = v_isSharedCheck_976_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_tail_932_);
lean_dec(v_a_929_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_976_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_string_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_975_; 
v_string_936_ = lean_ctor_get(v_head_931_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v_head_931_);
if (v_isSharedCheck_975_ == 0)
{
v___x_938_ = v_head_931_;
v_isShared_939_ = v_isSharedCheck_975_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_string_936_);
lean_dec(v_head_931_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_975_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_string_utf8_byte_size(v_string_936_);
lean_inc_ref(v_string_936_);
v___x_942_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_942_, 0, v_string_936_);
lean_ctor_set(v___x_942_, 1, v___x_940_);
lean_ctor_set(v___x_942_, 2, v___x_941_);
v___x_943_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_942_, v___x_940_);
lean_dec_ref_known(v___x_942_, 3);
v___x_944_ = lean_nat_dec_eq(v___x_943_, v___x_941_);
if (v___x_944_ == 0)
{
lean_object* v_s1_945_; lean_object* v_s2_946_; lean_object* v___x_948_; 
v_s1_945_ = lean_string_utf8_extract(v_string_936_, v___x_940_, v___x_943_);
v_s2_946_ = lean_string_utf8_extract(v_string_936_, v___x_943_, v___x_941_);
lean_dec(v___x_943_);
lean_dec_ref(v_string_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v_s2_946_);
v___x_948_ = v___x_938_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_s2_946_);
v___x_948_ = v_reuseFailAlloc_963_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_949_ = lean_array_mk(v_tail_932_);
v___x_950_ = lean_array_get_size(v___x_949_);
v___x_951_ = lean_nat_dec_eq(v___x_950_, v___x_940_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_mk_empty_array_with_capacity(v___x_952_);
v___x_954_ = lean_array_push(v___x_953_, v___x_948_);
v___x_955_ = l_Array_append___redArg(v___x_954_, v___x_949_);
lean_dec_ref(v___x_949_);
v___x_956_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
if (v_isShared_935_ == 0)
{
lean_ctor_set_tag(v___x_934_, 0);
lean_ctor_set(v___x_934_, 1, v___x_956_);
lean_ctor_set(v___x_934_, 0, v_s1_945_);
v___x_958_ = v___x_934_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_s1_945_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
else
{
lean_object* v___x_961_; 
lean_dec_ref(v___x_949_);
if (v_isShared_935_ == 0)
{
lean_ctor_set_tag(v___x_934_, 0);
lean_ctor_set(v___x_934_, 1, v___x_948_);
lean_ctor_set(v___x_934_, 0, v_s1_945_);
v___x_961_ = v___x_934_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_s1_945_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v___x_948_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
else
{
lean_object* v___x_964_; lean_object* v_fst_965_; lean_object* v_snd_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_974_; 
lean_dec(v___x_943_);
lean_del_object(v___x_938_);
lean_del_object(v___x_934_);
v___x_964_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_932_);
v_fst_965_ = lean_ctor_get(v___x_964_, 0);
v_snd_966_ = lean_ctor_get(v___x_964_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_974_ == 0)
{
v___x_968_ = v___x_964_;
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_snd_966_);
lean_inc(v_fst_965_);
lean_dec(v___x_964_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_970_ = lean_string_append(v_string_936_, v_fst_965_);
lean_dec(v_fst_965_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_970_);
v___x_972_ = v___x_968_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_snd_966_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_978_; lean_object* v_content_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_tail_978_ = lean_ctor_get(v_a_929_, 1);
lean_inc(v_tail_978_);
lean_dec_ref_known(v_a_929_, 2);
v_content_979_ = lean_ctor_get(v_head_931_, 0);
lean_inc_ref(v_content_979_);
lean_dec_ref_known(v_head_931_, 1);
v___x_980_ = lean_array_to_list(v_content_979_);
v___x_981_ = l_List_appendTR___redArg(v___x_980_, v_tail_978_);
v_a_929_ = v___x_981_;
goto _start;
}
default: 
{
lean_object* v_tail_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1021_; 
v_tail_983_ = lean_ctor_get(v_a_929_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_a_929_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v_a_929_, 0);
lean_dec(v_unused_1022_);
v___x_985_ = v_a_929_;
v_isShared_986_ = v_isSharedCheck_1021_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_tail_983_);
lean_dec(v_a_929_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1021_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_988_ = lean_array_mk(v_tail_983_);
if (lean_obj_tag(v_head_931_) == 9)
{
lean_object* v_content_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v_content_989_ = lean_ctor_get(v_head_931_, 0);
v___x_990_ = lean_array_get_size(v_content_989_);
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = lean_nat_dec_eq(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = lean_array_get_size(v___x_988_);
v___x_994_ = lean_nat_dec_eq(v___x_993_, v___x_991_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
lean_inc_ref(v_content_989_);
lean_dec_ref_known(v_head_931_, 1);
v___x_995_ = l_Array_append___redArg(v_content_989_, v___x_988_);
lean_dec_ref(v___x_988_);
v___x_996_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 0);
lean_ctor_set(v___x_985_, 1, v___x_996_);
lean_ctor_set(v___x_985_, 0, v___x_987_);
v___x_998_ = v___x_985_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
else
{
lean_object* v___x_1001_; 
lean_dec_ref(v___x_988_);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 0);
lean_ctor_set(v___x_985_, 1, v_head_931_);
lean_ctor_set(v___x_985_, 0, v___x_987_);
v___x_1001_ = v___x_985_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_head_931_);
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
lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec_ref_known(v_head_931_, 1);
v___x_1003_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_988_);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 0);
lean_ctor_set(v___x_985_, 1, v___x_1003_);
lean_ctor_set(v___x_985_, 0, v___x_987_);
v___x_1005_ = v___x_985_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1007_ = lean_array_get_size(v___x_988_);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_nat_dec_eq(v___x_1007_, v___x_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1010_ = lean_unsigned_to_nat(1u);
v___x_1011_ = lean_mk_empty_array_with_capacity(v___x_1010_);
v___x_1012_ = lean_array_push(v___x_1011_, v_head_931_);
v___x_1013_ = l_Array_append___redArg(v___x_1012_, v___x_988_);
lean_dec_ref(v___x_988_);
v___x_1014_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 0);
lean_ctor_set(v___x_985_, 1, v___x_1014_);
lean_ctor_set(v___x_985_, 0, v___x_987_);
v___x_1016_ = v___x_985_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
else
{
lean_object* v___x_1019_; 
lean_dec_ref(v___x_988_);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 0);
lean_ctor_set(v___x_985_, 1, v_head_931_);
lean_ctor_set(v___x_985_, 0, v___x_987_);
v___x_1019_ = v___x_985_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_head_931_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_inline_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_1030_, lean_object* v_inline_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_1033_, lean_object* v_pos_1034_){
_start:
{
lean_object* v_str_1035_; lean_object* v_startInclusive_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_str_1035_ = lean_ctor_get(v_s_1033_, 0);
v_startInclusive_1036_ = lean_ctor_get(v_s_1033_, 1);
v___x_1037_ = lean_nat_add(v_startInclusive_1036_, v_pos_1034_);
v___x_1038_ = lean_nat_sub(v___x_1037_, v_startInclusive_1036_);
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_nat_dec_eq(v___x_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___y_1049_; lean_object* v___x_1050_; uint32_t v___x_1051_; uint8_t v___y_1053_; uint32_t v___x_1058_; uint8_t v___x_1059_; 
lean_inc(v_startInclusive_1036_);
lean_inc_ref(v_str_1035_);
v___x_1041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1041_, 0, v_str_1035_);
lean_ctor_set(v___x_1041_, 1, v_startInclusive_1036_);
lean_ctor_set(v___x_1041_, 2, v___x_1037_);
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1043_ = lean_nat_sub(v___x_1038_, v___x_1042_);
lean_dec(v___x_1038_);
v___x_1044_ = l_String_Slice_posLE(v___x_1041_, v___x_1043_);
lean_dec_ref_known(v___x_1041_, 3);
v___x_1050_ = lean_nat_add(v_startInclusive_1036_, v___x_1044_);
v___x_1051_ = lean_string_utf8_get_fast(v_str_1035_, v___x_1050_);
lean_dec(v___x_1050_);
v___x_1058_ = 32;
v___x_1059_ = lean_uint32_dec_eq(v___x_1051_, v___x_1058_);
if (v___x_1059_ == 0)
{
uint32_t v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = 9;
v___x_1061_ = lean_uint32_dec_eq(v___x_1051_, v___x_1060_);
v___y_1053_ = v___x_1061_;
goto v___jp_1052_;
}
else
{
v___y_1053_ = v___x_1059_;
goto v___jp_1052_;
}
v___jp_1045_:
{
uint8_t v___x_1046_; 
v___x_1046_ = lean_nat_dec_lt(v___x_1044_, v_pos_1034_);
if (v___x_1046_ == 0)
{
lean_dec(v___x_1044_);
return v_pos_1034_;
}
else
{
lean_dec(v_pos_1034_);
v_pos_1034_ = v___x_1044_;
goto _start;
}
}
v___jp_1048_:
{
if (v___y_1049_ == 0)
{
lean_dec(v___x_1044_);
return v_pos_1034_;
}
else
{
goto v___jp_1045_;
}
}
v___jp_1052_:
{
if (v___y_1053_ == 0)
{
uint32_t v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = 13;
v___x_1055_ = lean_uint32_dec_eq(v___x_1051_, v___x_1054_);
if (v___x_1055_ == 0)
{
uint32_t v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = 10;
v___x_1057_ = lean_uint32_dec_eq(v___x_1051_, v___x_1056_);
v___y_1049_ = v___x_1057_;
goto v___jp_1048_;
}
else
{
v___y_1049_ = v___x_1055_;
goto v___jp_1048_;
}
}
else
{
goto v___jp_1045_;
}
}
}
else
{
lean_dec(v___x_1038_);
lean_dec(v___x_1037_);
return v_pos_1034_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_1062_, lean_object* v_pos_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_1062_, v_pos_1063_);
lean_dec_ref(v_s_1062_);
return v_res_1064_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1066_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_xs_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1069_ = lean_array_get_size(v_xs_1068_);
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = lean_nat_dec_eq(v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = lean_nat_sub(v___x_1069_, v___x_1072_);
v___x_1074_ = lean_array_fget(v_xs_1068_, v___x_1073_);
lean_dec(v___x_1073_);
switch(lean_obj_tag(v___x_1074_))
{
case 0:
{
lean_object* v_string_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1105_; 
v_string_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1105_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_string_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1105_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1079_ = lean_string_utf8_byte_size(v_string_1075_);
lean_inc_ref(v_string_1075_);
v___x_1080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1080_, 0, v_string_1075_);
lean_ctor_set(v___x_1080_, 1, v___x_1070_);
lean_ctor_set(v___x_1080_, 2, v___x_1079_);
v___x_1081_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_1080_, v___x_1070_);
v___x_1082_ = lean_nat_dec_eq(v___x_1081_, v___x_1079_);
lean_dec(v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1083_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_1080_, v___x_1079_);
lean_dec_ref_known(v___x_1080_, 3);
v___x_1084_ = lean_array_pop(v_xs_1068_);
v___x_1085_ = lean_string_utf8_extract(v_string_1075_, v___x_1070_, v___x_1083_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1085_);
v___x_1087_ = v___x_1077_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1088_ = lean_array_push(v___x_1084_, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
v___x_1090_ = lean_string_utf8_extract(v_string_1075_, v___x_1083_, v___x_1079_);
lean_dec(v___x_1083_);
lean_dec_ref(v_string_1075_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
return v___x_1091_;
}
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_fst_1095_; lean_object* v_snd_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref_known(v___x_1080_, 3);
lean_del_object(v___x_1077_);
v___x_1093_ = lean_array_pop(v_xs_1068_);
v___x_1094_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1093_);
v_fst_1095_ = lean_ctor_get(v___x_1094_, 0);
v_snd_1096_ = lean_ctor_get(v___x_1094_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1098_ = v___x_1094_;
v_isShared_1099_ = v_isSharedCheck_1104_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_snd_1096_);
lean_inc(v_fst_1095_);
lean_dec(v___x_1094_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1104_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1100_ = lean_string_append(v_snd_1096_, v_string_1075_);
lean_dec_ref(v_string_1075_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v___x_1100_);
v___x_1102_ = v___x_1098_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_fst_1095_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
case 9:
{
lean_object* v_content_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_content_1106_ = lean_ctor_get(v___x_1074_, 0);
lean_inc_ref(v_content_1106_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1107_ = lean_array_pop(v_xs_1068_);
v___x_1108_ = l_Array_append___redArg(v___x_1107_, v_content_1106_);
lean_dec_ref(v_content_1106_);
v_xs_1068_ = v___x_1108_;
goto _start;
}
default: 
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v___x_1074_);
v___x_1110_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_xs_1068_);
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
return v___x_1112_;
}
}
}
else
{
lean_object* v___x_1113_; 
lean_dec_ref(v_xs_1068_);
v___x_1113_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_1114_, lean_object* v_xs_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_xs_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_mk_empty_array_with_capacity(v___x_1118_);
v___x_1120_ = lean_array_push(v___x_1119_, v_inline_1117_);
v___x_1121_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_1122_, lean_object* v_inline_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v_fst_1127_; lean_object* v_snd_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1136_; 
v___x_1126_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1125_);
v_fst_1127_ = lean_ctor_get(v___x_1126_, 0);
v_snd_1128_ = lean_ctor_get(v___x_1126_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1130_ = v___x_1126_;
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_snd_1128_);
lean_inc(v_fst_1127_);
lean_dec(v___x_1126_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 1, v___x_1132_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_fst_1127_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_1137_, lean_object* v_inline_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_1138_);
return v___x_1139_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_instMonadEIO(lean_box(0));
return v___x_1140_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0);
v___x_1142_ = l_StateRefT_x27_instMonad___redArg(v___x_1141_);
return v___x_1142_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13));
v___x_1172_ = lean_unsigned_to_nat(3u);
v___x_1173_ = lean_mk_empty_array_with_capacity(v___x_1172_);
v___x_1174_ = lean_array_push(v___x_1173_, v___x_1171_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object* v_inst_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1177_, v_x_1178_, v_x_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_1185_, lean_object* v_x_1186_, lean_object* v_x_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_pieces_1193_; lean_object* v_pieces_1197_; lean_object* v___x_1200_; lean_object* v_toApplicative_1201_; lean_object* v_toFunctor_1202_; lean_object* v_toSeq_1203_; lean_object* v_toSeqLeft_1204_; lean_object* v_toSeqRight_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___f_1209_; lean_object* v___x_1210_; lean_object* v___f_1211_; lean_object* v___f_1212_; lean_object* v___f_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1200_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1201_ = lean_ctor_get(v___x_1200_, 0);
v_toFunctor_1202_ = lean_ctor_get(v_toApplicative_1201_, 0);
v_toSeq_1203_ = lean_ctor_get(v_toApplicative_1201_, 2);
v_toSeqLeft_1204_ = lean_ctor_get(v_toApplicative_1201_, 3);
v_toSeqRight_1205_ = lean_ctor_get(v_toApplicative_1201_, 4);
v___f_1206_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1207_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1202_, 2);
v___f_1208_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1208_, 0, v_toFunctor_1202_);
v___f_1209_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1209_, 0, v_toFunctor_1202_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___f_1208_);
lean_ctor_set(v___x_1210_, 1, v___f_1209_);
lean_inc(v_toSeqRight_1205_);
v___f_1211_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1211_, 0, v_toSeqRight_1205_);
lean_inc(v_toSeqLeft_1204_);
v___f_1212_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1212_, 0, v_toSeqLeft_1204_);
lean_inc(v_toSeq_1203_);
v___f_1213_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1213_, 0, v_toSeq_1203_);
v___x_1214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1210_);
lean_ctor_set(v___x_1214_, 1, v___f_1206_);
lean_ctor_set(v___x_1214_, 2, v___f_1213_);
lean_ctor_set(v___x_1214_, 3, v___f_1212_);
lean_ctor_set(v___x_1214_, 4, v___f_1211_);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___f_1207_);
v___x_1216_ = l_StateRefT_x27_instMonad___redArg(v___x_1215_);
switch(lean_obj_tag(v_x_1187_))
{
case 0:
{
lean_object* v_string_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec_ref(v___x_1216_);
lean_dec_ref(v_x_1186_);
lean_dec_ref(v_inst_1185_);
v_string_1217_ = lean_ctor_get(v_x_1187_, 0);
lean_inc_ref(v_string_1217_);
lean_dec_ref_known(v_x_1187_, 1);
v___x_1218_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1217_);
lean_dec_ref(v_string_1217_);
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = lean_mk_empty_array_with_capacity(v___x_1219_);
v___x_1221_ = lean_array_push(v___x_1220_, v___x_1218_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
case 1:
{
lean_object* v_content_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v___x_1216_);
v_content_1223_ = lean_ctor_get(v_x_1187_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_x_1187_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1225_ = v_x_1187_;
v_isShared_1226_ = v_isSharedCheck_1274_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_content_1223_);
lean_dec(v_x_1187_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1274_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set_tag(v___x_1225_, 9);
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_content_1223_);
v___x_1228_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1229_; lean_object* v_snd_1230_; lean_object* v_fst_1231_; lean_object* v_fst_1232_; lean_object* v_snd_1233_; lean_object* v_pieces_1235_; uint8_t v_inEmph_1243_; uint8_t v_inBold_1244_; uint8_t v_inLink_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1272_; 
v___x_1229_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1228_);
v_snd_1230_ = lean_ctor_get(v___x_1229_, 1);
lean_inc(v_snd_1230_);
v_fst_1231_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_fst_1231_);
lean_dec_ref(v___x_1229_);
v_fst_1232_ = lean_ctor_get(v_snd_1230_, 0);
lean_inc(v_fst_1232_);
v_snd_1233_ = lean_ctor_get(v_snd_1230_, 1);
lean_inc(v_snd_1233_);
lean_dec(v_snd_1230_);
v_inEmph_1243_ = lean_ctor_get_uint8(v_x_1186_, 0);
v_inBold_1244_ = lean_ctor_get_uint8(v_x_1186_, 1);
v_inLink_1245_ = lean_ctor_get_uint8(v_x_1186_, 2);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_x_1186_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1247_ = v_x_1186_;
v_isShared_1248_ = v_isSharedCheck_1272_;
goto v_resetjp_1246_;
}
else
{
lean_dec(v_x_1186_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1272_;
goto v_resetjp_1246_;
}
v___jp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1236_ = lean_string_utf8_byte_size(v_snd_1233_);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_nat_dec_eq(v___x_1236_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = lean_mk_empty_array_with_capacity(v___x_1239_);
v___x_1241_ = lean_array_push(v___x_1240_, v_snd_1233_);
v___x_1242_ = lean_array_push(v_pieces_1235_, v___x_1241_);
v_pieces_1197_ = v___x_1242_;
goto v___jp_1196_;
}
else
{
lean_dec(v_snd_1233_);
v_pieces_1197_ = v_pieces_1235_;
goto v___jp_1196_;
}
}
v_resetjp_1246_:
{
uint8_t v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = 1;
if (v_isShared_1248_ == 0)
{
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, 1, v_inBold_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, 2, v_inLink_1245_);
v___x_1251_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; 
lean_ctor_set_uint8(v___x_1251_, 0, v___x_1249_);
v___x_1252_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1185_, v___x_1251_, v_fst_1232_, v_a_1188_, v_a_1189_, v_a_1190_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v_pieces_1255_; lean_object* v_pieces_1260_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1265_ = lean_string_utf8_byte_size(v_fst_1231_);
v___x_1266_ = lean_nat_dec_eq(v___x_1265_, v___x_1263_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = lean_mk_empty_array_with_capacity(v___x_1267_);
v___x_1269_ = lean_array_push(v___x_1268_, v_fst_1231_);
v___x_1270_ = lean_array_push(v___x_1264_, v___x_1269_);
v_pieces_1260_ = v___x_1270_;
goto v___jp_1259_;
}
else
{
lean_dec(v_fst_1231_);
v_pieces_1260_ = v___x_1264_;
goto v___jp_1259_;
}
v___jp_1254_:
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_array_push(v_pieces_1255_, v_a_1253_);
if (v_inEmph_1243_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1258_ = lean_array_push(v___x_1256_, v___x_1257_);
v_pieces_1235_ = v___x_1258_;
goto v___jp_1234_;
}
else
{
v_pieces_1235_ = v___x_1256_;
goto v___jp_1234_;
}
}
v___jp_1259_:
{
if (v_inEmph_1243_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1262_ = lean_array_push(v_pieces_1260_, v___x_1261_);
v_pieces_1255_ = v___x_1262_;
goto v___jp_1254_;
}
else
{
v_pieces_1255_ = v_pieces_1260_;
goto v___jp_1254_;
}
}
}
else
{
lean_dec(v_snd_1233_);
lean_dec(v_fst_1231_);
return v___x_1252_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v___x_1216_);
v_content_1275_ = lean_ctor_get(v_x_1187_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_x_1187_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1277_ = v_x_1187_;
v_isShared_1278_ = v_isSharedCheck_1326_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_content_1275_);
lean_dec(v_x_1187_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1326_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 9);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_content_1275_);
v___x_1280_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v_snd_1282_; lean_object* v_fst_1283_; lean_object* v_fst_1284_; lean_object* v_snd_1285_; lean_object* v_pieces_1287_; uint8_t v_inEmph_1295_; uint8_t v_inBold_1296_; uint8_t v_inLink_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1324_; 
v___x_1281_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1280_);
v_snd_1282_ = lean_ctor_get(v___x_1281_, 1);
lean_inc(v_snd_1282_);
v_fst_1283_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_fst_1283_);
lean_dec_ref(v___x_1281_);
v_fst_1284_ = lean_ctor_get(v_snd_1282_, 0);
lean_inc(v_fst_1284_);
v_snd_1285_ = lean_ctor_get(v_snd_1282_, 1);
lean_inc(v_snd_1285_);
lean_dec(v_snd_1282_);
v_inEmph_1295_ = lean_ctor_get_uint8(v_x_1186_, 0);
v_inBold_1296_ = lean_ctor_get_uint8(v_x_1186_, 1);
v_inLink_1297_ = lean_ctor_get_uint8(v_x_1186_, 2);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_x_1186_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1299_ = v_x_1186_;
v_isShared_1300_ = v_isSharedCheck_1324_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v_x_1186_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1324_;
goto v_resetjp_1298_;
}
v___jp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1288_ = lean_string_utf8_byte_size(v_snd_1285_);
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = lean_nat_dec_eq(v___x_1288_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_mk_empty_array_with_capacity(v___x_1291_);
v___x_1293_ = lean_array_push(v___x_1292_, v_snd_1285_);
v___x_1294_ = lean_array_push(v_pieces_1287_, v___x_1293_);
v_pieces_1193_ = v___x_1294_;
goto v___jp_1192_;
}
else
{
lean_dec(v_snd_1285_);
v_pieces_1193_ = v_pieces_1287_;
goto v___jp_1192_;
}
}
v_resetjp_1298_:
{
uint8_t v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = 1;
if (v_isShared_1300_ == 0)
{
v___x_1303_ = v___x_1299_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 0, v_inEmph_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 2, v_inLink_1297_);
v___x_1303_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; 
lean_ctor_set_uint8(v___x_1303_, 1, v___x_1301_);
v___x_1304_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1185_, v___x_1303_, v_fst_1284_, v_a_1188_, v_a_1189_, v_a_1190_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v_pieces_1307_; lean_object* v_pieces_1312_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1317_ = lean_string_utf8_byte_size(v_fst_1283_);
v___x_1318_ = lean_nat_dec_eq(v___x_1317_, v___x_1315_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = lean_mk_empty_array_with_capacity(v___x_1319_);
v___x_1321_ = lean_array_push(v___x_1320_, v_fst_1283_);
v___x_1322_ = lean_array_push(v___x_1316_, v___x_1321_);
v_pieces_1312_ = v___x_1322_;
goto v___jp_1311_;
}
else
{
lean_dec(v_fst_1283_);
v_pieces_1312_ = v___x_1316_;
goto v___jp_1311_;
}
v___jp_1306_:
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_array_push(v_pieces_1307_, v_a_1305_);
if (v_inBold_1296_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1310_ = lean_array_push(v___x_1308_, v___x_1309_);
v_pieces_1287_ = v___x_1310_;
goto v___jp_1286_;
}
else
{
v_pieces_1287_ = v___x_1308_;
goto v___jp_1286_;
}
}
v___jp_1311_:
{
if (v_inBold_1296_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1314_ = lean_array_push(v_pieces_1312_, v___x_1313_);
v_pieces_1307_ = v___x_1314_;
goto v___jp_1306_;
}
else
{
v_pieces_1307_ = v_pieces_1312_;
goto v___jp_1306_;
}
}
}
else
{
lean_dec(v_snd_1285_);
lean_dec(v_fst_1283_);
return v___x_1304_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref(v___x_1216_);
lean_dec_ref(v_x_1186_);
lean_dec_ref(v_inst_1185_);
v_string_1327_ = lean_ctor_get(v_x_1187_, 0);
lean_inc_ref(v_string_1327_);
lean_dec_ref_known(v_x_1187_, 1);
v___x_1328_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1327_);
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = lean_mk_empty_array_with_capacity(v___x_1329_);
v___x_1331_ = lean_array_push(v___x_1330_, v___x_1328_);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
case 4:
{
uint8_t v_mode_1333_; 
lean_dec_ref(v___x_1216_);
lean_dec_ref(v_x_1186_);
lean_dec_ref(v_inst_1185_);
v_mode_1333_ = lean_ctor_get_uint8(v_x_1187_, sizeof(void*)*1);
if (v_mode_1333_ == 0)
{
lean_object* v_string_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_string_1334_ = lean_ctor_get(v_x_1187_, 0);
lean_inc_ref(v_string_1334_);
lean_dec_ref_known(v_x_1187_, 1);
v___x_1335_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_1336_ = lean_string_append(v___x_1335_, v_string_1334_);
lean_dec_ref(v_string_1334_);
v___x_1337_ = lean_string_append(v___x_1336_, v___x_1335_);
v___x_1338_ = lean_unsigned_to_nat(1u);
v___x_1339_ = lean_mk_empty_array_with_capacity(v___x_1338_);
v___x_1340_ = lean_array_push(v___x_1339_, v___x_1337_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
else
{
lean_object* v_string_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_string_1342_ = lean_ctor_get(v_x_1187_, 0);
lean_inc_ref(v_string_1342_);
lean_dec_ref_known(v_x_1187_, 1);
v___x_1343_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_1344_ = lean_string_append(v___x_1343_, v_string_1342_);
lean_dec_ref(v_string_1342_);
v___x_1345_ = lean_string_append(v___x_1344_, v___x_1343_);
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = lean_mk_empty_array_with_capacity(v___x_1346_);
v___x_1348_ = lean_array_push(v___x_1347_, v___x_1345_);
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
}
case 5:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec_ref_known(v_x_1187_, 1);
lean_dec_ref(v___x_1216_);
lean_dec_ref(v_x_1186_);
lean_dec_ref(v_inst_1185_);
v___x_1350_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
case 6:
{
uint8_t v_inLink_1352_; 
v_inLink_1352_ = lean_ctor_get_uint8(v_x_1186_, 2);
if (v_inLink_1352_ == 0)
{
lean_object* v_content_1353_; lean_object* v_url_1354_; uint8_t v_inEmph_1355_; uint8_t v_inBold_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v___x_1216_);
v_content_1353_ = lean_ctor_get(v_x_1187_, 0);
lean_inc_ref(v_content_1353_);
v_url_1354_ = lean_ctor_get(v_x_1187_, 1);
lean_inc_ref(v_url_1354_);
lean_dec_ref_known(v_x_1187_, 2);
v_inEmph_1355_ = lean_ctor_get_uint8(v_x_1186_, 0);
v_inBold_1356_ = lean_ctor_get_uint8(v_x_1186_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_x_1186_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1358_ = v_x_1186_;
v_isShared_1359_ = v_isSharedCheck_1385_;
goto v_resetjp_1357_;
}
else
{
lean_dec(v_x_1186_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1385_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
uint8_t v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = 1;
if (v_isShared_1359_ == 0)
{
v___x_1362_ = v___x_1358_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1384_, 0, v_inEmph_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1384_, 1, v_inBold_1356_);
v___x_1362_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_ctor_set_uint8(v___x_1362_, 2, v___x_1360_);
v___x_1363_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1363_, 0, v_content_1353_);
v___x_1364_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1185_, v___x_1362_, v___x_1363_, v_a_1188_, v_a_1189_, v_a_1190_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1383_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1383_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1383_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_mk_empty_array_with_capacity(v___x_1369_);
v___x_1371_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1372_ = lean_string_append(v___x_1371_, v_url_1354_);
lean_dec_ref(v_url_1354_);
v___x_1373_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1374_ = lean_string_append(v___x_1372_, v___x_1373_);
v___x_1375_ = lean_array_push(v___x_1370_, v___x_1374_);
v___x_1376_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_1377_ = lean_array_push(v___x_1376_, v_a_1365_);
v___x_1378_ = lean_array_push(v___x_1377_, v___x_1375_);
v___x_1379_ = l_Lean_Doc_joinInlines(v___x_1378_);
lean_dec_ref(v___x_1378_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1379_);
v___x_1381_ = v___x_1367_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
else
{
lean_dec_ref(v_url_1354_);
return v___x_1364_;
}
}
}
}
else
{
lean_object* v_content_1386_; lean_object* v___x_1387_; size_t v_sz_1388_; size_t v___x_1389_; lean_object* v___x_4875__overap_1390_; lean_object* v___x_1391_; 
v_content_1386_ = lean_ctor_get(v_x_1187_, 0);
lean_inc_ref(v_content_1386_);
lean_dec_ref_known(v_x_1187_, 2);
v___x_1387_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1387_, 0, v_inst_1185_);
lean_closure_set(v___x_1387_, 1, v_x_1186_);
v_sz_1388_ = lean_array_size(v_content_1386_);
v___x_1389_ = ((size_t)0ULL);
v___x_4875__overap_1390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1216_, v___x_1387_, v_sz_1388_, v___x_1389_, v_content_1386_);
lean_inc(v_a_1190_);
lean_inc_ref(v_a_1189_);
lean_inc(v_a_1188_);
v___x_1391_ = lean_apply_4(v___x_4875__overap_1390_, v_a_1188_, v_a_1189_, v_a_1190_, lean_box(0));
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1400_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1394_ = v___x_1391_;
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = l_Lean_Doc_joinInlines(v_a_1392_);
lean_dec(v_a_1392_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
v_a_1401_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1391_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1391_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
case 7:
{
lean_object* v_name_1409_; lean_object* v_content_1410_; lean_object* v___x_1411_; size_t v_sz_1412_; size_t v___x_1413_; lean_object* v___x_4878__overap_1414_; lean_object* v___x_1415_; 
v_name_1409_ = lean_ctor_get(v_x_1187_, 0);
lean_inc_ref(v_name_1409_);
v_content_1410_ = lean_ctor_get(v_x_1187_, 1);
lean_inc_ref(v_content_1410_);
lean_dec_ref_known(v_x_1187_, 2);
v___x_1411_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1411_, 0, v_inst_1185_);
lean_closure_set(v___x_1411_, 1, v_x_1186_);
v_sz_1412_ = lean_array_size(v_content_1410_);
v___x_1413_ = ((size_t)0ULL);
v___x_4878__overap_1414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1216_, v___x_1411_, v_sz_1412_, v___x_1413_, v_content_1410_);
lean_inc(v_a_1190_);
lean_inc_ref(v_a_1189_);
lean_inc(v_a_1188_);
v___x_1415_ = lean_apply_4(v___x_4878__overap_1414_, v_a_1188_, v_a_1189_, v_a_1190_, lean_box(0));
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_1418_ = l_Lean_Doc_joinInlines(v_a_1416_);
lean_dec(v_a_1416_);
v___x_1419_ = lean_array_to_list(v___x_1418_);
v___x_1420_ = l_String_intercalate(v___x_1417_, v___x_1419_);
lean_inc_ref(v_name_1409_);
v___x_1421_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_1409_, v___x_1420_, v_a_1188_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1435_; 
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v___x_1421_, 0);
lean_dec(v_unused_1436_);
v___x_1423_ = v___x_1421_;
v_isShared_1424_ = v_isSharedCheck_1435_;
goto v_resetjp_1422_;
}
else
{
lean_dec(v___x_1421_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1435_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1425_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_1426_ = lean_string_append(v___x_1425_, v_name_1409_);
lean_dec_ref(v_name_1409_);
v___x_1427_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_1428_ = lean_string_append(v___x_1426_, v___x_1427_);
v___x_1429_ = lean_unsigned_to_nat(1u);
v___x_1430_ = lean_mk_empty_array_with_capacity(v___x_1429_);
v___x_1431_ = lean_array_push(v___x_1430_, v___x_1428_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1431_);
v___x_1433_ = v___x_1423_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v_name_1409_);
v_a_1437_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1421_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1421_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v_name_1409_);
v_a_1445_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1415_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1415_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
case 8:
{
lean_object* v_alt_1453_; lean_object* v_url_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec_ref(v___x_1216_);
lean_dec_ref(v_x_1186_);
lean_dec_ref(v_inst_1185_);
v_alt_1453_ = lean_ctor_get(v_x_1187_, 0);
lean_inc_ref(v_alt_1453_);
v_url_1454_ = lean_ctor_get(v_x_1187_, 1);
lean_inc_ref(v_url_1454_);
lean_dec_ref_known(v_x_1187_, 2);
v___x_1455_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_1456_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1453_);
lean_dec_ref(v_alt_1453_);
v___x_1457_ = lean_string_append(v___x_1455_, v___x_1456_);
lean_dec_ref(v___x_1456_);
v___x_1458_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1459_ = lean_string_append(v___x_1457_, v___x_1458_);
v___x_1460_ = lean_string_append(v___x_1459_, v_url_1454_);
lean_dec_ref(v_url_1454_);
v___x_1461_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1462_ = lean_string_append(v___x_1460_, v___x_1461_);
v___x_1463_ = lean_unsigned_to_nat(1u);
v___x_1464_ = lean_mk_empty_array_with_capacity(v___x_1463_);
v___x_1465_ = lean_array_push(v___x_1464_, v___x_1462_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
case 9:
{
lean_object* v_content_1467_; lean_object* v___x_1468_; size_t v_sz_1469_; size_t v___x_1470_; lean_object* v___x_4881__overap_1471_; lean_object* v___x_1472_; 
v_content_1467_ = lean_ctor_get(v_x_1187_, 0);
lean_inc_ref(v_content_1467_);
lean_dec_ref_known(v_x_1187_, 1);
v___x_1468_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1468_, 0, v_inst_1185_);
lean_closure_set(v___x_1468_, 1, v_x_1186_);
v_sz_1469_ = lean_array_size(v_content_1467_);
v___x_1470_ = ((size_t)0ULL);
v___x_4881__overap_1471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1216_, v___x_1468_, v_sz_1469_, v___x_1470_, v_content_1467_);
lean_inc(v_a_1190_);
lean_inc_ref(v_a_1189_);
lean_inc(v_a_1188_);
v___x_1472_ = lean_apply_4(v___x_4881__overap_1471_, v_a_1188_, v_a_1189_, v_a_1190_, lean_box(0));
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1481_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1481_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1481_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1477_ = l_Lean_Doc_joinInlines(v_a_1473_);
lean_dec(v_a_1473_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1477_);
v___x_1479_ = v___x_1475_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_a_1482_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1472_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1472_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
default: 
{
lean_object* v_container_1490_; lean_object* v_content_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec_ref(v___x_1216_);
v_container_1490_ = lean_ctor_get(v_x_1187_, 0);
lean_inc(v_container_1490_);
v_content_1491_ = lean_ctor_get(v_x_1187_, 1);
lean_inc_ref(v_content_1491_);
lean_dec_ref_known(v_x_1187_, 2);
lean_inc_ref(v_inst_1185_);
v___x_1492_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1492_, 0, v_inst_1185_);
lean_closure_set(v___x_1492_, 1, v_x_1186_);
lean_inc(v_a_1190_);
lean_inc_ref(v_a_1189_);
lean_inc(v_a_1188_);
v___x_1493_ = lean_apply_7(v_inst_1185_, v___x_1492_, v_container_1490_, v_content_1491_, v_a_1188_, v_a_1189_, v_a_1190_, lean_box(0));
return v___x_1493_;
}
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
v___jp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = l_Lean_Doc_joinInlines(v_pieces_1197_);
lean_dec_ref(v_pieces_1197_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1494_, lean_object* v_inst_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1495_, v_x_1496_, v_x_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object* v_i_1503_, lean_object* v_inst_1504_, lean_object* v_x_1505_, lean_object* v_x_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(v_i_1503_, v_inst_1504_, v_x_1505_, v_x_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1519_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1512_, v___x_1518_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object* v_inst_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(v_inst_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec(v_a_1522_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1527_, lean_object* v_inst_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1535_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1528_, v___x_1534_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object* v_i_1536_, lean_object* v_inst_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(v_i_1536_, v_inst_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1545_, 0, lean_box(0));
lean_closure_set(v___x_1545_, 1, v_inst_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1546_, lean_object* v_inst_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1548_, 0, lean_box(0));
lean_closure_set(v___x_1548_, 1, v_inst_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(uint32_t v___x_1549_, lean_object* v_s_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_string_push(v_s_1550_, v___x_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object* v___x_1552_, lean_object* v_s_1553_){
_start:
{
uint32_t v___x_2723__boxed_1554_; lean_object* v_res_1555_; 
v___x_2723__boxed_1554_ = lean_unbox_uint32(v___x_1552_);
lean_dec(v___x_1552_);
v_res_1555_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v___x_2723__boxed_1554_, v_s_1553_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed(lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v___x_1560_, lean_object* v_item_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(v_inst_1558_, v_inst_1559_, v___x_1560_, v_item_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
return v_res_1566_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___f_1569_; 
v___x_1568_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___f_1569_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1569_, 0, v___x_1568_);
return v___f_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1570_, lean_object* v_inst_1571_, lean_object* v___x_1572_, lean_object* v___x_1573_, lean_object* v_a_1574_, lean_object* v_x_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; size_t v_sz_1582_; size_t v___x_1583_; lean_object* v___x_2656__overap_1584_; lean_object* v___x_1585_; 
v___x_1581_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1581_, 0, v_inst_1570_);
lean_closure_set(v___x_1581_, 1, v_inst_1571_);
v_sz_1582_ = lean_array_size(v_a_1574_);
v___x_1583_ = ((size_t)0ULL);
v___x_2656__overap_1584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1572_, v___x_1581_, v_sz_1582_, v___x_1583_, v_a_1574_);
lean_inc(v___y_1579_);
lean_inc_ref(v___y_1578_);
lean_inc(v___y_1577_);
v___x_1585_ = lean_apply_4(v___x_2656__overap_1584_, v___y_1577_, v___y_1578_, v___y_1579_, lean_box(0));
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1614_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1614_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1614_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v_fst_1590_; lean_object* v_snd_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1613_; 
v_fst_1590_ = lean_ctor_get(v___y_1576_, 0);
v_snd_1591_ = lean_ctor_get(v___y_1576_, 1);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___y_1576_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1593_ = v___y_1576_;
v_isShared_1594_ = v_isSharedCheck_1613_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_snd_1591_);
lean_inc(v_fst_1590_);
lean_dec(v___y_1576_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1613_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___f_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
lean_inc(v_snd_1591_);
v___x_1595_ = l_Nat_reprFast(v_snd_1591_);
v___x_1596_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_1597_ = lean_string_append(v___x_1595_, v___x_1596_);
v___x_1598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_1599_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1);
v___x_1600_ = lean_string_utf8_byte_size(v___x_1597_);
v___x_1601_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1599_, v___x_1600_, v___x_1598_);
v___x_1602_ = l_Lean_Doc_joinBlocks(v_a_1586_);
lean_dec(v_a_1586_);
v___x_1603_ = l_Lean_Doc_prefixListLines(v___x_1597_, v___x_1601_, v___x_1602_);
lean_dec_ref(v___x_1602_);
v___x_1604_ = lean_array_push(v_fst_1590_, v___x_1603_);
v___x_1605_ = lean_nat_add(v_snd_1591_, v___x_1573_);
lean_dec(v_snd_1591_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v___x_1605_);
lean_ctor_set(v___x_1593_, 0, v___x_1604_);
v___x_1607_ = v___x_1593_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1608_);
v___x_1610_ = v___x_1588_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v___y_1576_);
v_a_1615_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1585_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1585_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v___x_1625_, lean_object* v___x_1626_, lean_object* v_a_1627_, lean_object* v_x_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1623_, v_inst_1624_, v___x_1625_, v___x_1626_, v_a_1627_, v_x_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec(v___x_1626_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v___x_1642_, lean_object* v_item_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; lean_object* v_term_1649_; lean_object* v_desc_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1648_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_1649_ = lean_ctor_get(v_item_1643_, 0);
lean_inc_ref(v_term_1649_);
v_desc_1650_ = lean_ctor_get(v_item_1643_, 1);
lean_inc_ref(v_desc_1650_);
lean_dec_ref(v_item_1643_);
v___x_1651_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1651_, 0, v_term_1649_);
lean_inc_ref(v_inst_1640_);
v___x_1652_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1640_, v___x_1648_, v___x_1651_, v___y_1644_, v___y_1645_, v___y_1646_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1654_; size_t v_sz_1655_; size_t v___x_1656_; lean_object* v___x_2692__overap_1657_; lean_object* v___x_1658_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v___x_1654_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1654_, 0, v_inst_1640_);
lean_closure_set(v___x_1654_, 1, v_inst_1641_);
v_sz_1655_ = lean_array_size(v_desc_1650_);
v___x_1656_ = ((size_t)0ULL);
lean_inc_ref(v_desc_1650_);
v___x_2692__overap_1657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1642_, v___x_1654_, v_sz_1655_, v___x_1656_, v_desc_1650_);
lean_inc(v___y_1646_);
lean_inc_ref(v___y_1645_);
lean_inc(v___y_1644_);
v___x_1658_ = lean_apply_4(v___x_2692__overap_1657_, v___y_1644_, v___y_1645_, v___y_1646_, lean_box(0));
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1686_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1686_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1686_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___y_1664_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_mk_empty_array_with_capacity(v___x_1671_);
v___x_1673_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_1674_ = lean_unsigned_to_nat(2u);
v___x_1675_ = lean_mk_empty_array_with_capacity(v___x_1674_);
v___x_1676_ = lean_array_push(v___x_1675_, v_a_1653_);
v___x_1677_ = lean_array_push(v___x_1676_, v___x_1673_);
v___x_1678_ = l_Lean_Doc_joinInlines(v___x_1677_);
lean_dec_ref(v___x_1677_);
v___x_1679_ = lean_array_get_size(v_desc_1650_);
lean_dec_ref(v_desc_1650_);
v___x_1680_ = lean_nat_dec_le(v___x_1679_, v___x_1671_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = lean_array_push(v___x_1672_, v___x_1678_);
v___x_1682_ = l_Array_append___redArg(v___x_1681_, v_a_1659_);
lean_dec(v_a_1659_);
v___x_1683_ = l_Lean_Doc_joinBlocks(v___x_1682_);
lean_dec_ref(v___x_1682_);
v___y_1664_ = v___x_1683_;
goto v___jp_1663_;
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec_ref(v___x_1672_);
v___x_1684_ = l_Lean_Doc_joinBlocks(v_a_1659_);
lean_dec(v_a_1659_);
v___x_1685_ = l_Array_append___redArg(v___x_1678_, v___x_1684_);
lean_dec_ref(v___x_1684_);
v___y_1664_ = v___x_1685_;
goto v___jp_1663_;
}
v___jp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1665_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1666_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1667_ = l_Lean_Doc_prefixListLines(v___x_1665_, v___x_1666_, v___y_1664_);
lean_dec_ref(v___y_1664_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1667_);
v___x_1669_ = v___x_1661_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_a_1653_);
lean_dec_ref(v_desc_1650_);
v_a_1687_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1658_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1658_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
else
{
lean_dec_ref(v_desc_1650_);
lean_dec_ref(v___x_1642_);
lean_dec_ref(v_inst_1641_);
lean_dec_ref(v_inst_1640_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v___x_1697_, lean_object* v_item_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1695_, v_inst_1696_, v___x_1697_, v_item_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_x_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v___x_1712_; lean_object* v_toApplicative_1713_; lean_object* v_toFunctor_1714_; lean_object* v_toSeq_1715_; lean_object* v_toSeqLeft_1716_; lean_object* v_toSeqRight_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___f_1720_; lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1712_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1713_ = lean_ctor_get(v___x_1712_, 0);
v_toFunctor_1714_ = lean_ctor_get(v_toApplicative_1713_, 0);
v_toSeq_1715_ = lean_ctor_get(v_toApplicative_1713_, 2);
v_toSeqLeft_1716_ = lean_ctor_get(v_toApplicative_1713_, 3);
v_toSeqRight_1717_ = lean_ctor_get(v_toApplicative_1713_, 4);
v___f_1718_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1719_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1714_, 2);
v___f_1720_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1720_, 0, v_toFunctor_1714_);
v___f_1721_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1721_, 0, v_toFunctor_1714_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___f_1720_);
lean_ctor_set(v___x_1722_, 1, v___f_1721_);
lean_inc(v_toSeqRight_1717_);
v___f_1723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1723_, 0, v_toSeqRight_1717_);
lean_inc(v_toSeqLeft_1716_);
v___f_1724_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1724_, 0, v_toSeqLeft_1716_);
lean_inc(v_toSeq_1715_);
v___f_1725_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1725_, 0, v_toSeq_1715_);
v___x_1726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1722_);
lean_ctor_set(v___x_1726_, 1, v___f_1718_);
lean_ctor_set(v___x_1726_, 2, v___f_1725_);
lean_ctor_set(v___x_1726_, 3, v___f_1724_);
lean_ctor_set(v___x_1726_, 4, v___f_1723_);
v___x_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v___f_1719_);
v___x_1728_ = l_StateRefT_x27_instMonad___redArg(v___x_1727_);
switch(lean_obj_tag(v_x_1707_))
{
case 0:
{
lean_object* v_contents_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1738_; 
lean_dec_ref(v___x_1728_);
lean_dec_ref(v_inst_1706_);
v_contents_1729_ = lean_ctor_get(v_x_1707_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_x_1707_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1731_ = v_x_1707_;
v_isShared_1732_ = v_isSharedCheck_1738_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_contents_1729_);
lean_dec(v_x_1707_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1738_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_1732_ == 0)
{
lean_ctor_set_tag(v___x_1731_, 9);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_contents_1729_);
v___x_1735_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; 
v___x_1736_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1705_, v___x_1733_, v___x_1735_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_1736_;
}
}
}
case 1:
{
lean_object* v_content_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v___x_1728_);
lean_dec_ref(v_inst_1706_);
lean_dec_ref(v_inst_1705_);
v_content_1739_ = lean_ctor_get(v_x_1707_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_x_1707_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1741_ = v_x_1707_;
v_isShared_1742_ = v_isSharedCheck_1747_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_content_1739_);
lean_dec(v_x_1707_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1747_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1743_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_1739_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1743_);
v___x_1745_ = v___x_1741_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
case 2:
{
lean_object* v_items_1748_; lean_object* v___f_1749_; size_t v_sz_1750_; size_t v___x_1751_; lean_object* v___x_2592__overap_1752_; lean_object* v___x_1753_; 
v_items_1748_ = lean_ctor_get(v_x_1707_, 0);
lean_inc_ref(v_items_1748_);
lean_dec_ref_known(v_x_1707_, 1);
lean_inc_ref(v___x_1728_);
v___f_1749_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1749_, 0, v_inst_1705_);
lean_closure_set(v___f_1749_, 1, v_inst_1706_);
lean_closure_set(v___f_1749_, 2, v___x_1728_);
v_sz_1750_ = lean_array_size(v_items_1748_);
v___x_1751_ = ((size_t)0ULL);
v___x_2592__overap_1752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1728_, v___f_1749_, v_sz_1750_, v___x_1751_, v_items_1748_);
lean_inc(v_a_1710_);
lean_inc_ref(v_a_1709_);
lean_inc(v_a_1708_);
v___x_1753_ = lean_apply_4(v___x_2592__overap_1752_, v_a_1708_, v_a_1709_, v_a_1710_, lean_box(0));
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1762_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1762_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1762_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1758_ = l_Lean_Doc_joinBlocks(v_a_1754_);
lean_dec(v_a_1754_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1758_);
v___x_1760_ = v___x_1756_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_a_1763_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1753_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1753_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
case 3:
{
lean_object* v_start_1771_; lean_object* v_items_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1808_; 
v_start_1771_ = lean_ctor_get(v_x_1707_, 0);
v_items_1772_ = lean_ctor_get(v_x_1707_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_x_1707_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1774_ = v_x_1707_;
v_isShared_1775_ = v_isSharedCheck_1808_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_items_1772_);
lean_inc(v_start_1771_);
lean_dec(v_x_1707_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1808_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v_out_1776_; lean_object* v___x_1777_; lean_object* v___f_1778_; lean_object* v___y_1780_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_out_1776_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1777_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_1728_);
v___f_1778_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1778_, 0, v_inst_1705_);
lean_closure_set(v___f_1778_, 1, v_inst_1706_);
lean_closure_set(v___f_1778_, 2, v___x_1728_);
lean_closure_set(v___f_1778_, 3, v___x_1777_);
v___x_1806_ = l_Int_toNat(v_start_1771_);
lean_dec(v_start_1771_);
v___x_1807_ = lean_nat_dec_le(v___x_1777_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_dec(v___x_1806_);
v___y_1780_ = v___x_1777_;
goto v___jp_1779_;
}
else
{
v___y_1780_ = v___x_1806_;
goto v___jp_1779_;
}
v___jp_1779_:
{
lean_object* v___x_1782_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set_tag(v___x_1774_, 0);
lean_ctor_set(v___x_1774_, 1, v___y_1780_);
lean_ctor_set(v___x_1774_, 0, v_out_1776_);
v___x_1782_ = v___x_1774_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_out_1776_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v___y_1780_);
v___x_1782_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
size_t v_sz_1783_; size_t v___x_1784_; lean_object* v___x_2406__overap_1785_; lean_object* v___x_1786_; 
v_sz_1783_ = lean_array_size(v_items_1772_);
v___x_1784_ = ((size_t)0ULL);
v___x_2406__overap_1785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1728_, v_items_1772_, v___f_1778_, v_sz_1783_, v___x_1784_, v___x_1782_);
lean_inc(v_a_1710_);
lean_inc_ref(v_a_1709_);
lean_inc(v_a_1708_);
v___x_1786_ = lean_apply_4(v___x_2406__overap_1785_, v_a_1708_, v_a_1709_, v_a_1710_, lean_box(0));
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1796_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1796_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1796_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_fst_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
v_fst_1791_ = lean_ctor_get(v_a_1787_, 0);
lean_inc(v_fst_1791_);
lean_dec(v_a_1787_);
v___x_1792_ = l_Lean_Doc_joinBlocks(v_fst_1791_);
lean_dec(v_fst_1791_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1792_);
v___x_1794_ = v___x_1789_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
v_a_1797_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1786_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1786_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_1809_; lean_object* v___f_1810_; size_t v_sz_1811_; size_t v___x_1812_; lean_object* v___x_2598__overap_1813_; lean_object* v___x_1814_; 
v_items_1809_ = lean_ctor_get(v_x_1707_, 0);
lean_inc_ref(v_items_1809_);
lean_dec_ref_known(v_x_1707_, 1);
lean_inc_ref(v___x_1728_);
v___f_1810_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 8, 3);
lean_closure_set(v___f_1810_, 0, v_inst_1705_);
lean_closure_set(v___f_1810_, 1, v_inst_1706_);
lean_closure_set(v___f_1810_, 2, v___x_1728_);
v_sz_1811_ = lean_array_size(v_items_1809_);
v___x_1812_ = ((size_t)0ULL);
v___x_2598__overap_1813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1728_, v___f_1810_, v_sz_1811_, v___x_1812_, v_items_1809_);
lean_inc(v_a_1710_);
lean_inc_ref(v_a_1709_);
lean_inc(v_a_1708_);
v___x_1814_ = lean_apply_4(v___x_2598__overap_1813_, v_a_1708_, v_a_1709_, v_a_1710_, lean_box(0));
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1823_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = l_Lean_Doc_joinBlocks(v_a_1815_);
lean_dec(v_a_1815_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1819_);
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1814_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1814_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
case 5:
{
lean_object* v_items_1832_; lean_object* v___x_1833_; size_t v_sz_1834_; size_t v___x_1835_; lean_object* v___x_2601__overap_1836_; lean_object* v___x_1837_; 
v_items_1832_ = lean_ctor_get(v_x_1707_, 0);
lean_inc_ref(v_items_1832_);
lean_dec_ref_known(v_x_1707_, 1);
v___x_1833_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1833_, 0, v_inst_1705_);
lean_closure_set(v___x_1833_, 1, v_inst_1706_);
v_sz_1834_ = lean_array_size(v_items_1832_);
v___x_1835_ = ((size_t)0ULL);
v___x_2601__overap_1836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1728_, v___x_1833_, v_sz_1834_, v___x_1835_, v_items_1832_);
lean_inc(v_a_1710_);
lean_inc_ref(v_a_1709_);
lean_inc(v_a_1708_);
v___x_1837_ = lean_apply_4(v___x_2601__overap_1836_, v_a_1708_, v_a_1709_, v_a_1710_, lean_box(0));
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1848_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1848_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1848_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1842_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_1843_ = l_Lean_Doc_joinBlocks(v_a_1838_);
lean_dec(v_a_1838_);
v___x_1844_ = l_Lean_Doc_prefixLines(v___x_1842_, v___x_1843_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1844_);
v___x_1846_ = v___x_1840_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_a_1849_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1837_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1837_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
case 6:
{
lean_object* v_content_1857_; lean_object* v___x_1858_; size_t v_sz_1859_; size_t v___x_1860_; lean_object* v___x_2604__overap_1861_; lean_object* v___x_1862_; 
v_content_1857_ = lean_ctor_get(v_x_1707_, 0);
lean_inc_ref(v_content_1857_);
lean_dec_ref_known(v_x_1707_, 1);
v___x_1858_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1858_, 0, v_inst_1705_);
lean_closure_set(v___x_1858_, 1, v_inst_1706_);
v_sz_1859_ = lean_array_size(v_content_1857_);
v___x_1860_ = ((size_t)0ULL);
v___x_2604__overap_1861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1728_, v___x_1858_, v_sz_1859_, v___x_1860_, v_content_1857_);
lean_inc(v_a_1710_);
lean_inc_ref(v_a_1709_);
lean_inc(v_a_1708_);
v___x_1862_ = lean_apply_4(v___x_2604__overap_1861_, v_a_1708_, v_a_1709_, v_a_1710_, lean_box(0));
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1871_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1867_ = l_Lean_Doc_joinBlocks(v_a_1863_);
lean_dec(v_a_1863_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1867_);
v___x_1869_ = v___x_1865_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
v_a_1872_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1862_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1862_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
default: 
{
lean_object* v_container_1880_; lean_object* v_content_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec_ref(v___x_1728_);
v_container_1880_ = lean_ctor_get(v_x_1707_, 0);
lean_inc(v_container_1880_);
v_content_1881_ = lean_ctor_get(v_x_1707_, 1);
lean_inc_ref(v_content_1881_);
lean_dec_ref_known(v_x_1707_, 2);
v___x_1882_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc_ref(v_inst_1705_);
v___x_1883_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed), 8, 3);
lean_closure_set(v___x_1883_, 0, lean_box(0));
lean_closure_set(v___x_1883_, 1, v_inst_1705_);
lean_closure_set(v___x_1883_, 2, v___x_1882_);
lean_inc_ref(v_inst_1706_);
v___x_1884_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1884_, 0, v_inst_1705_);
lean_closure_set(v___x_1884_, 1, v_inst_1706_);
lean_inc(v_a_1710_);
lean_inc_ref(v_a_1709_);
lean_inc(v_a_1708_);
v___x_1885_ = lean_apply_8(v_inst_1706_, v___x_1883_, v___x_1884_, v_container_1880_, v_content_1881_, v_a_1708_, v_a_1709_, v_a_1710_, lean_box(0));
return v___x_1885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed(lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_x_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1886_, v_inst_1887_, v_x_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v_inst_1894_, lean_object* v_inst_1895_, lean_object* v___x_1896_, lean_object* v_item_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; size_t v_sz_1903_; size_t v___x_1904_; lean_object* v___x_2631__overap_1905_; lean_object* v___x_1906_; 
v___x_1902_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1902_, 0, v_inst_1894_);
lean_closure_set(v___x_1902_, 1, v_inst_1895_);
v_sz_1903_ = lean_array_size(v_item_1897_);
v___x_1904_ = ((size_t)0ULL);
v___x_2631__overap_1905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1896_, v___x_1902_, v_sz_1903_, v___x_1904_, v_item_1897_);
lean_inc(v___y_1900_);
lean_inc_ref(v___y_1899_);
lean_inc(v___y_1898_);
v___x_1906_ = lean_apply_4(v___x_2631__overap_1905_, v___y_1898_, v___y_1899_, v___y_1900_, lean_box(0));
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1918_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1918_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1918_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1911_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1912_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1913_ = l_Lean_Doc_joinBlocks(v_a_1907_);
lean_dec(v_a_1907_);
v___x_1914_ = l_Lean_Doc_prefixListLines(v___x_1911_, v___x_1912_, v___x_1913_);
lean_dec_ref(v___x_1913_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1914_);
v___x_1916_ = v___x_1909_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_a_1919_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1906_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1906_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1927_, lean_object* v_b_1928_, lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v_x_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1929_, v_inst_1930_, v_x_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object* v_i_1937_, lean_object* v_b_1938_, lean_object* v_inst_1939_, lean_object* v_inst_1940_, lean_object* v_x_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(v_i_1937_, v_b_1938_, v_inst_1939_, v_inst_1940_, v_x_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1947_, lean_object* v_inst_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1947_, v_inst_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1955_, v_inst_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1963_, lean_object* v_b_1964_, lean_object* v_inst_1965_, lean_object* v_inst_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1965_, v_inst_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1973_, lean_object* v_b_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1973_, v_b_1974_, v_inst_1975_, v_inst_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1983_, lean_object* v_inst_1984_){
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
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1986_, lean_object* v_b_1987_, lean_object* v_inst_1988_, lean_object* v_inst_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_1990_, 0, lean_box(0));
lean_closure_set(v___x_1990_, 1, lean_box(0));
lean_closure_set(v___x_1990_, 2, v_inst_1988_);
lean_closure_set(v___x_1990_, 3, v_inst_1989_);
return v___x_1990_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = 35;
v___x_1992_ = lean_box_uint32(v___x_1991_);
return v___x_1992_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___f_1994_; 
v___x_1993_ = l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1994_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1994_, 0, v___x_1993_);
return v___f_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1995_, lean_object* v_inst_1996_, lean_object* v_level_1997_, lean_object* v_part_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_Doc_partMarkdown___redArg(v_inst_1995_, v_inst_1996_, v_level_1997_, v_part_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec(v_level_1997_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg(lean_object* v_inst_2004_, lean_object* v_inst_2005_, lean_object* v_level_2006_, lean_object* v_part_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v___x_2012_; lean_object* v_toApplicative_2013_; lean_object* v_toFunctor_2014_; lean_object* v_toSeq_2015_; lean_object* v_toSeqLeft_2016_; lean_object* v_toSeqRight_2017_; lean_object* v___f_2018_; lean_object* v___f_2019_; lean_object* v___f_2020_; lean_object* v___f_2021_; lean_object* v___x_2022_; lean_object* v___f_2023_; lean_object* v___f_2024_; lean_object* v___f_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v_title_2029_; lean_object* v_content_2030_; lean_object* v_subParts_2031_; lean_object* v___x_2032_; size_t v_sz_2033_; size_t v___x_2034_; lean_object* v___x_680__overap_2035_; lean_object* v___x_2036_; 
v___x_2012_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2013_ = lean_ctor_get(v___x_2012_, 0);
v_toFunctor_2014_ = lean_ctor_get(v_toApplicative_2013_, 0);
v_toSeq_2015_ = lean_ctor_get(v_toApplicative_2013_, 2);
v_toSeqLeft_2016_ = lean_ctor_get(v_toApplicative_2013_, 3);
v_toSeqRight_2017_ = lean_ctor_get(v_toApplicative_2013_, 4);
v___f_2018_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2019_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2014_, 2);
v___f_2020_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2020_, 0, v_toFunctor_2014_);
v___f_2021_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2021_, 0, v_toFunctor_2014_);
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___f_2020_);
lean_ctor_set(v___x_2022_, 1, v___f_2021_);
lean_inc(v_toSeqRight_2017_);
v___f_2023_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2023_, 0, v_toSeqRight_2017_);
lean_inc(v_toSeqLeft_2016_);
v___f_2024_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2024_, 0, v_toSeqLeft_2016_);
lean_inc(v_toSeq_2015_);
v___f_2025_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2025_, 0, v_toSeq_2015_);
v___x_2026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2022_);
lean_ctor_set(v___x_2026_, 1, v___f_2018_);
lean_ctor_set(v___x_2026_, 2, v___f_2025_);
lean_ctor_set(v___x_2026_, 3, v___f_2024_);
lean_ctor_set(v___x_2026_, 4, v___f_2023_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set(v___x_2027_, 1, v___f_2019_);
v___x_2028_ = l_StateRefT_x27_instMonad___redArg(v___x_2027_);
v_title_2029_ = lean_ctor_get(v_part_2007_, 0);
lean_inc_ref(v_title_2029_);
v_content_2030_ = lean_ctor_get(v_part_2007_, 3);
lean_inc_ref(v_content_2030_);
v_subParts_2031_ = lean_ctor_get(v_part_2007_, 4);
lean_inc_ref(v_subParts_2031_);
lean_dec_ref(v_part_2007_);
lean_inc_ref(v_inst_2004_);
v___x_2032_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_2032_, 0, lean_box(0));
lean_closure_set(v___x_2032_, 1, v_inst_2004_);
v_sz_2033_ = lean_array_size(v_title_2029_);
v___x_2034_ = ((size_t)0ULL);
lean_inc_ref(v___x_2028_);
v___x_680__overap_2035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2028_, v___x_2032_, v_sz_2033_, v___x_2034_, v_title_2029_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
lean_inc(v_a_2008_);
v___x_2036_ = lean_apply_4(v___x_680__overap_2035_, v_a_2008_, v_a_2009_, v_a_2010_, lean_box(0));
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; size_t v_sz_2039_; lean_object* v___x_683__overap_2040_; lean_object* v___x_2041_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
lean_inc_ref(v_inst_2005_);
lean_inc_ref(v_inst_2004_);
v___x_2038_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_2038_, 0, lean_box(0));
lean_closure_set(v___x_2038_, 1, lean_box(0));
lean_closure_set(v___x_2038_, 2, v_inst_2004_);
lean_closure_set(v___x_2038_, 3, v_inst_2005_);
v_sz_2039_ = lean_array_size(v_content_2030_);
lean_inc_ref(v___x_2028_);
v___x_683__overap_2040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2028_, v___x_2038_, v_sz_2039_, v___x_2034_, v_content_2030_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
lean_inc(v_a_2008_);
v___x_2041_ = lean_apply_4(v___x_683__overap_2040_, v_a_2008_, v_a_2009_, v_a_2010_, lean_box(0));
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; lean_object* v___f_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; size_t v_sz_2049_; lean_object* v___x_686__overap_2050_; lean_object* v___x_2051_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_2044_ = lean_obj_once(&l_Lean_Doc_partMarkdown___redArg___closed__0, &l_Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_partMarkdown___redArg___closed__0);
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_add(v_level_2006_, v___x_2045_);
lean_inc(v___x_2046_);
v___x_2047_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_2044_, v___x_2046_, v___x_2043_);
v___x_2048_ = lean_alloc_closure((void*)(l_Lean_Doc_partMarkdown___redArg___boxed), 8, 3);
lean_closure_set(v___x_2048_, 0, v_inst_2004_);
lean_closure_set(v___x_2048_, 1, v_inst_2005_);
lean_closure_set(v___x_2048_, 2, v___x_2046_);
v_sz_2049_ = lean_array_size(v_subParts_2031_);
v___x_686__overap_2050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2028_, v___x_2048_, v_sz_2049_, v___x_2034_, v_subParts_2031_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
lean_inc(v_a_2008_);
v___x_2051_ = lean_apply_4(v___x_686__overap_2050_, v_a_2008_, v_a_2009_, v_a_2010_, lean_box(0));
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2070_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2070_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2070_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2056_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_2057_ = lean_string_append(v___x_2047_, v___x_2056_);
v___x_2058_ = lean_mk_empty_array_with_capacity(v___x_2045_);
lean_inc_ref_n(v___x_2058_, 2);
v___x_2059_ = lean_array_push(v___x_2058_, v___x_2057_);
v___x_2060_ = lean_array_push(v___x_2058_, v___x_2059_);
v___x_2061_ = l_Array_append___redArg(v___x_2060_, v_a_2037_);
lean_dec(v_a_2037_);
v___x_2062_ = l_Lean_Doc_joinInlines(v___x_2061_);
lean_dec_ref(v___x_2061_);
v___x_2063_ = lean_array_push(v___x_2058_, v___x_2062_);
v___x_2064_ = l_Array_append___redArg(v___x_2063_, v_a_2042_);
lean_dec(v_a_2042_);
v___x_2065_ = l_Array_append___redArg(v___x_2064_, v_a_2052_);
lean_dec(v_a_2052_);
v___x_2066_ = l_Lean_Doc_joinBlocks(v___x_2065_);
lean_dec_ref(v___x_2065_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2066_);
v___x_2068_ = v___x_2054_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v___x_2047_);
lean_dec(v_a_2042_);
lean_dec(v_a_2037_);
v_a_2071_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2051_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2051_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v_a_2037_);
lean_dec_ref(v_subParts_2031_);
lean_dec_ref(v___x_2028_);
lean_dec_ref(v_inst_2005_);
lean_dec_ref(v_inst_2004_);
v_a_2079_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2041_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2041_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref(v_subParts_2031_);
lean_dec_ref(v_content_2030_);
lean_dec_ref(v___x_2028_);
lean_dec_ref(v_inst_2005_);
lean_dec_ref(v_inst_2004_);
v_a_2087_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2036_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2036_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown(lean_object* v_i_2095_, lean_object* v_b_2096_, lean_object* v_p_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_level_2100_, lean_object* v_part_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2098_, v_inst_2099_, v_level_2100_, v_part_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___boxed(lean_object* v_i_2107_, lean_object* v_b_2108_, lean_object* v_p_2109_, lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_level_2112_, lean_object* v_part_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_Doc_partMarkdown(v_i_2107_, v_b_2108_, v_p_2109_, v_inst_2110_, v_inst_2111_, v_level_2112_, v_part_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec(v_level_2112_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_2119_, lean_object* v_inst_2120_, lean_object* v_part_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2119_, v_inst_2120_, v___x_2126_, v_part_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_2128_, lean_object* v_inst_2129_, lean_object* v_part_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_2128_, v_inst_2129_, v_part_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_2136_, lean_object* v_inst_2137_){
_start:
{
lean_object* v___f_2138_; 
v___f_2138_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2138_, 0, v_inst_2136_);
lean_closure_set(v___f_2138_, 1, v_inst_2137_);
return v___f_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_2139_, lean_object* v_b_2140_, lean_object* v_p_2141_, lean_object* v_inst_2142_, lean_object* v_inst_2143_){
_start:
{
lean_object* v___f_2144_; 
v___f_2144_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2144_, 0, v_inst_2142_);
lean_closure_set(v___f_2144_, 1, v_inst_2143_);
return v___f_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg(lean_object* v_inst_2145_, lean_object* v_f_2146_, lean_object* v_go_2147_, lean_object* v_val_2148_, lean_object* v_content_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v___x_2154_; lean_object* v_toApplicative_2155_; lean_object* v_toFunctor_2156_; lean_object* v_toSeq_2157_; lean_object* v_toSeqLeft_2158_; lean_object* v_toSeqRight_2159_; lean_object* v___f_2160_; lean_object* v___f_2161_; lean_object* v___f_2162_; lean_object* v___f_2163_; lean_object* v___x_2164_; lean_object* v___f_2165_; lean_object* v___f_2166_; lean_object* v___f_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2154_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2155_ = lean_ctor_get(v___x_2154_, 0);
v_toFunctor_2156_ = lean_ctor_get(v_toApplicative_2155_, 0);
v_toSeq_2157_ = lean_ctor_get(v_toApplicative_2155_, 2);
v_toSeqLeft_2158_ = lean_ctor_get(v_toApplicative_2155_, 3);
v_toSeqRight_2159_ = lean_ctor_get(v_toApplicative_2155_, 4);
v___f_2160_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2161_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2156_, 2);
v___f_2162_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2162_, 0, v_toFunctor_2156_);
v___f_2163_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2163_, 0, v_toFunctor_2156_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___f_2162_);
lean_ctor_set(v___x_2164_, 1, v___f_2163_);
lean_inc(v_toSeqRight_2159_);
v___f_2165_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2165_, 0, v_toSeqRight_2159_);
lean_inc(v_toSeqLeft_2158_);
v___f_2166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2166_, 0, v_toSeqLeft_2158_);
lean_inc(v_toSeq_2157_);
v___f_2167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2167_, 0, v_toSeq_2157_);
v___x_2168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2164_);
lean_ctor_set(v___x_2168_, 1, v___f_2160_);
lean_ctor_set(v___x_2168_, 2, v___f_2167_);
lean_ctor_set(v___x_2168_, 3, v___f_2166_);
lean_ctor_set(v___x_2168_, 4, v___f_2165_);
v___x_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___f_2161_);
v___x_2170_ = l_StateRefT_x27_instMonad___redArg(v___x_2169_);
v___x_2171_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2148_, v_inst_2145_);
if (lean_obj_tag(v___x_2171_) == 0)
{
size_t v_sz_2172_; size_t v___x_2173_; lean_object* v___x_288__overap_2174_; lean_object* v___x_2175_; 
lean_dec_ref(v_f_2146_);
v_sz_2172_ = lean_array_size(v_content_2149_);
v___x_2173_ = ((size_t)0ULL);
v___x_288__overap_2174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2170_, v_go_2147_, v_sz_2172_, v___x_2173_, v_content_2149_);
lean_inc(v_a_2152_);
lean_inc_ref(v_a_2151_);
lean_inc(v_a_2150_);
v___x_2175_ = lean_apply_4(v___x_288__overap_2174_, v_a_2150_, v_a_2151_, v_a_2152_, lean_box(0));
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2184_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2184_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2184_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2180_ = l_Lean_Doc_joinInlines(v_a_2176_);
lean_dec(v_a_2176_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2180_);
v___x_2182_ = v___x_2178_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
v_a_2185_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2175_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2175_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_object* v_val_2193_; lean_object* v___x_2194_; 
lean_dec_ref(v___x_2170_);
v_val_2193_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_val_2193_);
lean_dec_ref_known(v___x_2171_, 1);
lean_inc(v_a_2152_);
lean_inc_ref(v_a_2151_);
lean_inc(v_a_2150_);
v___x_2194_ = lean_apply_7(v_f_2146_, v_go_2147_, v_val_2193_, v_content_2149_, v_a_2150_, v_a_2151_, v_a_2152_, lean_box(0));
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg___boxed(lean_object* v_inst_2195_, lean_object* v_f_2196_, lean_object* v_go_2197_, lean_object* v_val_2198_, lean_object* v_content_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2195_, v_f_2196_, v_go_2197_, v_val_2198_, v_content_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec(v_val_2198_);
lean_dec(v_inst_2195_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer(lean_object* v_00_u03b1_2205_, lean_object* v_inst_2206_, lean_object* v_f_2207_, lean_object* v_go_2208_, lean_object* v_val_2209_, lean_object* v_content_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2206_, v_f_2207_, v_go_2208_, v_val_2209_, v_content_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___boxed(lean_object* v_00_u03b1_2216_, lean_object* v_inst_2217_, lean_object* v_f_2218_, lean_object* v_go_2219_, lean_object* v_val_2220_, lean_object* v_content_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_Doc_mkInlineMdRenderer(v_00_u03b1_2216_, v_inst_2217_, v_f_2218_, v_go_2219_, v_val_2220_, v_content_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec(v_val_2220_);
lean_dec(v_inst_2217_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg(lean_object* v_inst_2227_, lean_object* v_f_2228_, lean_object* v_goI_2229_, lean_object* v_goB_2230_, lean_object* v_val_2231_, lean_object* v_content_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v___x_2237_; lean_object* v_toApplicative_2238_; lean_object* v_toFunctor_2239_; lean_object* v_toSeq_2240_; lean_object* v_toSeqLeft_2241_; lean_object* v_toSeqRight_2242_; lean_object* v___f_2243_; lean_object* v___f_2244_; lean_object* v___f_2245_; lean_object* v___f_2246_; lean_object* v___x_2247_; lean_object* v___f_2248_; lean_object* v___f_2249_; lean_object* v___f_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2237_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2238_ = lean_ctor_get(v___x_2237_, 0);
v_toFunctor_2239_ = lean_ctor_get(v_toApplicative_2238_, 0);
v_toSeq_2240_ = lean_ctor_get(v_toApplicative_2238_, 2);
v_toSeqLeft_2241_ = lean_ctor_get(v_toApplicative_2238_, 3);
v_toSeqRight_2242_ = lean_ctor_get(v_toApplicative_2238_, 4);
v___f_2243_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2244_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2239_, 2);
v___f_2245_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2245_, 0, v_toFunctor_2239_);
v___f_2246_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2246_, 0, v_toFunctor_2239_);
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___f_2245_);
lean_ctor_set(v___x_2247_, 1, v___f_2246_);
lean_inc(v_toSeqRight_2242_);
v___f_2248_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2248_, 0, v_toSeqRight_2242_);
lean_inc(v_toSeqLeft_2241_);
v___f_2249_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2249_, 0, v_toSeqLeft_2241_);
lean_inc(v_toSeq_2240_);
v___f_2250_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2250_, 0, v_toSeq_2240_);
v___x_2251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2247_);
lean_ctor_set(v___x_2251_, 1, v___f_2243_);
lean_ctor_set(v___x_2251_, 2, v___f_2250_);
lean_ctor_set(v___x_2251_, 3, v___f_2249_);
lean_ctor_set(v___x_2251_, 4, v___f_2248_);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v___f_2244_);
v___x_2253_ = l_StateRefT_x27_instMonad___redArg(v___x_2252_);
v___x_2254_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2231_, v_inst_2227_);
if (lean_obj_tag(v___x_2254_) == 0)
{
size_t v_sz_2255_; size_t v___x_2256_; lean_object* v___x_288__overap_2257_; lean_object* v___x_2258_; 
lean_dec_ref(v_goI_2229_);
lean_dec_ref(v_f_2228_);
v_sz_2255_ = lean_array_size(v_content_2232_);
v___x_2256_ = ((size_t)0ULL);
v___x_288__overap_2257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2253_, v_goB_2230_, v_sz_2255_, v___x_2256_, v_content_2232_);
lean_inc(v_a_2235_);
lean_inc_ref(v_a_2234_);
lean_inc(v_a_2233_);
v___x_2258_ = lean_apply_4(v___x_288__overap_2257_, v_a_2233_, v_a_2234_, v_a_2235_, lean_box(0));
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2267_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2267_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2267_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2263_ = l_Lean_Doc_joinBlocks(v_a_2259_);
lean_dec(v_a_2259_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v___x_2263_);
v___x_2265_ = v___x_2261_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
v_a_2268_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2258_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2258_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_object* v_val_2276_; lean_object* v___x_2277_; 
lean_dec_ref(v___x_2253_);
v_val_2276_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_val_2276_);
lean_dec_ref_known(v___x_2254_, 1);
lean_inc(v_a_2235_);
lean_inc_ref(v_a_2234_);
lean_inc(v_a_2233_);
v___x_2277_ = lean_apply_8(v_f_2228_, v_goI_2229_, v_goB_2230_, v_val_2276_, v_content_2232_, v_a_2233_, v_a_2234_, v_a_2235_, lean_box(0));
return v___x_2277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg___boxed(lean_object* v_inst_2278_, lean_object* v_f_2279_, lean_object* v_goI_2280_, lean_object* v_goB_2281_, lean_object* v_val_2282_, lean_object* v_content_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2278_, v_f_2279_, v_goI_2280_, v_goB_2281_, v_val_2282_, v_content_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec(v_val_2282_);
lean_dec(v_inst_2278_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer(lean_object* v_00_u03b1_2289_, lean_object* v_inst_2290_, lean_object* v_f_2291_, lean_object* v_goI_2292_, lean_object* v_goB_2293_, lean_object* v_val_2294_, lean_object* v_content_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2290_, v_f_2291_, v_goI_2292_, v_goB_2293_, v_val_2294_, v_content_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___boxed(lean_object* v_00_u03b1_2301_, lean_object* v_inst_2302_, lean_object* v_f_2303_, lean_object* v_goI_2304_, lean_object* v_goB_2305_, lean_object* v_val_2306_, lean_object* v_content_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_Doc_mkBlockMdRenderer(v_00_u03b1_2301_, v_inst_2302_, v_f_2303_, v_goI_2304_, v_goB_2305_, v_val_2306_, v_content_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec(v_val_2306_);
lean_dec(v_inst_2302_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(lean_object* v_as_2317_, size_t v_i_2318_, size_t v_stop_2319_, lean_object* v_b_2320_){
_start:
{
uint8_t v___x_2321_; 
v___x_2321_ = lean_usize_dec_eq(v_i_2318_, v_stop_2319_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; lean_object* v_fst_2323_; lean_object* v_snd_2324_; lean_object* v___x_2325_; size_t v___x_2326_; size_t v___x_2327_; 
v___x_2322_ = lean_array_uget_borrowed(v_as_2317_, v_i_2318_);
v_fst_2323_ = lean_ctor_get(v___x_2322_, 0);
v_snd_2324_ = lean_ctor_get(v___x_2322_, 1);
lean_inc(v_snd_2324_);
lean_inc(v_fst_2323_);
v___x_2325_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2323_, v_snd_2324_, v_b_2320_);
v___x_2326_ = ((size_t)1ULL);
v___x_2327_ = lean_usize_add(v_i_2318_, v___x_2326_);
v_i_2318_ = v___x_2327_;
v_b_2320_ = v___x_2325_;
goto _start;
}
else
{
return v_b_2320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0___boxed(lean_object* v_as_2329_, lean_object* v_i_2330_, lean_object* v_stop_2331_, lean_object* v_b_2332_){
_start:
{
size_t v_i_boxed_2333_; size_t v_stop_boxed_2334_; lean_object* v_res_2335_; 
v_i_boxed_2333_ = lean_unbox_usize(v_i_2330_);
lean_dec(v_i_2330_);
v_stop_boxed_2334_ = lean_unbox_usize(v_stop_2331_);
lean_dec(v_stop_2331_);
v_res_2335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v_as_2329_, v_i_boxed_2333_, v_stop_boxed_2334_, v_b_2332_);
lean_dec_ref(v_as_2329_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(lean_object* v_as_2336_, size_t v_i_2337_, size_t v_stop_2338_, lean_object* v_b_2339_){
_start:
{
lean_object* v___y_2341_; uint8_t v___x_2345_; 
v___x_2345_ = lean_usize_dec_eq(v_i_2337_, v_stop_2338_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2346_ = lean_array_uget_borrowed(v_as_2336_, v_i_2337_);
v___x_2347_ = lean_unsigned_to_nat(0u);
v___x_2348_ = lean_array_get_size(v___x_2346_);
v___x_2349_ = lean_nat_dec_lt(v___x_2347_, v___x_2348_);
if (v___x_2349_ == 0)
{
v___y_2341_ = v_b_2339_;
goto v___jp_2340_;
}
else
{
uint8_t v___x_2350_; 
v___x_2350_ = lean_nat_dec_le(v___x_2348_, v___x_2348_);
if (v___x_2350_ == 0)
{
if (v___x_2349_ == 0)
{
v___y_2341_ = v_b_2339_;
goto v___jp_2340_;
}
else
{
size_t v___x_2351_; size_t v___x_2352_; lean_object* v___x_2353_; 
v___x_2351_ = ((size_t)0ULL);
v___x_2352_ = lean_usize_of_nat(v___x_2348_);
v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2346_, v___x_2351_, v___x_2352_, v_b_2339_);
v___y_2341_ = v___x_2353_;
goto v___jp_2340_;
}
}
else
{
size_t v___x_2354_; size_t v___x_2355_; lean_object* v___x_2356_; 
v___x_2354_ = ((size_t)0ULL);
v___x_2355_ = lean_usize_of_nat(v___x_2348_);
v___x_2356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2346_, v___x_2354_, v___x_2355_, v_b_2339_);
v___y_2341_ = v___x_2356_;
goto v___jp_2340_;
}
}
}
else
{
return v_b_2339_;
}
v___jp_2340_:
{
size_t v___x_2342_; size_t v___x_2343_; 
v___x_2342_ = ((size_t)1ULL);
v___x_2343_ = lean_usize_add(v_i_2337_, v___x_2342_);
v_i_2337_ = v___x_2343_;
v_b_2339_ = v___y_2341_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1___boxed(lean_object* v_as_2357_, lean_object* v_i_2358_, lean_object* v_stop_2359_, lean_object* v_b_2360_){
_start:
{
size_t v_i_boxed_2361_; size_t v_stop_boxed_2362_; lean_object* v_res_2363_; 
v_i_boxed_2361_ = lean_unbox_usize(v_i_2358_);
lean_dec(v_i_2358_);
v_stop_boxed_2362_ = lean_unbox_usize(v_stop_2359_);
lean_dec(v_stop_2359_);
v_res_2363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_as_2357_, v_i_boxed_2361_, v_stop_boxed_2362_, v_b_2360_);
lean_dec_ref(v_as_2357_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(lean_object* v_init_2364_, lean_object* v_es_2365_){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = lean_array_get_size(v_es_2365_);
v___x_2368_ = lean_nat_dec_lt(v___x_2366_, v___x_2367_);
if (v___x_2368_ == 0)
{
return v_init_2364_;
}
else
{
uint8_t v___x_2369_; 
v___x_2369_ = lean_nat_dec_le(v___x_2367_, v___x_2367_);
if (v___x_2369_ == 0)
{
if (v___x_2368_ == 0)
{
return v_init_2364_;
}
else
{
size_t v___x_2370_; size_t v___x_2371_; lean_object* v___x_2372_; 
v___x_2370_ = ((size_t)0ULL);
v___x_2371_ = lean_usize_of_nat(v___x_2367_);
v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2365_, v___x_2370_, v___x_2371_, v_init_2364_);
return v___x_2372_;
}
}
else
{
size_t v___x_2373_; size_t v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = ((size_t)0ULL);
v___x_2374_ = lean_usize_of_nat(v___x_2367_);
v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2365_, v___x_2373_, v___x_2374_, v_init_2364_);
return v___x_2375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries___boxed(lean_object* v_init_2376_, lean_object* v_es_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v_init_2376_, v_es_2377_);
lean_dec_ref(v_es_2377_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_2379_, lean_object* v_x_2380_){
_start:
{
if (lean_obj_tag(v_x_2380_) == 0)
{
lean_object* v_k_2381_; lean_object* v_v_2382_; lean_object* v_l_2383_; lean_object* v_r_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_k_2381_ = lean_ctor_get(v_x_2380_, 1);
v_v_2382_ = lean_ctor_get(v_x_2380_, 2);
v_l_2383_ = lean_ctor_get(v_x_2380_, 3);
v_r_2384_ = lean_ctor_get(v_x_2380_, 4);
v___x_2385_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2379_, v_l_2383_);
lean_inc(v_v_2382_);
lean_inc(v_k_2381_);
v___x_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2386_, 0, v_k_2381_);
lean_ctor_set(v___x_2386_, 1, v_v_2382_);
v___x_2387_ = lean_array_push(v___x_2385_, v___x_2386_);
v_init_2379_ = v___x_2387_;
v_x_2380_ = v_r_2384_;
goto _start;
}
else
{
return v_init_2379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_2389_, lean_object* v_x_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2389_, v_x_2390_);
lean_dec(v_x_2390_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2394_){
_start:
{
lean_object* v_current_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_current_2395_ = lean_ctor_get(v_s_2394_, 1);
v___x_2396_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2397_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2396_, v_current_2395_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_s_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_s_2398_);
lean_dec_ref(v_s_2398_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_box(0);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2402_);
lean_dec_ref(v_x_2402_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2404_, lean_object* v_s_2405_){
_start:
{
lean_object* v_current_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_current_2406_ = lean_ctor_get(v_s_2405_, 1);
v___x_2407_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2408_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2407_, v_current_2406_);
lean_inc_ref_n(v___x_2408_, 2);
v___x_2409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
lean_ctor_set(v___x_2409_, 2, v___x_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2410_, lean_object* v_s_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2410_, v_s_2411_);
lean_dec_ref(v_s_2411_);
lean_dec_ref(v_x_2410_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2413_, lean_object* v_x_2414_){
_start:
{
lean_object* v_fst_2415_; lean_object* v_snd_2416_; lean_object* v_imported_2417_; lean_object* v_current_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2426_; 
v_fst_2415_ = lean_ctor_get(v_x_2414_, 0);
lean_inc(v_fst_2415_);
v_snd_2416_ = lean_ctor_get(v_x_2414_, 1);
lean_inc(v_snd_2416_);
lean_dec_ref(v_x_2414_);
v_imported_2417_ = lean_ctor_get(v_s_2413_, 0);
v_current_2418_ = lean_ctor_get(v_s_2413_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_s_2413_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2420_ = v_s_2413_;
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_current_2418_);
lean_inc(v_imported_2417_);
lean_dec(v_s_2413_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2422_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2415_, v_snd_2416_, v_current_2418_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 1, v___x_2422_);
v___x_2424_ = v___x_2420_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_imported_2417_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2427_, lean_object* v_es_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_inc(v___x_2427_);
v___x_2431_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v___x_2427_, v_es_2428_);
v___x_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
lean_ctor_set(v___x_2432_, 1, v___x_2427_);
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2434_, lean_object* v_es_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2434_, v_es_2435_, v___y_2436_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_es_2435_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2439_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2442_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2474_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_a_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_();
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(lean_object* v_init_2477_, lean_object* v_t_2478_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2477_, v_t_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_2480_, lean_object* v_t_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(v_init_2480_, v_t_2481_);
lean_dec(v_t_2481_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_));
v___x_2502_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2____boxed(lean_object* v_a_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_();
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2506_ = lean_box(1);
v___x_2507_ = lean_st_mk_ref(v___x_2506_);
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2____boxed(lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_();
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = lean_box(1);
v___x_2513_ = lean_st_mk_ref(v___x_2512_);
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2____boxed(lean_object* v_a_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_();
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer(lean_object* v_type_2517_, lean_object* v_r_2518_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2520_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2521_ = lean_st_ref_take(v___x_2520_);
v___x_2522_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2517_, v_r_2518_, v___x_2521_);
v___x_2523_ = lean_st_ref_set(v___x_2520_, v___x_2522_);
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer___boxed(lean_object* v_type_2525_, lean_object* v_r_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_Doc_addBuiltinInlineMdRenderer(v_type_2525_, v_r_2526_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer(lean_object* v_type_2529_, lean_object* v_r_2530_){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2532_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2533_ = lean_st_ref_take(v___x_2532_);
v___x_2534_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2529_, v_r_2530_, v___x_2533_);
v___x_2535_ = lean_st_ref_set(v___x_2532_, v___x_2534_);
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer___boxed(lean_object* v_type_2537_, lean_object* v_r_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_Doc_addBuiltinBlockMdRenderer(v_type_2537_, v_r_2538_);
return v_res_2540_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2541_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2545_ = lean_unsigned_to_nat(0u);
v___x_2546_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
lean_ctor_set(v___x_2546_, 2, v___x_2545_);
lean_ctor_set(v___x_2546_, 3, v___x_2545_);
lean_ctor_set(v___x_2546_, 4, v___x_2544_);
lean_ctor_set(v___x_2546_, 5, v___x_2544_);
lean_ctor_set(v___x_2546_, 6, v___x_2544_);
lean_ctor_set(v___x_2546_, 7, v___x_2544_);
lean_ctor_set(v___x_2546_, 8, v___x_2544_);
lean_ctor_set(v___x_2546_, 9, v___x_2544_);
return v___x_2546_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = lean_unsigned_to_nat(32u);
v___x_2548_ = lean_mk_empty_array_with_capacity(v___x_2547_);
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2550_ = ((size_t)5ULL);
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = lean_unsigned_to_nat(32u);
v___x_2553_ = lean_mk_empty_array_with_capacity(v___x_2552_);
v___x_2554_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_2555_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v___x_2553_);
lean_ctor_set(v___x_2555_, 2, v___x_2551_);
lean_ctor_set(v___x_2555_, 3, v___x_2551_);
lean_ctor_set_usize(v___x_2555_, 4, v___x_2550_);
return v___x_2555_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2556_ = lean_box(1);
v___x_2557_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_2558_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v___x_2557_);
lean_ctor_set(v___x_2559_, 2, v___x_2556_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; lean_object* v_env_2565_; lean_object* v_options_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2564_ = lean_st_ref_get(v___y_2562_);
v_env_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc_ref(v_env_2565_);
lean_dec(v___x_2564_);
v_options_2566_ = lean_ctor_get(v___y_2561_, 2);
v___x_2567_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_2568_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_2566_);
v___x_2569_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2569_, 0, v_env_2565_);
lean_ctor_set(v___x_2569_, 1, v___x_2567_);
lean_ctor_set(v___x_2569_, 2, v___x_2568_);
lean_ctor_set(v___x_2569_, 3, v_options_2566_);
v___x_2570_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
lean_ctor_set(v___x_2570_, 1, v_msgData_2560_);
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_ref_2581_; lean_object* v___x_2582_; lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2591_; 
v_ref_2581_ = lean_ctor_get(v___y_2578_, 5);
v___x_2582_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_2577_, v___y_2578_, v___y_2579_);
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2591_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2591_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
lean_inc(v_ref_2581_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v_ref_2581_);
lean_ctor_set(v___x_2587_, 1, v_a_2583_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 0, v___x_2587_);
v___x_2589_ = v___x_2585_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(lean_object* v_x_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
if (lean_obj_tag(v_x_2597_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v_a_2601_ = lean_ctor_get(v_x_2597_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v_x_2597_, 1);
v___x_2602_ = l_Lean_stringToMessageData(v_a_2601_);
v___x_2603_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v___x_2602_, v___y_2598_, v___y_2599_);
return v___x_2603_;
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
v_a_2604_ = lean_ctor_get(v_x_2597_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_x_2597_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v_x_2597_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v_x_2597_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set_tag(v___x_2606_, 0);
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2612_, v___y_2613_, v___y_2614_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
return v_res_2616_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_box(0);
v___x_2618_ = l_Lean_Elab_abortCommandExceptionId;
v___x_2619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
lean_ctor_set(v___x_2619_, 1, v___x_2617_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(lean_object* v_constName_2625_, uint8_t v_checkMeta_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; lean_object* v_env_2631_; uint8_t v___x_2632_; 
v___x_2630_ = lean_st_ref_get(v___y_2628_);
v_env_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc_ref(v_env_2631_);
lean_dec(v___x_2630_);
lean_inc(v_constName_2625_);
v___x_2632_ = lean_has_compile_error(v_env_2631_, v_constName_2625_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; lean_object* v_env_2634_; lean_object* v_options_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2633_ = lean_st_ref_get(v___y_2628_);
v_env_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc_ref(v_env_2634_);
lean_dec(v___x_2633_);
v_options_2635_ = lean_ctor_get(v___y_2627_, 2);
v___x_2636_ = l_Lean_Environment_evalConst___redArg(v_env_2634_, v_options_2635_, v_constName_2625_, v_checkMeta_2626_);
lean_dec(v_constName_2625_);
lean_dec_ref(v_env_2634_);
v___x_2637_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2636_, v___y_2627_, v___y_2628_);
return v___x_2637_;
}
else
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v___x_2639_; lean_object* v_env_2640_; lean_object* v_options_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
lean_dec_ref_known(v___x_2638_, 1);
v___x_2639_ = lean_st_ref_get(v___y_2628_);
v_env_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc_ref(v_env_2640_);
lean_dec(v___x_2639_);
v_options_2641_ = lean_ctor_get(v___y_2627_, 2);
v___x_2642_ = l_Lean_Environment_evalConst___redArg(v_env_2640_, v_options_2641_, v_constName_2625_, v_checkMeta_2626_);
lean_dec(v_constName_2625_);
lean_dec_ref(v_env_2640_);
v___x_2643_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2642_, v___y_2627_, v___y_2628_);
return v___x_2643_;
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_constName_2625_);
v_a_2644_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2638_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2638_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg___boxed(lean_object* v_constName_2652_, lean_object* v_checkMeta_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
uint8_t v_checkMeta_boxed_2657_; lean_object* v_res_2658_; 
v_checkMeta_boxed_2657_ = lean_unbox(v_checkMeta_2653_);
v_res_2658_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2652_, v_checkMeta_boxed_2657_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(lean_object* v_type_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v___x_2663_; lean_object* v___y_2665_; lean_object* v_env_2696_; lean_object* v___x_2697_; lean_object* v_toEnvExtension_2698_; lean_object* v_asyncMode_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v_imported_2703_; lean_object* v_current_2704_; lean_object* v___x_2705_; 
v___x_2663_ = lean_st_ref_get(v_a_2661_);
v_env_2696_ = lean_ctor_get(v___x_2663_, 0);
lean_inc_ref(v_env_2696_);
lean_dec(v___x_2663_);
v___x_2697_ = l_Lean_Doc_docInlineMdExt;
v_toEnvExtension_2698_ = lean_ctor_get(v___x_2697_, 0);
v_asyncMode_2699_ = lean_ctor_get(v_toEnvExtension_2698_, 2);
v___x_2700_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2701_ = lean_box(0);
v___x_2702_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2700_, v___x_2697_, v_env_2696_, v_asyncMode_2699_, v___x_2701_);
v_imported_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_imported_2703_);
v_current_2704_ = lean_ctor_get(v___x_2702_, 1);
lean_inc(v_current_2704_);
lean_dec(v___x_2702_);
v___x_2705_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2704_, v_type_2659_);
lean_dec(v_current_2704_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2703_, v_type_2659_);
lean_dec(v_imported_2703_);
v___y_2665_ = v___x_2706_;
goto v___jp_2664_;
}
else
{
lean_dec(v_imported_2703_);
v___y_2665_ = v___x_2705_;
goto v___jp_2664_;
}
v___jp_2664_:
{
if (lean_obj_tag(v___y_2665_) == 0)
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2666_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2667_ = lean_st_ref_get(v___x_2666_);
v___x_2668_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2667_, v_type_2659_);
lean_dec(v___x_2667_);
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
return v___x_2669_;
}
else
{
lean_object* v_val_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2695_; 
v_val_2670_ = lean_ctor_get(v___y_2665_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___y_2665_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2672_ = v___y_2665_;
v_isShared_2673_ = v_isSharedCheck_2695_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_val_2670_);
lean_dec(v___y_2665_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2695_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
uint8_t v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = 1;
v___x_2675_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2670_, v___x_2674_, v_a_2660_, v_a_2661_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2686_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2686_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2686_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v_a_2676_);
v___x_2681_ = v___x_2672_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2683_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2681_);
v___x_2683_ = v___x_2678_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_del_object(v___x_2672_);
v_a_2687_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2675_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2675_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe___boxed(lean_object* v_type_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v_type_2707_, v_a_2708_, v_a_2709_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_type_2707_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(v_00_u03b1_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(lean_object* v_00_u03b1_2722_, lean_object* v_constName_2723_, uint8_t v_checkMeta_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2723_, v_checkMeta_2724_, v___y_2725_, v___y_2726_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___boxed(lean_object* v_00_u03b1_2729_, lean_object* v_constName_2730_, lean_object* v_checkMeta_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
uint8_t v_checkMeta_boxed_2735_; lean_object* v_res_2736_; 
v_checkMeta_boxed_2735_ = lean_unbox(v_checkMeta_2731_);
v_res_2736_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(v_00_u03b1_2729_, v_constName_2730_, v_checkMeta_boxed_2735_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_2737_, lean_object* v_x_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2738_, v___y_2739_, v___y_2740_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2743_, lean_object* v_x_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(v_00_u03b1_2743_, v_x_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2749_, lean_object* v_msg_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2750_, v___y_2751_, v___y_2752_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2755_, lean_object* v_msg_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_2755_, v_msg_2756_, v___y_2757_, v___y_2758_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(lean_object* v_typeName_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v___x_2765_; lean_object* v___y_2767_; lean_object* v_env_2798_; lean_object* v___x_2799_; lean_object* v_toEnvExtension_2800_; lean_object* v_asyncMode_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v_imported_2805_; lean_object* v_current_2806_; lean_object* v___x_2807_; 
v___x_2765_ = lean_st_ref_get(v_a_2763_);
v_env_2798_ = lean_ctor_get(v___x_2765_, 0);
lean_inc_ref(v_env_2798_);
lean_dec(v___x_2765_);
v___x_2799_ = l_Lean_Doc_docBlockMdExt;
v_toEnvExtension_2800_ = lean_ctor_get(v___x_2799_, 0);
v_asyncMode_2801_ = lean_ctor_get(v_toEnvExtension_2800_, 2);
v___x_2802_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2803_ = lean_box(0);
v___x_2804_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2802_, v___x_2799_, v_env_2798_, v_asyncMode_2801_, v___x_2803_);
v_imported_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_imported_2805_);
v_current_2806_ = lean_ctor_get(v___x_2804_, 1);
lean_inc(v_current_2806_);
lean_dec(v___x_2804_);
v___x_2807_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2806_, v_typeName_2761_);
lean_dec(v_current_2806_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2805_, v_typeName_2761_);
lean_dec(v_imported_2805_);
v___y_2767_ = v___x_2808_;
goto v___jp_2766_;
}
else
{
lean_dec(v_imported_2805_);
v___y_2767_ = v___x_2807_;
goto v___jp_2766_;
}
v___jp_2766_:
{
if (lean_obj_tag(v___y_2767_) == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2768_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2769_ = lean_st_ref_get(v___x_2768_);
v___x_2770_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2769_, v_typeName_2761_);
lean_dec(v___x_2769_);
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
return v___x_2771_;
}
else
{
lean_object* v_val_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2797_; 
v_val_2772_ = lean_ctor_get(v___y_2767_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___y_2767_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2774_ = v___y_2767_;
v_isShared_2775_ = v_isSharedCheck_2797_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_val_2772_);
lean_dec(v___y_2767_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2797_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
uint8_t v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = 1;
v___x_2777_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2772_, v___x_2776_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2788_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2788_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2788_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v_a_2778_);
v___x_2783_ = v___x_2774_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2785_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2783_);
v___x_2785_ = v___x_2780_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_del_object(v___x_2774_);
v_a_2789_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2777_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2777_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe___boxed(lean_object* v_typeName_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v_typeName_2809_, v_a_2810_, v_a_2811_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_typeName_2809_);
return v_res_2813_;
}
}
static lean_object* _init_l_Lean_Doc_mdRendererHeartbeats(void){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_unsigned_to_nat(200000u);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg(lean_object* v_x_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v___x_2820_; lean_object* v_fileName_2821_; lean_object* v_fileMap_2822_; lean_object* v_options_2823_; lean_object* v_currRecDepth_2824_; lean_object* v_maxRecDepth_2825_; lean_object* v_ref_2826_; lean_object* v_currNamespace_2827_; lean_object* v_openDecls_2828_; lean_object* v_quotContext_2829_; lean_object* v_currMacroScope_2830_; uint8_t v_diag_2831_; lean_object* v_cancelTk_x3f_2832_; uint8_t v_suppressElabErrors_2833_; lean_object* v_inheritedTraceOptions_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2820_ = lean_io_get_num_heartbeats();
v_fileName_2821_ = lean_ctor_get(v_a_2817_, 0);
v_fileMap_2822_ = lean_ctor_get(v_a_2817_, 1);
v_options_2823_ = lean_ctor_get(v_a_2817_, 2);
v_currRecDepth_2824_ = lean_ctor_get(v_a_2817_, 3);
v_maxRecDepth_2825_ = lean_ctor_get(v_a_2817_, 4);
v_ref_2826_ = lean_ctor_get(v_a_2817_, 5);
v_currNamespace_2827_ = lean_ctor_get(v_a_2817_, 6);
v_openDecls_2828_ = lean_ctor_get(v_a_2817_, 7);
v_quotContext_2829_ = lean_ctor_get(v_a_2817_, 10);
v_currMacroScope_2830_ = lean_ctor_get(v_a_2817_, 11);
v_diag_2831_ = lean_ctor_get_uint8(v_a_2817_, sizeof(void*)*14);
v_cancelTk_x3f_2832_ = lean_ctor_get(v_a_2817_, 12);
v_suppressElabErrors_2833_ = lean_ctor_get_uint8(v_a_2817_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2834_ = lean_ctor_get(v_a_2817_, 13);
v___x_2835_ = lean_unsigned_to_nat(200000u);
lean_inc_ref(v_inheritedTraceOptions_2834_);
lean_inc(v_cancelTk_x3f_2832_);
lean_inc(v_currMacroScope_2830_);
lean_inc(v_quotContext_2829_);
lean_inc(v_openDecls_2828_);
lean_inc(v_currNamespace_2827_);
lean_inc(v_ref_2826_);
lean_inc(v_maxRecDepth_2825_);
lean_inc(v_currRecDepth_2824_);
lean_inc_ref(v_options_2823_);
lean_inc_ref(v_fileMap_2822_);
lean_inc_ref(v_fileName_2821_);
v___x_2836_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2836_, 0, v_fileName_2821_);
lean_ctor_set(v___x_2836_, 1, v_fileMap_2822_);
lean_ctor_set(v___x_2836_, 2, v_options_2823_);
lean_ctor_set(v___x_2836_, 3, v_currRecDepth_2824_);
lean_ctor_set(v___x_2836_, 4, v_maxRecDepth_2825_);
lean_ctor_set(v___x_2836_, 5, v_ref_2826_);
lean_ctor_set(v___x_2836_, 6, v_currNamespace_2827_);
lean_ctor_set(v___x_2836_, 7, v_openDecls_2828_);
lean_ctor_set(v___x_2836_, 8, v___x_2820_);
lean_ctor_set(v___x_2836_, 9, v___x_2835_);
lean_ctor_set(v___x_2836_, 10, v_quotContext_2829_);
lean_ctor_set(v___x_2836_, 11, v_currMacroScope_2830_);
lean_ctor_set(v___x_2836_, 12, v_cancelTk_x3f_2832_);
lean_ctor_set(v___x_2836_, 13, v_inheritedTraceOptions_2834_);
lean_ctor_set_uint8(v___x_2836_, sizeof(void*)*14, v_diag_2831_);
lean_ctor_set_uint8(v___x_2836_, sizeof(void*)*14 + 1, v_suppressElabErrors_2833_);
lean_inc(v_a_2818_);
lean_inc(v_a_2816_);
v___x_2837_ = lean_apply_4(v_x_2815_, v_a_2816_, v___x_2836_, v_a_2818_, lean_box(0));
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg___boxed(lean_object* v_x_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_a_2839_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget(lean_object* v_00_u03b1_2844_, lean_object* v_x_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___boxed(lean_object* v_00_u03b1_2851_, lean_object* v_x_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Doc_withMdRendererBudget(v_00_u03b1_2851_, v_x_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback(lean_object* v_fallback_2858_, lean_object* v_act_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_){
_start:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_st_ref_get(v_a_2860_);
v___x_2865_ = l_Lean_Doc_withMdRendererBudget___redArg(v_act_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_dec(v___x_2864_);
lean_dec_ref(v_fallback_2858_);
return v___x_2865_;
}
else
{
lean_object* v_a_2866_; uint8_t v___x_2867_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
v___x_2867_ = l_Lean_Exception_isInterrupt(v_a_2866_);
lean_dec(v_a_2866_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_dec_ref_known(v___x_2865_, 1);
v___x_2868_ = lean_st_ref_set(v_a_2860_, v___x_2864_);
lean_inc(v_a_2862_);
lean_inc_ref(v_a_2861_);
lean_inc(v_a_2860_);
v___x_2869_ = lean_apply_4(v_fallback_2858_, v_a_2860_, v_a_2861_, v_a_2862_, lean_box(0));
return v___x_2869_;
}
else
{
lean_dec(v___x_2864_);
lean_dec_ref(v_fallback_2858_);
return v___x_2865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback___boxed(lean_object* v_fallback_2870_, lean_object* v_act_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_Doc_withRendererFallback(v_fallback_2870_, v_act_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
lean_dec(v_a_2872_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0(lean_object* v_____do__lift_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = l_Lean_Doc_joinInlines(v_____do__lift_2877_);
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0___boxed(lean_object* v_____do__lift_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__0(v_____do__lift_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v_____do__lift_2884_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1(lean_object* v___x_2890_, lean_object* v___x_2891_, lean_object* v___f_2892_, lean_object* v_go_2893_, lean_object* v_container_2894_, lean_object* v_content_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_container_2894_);
v___x_2901_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_2900_, v___y_2897_, v___y_2898_);
lean_dec(v___x_2900_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
if (lean_obj_tag(v_a_2902_) == 0)
{
size_t v_sz_2903_; size_t v___x_2904_; lean_object* v___x_422__overap_2905_; lean_object* v___x_2906_; 
lean_dec(v_container_2894_);
lean_dec_ref(v___f_2892_);
lean_dec_ref(v___x_2891_);
v_sz_2903_ = lean_array_size(v_content_2895_);
v___x_2904_ = ((size_t)0ULL);
v___x_422__overap_2905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2890_, v_go_2893_, v_sz_2903_, v___x_2904_, v_content_2895_);
lean_inc(v___y_2898_);
lean_inc_ref(v___y_2897_);
lean_inc(v___y_2896_);
v___x_2906_ = lean_apply_4(v___x_422__overap_2905_, v___y_2896_, v___y_2897_, v___y_2898_, lean_box(0));
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2915_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2909_ = v___x_2906_;
v_isShared_2910_ = v_isSharedCheck_2915_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2906_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2915_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2911_ = l_Lean_Doc_joinInlines(v_a_2907_);
lean_dec(v_a_2907_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 0, v___x_2911_);
v___x_2913_ = v___x_2909_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
v_a_2916_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2906_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2906_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_object* v_val_2924_; size_t v_sz_2925_; size_t v___x_2926_; lean_object* v___x_2927_; lean_object* v_fallback_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_val_2924_ = lean_ctor_get(v_a_2902_, 0);
lean_inc(v_val_2924_);
lean_dec_ref_known(v_a_2902_, 1);
v_sz_2925_ = lean_array_size(v_content_2895_);
v___x_2926_ = ((size_t)0ULL);
lean_inc_ref(v_content_2895_);
lean_inc_ref(v_go_2893_);
v___x_2927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2890_, v_go_2893_, v_sz_2925_, v___x_2926_, v_content_2895_);
v_fallback_2928_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v_fallback_2928_, 0, lean_box(0));
lean_closure_set(v_fallback_2928_, 1, lean_box(0));
lean_closure_set(v_fallback_2928_, 2, lean_box(0));
lean_closure_set(v_fallback_2928_, 3, v___x_2891_);
lean_closure_set(v_fallback_2928_, 4, lean_box(0));
lean_closure_set(v_fallback_2928_, 5, lean_box(0));
lean_closure_set(v_fallback_2928_, 6, v___x_2927_);
lean_closure_set(v_fallback_2928_, 7, v___f_2892_);
v___x_2929_ = lean_apply_3(v_val_2924_, v_go_2893_, v_container_2894_, v_content_2895_);
v___x_2930_ = l_Lean_Doc_withRendererFallback(v_fallback_2928_, v___x_2929_, v___y_2896_, v___y_2897_, v___y_2898_);
return v___x_2930_;
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec_ref(v_content_2895_);
lean_dec(v_container_2894_);
lean_dec_ref(v_go_2893_);
lean_dec_ref(v___f_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
v_a_2931_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2901_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2901_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed(lean_object* v___x_2939_, lean_object* v___x_2940_, lean_object* v___f_2941_, lean_object* v_go_2942_, lean_object* v_container_2943_, lean_object* v_content_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__1(v___x_2939_, v___x_2940_, v___f_2941_, v_go_2942_, v_container_2943_, v_content_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
return v_res_2949_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownInlineElabInline(void){
_start:
{
lean_object* v___x_2951_; lean_object* v_toApplicative_2952_; lean_object* v_toFunctor_2953_; lean_object* v_toSeq_2954_; lean_object* v_toSeqLeft_2955_; lean_object* v_toSeqRight_2956_; lean_object* v___f_2957_; lean_object* v___f_2958_; lean_object* v___f_2959_; lean_object* v___f_2960_; lean_object* v___f_2961_; lean_object* v___x_2962_; lean_object* v___f_2963_; lean_object* v___f_2964_; lean_object* v___f_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___f_2969_; 
v___x_2951_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2952_ = lean_ctor_get(v___x_2951_, 0);
v_toFunctor_2953_ = lean_ctor_get(v_toApplicative_2952_, 0);
v_toSeq_2954_ = lean_ctor_get(v_toApplicative_2952_, 2);
v_toSeqLeft_2955_ = lean_ctor_get(v_toApplicative_2952_, 3);
v_toSeqRight_2956_ = lean_ctor_get(v_toApplicative_2952_, 4);
v___f_2957_ = ((lean_object*)(l_Lean_Doc_instMarkdownInlineElabInline___closed__0));
v___f_2958_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2959_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2953_, 2);
v___f_2960_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2960_, 0, v_toFunctor_2953_);
v___f_2961_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2961_, 0, v_toFunctor_2953_);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___f_2960_);
lean_ctor_set(v___x_2962_, 1, v___f_2961_);
lean_inc(v_toSeqRight_2956_);
v___f_2963_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2963_, 0, v_toSeqRight_2956_);
lean_inc(v_toSeqLeft_2955_);
v___f_2964_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2964_, 0, v_toSeqLeft_2955_);
lean_inc(v_toSeq_2954_);
v___f_2965_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2965_, 0, v_toSeq_2954_);
v___x_2966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2962_);
lean_ctor_set(v___x_2966_, 1, v___f_2958_);
lean_ctor_set(v___x_2966_, 2, v___f_2965_);
lean_ctor_set(v___x_2966_, 3, v___f_2964_);
lean_ctor_set(v___x_2966_, 4, v___f_2963_);
v___x_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
lean_ctor_set(v___x_2967_, 1, v___f_2959_);
lean_inc_ref(v___x_2967_);
v___x_2968_ = l_StateRefT_x27_instMonad___redArg(v___x_2967_);
v___f_2969_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2969_, 0, v___x_2968_);
lean_closure_set(v___f_2969_, 1, v___x_2967_);
lean_closure_set(v___f_2969_, 2, v___f_2957_);
return v___f_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v_____do__lift_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = l_Lean_Doc_joinBlocks(v_____do__lift_2970_);
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object* v_____do__lift_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(v_____do__lift_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v_____do__lift_2977_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object* v___x_2983_, lean_object* v___x_2984_, lean_object* v___f_2985_, lean_object* v_goI_2986_, lean_object* v_goB_2987_, lean_object* v_container_2988_, lean_object* v_content_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_container_2988_);
v___x_2995_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_2994_, v___y_2991_, v___y_2992_);
lean_dec(v___x_2994_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
if (lean_obj_tag(v_a_2996_) == 0)
{
size_t v_sz_2997_; size_t v___x_2998_; lean_object* v___x_422__overap_2999_; lean_object* v___x_3000_; 
lean_dec(v_container_2988_);
lean_dec_ref(v_goI_2986_);
lean_dec_ref(v___f_2985_);
lean_dec_ref(v___x_2984_);
v_sz_2997_ = lean_array_size(v_content_2989_);
v___x_2998_ = ((size_t)0ULL);
v___x_422__overap_2999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2983_, v_goB_2987_, v_sz_2997_, v___x_2998_, v_content_2989_);
lean_inc(v___y_2992_);
lean_inc_ref(v___y_2991_);
lean_inc(v___y_2990_);
v___x_3000_ = lean_apply_4(v___x_422__overap_2999_, v___y_2990_, v___y_2991_, v___y_2992_, lean_box(0));
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3009_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3003_ = v___x_3000_;
v_isShared_3004_ = v_isSharedCheck_3009_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3009_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3005_ = l_Lean_Doc_joinBlocks(v_a_3001_);
lean_dec(v_a_3001_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_3005_);
v___x_3007_ = v___x_3003_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
v_a_3010_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_3000_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3000_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
else
{
lean_object* v_val_3018_; size_t v_sz_3019_; size_t v___x_3020_; lean_object* v___x_3021_; lean_object* v_fallback_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_val_3018_ = lean_ctor_get(v_a_2996_, 0);
lean_inc(v_val_3018_);
lean_dec_ref_known(v_a_2996_, 1);
v_sz_3019_ = lean_array_size(v_content_2989_);
v___x_3020_ = ((size_t)0ULL);
lean_inc_ref(v_content_2989_);
lean_inc_ref(v_goB_2987_);
v___x_3021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2983_, v_goB_2987_, v_sz_3019_, v___x_3020_, v_content_2989_);
v_fallback_3022_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v_fallback_3022_, 0, lean_box(0));
lean_closure_set(v_fallback_3022_, 1, lean_box(0));
lean_closure_set(v_fallback_3022_, 2, lean_box(0));
lean_closure_set(v_fallback_3022_, 3, v___x_2984_);
lean_closure_set(v_fallback_3022_, 4, lean_box(0));
lean_closure_set(v_fallback_3022_, 5, lean_box(0));
lean_closure_set(v_fallback_3022_, 6, v___x_3021_);
lean_closure_set(v_fallback_3022_, 7, v___f_2985_);
v___x_3023_ = lean_apply_4(v_val_3018_, v_goI_2986_, v_goB_2987_, v_container_2988_, v_content_2989_);
v___x_3024_ = l_Lean_Doc_withRendererFallback(v_fallback_3022_, v___x_3023_, v___y_2990_, v___y_2991_, v___y_2992_);
return v___x_3024_;
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v_content_2989_);
lean_dec(v_container_2988_);
lean_dec_ref(v_goB_2987_);
lean_dec_ref(v_goI_2986_);
lean_dec_ref(v___f_2985_);
lean_dec_ref(v___x_2984_);
lean_dec_ref(v___x_2983_);
v_a_3025_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2995_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2995_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object* v___x_3033_, lean_object* v___x_3034_, lean_object* v___f_3035_, lean_object* v_goI_3036_, lean_object* v_goB_3037_, lean_object* v_container_3038_, lean_object* v_content_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_3033_, v___x_3034_, v___f_3035_, v_goI_3036_, v_goB_3037_, v_container_3038_, v_content_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
return v_res_3044_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownBlockElabInlineElabBlock(void){
_start:
{
lean_object* v___x_3046_; lean_object* v_toApplicative_3047_; lean_object* v_toFunctor_3048_; lean_object* v_toSeq_3049_; lean_object* v_toSeqLeft_3050_; lean_object* v_toSeqRight_3051_; lean_object* v___f_3052_; lean_object* v___f_3053_; lean_object* v___f_3054_; lean_object* v___f_3055_; lean_object* v___f_3056_; lean_object* v___x_3057_; lean_object* v___f_3058_; lean_object* v___f_3059_; lean_object* v___f_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___f_3064_; 
v___x_3046_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3047_ = lean_ctor_get(v___x_3046_, 0);
v_toFunctor_3048_ = lean_ctor_get(v_toApplicative_3047_, 0);
v_toSeq_3049_ = lean_ctor_get(v_toApplicative_3047_, 2);
v_toSeqLeft_3050_ = lean_ctor_get(v_toApplicative_3047_, 3);
v_toSeqRight_3051_ = lean_ctor_get(v_toApplicative_3047_, 4);
v___f_3052_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___closed__0));
v___f_3053_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3054_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3048_, 2);
v___f_3055_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3055_, 0, v_toFunctor_3048_);
v___f_3056_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3056_, 0, v_toFunctor_3048_);
v___x_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___f_3055_);
lean_ctor_set(v___x_3057_, 1, v___f_3056_);
lean_inc(v_toSeqRight_3051_);
v___f_3058_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3058_, 0, v_toSeqRight_3051_);
lean_inc(v_toSeqLeft_3050_);
v___f_3059_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3059_, 0, v_toSeqLeft_3050_);
lean_inc(v_toSeq_3049_);
v___f_3060_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3060_, 0, v_toSeq_3049_);
v___x_3061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3057_);
lean_ctor_set(v___x_3061_, 1, v___f_3053_);
lean_ctor_set(v___x_3061_, 2, v___f_3060_);
lean_ctor_set(v___x_3061_, 3, v___f_3059_);
lean_ctor_set(v___x_3061_, 4, v___f_3058_);
v___x_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
lean_ctor_set(v___x_3062_, 1, v___f_3054_);
lean_inc_ref(v___x_3062_);
v___x_3063_ = l_StateRefT_x27_instMonad___redArg(v___x_3062_);
v___f_3064_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3064_, 0, v___x_3063_);
lean_closure_set(v___f_3064_, 1, v___x_3062_);
lean_closure_set(v___f_3064_, 2, v___f_3052_);
return v___f_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0(lean_object* v___x_3065_, lean_object* v___x_3066_, lean_object* v_part_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = lean_unsigned_to_nat(0u);
v___x_3073_ = l_Lean_Doc_partMarkdown___redArg(v___x_3065_, v___x_3066_, v___x_3072_, v_part_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed(lean_object* v___x_3074_, lean_object* v___x_3075_, lean_object* v_part_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__0(v___x_3074_, v___x_3075_, v_part_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1(lean_object* v___x_3082_, lean_object* v___x_3083_, lean_object* v___x_3084_, lean_object* v___f_3085_, lean_object* v_x_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_text_3091_; lean_object* v_subsections_3092_; lean_object* v___x_3093_; size_t v_sz_3094_; size_t v___x_3095_; lean_object* v___x_440__overap_3096_; lean_object* v___x_3097_; 
v_text_3091_ = lean_ctor_get(v_x_3086_, 0);
lean_inc_ref(v_text_3091_);
v_subsections_3092_ = lean_ctor_get(v_x_3086_, 1);
lean_inc_ref(v_subsections_3092_);
lean_dec_ref(v_x_3086_);
v___x_3093_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3093_, 0, lean_box(0));
lean_closure_set(v___x_3093_, 1, lean_box(0));
lean_closure_set(v___x_3093_, 2, v___x_3082_);
lean_closure_set(v___x_3093_, 3, v___x_3083_);
v_sz_3094_ = lean_array_size(v_text_3091_);
v___x_3095_ = ((size_t)0ULL);
lean_inc_ref(v___x_3084_);
v___x_440__overap_3096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3084_, v___x_3093_, v_sz_3094_, v___x_3095_, v_text_3091_);
lean_inc(v___y_3089_);
lean_inc_ref(v___y_3088_);
lean_inc(v___y_3087_);
v___x_3097_ = lean_apply_4(v___x_440__overap_3096_, v___y_3087_, v___y_3088_, v___y_3089_, lean_box(0));
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; size_t v_sz_3099_; lean_object* v___x_443__overap_3100_; lean_object* v___x_3101_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v_sz_3099_ = lean_array_size(v_subsections_3092_);
v___x_443__overap_3100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3084_, v___f_3085_, v_sz_3099_, v___x_3095_, v_subsections_3092_);
lean_inc(v___y_3089_);
lean_inc_ref(v___y_3088_);
lean_inc(v___y_3087_);
v___x_3101_ = lean_apply_4(v___x_443__overap_3100_, v___y_3087_, v___y_3088_, v___y_3089_, lean_box(0));
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3111_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3111_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3111_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3106_ = l_Array_append___redArg(v_a_3098_, v_a_3102_);
lean_dec(v_a_3102_);
v___x_3107_ = l_Lean_Doc_joinBlocks(v___x_3106_);
lean_dec_ref(v___x_3106_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v___x_3107_);
v___x_3109_ = v___x_3104_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec(v_a_3098_);
v_a_3112_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3101_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3101_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v_subsections_3092_);
lean_dec_ref(v___f_3085_);
lean_dec_ref(v___x_3084_);
v_a_3120_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3097_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3097_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed(lean_object* v___x_3128_, lean_object* v___x_3129_, lean_object* v___x_3130_, lean_object* v___f_3131_, lean_object* v_x_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__1(v___x_3128_, v___x_3129_, v___x_3130_, v___f_3131_, v_x_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
return v_res_3137_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___f_3140_; 
v___x_3138_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3139_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3140_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3140_, 0, v___x_3139_);
lean_closure_set(v___f_3140_, 1, v___x_3138_);
return v___f_3140_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString(void){
_start:
{
lean_object* v___x_3141_; lean_object* v_toApplicative_3142_; lean_object* v_toFunctor_3143_; lean_object* v_toSeq_3144_; lean_object* v_toSeqLeft_3145_; lean_object* v_toSeqRight_3146_; lean_object* v___f_3147_; lean_object* v___f_3148_; lean_object* v___f_3149_; lean_object* v___f_3150_; lean_object* v___x_3151_; lean_object* v___f_3152_; lean_object* v___f_3153_; lean_object* v___f_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___f_3160_; lean_object* v___f_3161_; 
v___x_3141_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3142_ = lean_ctor_get(v___x_3141_, 0);
v_toFunctor_3143_ = lean_ctor_get(v_toApplicative_3142_, 0);
v_toSeq_3144_ = lean_ctor_get(v_toApplicative_3142_, 2);
v_toSeqLeft_3145_ = lean_ctor_get(v_toApplicative_3142_, 3);
v_toSeqRight_3146_ = lean_ctor_get(v_toApplicative_3142_, 4);
v___f_3147_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3148_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3143_, 2);
v___f_3149_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3149_, 0, v_toFunctor_3143_);
v___f_3150_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3150_, 0, v_toFunctor_3143_);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___f_3149_);
lean_ctor_set(v___x_3151_, 1, v___f_3150_);
lean_inc(v_toSeqRight_3146_);
v___f_3152_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3152_, 0, v_toSeqRight_3146_);
lean_inc(v_toSeqLeft_3145_);
v___f_3153_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3153_, 0, v_toSeqLeft_3145_);
lean_inc(v_toSeq_3144_);
v___f_3154_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3154_, 0, v_toSeq_3144_);
v___x_3155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3151_);
lean_ctor_set(v___x_3155_, 1, v___f_3147_);
lean_ctor_set(v___x_3155_, 2, v___f_3154_);
lean_ctor_set(v___x_3155_, 3, v___f_3153_);
lean_ctor_set(v___x_3155_, 4, v___f_3152_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
lean_ctor_set(v___x_3156_, 1, v___f_3148_);
v___x_3157_ = l_StateRefT_x27_instMonad___redArg(v___x_3156_);
v___x_3158_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3159_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3160_ = lean_obj_once(&l_Lean_Doc_instToMarkdownVersoDocString___closed__0, &l_Lean_Doc_instToMarkdownVersoDocString___closed__0_once, _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0);
v___f_3161_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3161_, 0, v___x_3158_);
lean_closure_set(v___f_3161_, 1, v___x_3159_);
lean_closure_set(v___f_3161_, 2, v___x_3157_);
lean_closure_set(v___f_3161_, 3, v___f_3160_);
return v___f_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0(lean_object* v___x_3162_, lean_object* v___x_3163_, lean_object* v_x_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v_snd_3169_; lean_object* v_fst_3170_; lean_object* v_snd_3171_; lean_object* v___x_3172_; 
v_snd_3169_ = lean_ctor_get(v_x_3164_, 1);
lean_inc(v_snd_3169_);
v_fst_3170_ = lean_ctor_get(v_x_3164_, 0);
lean_inc(v_fst_3170_);
lean_dec_ref(v_x_3164_);
v_snd_3171_ = lean_ctor_get(v_snd_3169_, 1);
lean_inc(v_snd_3171_);
lean_dec(v_snd_3169_);
v___x_3172_ = l_Lean_Doc_partMarkdown___redArg(v___x_3162_, v___x_3163_, v_fst_3170_, v_snd_3171_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v_fst_3170_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_3173_, lean_object* v___x_3174_, lean_object* v_x_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_Lean_Doc_instToMarkdownSnippet___lam__0(v___x_3173_, v___x_3174_, v_x_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1(lean_object* v___x_3181_, lean_object* v___x_3182_, lean_object* v___x_3183_, lean_object* v___f_3184_, lean_object* v_x_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_text_3190_; lean_object* v_sections_3191_; lean_object* v___x_3192_; size_t v_sz_3193_; size_t v___x_3194_; lean_object* v___x_487__overap_3195_; lean_object* v___x_3196_; 
v_text_3190_ = lean_ctor_get(v_x_3185_, 0);
lean_inc_ref(v_text_3190_);
v_sections_3191_ = lean_ctor_get(v_x_3185_, 1);
lean_inc_ref(v_sections_3191_);
lean_dec_ref(v_x_3185_);
v___x_3192_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3192_, 0, lean_box(0));
lean_closure_set(v___x_3192_, 1, lean_box(0));
lean_closure_set(v___x_3192_, 2, v___x_3181_);
lean_closure_set(v___x_3192_, 3, v___x_3182_);
v_sz_3193_ = lean_array_size(v_text_3190_);
v___x_3194_ = ((size_t)0ULL);
lean_inc_ref(v___x_3183_);
v___x_487__overap_3195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3183_, v___x_3192_, v_sz_3193_, v___x_3194_, v_text_3190_);
lean_inc(v___y_3188_);
lean_inc_ref(v___y_3187_);
lean_inc(v___y_3186_);
v___x_3196_ = lean_apply_4(v___x_487__overap_3195_, v___y_3186_, v___y_3187_, v___y_3188_, lean_box(0));
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; size_t v_sz_3198_; lean_object* v___x_490__overap_3199_; lean_object* v___x_3200_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v_sz_3198_ = lean_array_size(v_sections_3191_);
v___x_490__overap_3199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3183_, v___f_3184_, v_sz_3198_, v___x_3194_, v_sections_3191_);
lean_inc(v___y_3188_);
lean_inc_ref(v___y_3187_);
lean_inc(v___y_3186_);
v___x_3200_ = lean_apply_4(v___x_490__overap_3199_, v___y_3186_, v___y_3187_, v___y_3188_, lean_box(0));
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3210_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3210_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3210_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3208_; 
v___x_3205_ = l_Array_append___redArg(v_a_3197_, v_a_3201_);
lean_dec(v_a_3201_);
v___x_3206_ = l_Lean_Doc_joinBlocks(v___x_3205_);
lean_dec_ref(v___x_3205_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3206_);
v___x_3208_ = v___x_3203_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3206_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v_a_3197_);
v_a_3211_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3200_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3200_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec_ref(v_sections_3191_);
lean_dec_ref(v___f_3184_);
lean_dec_ref(v___x_3183_);
v_a_3219_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3196_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3196_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_3227_, lean_object* v___x_3228_, lean_object* v___x_3229_, lean_object* v___f_3230_, lean_object* v_x_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Lean_Doc_instToMarkdownSnippet___lam__1(v___x_3227_, v___x_3228_, v___x_3229_, v___f_3230_, v_x_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
return v_res_3236_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___f_3239_; 
v___x_3237_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3238_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3239_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3239_, 0, v___x_3238_);
lean_closure_set(v___f_3239_, 1, v___x_3237_);
return v___f_3239_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet(void){
_start:
{
lean_object* v___x_3240_; lean_object* v_toApplicative_3241_; lean_object* v_toFunctor_3242_; lean_object* v_toSeq_3243_; lean_object* v_toSeqLeft_3244_; lean_object* v_toSeqRight_3245_; lean_object* v___f_3246_; lean_object* v___f_3247_; lean_object* v___f_3248_; lean_object* v___f_3249_; lean_object* v___x_3250_; lean_object* v___f_3251_; lean_object* v___f_3252_; lean_object* v___f_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___f_3259_; lean_object* v___f_3260_; 
v___x_3240_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3241_ = lean_ctor_get(v___x_3240_, 0);
v_toFunctor_3242_ = lean_ctor_get(v_toApplicative_3241_, 0);
v_toSeq_3243_ = lean_ctor_get(v_toApplicative_3241_, 2);
v_toSeqLeft_3244_ = lean_ctor_get(v_toApplicative_3241_, 3);
v_toSeqRight_3245_ = lean_ctor_get(v_toApplicative_3241_, 4);
v___f_3246_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3247_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3242_, 2);
v___f_3248_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3248_, 0, v_toFunctor_3242_);
v___f_3249_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3249_, 0, v_toFunctor_3242_);
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___f_3248_);
lean_ctor_set(v___x_3250_, 1, v___f_3249_);
lean_inc(v_toSeqRight_3245_);
v___f_3251_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3251_, 0, v_toSeqRight_3245_);
lean_inc(v_toSeqLeft_3244_);
v___f_3252_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3252_, 0, v_toSeqLeft_3244_);
lean_inc(v_toSeq_3243_);
v___f_3253_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3253_, 0, v_toSeq_3243_);
v___x_3254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3250_);
lean_ctor_set(v___x_3254_, 1, v___f_3246_);
lean_ctor_set(v___x_3254_, 2, v___f_3253_);
lean_ctor_set(v___x_3254_, 3, v___f_3252_);
lean_ctor_set(v___x_3254_, 4, v___f_3251_);
v___x_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
lean_ctor_set(v___x_3255_, 1, v___f_3247_);
v___x_3256_ = l_StateRefT_x27_instMonad___redArg(v___x_3255_);
v___x_3257_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3258_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3259_ = lean_obj_once(&l_Lean_Doc_instToMarkdownSnippet___closed__0, &l_Lean_Doc_instToMarkdownSnippet___closed__0_once, _init_l_Lean_Doc_instToMarkdownSnippet___closed__0);
v___f_3260_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3260_, 0, v___x_3257_);
lean_closure_set(v___f_3260_, 1, v___x_3258_);
lean_closure_set(v___f_3260_, 2, v___x_3256_);
lean_closure_set(v___f_3260_, 3, v___f_3259_);
return v___f_3260_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(lean_object* v_opts_3261_, lean_object* v_opt_3262_){
_start:
{
lean_object* v_name_3263_; lean_object* v_defValue_3264_; lean_object* v_map_3265_; lean_object* v___x_3266_; 
v_name_3263_ = lean_ctor_get(v_opt_3262_, 0);
v_defValue_3264_ = lean_ctor_get(v_opt_3262_, 1);
v_map_3265_ = lean_ctor_get(v_opts_3261_, 0);
v___x_3266_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3265_, v_name_3263_);
if (lean_obj_tag(v___x_3266_) == 0)
{
uint8_t v___x_3267_; 
v___x_3267_ = lean_unbox(v_defValue_3264_);
return v___x_3267_;
}
else
{
lean_object* v_val_3268_; 
v_val_3268_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_val_3268_);
lean_dec_ref_known(v___x_3266_, 1);
if (lean_obj_tag(v_val_3268_) == 1)
{
uint8_t v_v_3269_; 
v_v_3269_ = lean_ctor_get_uint8(v_val_3268_, 0);
lean_dec_ref_known(v_val_3268_, 0);
return v_v_3269_;
}
else
{
uint8_t v___x_3270_; 
lean_dec(v_val_3268_);
v___x_3270_ = lean_unbox(v_defValue_3264_);
return v___x_3270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0___boxed(lean_object* v_opts_3271_, lean_object* v_opt_3272_){
_start:
{
uint8_t v_res_3273_; lean_object* v_r_3274_; 
v_res_3273_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_opts_3271_, v_opt_3272_);
lean_dec_ref(v_opt_3272_);
lean_dec_ref(v_opts_3271_);
v_r_3274_ = lean_box(v_res_3273_);
return v_r_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(lean_object* v_opts_3275_, lean_object* v_opt_3276_){
_start:
{
lean_object* v_name_3277_; lean_object* v_defValue_3278_; lean_object* v_map_3279_; lean_object* v___x_3280_; 
v_name_3277_ = lean_ctor_get(v_opt_3276_, 0);
v_defValue_3278_ = lean_ctor_get(v_opt_3276_, 1);
v_map_3279_ = lean_ctor_get(v_opts_3275_, 0);
v___x_3280_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3279_, v_name_3277_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_inc(v_defValue_3278_);
return v_defValue_3278_;
}
else
{
lean_object* v_val_3281_; 
v_val_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_val_3281_);
lean_dec_ref_known(v___x_3280_, 1);
if (lean_obj_tag(v_val_3281_) == 3)
{
lean_object* v_v_3282_; 
v_v_3282_ = lean_ctor_get(v_val_3281_, 0);
lean_inc(v_v_3282_);
lean_dec_ref_known(v_val_3281_, 1);
return v_v_3282_;
}
else
{
lean_dec(v_val_3281_);
lean_inc(v_defValue_3278_);
return v_defValue_3278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1___boxed(lean_object* v_opts_3283_, lean_object* v_opt_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(v_opts_3283_, v_opt_3284_);
lean_dec_ref(v_opt_3284_);
lean_dec_ref(v_opts_3283_);
return v_res_3285_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3286_ = lean_unsigned_to_nat(32u);
v___x_3287_ = lean_mk_empty_array_with_capacity(v___x_3286_);
v___x_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
return v___x_3288_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__1(void){
_start:
{
size_t v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3289_ = ((size_t)5ULL);
v___x_3290_ = lean_unsigned_to_nat(0u);
v___x_3291_ = lean_unsigned_to_nat(32u);
v___x_3292_ = lean_mk_empty_array_with_capacity(v___x_3291_);
v___x_3293_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__0, &l_Lean_Doc_runMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__0);
v___x_3294_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v___x_3292_);
lean_ctor_set(v___x_3294_, 2, v___x_3290_);
lean_ctor_set(v___x_3294_, 3, v___x_3290_);
lean_ctor_set_usize(v___x_3294_, 4, v___x_3289_);
return v___x_3294_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__2(void){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3295_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__3(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__2, &l_Lean_Doc_runMarkdown___redArg___closed__2_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__2);
v___x_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
return v___x_3297_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__4(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__3, &l_Lean_Doc_runMarkdown___redArg___closed__3_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__3);
v___x_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
return v___x_3299_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__5(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = l_Lean_NameSet_empty;
v___x_3301_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
lean_ctor_set(v___x_3302_, 2, v___x_3300_);
return v___x_3302_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__6(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = lean_unsigned_to_nat(1u);
v___x_3304_ = l_Lean_firstFrontendMacroScope;
v___x_3305_ = lean_nat_add(v___x_3304_, v___x_3303_);
return v___x_3305_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__11(void){
_start:
{
lean_object* v___x_3316_; uint64_t v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3317_ = 0ULL;
v___x_3318_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set_uint64(v___x_3318_, sizeof(void*)*1, v___x_3317_);
return v___x_3318_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__12(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; lean_object* v___x_3322_; 
v___x_3319_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3320_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__3, &l_Lean_Doc_runMarkdown___redArg___closed__3_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__3);
v___x_3321_ = 1;
v___x_3322_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3320_);
lean_ctor_set(v___x_3322_, 2, v___x_3319_);
lean_ctor_set_uint8(v___x_3322_, sizeof(void*)*3, v___x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg(lean_object* v_env_3329_, lean_object* v_act_3330_, lean_object* v_options_3331_, lean_object* v_currNamespace_3332_, lean_object* v_openDecls_3333_, lean_object* v_cancelTk_x3f_3334_){
_start:
{
lean_object* v_a_3337_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v_env_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; lean_object* v_fileName_3367_; lean_object* v_fileMap_3368_; lean_object* v_currRecDepth_3369_; lean_object* v_ref_3370_; lean_object* v_currNamespace_3371_; lean_object* v_openDecls_3372_; lean_object* v_initHeartbeats_3373_; lean_object* v_maxHeartbeats_3374_; lean_object* v_quotContext_3375_; lean_object* v_currMacroScope_3376_; lean_object* v_cancelTk_x3f_3377_; uint8_t v_suppressElabErrors_3378_; lean_object* v_inheritedTraceOptions_3379_; lean_object* v___y_3380_; uint8_t v___y_3417_; uint8_t v___x_3437_; 
v___x_3340_ = lean_unsigned_to_nat(0u);
v___x_3341_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__4, &l_Lean_Doc_runMarkdown___redArg___closed__4_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__4);
v___x_3342_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__5, &l_Lean_Doc_runMarkdown___redArg___closed__5_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__5);
v___x_3343_ = lean_io_get_num_heartbeats();
v___x_3344_ = l_Lean_firstFrontendMacroScope;
v___x_3345_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__6, &l_Lean_Doc_runMarkdown___redArg___closed__6_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__6);
v___x_3346_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__9));
v___x_3347_ = lean_box(0);
v___x_3348_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__10));
v___x_3349_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__11, &l_Lean_Doc_runMarkdown___redArg___closed__11_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__11);
v___x_3350_ = 1;
v___x_3351_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__12, &l_Lean_Doc_runMarkdown___redArg___closed__12_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__12);
v___x_3352_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__13));
v___x_3353_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3353_, 0, v_env_3329_);
lean_ctor_set(v___x_3353_, 1, v___x_3345_);
lean_ctor_set(v___x_3353_, 2, v___x_3346_);
lean_ctor_set(v___x_3353_, 3, v___x_3348_);
lean_ctor_set(v___x_3353_, 4, v___x_3349_);
lean_ctor_set(v___x_3353_, 5, v___x_3341_);
lean_ctor_set(v___x_3353_, 6, v___x_3342_);
lean_ctor_set(v___x_3353_, 7, v___x_3351_);
lean_ctor_set(v___x_3353_, 8, v___x_3352_);
v___x_3354_ = lean_st_mk_ref(v___x_3353_);
v___x_3355_ = l_Lean_inheritedTraceOptions;
v___x_3356_ = lean_st_ref_get(v___x_3355_);
v___x_3357_ = lean_st_ref_get(v___x_3354_);
v_env_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc_ref(v_env_3358_);
lean_dec(v___x_3357_);
v___x_3359_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__14));
v___x_3360_ = l_Lean_instInhabitedFileMap_default;
v___x_3361_ = lean_box(0);
v___x_3362_ = l_Lean_Core_getMaxHeartbeats(v_options_3331_);
v___x_3363_ = 0;
v___x_3364_ = l_Lean_diagnostics;
v___x_3365_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_options_3331_, v___x_3364_);
v___x_3437_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3358_);
lean_dec_ref(v_env_3358_);
if (v___x_3437_ == 0)
{
if (v___x_3365_ == 0)
{
lean_inc(v___x_3354_);
v_fileName_3367_ = v___x_3359_;
v_fileMap_3368_ = v___x_3360_;
v_currRecDepth_3369_ = v___x_3340_;
v_ref_3370_ = v___x_3361_;
v_currNamespace_3371_ = v_currNamespace_3332_;
v_openDecls_3372_ = v_openDecls_3333_;
v_initHeartbeats_3373_ = v___x_3343_;
v_maxHeartbeats_3374_ = v___x_3362_;
v_quotContext_3375_ = v___x_3347_;
v_currMacroScope_3376_ = v___x_3344_;
v_cancelTk_x3f_3377_ = v_cancelTk_x3f_3334_;
v_suppressElabErrors_3378_ = v___x_3363_;
v_inheritedTraceOptions_3379_ = v___x_3356_;
v___y_3380_ = v___x_3354_;
goto v___jp_3366_;
}
else
{
v___y_3417_ = v___x_3437_;
goto v___jp_3416_;
}
}
else
{
v___y_3417_ = v___x_3365_;
goto v___jp_3416_;
}
v___jp_3336_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = lean_mk_io_user_error(v_a_3337_);
v___x_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
return v___x_3339_;
}
v___jp_3366_:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3381_ = l_Lean_maxRecDepth;
v___x_3382_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(v_options_3331_, v___x_3381_);
lean_inc(v_currMacroScope_3376_);
lean_inc(v_quotContext_3375_);
lean_inc(v_ref_3370_);
lean_inc_ref(v_fileMap_3368_);
lean_inc_ref(v_fileName_3367_);
v___x_3383_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3383_, 0, v_fileName_3367_);
lean_ctor_set(v___x_3383_, 1, v_fileMap_3368_);
lean_ctor_set(v___x_3383_, 2, v_options_3331_);
lean_ctor_set(v___x_3383_, 3, v_currRecDepth_3369_);
lean_ctor_set(v___x_3383_, 4, v___x_3382_);
lean_ctor_set(v___x_3383_, 5, v_ref_3370_);
lean_ctor_set(v___x_3383_, 6, v_currNamespace_3371_);
lean_ctor_set(v___x_3383_, 7, v_openDecls_3372_);
lean_ctor_set(v___x_3383_, 8, v_initHeartbeats_3373_);
lean_ctor_set(v___x_3383_, 9, v_maxHeartbeats_3374_);
lean_ctor_set(v___x_3383_, 10, v_quotContext_3375_);
lean_ctor_set(v___x_3383_, 11, v_currMacroScope_3376_);
lean_ctor_set(v___x_3383_, 12, v_cancelTk_x3f_3377_);
lean_ctor_set(v___x_3383_, 13, v_inheritedTraceOptions_3379_);
lean_ctor_set_uint8(v___x_3383_, sizeof(void*)*14, v___x_3365_);
lean_ctor_set_uint8(v___x_3383_, sizeof(void*)*14 + 1, v_suppressElabErrors_3378_);
v___x_3384_ = lean_apply_3(v_act_3330_, v___x_3383_, v___y_3380_, lean_box(0));
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3393_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3387_ = v___x_3384_;
v_isShared_3388_ = v_isSharedCheck_3393_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3384_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3393_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3389_ = lean_st_ref_get(v___x_3354_);
lean_dec(v___x_3354_);
lean_dec(v___x_3389_);
if (v_isShared_3388_ == 0)
{
v___x_3391_ = v___x_3387_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3385_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3415_; 
lean_dec(v___x_3354_);
v_a_3394_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3396_ = v___x_3384_;
v_isShared_3397_ = v_isSharedCheck_3415_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3384_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3415_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
if (lean_obj_tag(v_a_3394_) == 0)
{
lean_object* v_msg_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3402_; 
v_msg_3398_ = lean_ctor_get(v_a_3394_, 1);
lean_inc_ref(v_msg_3398_);
lean_dec_ref_known(v_a_3394_, 2);
v___x_3399_ = l_Lean_MessageData_toString(v_msg_3398_);
v___x_3400_ = lean_mk_io_user_error(v___x_3399_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3400_);
v___x_3402_ = v___x_3396_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
else
{
lean_object* v_id_3404_; lean_object* v___x_3405_; 
lean_del_object(v___x_3396_);
v_id_3404_ = lean_ctor_get(v_a_3394_, 0);
lean_inc(v_id_3404_);
lean_dec_ref_known(v_a_3394_, 2);
v___x_3405_ = l_Lean_InternalExceptionId_getName(v_id_3404_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
lean_dec(v_id_3404_);
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__15));
v___x_3408_ = l_Lean_Name_toString(v_a_3406_, v___x_3350_);
v___x_3409_ = lean_string_append(v___x_3407_, v___x_3408_);
lean_dec_ref(v___x_3408_);
v_a_3337_ = v___x_3409_;
goto v___jp_3336_;
}
else
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_dec_ref_known(v___x_3405_, 1);
v___x_3410_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__16));
v___x_3411_ = l_Nat_reprFast(v_id_3404_);
v___x_3412_ = lean_string_append(v___x_3410_, v___x_3411_);
lean_dec_ref(v___x_3411_);
v___x_3413_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__17));
v___x_3414_ = lean_string_append(v___x_3412_, v___x_3413_);
v_a_3337_ = v___x_3414_;
goto v___jp_3336_;
}
}
}
}
}
v___jp_3416_:
{
if (v___y_3417_ == 0)
{
lean_object* v___x_3418_; lean_object* v_env_3419_; lean_object* v_nextMacroScope_3420_; lean_object* v_ngen_3421_; lean_object* v_auxDeclNGen_3422_; lean_object* v_traceState_3423_; lean_object* v_messages_3424_; lean_object* v_infoState_3425_; lean_object* v_snapshotTasks_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3435_; 
v___x_3418_ = lean_st_ref_take(v___x_3354_);
v_env_3419_ = lean_ctor_get(v___x_3418_, 0);
v_nextMacroScope_3420_ = lean_ctor_get(v___x_3418_, 1);
v_ngen_3421_ = lean_ctor_get(v___x_3418_, 2);
v_auxDeclNGen_3422_ = lean_ctor_get(v___x_3418_, 3);
v_traceState_3423_ = lean_ctor_get(v___x_3418_, 4);
v_messages_3424_ = lean_ctor_get(v___x_3418_, 6);
v_infoState_3425_ = lean_ctor_get(v___x_3418_, 7);
v_snapshotTasks_3426_ = lean_ctor_get(v___x_3418_, 8);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v___x_3418_, 5);
lean_dec(v_unused_3436_);
v___x_3428_ = v___x_3418_;
v_isShared_3429_ = v_isSharedCheck_3435_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_snapshotTasks_3426_);
lean_inc(v_infoState_3425_);
lean_inc(v_messages_3424_);
lean_inc(v_traceState_3423_);
lean_inc(v_auxDeclNGen_3422_);
lean_inc(v_ngen_3421_);
lean_inc(v_nextMacroScope_3420_);
lean_inc(v_env_3419_);
lean_dec(v___x_3418_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3435_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3430_; lean_object* v___x_3432_; 
v___x_3430_ = l_Lean_Kernel_enableDiag(v_env_3419_, v___x_3365_);
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 5, v___x_3341_);
lean_ctor_set(v___x_3428_, 0, v___x_3430_);
v___x_3432_ = v___x_3428_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3430_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_nextMacroScope_3420_);
lean_ctor_set(v_reuseFailAlloc_3434_, 2, v_ngen_3421_);
lean_ctor_set(v_reuseFailAlloc_3434_, 3, v_auxDeclNGen_3422_);
lean_ctor_set(v_reuseFailAlloc_3434_, 4, v_traceState_3423_);
lean_ctor_set(v_reuseFailAlloc_3434_, 5, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3434_, 6, v_messages_3424_);
lean_ctor_set(v_reuseFailAlloc_3434_, 7, v_infoState_3425_);
lean_ctor_set(v_reuseFailAlloc_3434_, 8, v_snapshotTasks_3426_);
v___x_3432_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_st_ref_set(v___x_3354_, v___x_3432_);
lean_inc(v___x_3354_);
v_fileName_3367_ = v___x_3359_;
v_fileMap_3368_ = v___x_3360_;
v_currRecDepth_3369_ = v___x_3340_;
v_ref_3370_ = v___x_3361_;
v_currNamespace_3371_ = v_currNamespace_3332_;
v_openDecls_3372_ = v_openDecls_3333_;
v_initHeartbeats_3373_ = v___x_3343_;
v_maxHeartbeats_3374_ = v___x_3362_;
v_quotContext_3375_ = v___x_3347_;
v_currMacroScope_3376_ = v___x_3344_;
v_cancelTk_x3f_3377_ = v_cancelTk_x3f_3334_;
v_suppressElabErrors_3378_ = v___x_3363_;
v_inheritedTraceOptions_3379_ = v___x_3356_;
v___y_3380_ = v___x_3354_;
goto v___jp_3366_;
}
}
}
else
{
lean_inc(v___x_3354_);
v_fileName_3367_ = v___x_3359_;
v_fileMap_3368_ = v___x_3360_;
v_currRecDepth_3369_ = v___x_3340_;
v_ref_3370_ = v___x_3361_;
v_currNamespace_3371_ = v_currNamespace_3332_;
v_openDecls_3372_ = v_openDecls_3333_;
v_initHeartbeats_3373_ = v___x_3343_;
v_maxHeartbeats_3374_ = v___x_3362_;
v_quotContext_3375_ = v___x_3347_;
v_currMacroScope_3376_ = v___x_3344_;
v_cancelTk_x3f_3377_ = v_cancelTk_x3f_3334_;
v_suppressElabErrors_3378_ = v___x_3363_;
v_inheritedTraceOptions_3379_ = v___x_3356_;
v___y_3380_ = v___x_3354_;
goto v___jp_3366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg___boxed(lean_object* v_env_3438_, lean_object* v_act_3439_, lean_object* v_options_3440_, lean_object* v_currNamespace_3441_, lean_object* v_openDecls_3442_, lean_object* v_cancelTk_x3f_3443_, lean_object* v_a_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lean_Doc_runMarkdown___redArg(v_env_3438_, v_act_3439_, v_options_3440_, v_currNamespace_3441_, v_openDecls_3442_, v_cancelTk_x3f_3443_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown(lean_object* v_00_u03b1_3446_, lean_object* v_env_3447_, lean_object* v_act_3448_, lean_object* v_options_3449_, lean_object* v_currNamespace_3450_, lean_object* v_openDecls_3451_, lean_object* v_cancelTk_x3f_3452_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Lean_Doc_runMarkdown___redArg(v_env_3447_, v_act_3448_, v_options_3449_, v_currNamespace_3450_, v_openDecls_3451_, v_cancelTk_x3f_3452_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___boxed(lean_object* v_00_u03b1_3455_, lean_object* v_env_3456_, lean_object* v_act_3457_, lean_object* v_options_3458_, lean_object* v_currNamespace_3459_, lean_object* v_openDecls_3460_, lean_object* v_cancelTk_x3f_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_Doc_runMarkdown(v_00_u03b1_3455_, v_env_3456_, v_act_3457_, v_options_3458_, v_currNamespace_3459_, v_openDecls_3460_, v_cancelTk_x3f_3461_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(lean_object* v_x_3464_, size_t v_sz_3465_, size_t v_i_3466_, lean_object* v_bs_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
uint8_t v___x_3472_; 
v___x_3472_ = lean_usize_dec_lt(v_i_3466_, v_sz_3465_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; 
lean_dec_ref(v_x_3464_);
v___x_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3473_, 0, v_bs_3467_);
return v___x_3473_;
}
else
{
lean_object* v_v_3474_; lean_object* v___x_3475_; 
v_v_3474_ = lean_array_uget_borrowed(v_bs_3467_, v_i_3466_);
lean_inc(v_v_3474_);
lean_inc_ref(v_x_3464_);
v___x_3475_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3464_, v_v_3474_, v___y_3468_, v___y_3469_, v___y_3470_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3477_; lean_object* v_bs_x27_3478_; size_t v___x_3479_; size_t v___x_3480_; lean_object* v___x_3481_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3476_);
lean_dec_ref_known(v___x_3475_, 1);
v___x_3477_ = lean_unsigned_to_nat(0u);
v_bs_x27_3478_ = lean_array_uset(v_bs_3467_, v_i_3466_, v___x_3477_);
v___x_3479_ = ((size_t)1ULL);
v___x_3480_ = lean_usize_add(v_i_3466_, v___x_3479_);
v___x_3481_ = lean_array_uset(v_bs_x27_3478_, v_i_3466_, v_a_3476_);
v_i_3466_ = v___x_3480_;
v_bs_3467_ = v___x_3481_;
goto _start;
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v_bs_3467_);
lean_dec_ref(v_x_3464_);
v_a_3483_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3475_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3475_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed(lean_object* v_x_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(v_x_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(lean_object* v_x_3500_, size_t v_sz_3501_, size_t v___x_3502_, lean_object* v_content_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3500_, v_sz_3501_, v___x_3502_, v_content_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3517_; 
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3511_ = v___x_3508_;
v_isShared_3512_ = v_isSharedCheck_3517_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3508_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3517_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3513_ = l_Lean_Doc_joinInlines(v_a_3509_);
lean_dec(v_a_3509_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v___x_3513_);
v___x_3515_ = v___x_3511_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
v_a_3518_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3508_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3508_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed(lean_object* v_x_3526_, lean_object* v_sz_3527_, lean_object* v___x_3528_, lean_object* v_content_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
size_t v_sz_boxed_3534_; size_t v___x_3921__boxed_3535_; lean_object* v_res_3536_; 
v_sz_boxed_3534_ = lean_unbox_usize(v_sz_3527_);
lean_dec(v_sz_3527_);
v___x_3921__boxed_3535_ = lean_unbox_usize(v___x_3528_);
lean_dec(v___x_3528_);
v_res_3536_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(v_x_3526_, v_sz_boxed_3534_, v___x_3921__boxed_3535_, v_content_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(lean_object* v_x_3537_, lean_object* v_x_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_pieces_3544_; lean_object* v_pieces_3548_; 
switch(lean_obj_tag(v_x_3538_))
{
case 0:
{
lean_object* v_string_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
lean_dec_ref(v_x_3537_);
v_string_3551_ = lean_ctor_get(v_x_3538_, 0);
lean_inc_ref(v_string_3551_);
lean_dec_ref_known(v_x_3538_, 1);
v___x_3552_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_3551_);
lean_dec_ref(v_string_3551_);
v___x_3553_ = lean_unsigned_to_nat(1u);
v___x_3554_ = lean_mk_empty_array_with_capacity(v___x_3553_);
v___x_3555_ = lean_array_push(v___x_3554_, v___x_3552_);
v___x_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
return v___x_3556_;
}
case 1:
{
lean_object* v_content_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3612_; 
v_content_3557_ = lean_ctor_get(v_x_3538_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_x_3538_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3559_ = v_x_3538_;
v_isShared_3560_ = v_isSharedCheck_3612_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_content_3557_);
lean_dec(v_x_3538_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3612_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
lean_ctor_set_tag(v___x_3559_, 9);
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_content_3557_);
v___x_3562_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3563_; lean_object* v_snd_3564_; lean_object* v_fst_3565_; lean_object* v_fst_3566_; lean_object* v_snd_3567_; lean_object* v_pieces_3569_; uint8_t v_inEmph_3577_; uint8_t v_inBold_3578_; uint8_t v_inLink_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3610_; 
v___x_3563_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3562_);
v_snd_3564_ = lean_ctor_get(v___x_3563_, 1);
lean_inc(v_snd_3564_);
v_fst_3565_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_fst_3565_);
lean_dec_ref(v___x_3563_);
v_fst_3566_ = lean_ctor_get(v_snd_3564_, 0);
lean_inc(v_fst_3566_);
v_snd_3567_ = lean_ctor_get(v_snd_3564_, 1);
lean_inc(v_snd_3567_);
lean_dec(v_snd_3564_);
v_inEmph_3577_ = lean_ctor_get_uint8(v_x_3537_, 0);
v_inBold_3578_ = lean_ctor_get_uint8(v_x_3537_, 1);
v_inLink_3579_ = lean_ctor_get_uint8(v_x_3537_, 2);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_x_3537_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3581_ = v_x_3537_;
v_isShared_3582_ = v_isSharedCheck_3610_;
goto v_resetjp_3580_;
}
else
{
lean_dec(v_x_3537_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3610_;
goto v_resetjp_3580_;
}
v___jp_3568_:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; uint8_t v___x_3572_; 
v___x_3570_ = lean_string_utf8_byte_size(v_snd_3567_);
v___x_3571_ = lean_unsigned_to_nat(0u);
v___x_3572_ = lean_nat_dec_eq(v___x_3570_, v___x_3571_);
if (v___x_3572_ == 0)
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3573_ = lean_unsigned_to_nat(1u);
v___x_3574_ = lean_mk_empty_array_with_capacity(v___x_3573_);
v___x_3575_ = lean_array_push(v___x_3574_, v_snd_3567_);
v___x_3576_ = lean_array_push(v_pieces_3569_, v___x_3575_);
v_pieces_3548_ = v___x_3576_;
goto v___jp_3547_;
}
else
{
lean_dec(v_snd_3567_);
v_pieces_3548_ = v_pieces_3569_;
goto v___jp_3547_;
}
}
v_resetjp_3580_:
{
uint8_t v___x_3583_; lean_object* v___x_3585_; 
v___x_3583_ = 1;
if (v_isShared_3582_ == 0)
{
v___x_3585_ = v___x_3581_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3609_, 1, v_inBold_3578_);
lean_ctor_set_uint8(v_reuseFailAlloc_3609_, 2, v_inLink_3579_);
v___x_3585_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3586_; 
lean_ctor_set_uint8(v___x_3585_, 0, v___x_3583_);
v___x_3586_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3585_, v_fst_3566_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; lean_object* v_pieces_3589_; lean_object* v_pieces_3596_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_a_3587_);
lean_dec_ref_known(v___x_3586_, 1);
v___x_3601_ = lean_unsigned_to_nat(0u);
v___x_3602_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3603_ = lean_string_utf8_byte_size(v_fst_3565_);
v___x_3604_ = lean_nat_dec_eq(v___x_3603_, v___x_3601_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3605_ = lean_unsigned_to_nat(1u);
v___x_3606_ = lean_mk_empty_array_with_capacity(v___x_3605_);
v___x_3607_ = lean_array_push(v___x_3606_, v_fst_3565_);
v___x_3608_ = lean_array_push(v___x_3602_, v___x_3607_);
v_pieces_3596_ = v___x_3608_;
goto v___jp_3595_;
}
else
{
lean_dec(v_fst_3565_);
v_pieces_3596_ = v___x_3602_;
goto v___jp_3595_;
}
v___jp_3588_:
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_array_push(v_pieces_3589_, v_a_3587_);
if (v_inEmph_3577_ == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3591_ = lean_unsigned_to_nat(1u);
v___x_3592_ = lean_mk_empty_array_with_capacity(v___x_3591_);
lean_dec_ref(v___x_3592_);
v___x_3593_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3594_ = lean_array_push(v___x_3590_, v___x_3593_);
v_pieces_3569_ = v___x_3594_;
goto v___jp_3568_;
}
else
{
v_pieces_3569_ = v___x_3590_;
goto v___jp_3568_;
}
}
v___jp_3595_:
{
if (v_inEmph_3577_ == 0)
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3597_ = lean_unsigned_to_nat(1u);
v___x_3598_ = lean_mk_empty_array_with_capacity(v___x_3597_);
lean_dec_ref(v___x_3598_);
v___x_3599_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3600_ = lean_array_push(v_pieces_3596_, v___x_3599_);
v_pieces_3589_ = v___x_3600_;
goto v___jp_3588_;
}
else
{
v_pieces_3589_ = v_pieces_3596_;
goto v___jp_3588_;
}
}
}
else
{
lean_dec(v_snd_3567_);
lean_dec(v_fst_3565_);
return v___x_3586_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3668_; 
v_content_3613_ = lean_ctor_get(v_x_3538_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_x_3538_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3615_ = v_x_3538_;
v_isShared_3616_ = v_isSharedCheck_3668_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_content_3613_);
lean_dec(v_x_3538_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3668_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 9);
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_content_3613_);
v___x_3618_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; lean_object* v_snd_3620_; lean_object* v_fst_3621_; lean_object* v_fst_3622_; lean_object* v_snd_3623_; lean_object* v_pieces_3625_; uint8_t v_inEmph_3633_; uint8_t v_inBold_3634_; uint8_t v_inLink_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3666_; 
v___x_3619_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3618_);
v_snd_3620_ = lean_ctor_get(v___x_3619_, 1);
lean_inc(v_snd_3620_);
v_fst_3621_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_fst_3621_);
lean_dec_ref(v___x_3619_);
v_fst_3622_ = lean_ctor_get(v_snd_3620_, 0);
lean_inc(v_fst_3622_);
v_snd_3623_ = lean_ctor_get(v_snd_3620_, 1);
lean_inc(v_snd_3623_);
lean_dec(v_snd_3620_);
v_inEmph_3633_ = lean_ctor_get_uint8(v_x_3537_, 0);
v_inBold_3634_ = lean_ctor_get_uint8(v_x_3537_, 1);
v_inLink_3635_ = lean_ctor_get_uint8(v_x_3537_, 2);
v_isSharedCheck_3666_ = !lean_is_exclusive(v_x_3537_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3637_ = v_x_3537_;
v_isShared_3638_ = v_isSharedCheck_3666_;
goto v_resetjp_3636_;
}
else
{
lean_dec(v_x_3537_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3666_;
goto v_resetjp_3636_;
}
v___jp_3624_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3626_ = lean_string_utf8_byte_size(v_snd_3623_);
v___x_3627_ = lean_unsigned_to_nat(0u);
v___x_3628_ = lean_nat_dec_eq(v___x_3626_, v___x_3627_);
if (v___x_3628_ == 0)
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3629_ = lean_unsigned_to_nat(1u);
v___x_3630_ = lean_mk_empty_array_with_capacity(v___x_3629_);
v___x_3631_ = lean_array_push(v___x_3630_, v_snd_3623_);
v___x_3632_ = lean_array_push(v_pieces_3625_, v___x_3631_);
v_pieces_3544_ = v___x_3632_;
goto v___jp_3543_;
}
else
{
lean_dec(v_snd_3623_);
v_pieces_3544_ = v_pieces_3625_;
goto v___jp_3543_;
}
}
v_resetjp_3636_:
{
uint8_t v___x_3639_; lean_object* v___x_3641_; 
v___x_3639_ = 1;
if (v_isShared_3638_ == 0)
{
v___x_3641_ = v___x_3637_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, 0, v_inEmph_3633_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, 2, v_inLink_3635_);
v___x_3641_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3642_; 
lean_ctor_set_uint8(v___x_3641_, 1, v___x_3639_);
v___x_3642_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3641_, v_fst_3622_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v_pieces_3645_; lean_object* v_pieces_3652_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref_known(v___x_3642_, 1);
v___x_3657_ = lean_unsigned_to_nat(0u);
v___x_3658_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3659_ = lean_string_utf8_byte_size(v_fst_3621_);
v___x_3660_ = lean_nat_dec_eq(v___x_3659_, v___x_3657_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3661_ = lean_unsigned_to_nat(1u);
v___x_3662_ = lean_mk_empty_array_with_capacity(v___x_3661_);
v___x_3663_ = lean_array_push(v___x_3662_, v_fst_3621_);
v___x_3664_ = lean_array_push(v___x_3658_, v___x_3663_);
v_pieces_3652_ = v___x_3664_;
goto v___jp_3651_;
}
else
{
lean_dec(v_fst_3621_);
v_pieces_3652_ = v___x_3658_;
goto v___jp_3651_;
}
v___jp_3644_:
{
lean_object* v___x_3646_; 
v___x_3646_ = lean_array_push(v_pieces_3645_, v_a_3643_);
if (v_inBold_3634_ == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3647_ = lean_unsigned_to_nat(1u);
v___x_3648_ = lean_mk_empty_array_with_capacity(v___x_3647_);
lean_dec_ref(v___x_3648_);
v___x_3649_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3650_ = lean_array_push(v___x_3646_, v___x_3649_);
v_pieces_3625_ = v___x_3650_;
goto v___jp_3624_;
}
else
{
v_pieces_3625_ = v___x_3646_;
goto v___jp_3624_;
}
}
v___jp_3651_:
{
if (v_inBold_3634_ == 0)
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3653_ = lean_unsigned_to_nat(1u);
v___x_3654_ = lean_mk_empty_array_with_capacity(v___x_3653_);
lean_dec_ref(v___x_3654_);
v___x_3655_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3656_ = lean_array_push(v_pieces_3652_, v___x_3655_);
v_pieces_3645_ = v___x_3656_;
goto v___jp_3644_;
}
else
{
v_pieces_3645_ = v_pieces_3652_;
goto v___jp_3644_;
}
}
}
else
{
lean_dec(v_snd_3623_);
lean_dec(v_fst_3621_);
return v___x_3642_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
lean_dec_ref(v_x_3537_);
v_string_3669_ = lean_ctor_get(v_x_3538_, 0);
lean_inc_ref(v_string_3669_);
lean_dec_ref_known(v_x_3538_, 1);
v___x_3670_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_3669_);
v___x_3671_ = lean_unsigned_to_nat(1u);
v___x_3672_ = lean_mk_empty_array_with_capacity(v___x_3671_);
v___x_3673_ = lean_array_push(v___x_3672_, v___x_3670_);
v___x_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
return v___x_3674_;
}
case 4:
{
uint8_t v_mode_3675_; 
lean_dec_ref(v_x_3537_);
v_mode_3675_ = lean_ctor_get_uint8(v_x_3538_, sizeof(void*)*1);
if (v_mode_3675_ == 0)
{
lean_object* v_string_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v_string_3676_ = lean_ctor_get(v_x_3538_, 0);
lean_inc_ref(v_string_3676_);
lean_dec_ref_known(v_x_3538_, 1);
v___x_3677_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_3678_ = lean_string_append(v___x_3677_, v_string_3676_);
lean_dec_ref(v_string_3676_);
v___x_3679_ = lean_string_append(v___x_3678_, v___x_3677_);
v___x_3680_ = lean_unsigned_to_nat(1u);
v___x_3681_ = lean_mk_empty_array_with_capacity(v___x_3680_);
v___x_3682_ = lean_array_push(v___x_3681_, v___x_3679_);
v___x_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
return v___x_3683_;
}
else
{
lean_object* v_string_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v_string_3684_ = lean_ctor_get(v_x_3538_, 0);
lean_inc_ref(v_string_3684_);
lean_dec_ref_known(v_x_3538_, 1);
v___x_3685_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_3686_ = lean_string_append(v___x_3685_, v_string_3684_);
lean_dec_ref(v_string_3684_);
v___x_3687_ = lean_string_append(v___x_3686_, v___x_3685_);
v___x_3688_ = lean_unsigned_to_nat(1u);
v___x_3689_ = lean_mk_empty_array_with_capacity(v___x_3688_);
v___x_3690_ = lean_array_push(v___x_3689_, v___x_3687_);
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
return v___x_3691_;
}
}
case 5:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
lean_dec_ref_known(v_x_3538_, 1);
lean_dec_ref(v_x_3537_);
v___x_3692_ = lean_unsigned_to_nat(2u);
v___x_3693_ = lean_mk_empty_array_with_capacity(v___x_3692_);
lean_dec_ref(v___x_3693_);
v___x_3694_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
return v___x_3695_;
}
case 6:
{
uint8_t v_inLink_3696_; 
v_inLink_3696_ = lean_ctor_get_uint8(v_x_3537_, 2);
if (v_inLink_3696_ == 0)
{
lean_object* v_content_3697_; lean_object* v_url_3698_; uint8_t v_inEmph_3699_; uint8_t v_inBold_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3731_; 
v_content_3697_ = lean_ctor_get(v_x_3538_, 0);
lean_inc_ref(v_content_3697_);
v_url_3698_ = lean_ctor_get(v_x_3538_, 1);
lean_inc_ref(v_url_3698_);
lean_dec_ref_known(v_x_3538_, 2);
v_inEmph_3699_ = lean_ctor_get_uint8(v_x_3537_, 0);
v_inBold_3700_ = lean_ctor_get_uint8(v_x_3537_, 1);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_x_3537_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3702_ = v_x_3537_;
v_isShared_3703_ = v_isSharedCheck_3731_;
goto v_resetjp_3701_;
}
else
{
lean_dec(v_x_3537_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3731_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
uint8_t v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = 1;
if (v_isShared_3703_ == 0)
{
v___x_3706_ = v___x_3702_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3730_, 0, v_inEmph_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3730_, 1, v_inBold_3700_);
v___x_3706_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
lean_ctor_set_uint8(v___x_3706_, 2, v___x_3704_);
v___x_3707_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3707_, 0, v_content_3697_);
v___x_3708_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3706_, v___x_3707_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3729_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3711_ = v___x_3708_;
v_isShared_3712_ = v_isSharedCheck_3729_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3708_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3729_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3713_ = lean_unsigned_to_nat(1u);
v___x_3714_ = lean_mk_empty_array_with_capacity(v___x_3713_);
v___x_3715_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3716_ = lean_string_append(v___x_3715_, v_url_3698_);
lean_dec_ref(v_url_3698_);
v___x_3717_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3718_ = lean_string_append(v___x_3716_, v___x_3717_);
v___x_3719_ = lean_array_push(v___x_3714_, v___x_3718_);
v___x_3720_ = lean_unsigned_to_nat(3u);
v___x_3721_ = lean_mk_empty_array_with_capacity(v___x_3720_);
lean_dec_ref(v___x_3721_);
v___x_3722_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_3723_ = lean_array_push(v___x_3722_, v_a_3709_);
v___x_3724_ = lean_array_push(v___x_3723_, v___x_3719_);
v___x_3725_ = l_Lean_Doc_joinInlines(v___x_3724_);
lean_dec_ref(v___x_3724_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 0, v___x_3725_);
v___x_3727_ = v___x_3711_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
else
{
lean_dec_ref(v_url_3698_);
return v___x_3708_;
}
}
}
}
else
{
lean_object* v_content_3732_; size_t v_sz_3733_; size_t v___x_3734_; lean_object* v___x_3735_; 
v_content_3732_ = lean_ctor_get(v_x_3538_, 0);
lean_inc_ref(v_content_3732_);
lean_dec_ref_known(v_x_3538_, 2);
v_sz_3733_ = lean_array_size(v_content_3732_);
v___x_3734_ = ((size_t)0ULL);
v___x_3735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3537_, v_sz_3733_, v___x_3734_, v_content_3732_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3744_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3738_ = v___x_3735_;
v_isShared_3739_ = v_isSharedCheck_3744_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3735_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3744_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3740_; lean_object* v___x_3742_; 
v___x_3740_ = l_Lean_Doc_joinInlines(v_a_3736_);
lean_dec(v_a_3736_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 0, v___x_3740_);
v___x_3742_ = v___x_3738_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
v_a_3745_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3735_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3735_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
}
case 7:
{
lean_object* v_name_3753_; lean_object* v_content_3754_; size_t v_sz_3755_; size_t v___x_3756_; lean_object* v___x_3757_; 
v_name_3753_ = lean_ctor_get(v_x_3538_, 0);
lean_inc_ref(v_name_3753_);
v_content_3754_ = lean_ctor_get(v_x_3538_, 1);
lean_inc_ref(v_content_3754_);
lean_dec_ref_known(v_x_3538_, 2);
v_sz_3755_ = lean_array_size(v_content_3754_);
v___x_3756_ = ((size_t)0ULL);
v___x_3757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3537_, v_sz_3755_, v___x_3756_, v_content_3754_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3757_, 1);
v___x_3759_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_3760_ = l_Lean_Doc_joinInlines(v_a_3758_);
lean_dec(v_a_3758_);
v___x_3761_ = lean_array_to_list(v___x_3760_);
v___x_3762_ = l_String_intercalate(v___x_3759_, v___x_3761_);
lean_inc_ref(v_name_3753_);
v___x_3763_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_3753_, v___x_3762_, v_a_3539_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3777_; 
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3777_ == 0)
{
lean_object* v_unused_3778_; 
v_unused_3778_ = lean_ctor_get(v___x_3763_, 0);
lean_dec(v_unused_3778_);
v___x_3765_ = v___x_3763_;
v_isShared_3766_ = v_isSharedCheck_3777_;
goto v_resetjp_3764_;
}
else
{
lean_dec(v___x_3763_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3777_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3775_; 
v___x_3767_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_3768_ = lean_string_append(v___x_3767_, v_name_3753_);
lean_dec_ref(v_name_3753_);
v___x_3769_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_3770_ = lean_string_append(v___x_3768_, v___x_3769_);
v___x_3771_ = lean_unsigned_to_nat(1u);
v___x_3772_ = lean_mk_empty_array_with_capacity(v___x_3771_);
v___x_3773_ = lean_array_push(v___x_3772_, v___x_3770_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v___x_3773_);
v___x_3775_ = v___x_3765_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3773_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec_ref(v_name_3753_);
v_a_3779_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3763_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3763_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec_ref(v_name_3753_);
v_a_3787_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3757_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3757_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
case 8:
{
lean_object* v_alt_3795_; lean_object* v_url_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
lean_dec_ref(v_x_3537_);
v_alt_3795_ = lean_ctor_get(v_x_3538_, 0);
lean_inc_ref(v_alt_3795_);
v_url_3796_ = lean_ctor_get(v_x_3538_, 1);
lean_inc_ref(v_url_3796_);
lean_dec_ref_known(v_x_3538_, 2);
v___x_3797_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_3798_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_3795_);
lean_dec_ref(v_alt_3795_);
v___x_3799_ = lean_string_append(v___x_3797_, v___x_3798_);
lean_dec_ref(v___x_3798_);
v___x_3800_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3801_ = lean_string_append(v___x_3799_, v___x_3800_);
v___x_3802_ = lean_string_append(v___x_3801_, v_url_3796_);
lean_dec_ref(v_url_3796_);
v___x_3803_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3804_ = lean_string_append(v___x_3802_, v___x_3803_);
v___x_3805_ = lean_unsigned_to_nat(1u);
v___x_3806_ = lean_mk_empty_array_with_capacity(v___x_3805_);
v___x_3807_ = lean_array_push(v___x_3806_, v___x_3804_);
v___x_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
return v___x_3808_;
}
case 9:
{
lean_object* v_content_3809_; size_t v_sz_3810_; size_t v___x_3811_; lean_object* v___x_3812_; 
v_content_3809_ = lean_ctor_get(v_x_3538_, 0);
lean_inc_ref(v_content_3809_);
lean_dec_ref_known(v_x_3538_, 1);
v_sz_3810_ = lean_array_size(v_content_3809_);
v___x_3811_ = ((size_t)0ULL);
v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3537_, v_sz_3810_, v___x_3811_, v_content_3809_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3821_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3815_ = v___x_3812_;
v_isShared_3816_ = v_isSharedCheck_3821_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3812_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3821_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3817_; lean_object* v___x_3819_; 
v___x_3817_ = l_Lean_Doc_joinInlines(v_a_3813_);
lean_dec(v_a_3813_);
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 0, v___x_3817_);
v___x_3819_ = v___x_3815_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3817_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
v_a_3822_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3812_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3812_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
default: 
{
lean_object* v_container_3830_; lean_object* v_content_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v_container_3830_ = lean_ctor_get(v_x_3538_, 0);
lean_inc(v_container_3830_);
v_content_3831_ = lean_ctor_get(v_x_3538_, 1);
lean_inc_ref(v_content_3831_);
lean_dec_ref_known(v_x_3538_, 2);
v___x_3832_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_container_3830_);
v___x_3833_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_3832_, v_a_3540_, v_a_3541_);
lean_dec(v___x_3832_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___x_3833_, 1);
if (lean_obj_tag(v_a_3834_) == 0)
{
size_t v_sz_3835_; size_t v___x_3836_; lean_object* v___x_3837_; 
lean_dec(v_container_3830_);
v_sz_3835_ = lean_array_size(v_content_3831_);
v___x_3836_ = ((size_t)0ULL);
v___x_3837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3537_, v_sz_3835_, v___x_3836_, v_content_3831_, v_a_3539_, v_a_3540_, v_a_3541_);
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
else
{
lean_object* v_val_3855_; lean_object* v___f_3856_; size_t v_sz_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v_fallback_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v_val_3855_ = lean_ctor_get(v_a_3834_, 0);
lean_inc(v_val_3855_);
lean_dec_ref_known(v_a_3834_, 1);
lean_inc_ref(v_x_3537_);
v___f_3856_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3856_, 0, v_x_3537_);
v_sz_3857_ = lean_array_size(v_content_3831_);
v___x_3858_ = lean_box_usize(v_sz_3857_);
v___x_3859_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
lean_inc_ref(v_content_3831_);
v_fallback_3860_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v_fallback_3860_, 0, v_x_3537_);
lean_closure_set(v_fallback_3860_, 1, v___x_3858_);
lean_closure_set(v_fallback_3860_, 2, v___x_3859_);
lean_closure_set(v_fallback_3860_, 3, v_content_3831_);
v___x_3861_ = lean_apply_3(v_val_3855_, v___f_3856_, v_container_3830_, v_content_3831_);
v___x_3862_ = l_Lean_Doc_withRendererFallback(v_fallback_3860_, v___x_3861_, v_a_3539_, v_a_3540_, v_a_3541_);
return v___x_3862_;
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_dec_ref(v_content_3831_);
lean_dec(v_container_3830_);
lean_dec_ref(v_x_3537_);
v_a_3863_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3833_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3833_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
}
v___jp_3543_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = l_Lean_Doc_joinInlines(v_pieces_3544_);
lean_dec_ref(v_pieces_3544_);
v___x_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
return v___x_3546_;
}
v___jp_3547_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = l_Lean_Doc_joinInlines(v_pieces_3548_);
lean_dec_ref(v_pieces_3548_);
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
return v___x_3550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(lean_object* v_x_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3878_, lean_object* v_sz_3879_, lean_object* v_i_3880_, lean_object* v_bs_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
size_t v_sz_boxed_3886_; size_t v_i_boxed_3887_; lean_object* v_res_3888_; 
v_sz_boxed_3886_ = lean_unbox_usize(v_sz_3879_);
lean_dec(v_sz_3879_);
v_i_boxed_3887_ = lean_unbox_usize(v_i_3880_);
lean_dec(v_i_3880_);
v_res_3888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3878_, v_sz_boxed_3886_, v_i_boxed_3887_, v_bs_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed(lean_object* v_x_3889_, lean_object* v_x_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3889_, v_x_3890_, v_a_3891_, v_a_3892_, v_a_3893_);
lean_dec(v_a_3893_);
lean_dec_ref(v_a_3892_);
lean_dec(v_a_3891_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(lean_object* v___x_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0___boxed(lean_object* v___x_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(v___x_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(lean_object* v_x_3910_, lean_object* v_x_3911_){
_start:
{
lean_object* v_zero_3912_; uint8_t v_isZero_3913_; 
v_zero_3912_ = lean_unsigned_to_nat(0u);
v_isZero_3913_ = lean_nat_dec_eq(v_x_3910_, v_zero_3912_);
if (v_isZero_3913_ == 1)
{
lean_dec(v_x_3910_);
return v_x_3911_;
}
else
{
uint32_t v___x_3914_; lean_object* v_one_3915_; lean_object* v_n_3916_; lean_object* v___x_3917_; 
v___x_3914_ = 32;
v_one_3915_ = lean_unsigned_to_nat(1u);
v_n_3916_ = lean_nat_sub(v_x_3910_, v_one_3915_);
lean_dec(v_x_3910_);
v___x_3917_ = lean_string_push(v_x_3911_, v___x_3914_);
v_x_3910_ = v_n_3916_;
v_x_3911_ = v___x_3917_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(size_t v_sz_3919_, size_t v_i_3920_, lean_object* v_bs_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
uint8_t v___x_3926_; 
v___x_3926_ = lean_usize_dec_lt(v_i_3920_, v_sz_3919_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; 
v___x_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3927_, 0, v_bs_3921_);
return v___x_3927_;
}
else
{
lean_object* v_v_3928_; size_t v_sz_3929_; size_t v___x_3930_; lean_object* v___x_3931_; 
v_v_3928_ = lean_array_uget_borrowed(v_bs_3921_, v_i_3920_);
v_sz_3929_ = lean_array_size(v_v_3928_);
v___x_3930_ = ((size_t)0ULL);
lean_inc(v_v_3928_);
v___x_3931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_3929_, v___x_3930_, v_v_3928_, v___y_3922_, v___y_3923_, v___y_3924_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3933_; lean_object* v_bs_x27_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; size_t v___x_3939_; size_t v___x_3940_; lean_object* v___x_3941_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v___x_3933_ = lean_unsigned_to_nat(0u);
v_bs_x27_3934_ = lean_array_uset(v_bs_3921_, v_i_3920_, v___x_3933_);
v___x_3935_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_3936_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_3937_ = l_Lean_Doc_joinBlocks(v_a_3932_);
lean_dec(v_a_3932_);
v___x_3938_ = l_Lean_Doc_prefixListLines(v___x_3935_, v___x_3936_, v___x_3937_);
lean_dec_ref(v___x_3937_);
v___x_3939_ = ((size_t)1ULL);
v___x_3940_ = lean_usize_add(v_i_3920_, v___x_3939_);
v___x_3941_ = lean_array_uset(v_bs_x27_3934_, v_i_3920_, v___x_3938_);
v_i_3920_ = v___x_3940_;
v_bs_3921_ = v___x_3941_;
goto _start;
}
else
{
lean_dec_ref(v_bs_3921_);
return v___x_3931_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(lean_object* v_as_3943_, size_t v_sz_3944_, size_t v_i_3945_, lean_object* v_b_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
uint8_t v___x_3951_; 
v___x_3951_ = lean_usize_dec_lt(v_i_3945_, v_sz_3944_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3952_, 0, v_b_3946_);
return v___x_3952_;
}
else
{
lean_object* v_a_3953_; size_t v_sz_3954_; size_t v___x_3955_; lean_object* v___x_3956_; 
v_a_3953_ = lean_array_uget_borrowed(v_as_3943_, v_i_3945_);
v_sz_3954_ = lean_array_size(v_a_3953_);
v___x_3955_ = ((size_t)0ULL);
lean_inc(v_a_3953_);
v___x_3956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_3954_, v___x_3955_, v_a_3953_, v___y_3947_, v___y_3948_, v___y_3949_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v_fst_3958_; lean_object* v_snd_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3980_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_a_3957_);
lean_dec_ref_known(v___x_3956_, 1);
v_fst_3958_ = lean_ctor_get(v_b_3946_, 0);
v_snd_3959_ = lean_ctor_get(v_b_3946_, 1);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_b_3946_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3961_ = v_b_3946_;
v_isShared_3962_ = v_isSharedCheck_3980_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_snd_3959_);
lean_inc(v_fst_3958_);
lean_dec(v_b_3946_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3980_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3975_; 
v___x_3963_ = lean_unsigned_to_nat(1u);
lean_inc(v_snd_3959_);
v___x_3964_ = l_Nat_reprFast(v_snd_3959_);
v___x_3965_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_3966_ = lean_string_append(v___x_3964_, v___x_3965_);
v___x_3967_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_3968_ = lean_string_utf8_byte_size(v___x_3966_);
v___x_3969_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(v___x_3968_, v___x_3967_);
v___x_3970_ = l_Lean_Doc_joinBlocks(v_a_3957_);
lean_dec(v_a_3957_);
v___x_3971_ = l_Lean_Doc_prefixListLines(v___x_3966_, v___x_3969_, v___x_3970_);
lean_dec_ref(v___x_3970_);
v___x_3972_ = lean_array_push(v_fst_3958_, v___x_3971_);
v___x_3973_ = lean_nat_add(v_snd_3959_, v___x_3963_);
lean_dec(v_snd_3959_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 1, v___x_3973_);
lean_ctor_set(v___x_3961_, 0, v___x_3972_);
v___x_3975_ = v___x_3961_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3972_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v___x_3973_);
v___x_3975_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
size_t v___x_3976_; size_t v___x_3977_; 
v___x_3976_ = ((size_t)1ULL);
v___x_3977_ = lean_usize_add(v_i_3945_, v___x_3976_);
v_i_3945_ = v___x_3977_;
v_b_3946_ = v___x_3975_;
goto _start;
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec_ref(v_b_3946_);
v_a_3981_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3956_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3956_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(size_t v_sz_3989_, size_t v_i_3990_, lean_object* v_bs_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
uint8_t v___x_3996_; 
v___x_3996_ = lean_usize_dec_lt(v_i_3990_, v_sz_3989_);
if (v___x_3996_ == 0)
{
lean_object* v___x_3997_; 
v___x_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3997_, 0, v_bs_3991_);
return v___x_3997_;
}
else
{
lean_object* v_v_3998_; lean_object* v___x_3999_; lean_object* v_term_4000_; lean_object* v_desc_4001_; lean_object* v___x_4002_; lean_object* v_bs_x27_4003_; lean_object* v_a_4005_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v_v_3998_ = lean_array_uget_borrowed(v_bs_3991_, v_i_3990_);
v___x_3999_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_4000_ = lean_ctor_get(v_v_3998_, 0);
lean_inc_ref(v_term_4000_);
v_desc_4001_ = lean_ctor_get(v_v_3998_, 1);
lean_inc_ref(v_desc_4001_);
v___x_4002_ = lean_unsigned_to_nat(0u);
v_bs_x27_4003_ = lean_array_uset(v_bs_3991_, v_i_3990_, v___x_4002_);
v___x_4010_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4010_, 0, v_term_4000_);
v___x_4011_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3999_, v___x_4010_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; size_t v_sz_4013_; size_t v___x_4014_; lean_object* v___x_4015_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v___x_4011_, 1);
v_sz_4013_ = lean_array_size(v_desc_4001_);
v___x_4014_ = ((size_t)0ULL);
lean_inc_ref(v_desc_4001_);
v___x_4015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4013_, v___x_4014_, v_desc_4001_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___y_4018_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; uint8_t v___x_4031_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v___x_4015_, 1);
v___x_4022_ = lean_unsigned_to_nat(1u);
v___x_4023_ = lean_mk_empty_array_with_capacity(v___x_4022_);
v___x_4024_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_4025_ = lean_unsigned_to_nat(2u);
v___x_4026_ = lean_mk_empty_array_with_capacity(v___x_4025_);
v___x_4027_ = lean_array_push(v___x_4026_, v_a_4012_);
v___x_4028_ = lean_array_push(v___x_4027_, v___x_4024_);
v___x_4029_ = l_Lean_Doc_joinInlines(v___x_4028_);
lean_dec_ref(v___x_4028_);
v___x_4030_ = lean_array_get_size(v_desc_4001_);
lean_dec_ref(v_desc_4001_);
v___x_4031_ = lean_nat_dec_le(v___x_4030_, v___x_4022_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4032_ = lean_array_push(v___x_4023_, v___x_4029_);
v___x_4033_ = l_Array_append___redArg(v___x_4032_, v_a_4016_);
lean_dec(v_a_4016_);
v___x_4034_ = l_Lean_Doc_joinBlocks(v___x_4033_);
lean_dec_ref(v___x_4033_);
v___y_4018_ = v___x_4034_;
goto v___jp_4017_;
}
else
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
lean_dec_ref(v___x_4023_);
v___x_4035_ = l_Lean_Doc_joinBlocks(v_a_4016_);
lean_dec(v_a_4016_);
v___x_4036_ = l_Array_append___redArg(v___x_4029_, v___x_4035_);
lean_dec_ref(v___x_4035_);
v___y_4018_ = v___x_4036_;
goto v___jp_4017_;
}
v___jp_4017_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4019_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_4020_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_4021_ = l_Lean_Doc_prefixListLines(v___x_4019_, v___x_4020_, v___y_4018_);
lean_dec_ref(v___y_4018_);
v_a_4005_ = v___x_4021_;
goto v___jp_4004_;
}
}
else
{
lean_dec(v_a_4012_);
lean_dec_ref(v_bs_x27_4003_);
lean_dec_ref(v_desc_4001_);
return v___x_4015_;
}
}
else
{
lean_dec_ref(v_desc_4001_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4037_; 
v_a_4037_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4011_, 1);
v_a_4005_ = v_a_4037_;
goto v___jp_4004_;
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec_ref(v_bs_x27_4003_);
v_a_4038_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4011_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4011_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
v___jp_4004_:
{
size_t v___x_4006_; size_t v___x_4007_; lean_object* v___x_4008_; 
v___x_4006_ = ((size_t)1ULL);
v___x_4007_ = lean_usize_add(v_i_3990_, v___x_4006_);
v___x_4008_ = lean_array_uset(v_bs_x27_4003_, v_i_3990_, v_a_4005_);
v_i_3990_ = v___x_4007_;
v_bs_3991_ = v___x_4008_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed(lean_object* v_x_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_x_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
lean_dec(v_a_4049_);
lean_dec_ref(v_a_4048_);
lean_dec(v_a_4047_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed(lean_object* v_sz_4054_, lean_object* v___x_4055_, lean_object* v_content_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
size_t v_sz_boxed_4061_; size_t v___x_4734__boxed_4062_; lean_object* v_res_4063_; 
v_sz_boxed_4061_ = lean_unbox_usize(v_sz_4054_);
lean_dec(v_sz_4054_);
v___x_4734__boxed_4062_ = lean_unbox_usize(v___x_4055_);
lean_dec(v___x_4055_);
v_res_4063_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(v_sz_boxed_4061_, v___x_4734__boxed_4062_, v_content_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(lean_object* v_x_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_){
_start:
{
switch(lean_obj_tag(v_x_4064_))
{
case 0:
{
lean_object* v_contents_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4078_; 
v_contents_4069_ = lean_ctor_get(v_x_4064_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v_x_4064_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4071_ = v_x_4064_;
v_isShared_4072_ = v_isSharedCheck_4078_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_contents_4069_);
lean_dec(v_x_4064_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4078_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; lean_object* v___x_4075_; 
v___x_4073_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_4072_ == 0)
{
lean_ctor_set_tag(v___x_4071_, 9);
v___x_4075_ = v___x_4071_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_contents_4069_);
v___x_4075_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4076_; 
v___x_4076_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4073_, v___x_4075_, v_a_4065_, v_a_4066_, v_a_4067_);
return v___x_4076_;
}
}
}
case 1:
{
lean_object* v_content_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4087_; 
v_content_4079_ = lean_ctor_get(v_x_4064_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_x_4064_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4081_ = v_x_4064_;
v_isShared_4082_ = v_isSharedCheck_4087_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_content_4079_);
lean_dec(v_x_4064_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4087_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; lean_object* v___x_4085_; 
v___x_4083_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_4079_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set_tag(v___x_4081_, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4083_);
v___x_4085_ = v___x_4081_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4083_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
case 2:
{
lean_object* v_items_4088_; size_t v_sz_4089_; size_t v___x_4090_; lean_object* v___x_4091_; 
v_items_4088_ = lean_ctor_get(v_x_4064_, 0);
lean_inc_ref(v_items_4088_);
lean_dec_ref_known(v_x_4064_, 1);
v_sz_4089_ = lean_array_size(v_items_4088_);
v___x_4090_ = ((size_t)0ULL);
v___x_4091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_4089_, v___x_4090_, v_items_4088_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4100_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4094_ = v___x_4091_;
v_isShared_4095_ = v_isSharedCheck_4100_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4091_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4100_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4096_; lean_object* v___x_4098_; 
v___x_4096_ = l_Lean_Doc_joinBlocks(v_a_4092_);
lean_dec(v_a_4092_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 0, v___x_4096_);
v___x_4098_ = v___x_4094_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4096_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
v_a_4101_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4091_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4091_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
case 3:
{
lean_object* v_start_4109_; lean_object* v_items_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4144_; 
v_start_4109_ = lean_ctor_get(v_x_4064_, 0);
v_items_4110_ = lean_ctor_get(v_x_4064_, 1);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_x_4064_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4112_ = v_x_4064_;
v_isShared_4113_ = v_isSharedCheck_4144_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_items_4110_);
lean_inc(v_start_4109_);
lean_dec(v_x_4064_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4144_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v_out_4114_; lean_object* v___y_4116_; lean_object* v___x_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; 
v_out_4114_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_4141_ = lean_unsigned_to_nat(1u);
v___x_4142_ = l_Int_toNat(v_start_4109_);
lean_dec(v_start_4109_);
v___x_4143_ = lean_nat_dec_le(v___x_4141_, v___x_4142_);
if (v___x_4143_ == 0)
{
lean_dec(v___x_4142_);
v___y_4116_ = v___x_4141_;
goto v___jp_4115_;
}
else
{
v___y_4116_ = v___x_4142_;
goto v___jp_4115_;
}
v___jp_4115_:
{
lean_object* v___x_4118_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set_tag(v___x_4112_, 0);
lean_ctor_set(v___x_4112_, 1, v___y_4116_);
lean_ctor_set(v___x_4112_, 0, v_out_4114_);
v___x_4118_ = v___x_4112_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_out_4114_);
lean_ctor_set(v_reuseFailAlloc_4140_, 1, v___y_4116_);
v___x_4118_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
size_t v_sz_4119_; size_t v___x_4120_; lean_object* v___x_4121_; 
v_sz_4119_ = lean_array_size(v_items_4110_);
v___x_4120_ = ((size_t)0ULL);
v___x_4121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_items_4110_, v_sz_4119_, v___x_4120_, v___x_4118_, v_a_4065_, v_a_4066_, v_a_4067_);
lean_dec_ref(v_items_4110_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4131_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4124_ = v___x_4121_;
v_isShared_4125_ = v_isSharedCheck_4131_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4121_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4131_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v_fst_4126_; lean_object* v___x_4127_; lean_object* v___x_4129_; 
v_fst_4126_ = lean_ctor_get(v_a_4122_, 0);
lean_inc(v_fst_4126_);
lean_dec(v_a_4122_);
v___x_4127_ = l_Lean_Doc_joinBlocks(v_fst_4126_);
lean_dec(v_fst_4126_);
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 0, v___x_4127_);
v___x_4129_ = v___x_4124_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v___x_4127_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
v_a_4132_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4121_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4121_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_4145_; size_t v_sz_4146_; size_t v___x_4147_; lean_object* v___x_4148_; 
v_items_4145_ = lean_ctor_get(v_x_4064_, 0);
lean_inc_ref(v_items_4145_);
lean_dec_ref_known(v_x_4064_, 1);
v_sz_4146_ = lean_array_size(v_items_4145_);
v___x_4147_ = ((size_t)0ULL);
v___x_4148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_4146_, v___x_4147_, v_items_4145_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4157_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4151_ = v___x_4148_;
v_isShared_4152_ = v_isSharedCheck_4157_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4148_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4157_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4153_; lean_object* v___x_4155_; 
v___x_4153_ = l_Lean_Doc_joinBlocks(v_a_4149_);
lean_dec(v_a_4149_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4153_);
v___x_4155_ = v___x_4151_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4153_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
v_a_4158_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4148_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4148_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
case 5:
{
lean_object* v_items_4166_; size_t v_sz_4167_; size_t v___x_4168_; lean_object* v___x_4169_; 
v_items_4166_ = lean_ctor_get(v_x_4064_, 0);
lean_inc_ref(v_items_4166_);
lean_dec_ref_known(v_x_4064_, 1);
v_sz_4167_ = lean_array_size(v_items_4166_);
v___x_4168_ = ((size_t)0ULL);
v___x_4169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4167_, v___x_4168_, v_items_4166_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4180_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4172_ = v___x_4169_;
v_isShared_4173_ = v_isSharedCheck_4180_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4169_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4180_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4178_; 
v___x_4174_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_4175_ = l_Lean_Doc_joinBlocks(v_a_4170_);
lean_dec(v_a_4170_);
v___x_4176_ = l_Lean_Doc_prefixLines(v___x_4174_, v___x_4175_);
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 0, v___x_4176_);
v___x_4178_ = v___x_4172_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4176_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
v_a_4181_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4169_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4169_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
case 6:
{
lean_object* v_content_4189_; size_t v_sz_4190_; size_t v___x_4191_; lean_object* v___x_4192_; 
v_content_4189_ = lean_ctor_get(v_x_4064_, 0);
lean_inc_ref(v_content_4189_);
lean_dec_ref_known(v_x_4064_, 1);
v_sz_4190_ = lean_array_size(v_content_4189_);
v___x_4191_ = ((size_t)0ULL);
v___x_4192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4190_, v___x_4191_, v_content_4189_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4201_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4195_ = v___x_4192_;
v_isShared_4196_ = v_isSharedCheck_4201_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4192_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4201_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4197_; lean_object* v___x_4199_; 
v___x_4197_ = l_Lean_Doc_joinBlocks(v_a_4193_);
lean_dec(v_a_4193_);
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 0, v___x_4197_);
v___x_4199_ = v___x_4195_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4197_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
v_a_4202_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4192_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4192_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
default: 
{
lean_object* v_container_4210_; lean_object* v_content_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v_container_4210_ = lean_ctor_get(v_x_4064_, 0);
lean_inc(v_container_4210_);
v_content_4211_ = lean_ctor_get(v_x_4064_, 1);
lean_inc_ref(v_content_4211_);
lean_dec_ref_known(v_x_4064_, 2);
v___x_4212_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_container_4210_);
v___x_4213_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_4212_, v_a_4066_, v_a_4067_);
lean_dec(v___x_4212_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v_a_4214_; 
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_a_4214_);
lean_dec_ref_known(v___x_4213_, 1);
if (lean_obj_tag(v_a_4214_) == 0)
{
size_t v_sz_4215_; size_t v___x_4216_; lean_object* v___x_4217_; 
lean_dec(v_container_4210_);
v_sz_4215_ = lean_array_size(v_content_4211_);
v___x_4216_ = ((size_t)0ULL);
v___x_4217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4215_, v___x_4216_, v_content_4211_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4226_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4220_ = v___x_4217_;
v_isShared_4221_ = v_isSharedCheck_4226_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4217_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4226_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4222_; lean_object* v___x_4224_; 
v___x_4222_ = l_Lean_Doc_joinBlocks(v_a_4218_);
lean_dec(v_a_4218_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v___x_4222_);
v___x_4224_ = v___x_4220_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4222_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
v_a_4227_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4217_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4217_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
else
{
lean_object* v_val_4235_; lean_object* v___f_4236_; lean_object* v___f_4237_; size_t v_sz_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v_fallback_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
v_val_4235_ = lean_ctor_get(v_a_4214_, 0);
lean_inc(v_val_4235_);
lean_dec_ref_known(v_a_4214_, 1);
v___f_4236_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed), 5, 0);
v___f_4237_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___closed__0));
v_sz_4238_ = lean_array_size(v_content_4211_);
v___x_4239_ = lean_box_usize(v_sz_4238_);
v___x_4240_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
lean_inc_ref(v_content_4211_);
v_fallback_4241_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_fallback_4241_, 0, v___x_4239_);
lean_closure_set(v_fallback_4241_, 1, v___x_4240_);
lean_closure_set(v_fallback_4241_, 2, v_content_4211_);
v___x_4242_ = lean_apply_4(v_val_4235_, v___f_4237_, v___f_4236_, v_container_4210_, v_content_4211_);
v___x_4243_ = l_Lean_Doc_withRendererFallback(v_fallback_4241_, v___x_4242_, v_a_4065_, v_a_4066_, v_a_4067_);
return v___x_4243_;
}
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec_ref(v_content_4211_);
lean_dec(v_container_4210_);
v_a_4244_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4213_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4213_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(size_t v_sz_4252_, size_t v_i_4253_, lean_object* v_bs_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
uint8_t v___x_4259_; 
v___x_4259_ = lean_usize_dec_lt(v_i_4253_, v_sz_4252_);
if (v___x_4259_ == 0)
{
lean_object* v___x_4260_; 
v___x_4260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4260_, 0, v_bs_4254_);
return v___x_4260_;
}
else
{
lean_object* v_v_4261_; lean_object* v___x_4262_; 
v_v_4261_ = lean_array_uget_borrowed(v_bs_4254_, v_i_4253_);
lean_inc(v_v_4261_);
v___x_4262_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_v_4261_, v___y_4255_, v___y_4256_, v___y_4257_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4264_; lean_object* v_bs_x27_4265_; size_t v___x_4266_; size_t v___x_4267_; lean_object* v___x_4268_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
v___x_4264_ = lean_unsigned_to_nat(0u);
v_bs_x27_4265_ = lean_array_uset(v_bs_4254_, v_i_4253_, v___x_4264_);
v___x_4266_ = ((size_t)1ULL);
v___x_4267_ = lean_usize_add(v_i_4253_, v___x_4266_);
v___x_4268_ = lean_array_uset(v_bs_x27_4265_, v_i_4253_, v_a_4263_);
v_i_4253_ = v___x_4267_;
v_bs_4254_ = v___x_4268_;
goto _start;
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_dec_ref(v_bs_4254_);
v_a_4270_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4262_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4262_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(size_t v_sz_4278_, size_t v___x_4279_, lean_object* v_content_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
lean_object* v___x_4285_; 
v___x_4285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4278_, v___x_4279_, v_content_4280_, v___y_4281_, v___y_4282_, v___y_4283_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4294_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4288_ = v___x_4285_;
v_isShared_4289_ = v_isSharedCheck_4294_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4285_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4294_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4290_; lean_object* v___x_4292_; 
v___x_4290_ = l_Lean_Doc_joinBlocks(v_a_4286_);
lean_dec(v_a_4286_);
if (v_isShared_4289_ == 0)
{
lean_ctor_set(v___x_4288_, 0, v___x_4290_);
v___x_4292_ = v___x_4288_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4290_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
v_a_4295_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4285_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4285_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2___boxed(lean_object* v_sz_4303_, lean_object* v_i_4304_, lean_object* v_bs_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
size_t v_sz_boxed_4310_; size_t v_i_boxed_4311_; lean_object* v_res_4312_; 
v_sz_boxed_4310_ = lean_unbox_usize(v_sz_4303_);
lean_dec(v_sz_4303_);
v_i_boxed_4311_ = lean_unbox_usize(v_i_4304_);
lean_dec(v_i_4304_);
v_res_4312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_boxed_4310_, v_i_boxed_4311_, v_bs_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5___boxed(lean_object* v_sz_4313_, lean_object* v_i_4314_, lean_object* v_bs_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
size_t v_sz_boxed_4320_; size_t v_i_boxed_4321_; lean_object* v_res_4322_; 
v_sz_boxed_4320_ = lean_unbox_usize(v_sz_4313_);
lean_dec(v_sz_4313_);
v_i_boxed_4321_ = lean_unbox_usize(v_i_4314_);
lean_dec(v_i_4314_);
v_res_4322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_boxed_4320_, v_i_boxed_4321_, v_bs_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7___boxed(lean_object* v_as_4323_, lean_object* v_sz_4324_, lean_object* v_i_4325_, lean_object* v_b_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
size_t v_sz_boxed_4331_; size_t v_i_boxed_4332_; lean_object* v_res_4333_; 
v_sz_boxed_4331_ = lean_unbox_usize(v_sz_4324_);
lean_dec(v_sz_4324_);
v_i_boxed_4332_ = lean_unbox_usize(v_i_4325_);
lean_dec(v_i_4325_);
v_res_4333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_as_4323_, v_sz_boxed_4331_, v_i_boxed_4332_, v_b_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec(v___y_4327_);
lean_dec_ref(v_as_4323_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8___boxed(lean_object* v_sz_4334_, lean_object* v_i_4335_, lean_object* v_bs_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
size_t v_sz_boxed_4341_; size_t v_i_boxed_4342_; lean_object* v_res_4343_; 
v_sz_boxed_4341_ = lean_unbox_usize(v_sz_4334_);
lean_dec(v_sz_4334_);
v_i_boxed_4342_ = lean_unbox_usize(v_i_4335_);
lean_dec(v_i_4335_);
v_res_4343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_boxed_4341_, v_i_boxed_4342_, v_bs_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(size_t v_sz_4344_, size_t v_i_4345_, lean_object* v_bs_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
uint8_t v___x_4351_; 
v___x_4351_ = lean_usize_dec_lt(v_i_4345_, v_sz_4344_);
if (v___x_4351_ == 0)
{
lean_object* v___x_4352_; 
v___x_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4352_, 0, v_bs_4346_);
return v___x_4352_;
}
else
{
lean_object* v_v_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v_v_4353_ = lean_array_uget_borrowed(v_bs_4346_, v_i_4345_);
v___x_4354_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc(v_v_4353_);
v___x_4355_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4354_, v_v_4353_, v___y_4347_, v___y_4348_, v___y_4349_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4357_; lean_object* v_bs_x27_4358_; size_t v___x_4359_; size_t v___x_4360_; lean_object* v___x_4361_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
v___x_4357_ = lean_unsigned_to_nat(0u);
v_bs_x27_4358_ = lean_array_uset(v_bs_4346_, v_i_4345_, v___x_4357_);
v___x_4359_ = ((size_t)1ULL);
v___x_4360_ = lean_usize_add(v_i_4345_, v___x_4359_);
v___x_4361_ = lean_array_uset(v_bs_x27_4358_, v_i_4345_, v_a_4356_);
v_i_4345_ = v___x_4360_;
v_bs_4346_ = v___x_4361_;
goto _start;
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec_ref(v_bs_4346_);
v_a_4363_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4355_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4355_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1___boxed(lean_object* v_sz_4371_, lean_object* v_i_4372_, lean_object* v_bs_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
size_t v_sz_boxed_4378_; size_t v_i_boxed_4379_; lean_object* v_res_4380_; 
v_sz_boxed_4378_ = lean_unbox_usize(v_sz_4371_);
lean_dec(v_sz_4371_);
v_i_boxed_4379_ = lean_unbox_usize(v_i_4372_);
lean_dec(v_i_4372_);
v_res_4380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_boxed_4378_, v_i_boxed_4379_, v_bs_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(lean_object* v_x_4381_, lean_object* v_x_4382_){
_start:
{
lean_object* v_zero_4383_; uint8_t v_isZero_4384_; 
v_zero_4383_ = lean_unsigned_to_nat(0u);
v_isZero_4384_ = lean_nat_dec_eq(v_x_4381_, v_zero_4383_);
if (v_isZero_4384_ == 1)
{
lean_dec(v_x_4381_);
return v_x_4382_;
}
else
{
uint32_t v___x_4385_; lean_object* v_one_4386_; lean_object* v_n_4387_; lean_object* v___x_4388_; 
v___x_4385_ = 35;
v_one_4386_ = lean_unsigned_to_nat(1u);
v_n_4387_ = lean_nat_sub(v_x_4381_, v_one_4386_);
lean_dec(v_x_4381_);
v___x_4388_ = lean_string_push(v_x_4382_, v___x_4385_);
v_x_4381_ = v_n_4387_;
v_x_4382_ = v___x_4388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(lean_object* v_level_4390_, lean_object* v_part_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
lean_object* v_title_4396_; lean_object* v_content_4397_; lean_object* v_subParts_4398_; size_t v_sz_4399_; size_t v___x_4400_; lean_object* v___x_4401_; 
v_title_4396_ = lean_ctor_get(v_part_4391_, 0);
lean_inc_ref(v_title_4396_);
v_content_4397_ = lean_ctor_get(v_part_4391_, 3);
lean_inc_ref(v_content_4397_);
v_subParts_4398_ = lean_ctor_get(v_part_4391_, 4);
lean_inc_ref(v_subParts_4398_);
lean_dec_ref(v_part_4391_);
v_sz_4399_ = lean_array_size(v_title_4396_);
v___x_4400_ = ((size_t)0ULL);
v___x_4401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_4399_, v___x_4400_, v_title_4396_, v_a_4392_, v_a_4393_, v_a_4394_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; size_t v_sz_4403_; lean_object* v___x_4404_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
v_sz_4403_ = lean_array_size(v_content_4397_);
v___x_4404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4403_, v___x_4400_, v_content_4397_, v_a_4392_, v_a_4393_, v_a_4394_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_a_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; size_t v_sz_4410_; lean_object* v___x_4411_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4405_);
lean_dec_ref_known(v___x_4404_, 1);
v___x_4406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4407_ = lean_unsigned_to_nat(1u);
v___x_4408_ = lean_nat_add(v_level_4390_, v___x_4407_);
lean_inc(v___x_4408_);
v___x_4409_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(v___x_4408_, v___x_4406_);
v_sz_4410_ = lean_array_size(v_subParts_4398_);
v___x_4411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4408_, v_sz_4410_, v___x_4400_, v_subParts_4398_, v_a_4392_, v_a_4393_, v_a_4394_);
lean_dec(v___x_4408_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4430_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4414_ = v___x_4411_;
v_isShared_4415_ = v_isSharedCheck_4430_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4411_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4430_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4428_; 
v___x_4416_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_4417_ = lean_string_append(v___x_4409_, v___x_4416_);
v___x_4418_ = lean_mk_empty_array_with_capacity(v___x_4407_);
lean_inc_ref_n(v___x_4418_, 2);
v___x_4419_ = lean_array_push(v___x_4418_, v___x_4417_);
v___x_4420_ = lean_array_push(v___x_4418_, v___x_4419_);
v___x_4421_ = l_Array_append___redArg(v___x_4420_, v_a_4402_);
lean_dec(v_a_4402_);
v___x_4422_ = l_Lean_Doc_joinInlines(v___x_4421_);
lean_dec_ref(v___x_4421_);
v___x_4423_ = lean_array_push(v___x_4418_, v___x_4422_);
v___x_4424_ = l_Array_append___redArg(v___x_4423_, v_a_4405_);
lean_dec(v_a_4405_);
v___x_4425_ = l_Array_append___redArg(v___x_4424_, v_a_4412_);
lean_dec(v_a_4412_);
v___x_4426_ = l_Lean_Doc_joinBlocks(v___x_4425_);
lean_dec_ref(v___x_4425_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 0, v___x_4426_);
v___x_4428_ = v___x_4414_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4426_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_dec_ref(v___x_4409_);
lean_dec(v_a_4405_);
lean_dec(v_a_4402_);
v_a_4431_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4411_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4411_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
lean_dec(v_a_4402_);
lean_dec_ref(v_subParts_4398_);
v_a_4439_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___x_4404_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4404_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
if (v_isShared_4442_ == 0)
{
v___x_4444_ = v___x_4441_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_a_4439_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec_ref(v_subParts_4398_);
lean_dec_ref(v_content_4397_);
v_a_4447_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4401_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4401_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(lean_object* v___x_4455_, size_t v_sz_4456_, size_t v_i_4457_, lean_object* v_bs_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
uint8_t v___x_4463_; 
v___x_4463_ = lean_usize_dec_lt(v_i_4457_, v_sz_4456_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; 
v___x_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4464_, 0, v_bs_4458_);
return v___x_4464_;
}
else
{
lean_object* v_v_4465_; lean_object* v___x_4466_; 
v_v_4465_ = lean_array_uget_borrowed(v_bs_4458_, v_i_4457_);
lean_inc(v_v_4465_);
v___x_4466_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4455_, v_v_4465_, v___y_4459_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; lean_object* v___x_4468_; lean_object* v_bs_x27_4469_; size_t v___x_4470_; size_t v___x_4471_; lean_object* v___x_4472_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_a_4467_);
lean_dec_ref_known(v___x_4466_, 1);
v___x_4468_ = lean_unsigned_to_nat(0u);
v_bs_x27_4469_ = lean_array_uset(v_bs_4458_, v_i_4457_, v___x_4468_);
v___x_4470_ = ((size_t)1ULL);
v___x_4471_ = lean_usize_add(v_i_4457_, v___x_4470_);
v___x_4472_ = lean_array_uset(v_bs_x27_4469_, v_i_4457_, v_a_4467_);
v_i_4457_ = v___x_4471_;
v_bs_4458_ = v___x_4472_;
goto _start;
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
lean_dec_ref(v_bs_4458_);
v_a_4474_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4466_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4466_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg___boxed(lean_object* v___x_4482_, lean_object* v_sz_4483_, lean_object* v_i_4484_, lean_object* v_bs_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
size_t v_sz_boxed_4490_; size_t v_i_boxed_4491_; lean_object* v_res_4492_; 
v_sz_boxed_4490_ = lean_unbox_usize(v_sz_4483_);
lean_dec(v_sz_4483_);
v_i_boxed_4491_ = lean_unbox_usize(v_i_4484_);
lean_dec(v_i_4484_);
v_res_4492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4482_, v_sz_boxed_4490_, v_i_boxed_4491_, v_bs_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec(v___x_4482_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg___boxed(lean_object* v_level_4493_, lean_object* v_part_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_){
_start:
{
lean_object* v_res_4499_; 
v_res_4499_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4493_, v_part_4494_, v_a_4495_, v_a_4496_, v_a_4497_);
lean_dec(v_a_4497_);
lean_dec_ref(v_a_4496_);
lean_dec(v_a_4495_);
lean_dec(v_level_4493_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(size_t v_sz_4500_, size_t v_i_4501_, lean_object* v_bs_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
uint8_t v___x_4507_; 
v___x_4507_ = lean_usize_dec_lt(v_i_4501_, v_sz_4500_);
if (v___x_4507_ == 0)
{
lean_object* v___x_4508_; 
v___x_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4508_, 0, v_bs_4502_);
return v___x_4508_;
}
else
{
lean_object* v_v_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v_v_4509_ = lean_array_uget_borrowed(v_bs_4502_, v_i_4501_);
v___x_4510_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_4509_);
v___x_4511_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4510_, v_v_4509_, v___y_4503_, v___y_4504_, v___y_4505_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; lean_object* v_bs_x27_4513_; size_t v___x_4514_; size_t v___x_4515_; lean_object* v___x_4516_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4512_);
lean_dec_ref_known(v___x_4511_, 1);
v_bs_x27_4513_ = lean_array_uset(v_bs_4502_, v_i_4501_, v___x_4510_);
v___x_4514_ = ((size_t)1ULL);
v___x_4515_ = lean_usize_add(v_i_4501_, v___x_4514_);
v___x_4516_ = lean_array_uset(v_bs_x27_4513_, v_i_4501_, v_a_4512_);
v_i_4501_ = v___x_4515_;
v_bs_4502_ = v___x_4516_;
goto _start;
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4525_; 
lean_dec_ref(v_bs_4502_);
v_a_4518_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4520_ = v___x_4511_;
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4511_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4523_; 
if (v_isShared_4521_ == 0)
{
v___x_4523_ = v___x_4520_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_a_4518_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3___boxed(lean_object* v_sz_4526_, lean_object* v_i_4527_, lean_object* v_bs_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
size_t v_sz_boxed_4533_; size_t v_i_boxed_4534_; lean_object* v_res_4535_; 
v_sz_boxed_4533_ = lean_unbox_usize(v_sz_4526_);
lean_dec(v_sz_4526_);
v_i_boxed_4534_ = lean_unbox_usize(v_i_4527_);
lean_dec(v_i_4527_);
v_res_4535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_boxed_4533_, v_i_boxed_4534_, v_bs_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0(lean_object* v_val_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v_text_4541_; lean_object* v_subsections_4542_; size_t v_sz_4543_; size_t v___x_4544_; lean_object* v___x_4545_; 
v_text_4541_ = lean_ctor_get(v_val_4536_, 0);
lean_inc_ref(v_text_4541_);
v_subsections_4542_ = lean_ctor_get(v_val_4536_, 1);
lean_inc_ref(v_subsections_4542_);
lean_dec_ref(v_val_4536_);
v_sz_4543_ = lean_array_size(v_text_4541_);
v___x_4544_ = ((size_t)0ULL);
v___x_4545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4543_, v___x_4544_, v_text_4541_, v___y_4537_, v___y_4538_, v___y_4539_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_object* v_a_4546_; size_t v_sz_4547_; lean_object* v___x_4548_; 
v_a_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc(v_a_4546_);
lean_dec_ref_known(v___x_4545_, 1);
v_sz_4547_ = lean_array_size(v_subsections_4542_);
v___x_4548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_4547_, v___x_4544_, v_subsections_4542_, v___y_4537_, v___y_4538_, v___y_4539_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4558_; 
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4551_ = v___x_4548_;
v_isShared_4552_ = v_isSharedCheck_4558_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4558_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4556_; 
v___x_4553_ = l_Array_append___redArg(v_a_4546_, v_a_4549_);
lean_dec(v_a_4549_);
v___x_4554_ = l_Lean_Doc_joinBlocks(v___x_4553_);
lean_dec_ref(v___x_4553_);
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v___x_4554_);
v___x_4556_ = v___x_4551_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
else
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4566_; 
lean_dec(v_a_4546_);
v_a_4559_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4561_ = v___x_4548_;
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4548_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4559_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
else
{
lean_object* v_a_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4574_; 
lean_dec_ref(v_subsections_4542_);
v_a_4567_ = lean_ctor_get(v___x_4545_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4569_ = v___x_4545_;
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_a_4567_);
lean_dec(v___x_4545_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4572_; 
if (v_isShared_4570_ == 0)
{
v___x_4572_ = v___x_4569_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v_a_4567_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0___boxed(lean_object* v_val_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Lean_findSimpleDocString_x3f___lam__0(v_val_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_4581_, lean_object* v_declName_4582_, uint8_t v_includeBuiltin_4583_, lean_object* v_options_4584_, lean_object* v_currNamespace_4585_, lean_object* v_openDecls_4586_, lean_object* v_cancelTk_x3f_4587_){
_start:
{
lean_object* v___x_4589_; 
lean_inc_ref(v_env_4581_);
v___x_4589_ = l_Lean_findInternalDocString_x3f(v_env_4581_, v_declName_4582_, v_includeBuiltin_4583_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4633_; 
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4592_ = v___x_4589_;
v_isShared_4593_ = v_isSharedCheck_4633_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4589_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4633_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
if (lean_obj_tag(v_a_4590_) == 0)
{
lean_object* v___x_4594_; lean_object* v___x_4596_; 
lean_dec(v_cancelTk_x3f_4587_);
lean_dec(v_openDecls_4586_);
lean_dec(v_currNamespace_4585_);
lean_dec_ref(v_options_4584_);
lean_dec_ref(v_env_4581_);
v___x_4594_ = lean_box(0);
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 0, v___x_4594_);
v___x_4596_ = v___x_4592_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4594_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
else
{
lean_object* v_val_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4632_; 
v_val_4598_ = lean_ctor_get(v_a_4590_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v_a_4590_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4600_ = v_a_4590_;
v_isShared_4601_ = v_isSharedCheck_4632_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_val_4598_);
lean_dec(v_a_4590_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4632_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
if (lean_obj_tag(v_val_4598_) == 0)
{
lean_object* v_val_4602_; lean_object* v___x_4604_; 
lean_dec(v_cancelTk_x3f_4587_);
lean_dec(v_openDecls_4586_);
lean_dec(v_currNamespace_4585_);
lean_dec_ref(v_options_4584_);
lean_dec_ref(v_env_4581_);
v_val_4602_ = lean_ctor_get(v_val_4598_, 0);
lean_inc(v_val_4602_);
lean_dec_ref_known(v_val_4598_, 1);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v_val_4602_);
v___x_4604_ = v___x_4600_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_val_4602_);
v___x_4604_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
lean_object* v___x_4606_; 
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 0, v___x_4604_);
v___x_4606_ = v___x_4592_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4604_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
else
{
lean_object* v_val_4609_; lean_object* v___f_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
lean_del_object(v___x_4592_);
v_val_4609_ = lean_ctor_get(v_val_4598_, 0);
lean_inc(v_val_4609_);
lean_dec_ref_known(v_val_4598_, 1);
v___f_4610_ = lean_alloc_closure((void*)(l_Lean_findSimpleDocString_x3f___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4610_, 0, v_val_4609_);
v___x_4611_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_4611_, 0, v___f_4610_);
v___x_4612_ = l_Lean_Doc_runMarkdown___redArg(v_env_4581_, v___x_4611_, v_options_4584_, v_currNamespace_4585_, v_openDecls_4586_, v_cancelTk_x3f_4587_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4623_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4615_ = v___x_4612_;
v_isShared_4616_ = v_isSharedCheck_4623_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4612_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4623_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v_a_4613_);
v___x_4618_ = v___x_4600_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4620_; 
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v___x_4618_);
v___x_4620_ = v___x_4615_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4618_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
lean_del_object(v___x_4600_);
v_a_4624_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4612_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4612_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
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
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4641_; 
lean_dec(v_cancelTk_x3f_4587_);
lean_dec(v_openDecls_4586_);
lean_dec(v_currNamespace_4585_);
lean_dec_ref(v_options_4584_);
lean_dec_ref(v_env_4581_);
v_a_4634_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4636_ = v___x_4589_;
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4589_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4639_; 
if (v_isShared_4637_ == 0)
{
v___x_4639_ = v___x_4636_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4634_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
return v___x_4639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_4642_, lean_object* v_declName_4643_, lean_object* v_includeBuiltin_4644_, lean_object* v_options_4645_, lean_object* v_currNamespace_4646_, lean_object* v_openDecls_4647_, lean_object* v_cancelTk_x3f_4648_, lean_object* v_a_4649_){
_start:
{
uint8_t v_includeBuiltin_boxed_4650_; lean_object* v_res_4651_; 
v_includeBuiltin_boxed_4650_ = lean_unbox(v_includeBuiltin_4644_);
v_res_4651_ = l_Lean_findSimpleDocString_x3f(v_env_4642_, v_declName_4643_, v_includeBuiltin_boxed_4650_, v_options_4645_, v_currNamespace_4646_, v_openDecls_4647_, v_cancelTk_x3f_4648_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(lean_object* v_p_4652_, lean_object* v_level_4653_, lean_object* v_part_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4653_, v_part_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___boxed(lean_object* v_p_4660_, lean_object* v_level_4661_, lean_object* v_part_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(v_p_4660_, v_level_4661_, v_part_4662_, v_a_4663_, v_a_4664_, v_a_4665_);
lean_dec(v_a_4665_);
lean_dec_ref(v_a_4664_);
lean_dec(v_a_4663_);
lean_dec(v_level_4661_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(lean_object* v_p_4668_, lean_object* v___x_4669_, size_t v_sz_4670_, size_t v_i_4671_, lean_object* v_bs_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v___x_4677_; 
v___x_4677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4669_, v_sz_4670_, v_i_4671_, v_bs_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
return v___x_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___boxed(lean_object* v_p_4678_, lean_object* v___x_4679_, lean_object* v_sz_4680_, lean_object* v_i_4681_, lean_object* v_bs_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
size_t v_sz_boxed_4687_; size_t v_i_boxed_4688_; lean_object* v_res_4689_; 
v_sz_boxed_4687_ = lean_unbox_usize(v_sz_4680_);
lean_dec(v_sz_4680_);
v_i_boxed_4688_ = lean_unbox_usize(v_i_4681_);
lean_dec(v_i_4681_);
v_res_4689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(v_p_4678_, v___x_4679_, v_sz_boxed_4687_, v_i_boxed_4688_, v_bs_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec(v___x_4679_);
return v_res_4689_;
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
