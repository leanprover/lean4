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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v_content_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v___x_1212_);
v_content_1219_ = lean_ctor_get(v_x_1183_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_x_1183_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1221_ = v_x_1183_;
v_isShared_1222_ = v_isSharedCheck_1274_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_content_1219_);
lean_dec(v_x_1183_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1274_;
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
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_content_1219_);
v___x_1224_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; lean_object* v_snd_1226_; lean_object* v_fst_1227_; lean_object* v_fst_1228_; lean_object* v_snd_1229_; lean_object* v_pieces_1231_; uint8_t v_inEmph_1240_; uint8_t v_inBold_1241_; uint8_t v_inLink_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1272_; 
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
v_inEmph_1240_ = lean_ctor_get_uint8(v_x_1182_, 0);
v_inBold_1241_ = lean_ctor_get_uint8(v_x_1182_, 1);
v_inLink_1242_ = lean_ctor_get_uint8(v_x_1182_, 2);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1244_ = v_x_1182_;
v_isShared_1245_ = v_isSharedCheck_1272_;
goto v_resetjp_1243_;
}
else
{
lean_dec(v_x_1182_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1272_;
goto v_resetjp_1243_;
}
v___jp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; uint8_t v___x_1235_; 
v___x_1232_ = lean_string_utf8_byte_size(v_snd_1229_);
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = lean_nat_dec_eq(v___x_1232_, v___x_1233_);
v___x_1235_ = lean_bool_not(v___x_1234_);
if (v___x_1235_ == 0)
{
lean_dec(v_snd_1229_);
v_pieces_1193_ = v_pieces_1231_;
goto v___jp_1192_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1236_ = lean_unsigned_to_nat(1u);
v___x_1237_ = lean_mk_empty_array_with_capacity(v___x_1236_);
v___x_1238_ = lean_array_push(v___x_1237_, v_snd_1229_);
v___x_1239_ = lean_array_push(v_pieces_1231_, v___x_1238_);
v_pieces_1193_ = v___x_1239_;
goto v___jp_1192_;
}
}
v_resetjp_1243_:
{
uint8_t v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = 1;
if (v_isShared_1245_ == 0)
{
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, 1, v_inBold_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, 2, v_inLink_1242_);
v___x_1248_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; 
lean_ctor_set_uint8(v___x_1248_, 0, v___x_1246_);
v___x_1249_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1181_, v___x_1248_, v_fst_1228_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v_pieces_1252_; lean_object* v_pieces_1258_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; uint8_t v___x_1266_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1264_ = lean_string_utf8_byte_size(v_fst_1227_);
v___x_1265_ = lean_nat_dec_eq(v___x_1264_, v___x_1262_);
v___x_1266_ = lean_bool_not(v___x_1265_);
if (v___x_1266_ == 0)
{
lean_dec(v_fst_1227_);
v_pieces_1258_ = v___x_1263_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = lean_mk_empty_array_with_capacity(v___x_1267_);
v___x_1269_ = lean_array_push(v___x_1268_, v_fst_1227_);
v___x_1270_ = lean_array_push(v___x_1263_, v___x_1269_);
v_pieces_1258_ = v___x_1270_;
goto v___jp_1257_;
}
v___jp_1251_:
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = lean_array_push(v_pieces_1252_, v_a_1250_);
v___x_1254_ = lean_bool_not(v_inEmph_1240_);
if (v___x_1254_ == 0)
{
v_pieces_1231_ = v___x_1253_;
goto v___jp_1230_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1256_ = lean_array_push(v___x_1253_, v___x_1255_);
v_pieces_1231_ = v___x_1256_;
goto v___jp_1230_;
}
}
v___jp_1257_:
{
uint8_t v___x_1259_; 
v___x_1259_ = lean_bool_not(v_inEmph_1240_);
if (v___x_1259_ == 0)
{
v_pieces_1252_ = v_pieces_1258_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1261_ = lean_array_push(v_pieces_1258_, v___x_1260_);
v_pieces_1252_ = v___x_1261_;
goto v___jp_1251_;
}
}
}
else
{
lean_dec(v_snd_1229_);
lean_dec(v_fst_1227_);
return v___x_1249_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1330_; 
lean_dec_ref(v___x_1212_);
v_content_1275_ = lean_ctor_get(v_x_1183_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_x_1183_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1277_ = v_x_1183_;
v_isShared_1278_ = v_isSharedCheck_1330_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_content_1275_);
lean_dec(v_x_1183_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1330_;
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
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_content_1275_);
v___x_1280_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v_snd_1282_; lean_object* v_fst_1283_; lean_object* v_fst_1284_; lean_object* v_snd_1285_; lean_object* v_pieces_1287_; uint8_t v_inEmph_1296_; uint8_t v_inBold_1297_; uint8_t v_inLink_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1328_; 
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
v_inEmph_1296_ = lean_ctor_get_uint8(v_x_1182_, 0);
v_inBold_1297_ = lean_ctor_get_uint8(v_x_1182_, 1);
v_inLink_1298_ = lean_ctor_get_uint8(v_x_1182_, 2);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1300_ = v_x_1182_;
v_isShared_1301_ = v_isSharedCheck_1328_;
goto v_resetjp_1299_;
}
else
{
lean_dec(v_x_1182_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1328_;
goto v_resetjp_1299_;
}
v___jp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; uint8_t v___x_1291_; 
v___x_1288_ = lean_string_utf8_byte_size(v_snd_1285_);
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = lean_nat_dec_eq(v___x_1288_, v___x_1289_);
v___x_1291_ = lean_bool_not(v___x_1290_);
if (v___x_1291_ == 0)
{
lean_dec(v_snd_1285_);
v_pieces_1189_ = v_pieces_1287_;
goto v___jp_1188_;
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1292_ = lean_unsigned_to_nat(1u);
v___x_1293_ = lean_mk_empty_array_with_capacity(v___x_1292_);
v___x_1294_ = lean_array_push(v___x_1293_, v_snd_1285_);
v___x_1295_ = lean_array_push(v_pieces_1287_, v___x_1294_);
v_pieces_1189_ = v___x_1295_;
goto v___jp_1188_;
}
}
v_resetjp_1299_:
{
uint8_t v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = 1;
if (v_isShared_1301_ == 0)
{
v___x_1304_ = v___x_1300_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, 0, v_inEmph_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, 2, v_inLink_1298_);
v___x_1304_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; 
lean_ctor_set_uint8(v___x_1304_, 1, v___x_1302_);
v___x_1305_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1181_, v___x_1304_, v_fst_1284_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v_pieces_1308_; lean_object* v_pieces_1314_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; uint8_t v___x_1322_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1320_ = lean_string_utf8_byte_size(v_fst_1283_);
v___x_1321_ = lean_nat_dec_eq(v___x_1320_, v___x_1318_);
v___x_1322_ = lean_bool_not(v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec(v_fst_1283_);
v_pieces_1314_ = v___x_1319_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = lean_mk_empty_array_with_capacity(v___x_1323_);
v___x_1325_ = lean_array_push(v___x_1324_, v_fst_1283_);
v___x_1326_ = lean_array_push(v___x_1319_, v___x_1325_);
v_pieces_1314_ = v___x_1326_;
goto v___jp_1313_;
}
v___jp_1307_:
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = lean_array_push(v_pieces_1308_, v_a_1306_);
v___x_1310_ = lean_bool_not(v_inBold_1297_);
if (v___x_1310_ == 0)
{
v_pieces_1287_ = v___x_1309_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1312_ = lean_array_push(v___x_1309_, v___x_1311_);
v_pieces_1287_ = v___x_1312_;
goto v___jp_1286_;
}
}
v___jp_1313_:
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_bool_not(v_inBold_1297_);
if (v___x_1315_ == 0)
{
v_pieces_1308_ = v_pieces_1314_;
goto v___jp_1307_;
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1317_ = lean_array_push(v_pieces_1314_, v___x_1316_);
v_pieces_1308_ = v___x_1317_;
goto v___jp_1307_;
}
}
}
else
{
lean_dec(v_snd_1285_);
lean_dec(v_fst_1283_);
return v___x_1305_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec_ref(v___x_1212_);
lean_dec_ref(v_x_1182_);
lean_dec_ref(v_inst_1181_);
v_string_1331_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_string_1331_);
lean_dec_ref_known(v_x_1183_, 1);
v___x_1332_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1331_);
v___x_1333_ = lean_unsigned_to_nat(1u);
v___x_1334_ = lean_mk_empty_array_with_capacity(v___x_1333_);
v___x_1335_ = lean_array_push(v___x_1334_, v___x_1332_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
return v___x_1336_;
}
case 4:
{
uint8_t v_mode_1337_; 
lean_dec_ref(v___x_1212_);
lean_dec_ref(v_x_1182_);
lean_dec_ref(v_inst_1181_);
v_mode_1337_ = lean_ctor_get_uint8(v_x_1183_, sizeof(void*)*1);
if (v_mode_1337_ == 0)
{
lean_object* v_string_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_string_1338_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_string_1338_);
lean_dec_ref_known(v_x_1183_, 1);
v___x_1339_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
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
else
{
lean_object* v_string_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_string_1346_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_string_1346_);
lean_dec_ref_known(v_x_1183_, 1);
v___x_1347_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_1348_ = lean_string_append(v___x_1347_, v_string_1346_);
lean_dec_ref(v_string_1346_);
v___x_1349_ = lean_string_append(v___x_1348_, v___x_1347_);
v___x_1350_ = lean_unsigned_to_nat(1u);
v___x_1351_ = lean_mk_empty_array_with_capacity(v___x_1350_);
v___x_1352_ = lean_array_push(v___x_1351_, v___x_1349_);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
}
case 5:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec_ref_known(v_x_1183_, 1);
lean_dec_ref(v___x_1212_);
lean_dec_ref(v_x_1182_);
lean_dec_ref(v_inst_1181_);
v___x_1354_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
case 6:
{
uint8_t v_inLink_1356_; 
v_inLink_1356_ = lean_ctor_get_uint8(v_x_1182_, 2);
if (v_inLink_1356_ == 0)
{
lean_object* v_content_1357_; lean_object* v_url_1358_; uint8_t v_inEmph_1359_; uint8_t v_inBold_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref(v___x_1212_);
v_content_1357_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_content_1357_);
v_url_1358_ = lean_ctor_get(v_x_1183_, 1);
lean_inc_ref(v_url_1358_);
lean_dec_ref_known(v_x_1183_, 2);
v_inEmph_1359_ = lean_ctor_get_uint8(v_x_1182_, 0);
v_inBold_1360_ = lean_ctor_get_uint8(v_x_1182_, 1);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1362_ = v_x_1182_;
v_isShared_1363_ = v_isSharedCheck_1389_;
goto v_resetjp_1361_;
}
else
{
lean_dec(v_x_1182_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1389_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
uint8_t v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = 1;
if (v_isShared_1363_ == 0)
{
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1388_, 0, v_inEmph_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1388_, 1, v_inBold_1360_);
v___x_1366_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_ctor_set_uint8(v___x_1366_, 2, v___x_1364_);
v___x_1367_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_content_1357_);
v___x_1368_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1181_, v___x_1366_, v___x_1367_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1387_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1387_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1387_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_mk_empty_array_with_capacity(v___x_1373_);
v___x_1375_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1376_ = lean_string_append(v___x_1375_, v_url_1358_);
lean_dec_ref(v_url_1358_);
v___x_1377_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1378_ = lean_string_append(v___x_1376_, v___x_1377_);
v___x_1379_ = lean_array_push(v___x_1374_, v___x_1378_);
v___x_1380_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_1381_ = lean_array_push(v___x_1380_, v_a_1369_);
v___x_1382_ = lean_array_push(v___x_1381_, v___x_1379_);
v___x_1383_ = l_Lean_Doc_joinInlines(v___x_1382_);
lean_dec_ref(v___x_1382_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1383_);
v___x_1385_ = v___x_1371_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
else
{
lean_dec_ref(v_url_1358_);
return v___x_1368_;
}
}
}
}
else
{
lean_object* v_content_1390_; lean_object* v___x_1391_; size_t v_sz_1392_; size_t v___x_1393_; lean_object* v___x_4547__overap_1394_; lean_object* v___x_1395_; 
v_content_1390_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_content_1390_);
lean_dec_ref_known(v_x_1183_, 2);
v___x_1391_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1391_, 0, v_inst_1181_);
lean_closure_set(v___x_1391_, 1, v_x_1182_);
v_sz_1392_ = lean_array_size(v_content_1390_);
v___x_1393_ = ((size_t)0ULL);
v___x_4547__overap_1394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1212_, v___x_1391_, v_sz_1392_, v___x_1393_, v_content_1390_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
v___x_1395_ = lean_apply_4(v___x_4547__overap_1394_, v_a_1184_, v_a_1185_, v_a_1186_, lean_box(0));
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1404_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = l_Lean_Doc_joinInlines(v_a_1396_);
lean_dec(v_a_1396_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1395_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1395_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
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
}
case 7:
{
lean_object* v_name_1413_; lean_object* v_content_1414_; lean_object* v___x_1415_; size_t v_sz_1416_; size_t v___x_1417_; lean_object* v___x_4550__overap_1418_; lean_object* v___x_1419_; 
v_name_1413_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_name_1413_);
v_content_1414_ = lean_ctor_get(v_x_1183_, 1);
lean_inc_ref(v_content_1414_);
lean_dec_ref_known(v_x_1183_, 2);
v___x_1415_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1415_, 0, v_inst_1181_);
lean_closure_set(v___x_1415_, 1, v_x_1182_);
v_sz_1416_ = lean_array_size(v_content_1414_);
v___x_1417_ = ((size_t)0ULL);
v___x_4550__overap_1418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1212_, v___x_1415_, v_sz_1416_, v___x_1417_, v_content_1414_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
v___x_1419_ = lean_apply_4(v___x_4550__overap_1418_, v_a_1184_, v_a_1185_, v_a_1186_, lean_box(0));
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1421_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_1422_ = l_Lean_Doc_joinInlines(v_a_1420_);
lean_dec(v_a_1420_);
v___x_1423_ = lean_array_to_list(v___x_1422_);
v___x_1424_ = l_String_intercalate(v___x_1421_, v___x_1423_);
lean_inc_ref(v_name_1413_);
v___x_1425_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_1413_, v___x_1424_, v_a_1184_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1439_; 
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v___x_1425_, 0);
lean_dec(v_unused_1440_);
v___x_1427_ = v___x_1425_;
v_isShared_1428_ = v_isSharedCheck_1439_;
goto v_resetjp_1426_;
}
else
{
lean_dec(v___x_1425_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1439_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1429_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_1430_ = lean_string_append(v___x_1429_, v_name_1413_);
lean_dec_ref(v_name_1413_);
v___x_1431_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_1432_ = lean_string_append(v___x_1430_, v___x_1431_);
v___x_1433_ = lean_unsigned_to_nat(1u);
v___x_1434_ = lean_mk_empty_array_with_capacity(v___x_1433_);
v___x_1435_ = lean_array_push(v___x_1434_, v___x_1432_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1435_);
v___x_1437_ = v___x_1427_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec_ref(v_name_1413_);
v_a_1441_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1425_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1425_);
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
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref(v_name_1413_);
v_a_1449_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1419_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1419_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
case 8:
{
lean_object* v_alt_1457_; lean_object* v_url_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec_ref(v___x_1212_);
lean_dec_ref(v_x_1182_);
lean_dec_ref(v_inst_1181_);
v_alt_1457_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_alt_1457_);
v_url_1458_ = lean_ctor_get(v_x_1183_, 1);
lean_inc_ref(v_url_1458_);
lean_dec_ref_known(v_x_1183_, 2);
v___x_1459_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_1460_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1457_);
lean_dec_ref(v_alt_1457_);
v___x_1461_ = lean_string_append(v___x_1459_, v___x_1460_);
lean_dec_ref(v___x_1460_);
v___x_1462_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1463_ = lean_string_append(v___x_1461_, v___x_1462_);
v___x_1464_ = lean_string_append(v___x_1463_, v_url_1458_);
lean_dec_ref(v_url_1458_);
v___x_1465_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1466_ = lean_string_append(v___x_1464_, v___x_1465_);
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_mk_empty_array_with_capacity(v___x_1467_);
v___x_1469_ = lean_array_push(v___x_1468_, v___x_1466_);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
case 9:
{
lean_object* v_content_1471_; lean_object* v___x_1472_; size_t v_sz_1473_; size_t v___x_1474_; lean_object* v___x_4553__overap_1475_; lean_object* v___x_1476_; 
v_content_1471_ = lean_ctor_get(v_x_1183_, 0);
lean_inc_ref(v_content_1471_);
lean_dec_ref_known(v_x_1183_, 1);
v___x_1472_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1472_, 0, v_inst_1181_);
lean_closure_set(v___x_1472_, 1, v_x_1182_);
v_sz_1473_ = lean_array_size(v_content_1471_);
v___x_1474_ = ((size_t)0ULL);
v___x_4553__overap_1475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1212_, v___x_1472_, v_sz_1473_, v___x_1474_, v_content_1471_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
v___x_1476_ = lean_apply_4(v___x_4553__overap_1475_, v_a_1184_, v_a_1185_, v_a_1186_, lean_box(0));
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1485_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1485_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1485_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1481_ = l_Lean_Doc_joinInlines(v_a_1477_);
lean_dec(v_a_1477_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1481_);
v___x_1483_ = v___x_1479_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
v_a_1486_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1476_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1476_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
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
default: 
{
lean_object* v_container_1494_; lean_object* v_content_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_dec_ref(v___x_1212_);
v_container_1494_ = lean_ctor_get(v_x_1183_, 0);
lean_inc(v_container_1494_);
v_content_1495_ = lean_ctor_get(v_x_1183_, 1);
lean_inc_ref(v_content_1495_);
lean_dec_ref_known(v_x_1183_, 2);
lean_inc_ref(v_inst_1181_);
v___x_1496_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1496_, 0, v_inst_1181_);
lean_closure_set(v___x_1496_, 1, v_x_1182_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
v___x_1497_ = lean_apply_7(v_inst_1181_, v___x_1496_, v_container_1494_, v_content_1495_, v_a_1184_, v_a_1185_, v_a_1186_, lean_box(0));
return v___x_1497_;
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1498_, lean_object* v_inst_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1499_, v_x_1500_, v_x_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object* v_i_1507_, lean_object* v_inst_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(v_i_1507_, v_inst_1508_, v_x_1509_, v_x_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1523_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1516_, v___x_1522_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object* v_inst_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(v_inst_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1531_, lean_object* v_inst_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1539_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1532_, v___x_1538_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object* v_i_1540_, lean_object* v_inst_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(v_i_1540_, v_inst_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
lean_dec(v_a_1543_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1549_, 0, lean_box(0));
lean_closure_set(v___x_1549_, 1, v_inst_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1550_, lean_object* v_inst_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1552_, 0, lean_box(0));
lean_closure_set(v___x_1552_, 1, v_inst_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(uint32_t v___x_1553_, lean_object* v_s_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_string_push(v_s_1554_, v___x_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object* v___x_1556_, lean_object* v_s_1557_){
_start:
{
uint32_t v___x_2723__boxed_1558_; lean_object* v_res_1559_; 
v___x_2723__boxed_1558_ = lean_unbox_uint32(v___x_1556_);
lean_dec(v___x_1556_);
v_res_1559_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v___x_2723__boxed_1558_, v_s_1557_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed(lean_object* v_inst_1562_, lean_object* v_inst_1563_, lean_object* v___x_1564_, lean_object* v_item_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(v_inst_1562_, v_inst_1563_, v___x_1564_, v_item_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
return v_res_1570_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___f_1573_; 
v___x_1572_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___f_1573_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1573_, 0, v___x_1572_);
return v___f_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v___x_1576_, lean_object* v___x_1577_, lean_object* v_a_1578_, lean_object* v_x_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; size_t v_sz_1586_; size_t v___x_1587_; lean_object* v___x_2656__overap_1588_; lean_object* v___x_1589_; 
v___x_1585_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1585_, 0, v_inst_1574_);
lean_closure_set(v___x_1585_, 1, v_inst_1575_);
v_sz_1586_ = lean_array_size(v_a_1578_);
v___x_1587_ = ((size_t)0ULL);
v___x_2656__overap_1588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1576_, v___x_1585_, v_sz_1586_, v___x_1587_, v_a_1578_);
lean_inc(v___y_1583_);
lean_inc_ref(v___y_1582_);
lean_inc(v___y_1581_);
v___x_1589_ = lean_apply_4(v___x_2656__overap_1588_, v___y_1581_, v___y_1582_, v___y_1583_, lean_box(0));
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1618_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1618_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1618_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_fst_1594_; lean_object* v_snd_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1617_; 
v_fst_1594_ = lean_ctor_get(v___y_1580_, 0);
v_snd_1595_ = lean_ctor_get(v___y_1580_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___y_1580_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1597_ = v___y_1580_;
v_isShared_1598_ = v_isSharedCheck_1617_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_snd_1595_);
lean_inc(v_fst_1594_);
lean_dec(v___y_1580_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1617_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___f_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1611_; 
lean_inc(v_snd_1595_);
v___x_1599_ = l_Nat_reprFast(v_snd_1595_);
v___x_1600_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_1601_ = lean_string_append(v___x_1599_, v___x_1600_);
v___x_1602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_1603_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1);
v___x_1604_ = lean_string_utf8_byte_size(v___x_1601_);
v___x_1605_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1603_, v___x_1604_, v___x_1602_);
v___x_1606_ = l_Lean_Doc_joinBlocks(v_a_1590_);
lean_dec(v_a_1590_);
v___x_1607_ = l_Lean_Doc_prefixListLines(v___x_1601_, v___x_1605_, v___x_1606_);
v___x_1608_ = lean_array_push(v_fst_1594_, v___x_1607_);
v___x_1609_ = lean_nat_add(v_snd_1595_, v___x_1577_);
lean_dec(v_snd_1595_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 1, v___x_1609_);
lean_ctor_set(v___x_1597_, 0, v___x_1608_);
v___x_1611_ = v___x_1597_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1608_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1612_);
v___x_1614_ = v___x_1592_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v___y_1580_);
v_a_1619_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1589_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1589_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v___x_1629_, lean_object* v___x_1630_, lean_object* v_a_1631_, lean_object* v_x_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1627_, v_inst_1628_, v___x_1629_, v___x_1630_, v_a_1631_, v_x_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec(v___x_1630_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v___x_1646_, lean_object* v_item_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; lean_object* v_term_1653_; lean_object* v_desc_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1652_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_1653_ = lean_ctor_get(v_item_1647_, 0);
lean_inc_ref(v_term_1653_);
v_desc_1654_ = lean_ctor_get(v_item_1647_, 1);
lean_inc_ref(v_desc_1654_);
lean_dec_ref(v_item_1647_);
v___x_1655_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_term_1653_);
lean_inc_ref(v_inst_1644_);
v___x_1656_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1644_, v___x_1652_, v___x_1655_, v___y_1648_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1658_; size_t v_sz_1659_; size_t v___x_1660_; lean_object* v___x_2692__overap_1661_; lean_object* v___x_1662_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1658_, 0, v_inst_1644_);
lean_closure_set(v___x_1658_, 1, v_inst_1645_);
v_sz_1659_ = lean_array_size(v_desc_1654_);
v___x_1660_ = ((size_t)0ULL);
lean_inc_ref(v_desc_1654_);
v___x_2692__overap_1661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1646_, v___x_1658_, v_sz_1659_, v___x_1660_, v_desc_1654_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
lean_inc(v___y_1648_);
v___x_1662_ = lean_apply_4(v___x_2692__overap_1661_, v___y_1648_, v___y_1649_, v___y_1650_, lean_box(0));
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1690_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1690_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1690_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___y_1668_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = lean_mk_empty_array_with_capacity(v___x_1675_);
v___x_1677_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_1678_ = lean_unsigned_to_nat(2u);
v___x_1679_ = lean_mk_empty_array_with_capacity(v___x_1678_);
v___x_1680_ = lean_array_push(v___x_1679_, v_a_1657_);
v___x_1681_ = lean_array_push(v___x_1680_, v___x_1677_);
v___x_1682_ = l_Lean_Doc_joinInlines(v___x_1681_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = lean_array_get_size(v_desc_1654_);
lean_dec_ref(v_desc_1654_);
v___x_1684_ = lean_nat_dec_le(v___x_1683_, v___x_1675_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_array_push(v___x_1676_, v___x_1682_);
v___x_1686_ = l_Array_append___redArg(v___x_1685_, v_a_1663_);
lean_dec(v_a_1663_);
v___x_1687_ = l_Lean_Doc_joinBlocks(v___x_1686_);
lean_dec_ref(v___x_1686_);
v___y_1668_ = v___x_1687_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_dec_ref(v___x_1676_);
v___x_1688_ = l_Lean_Doc_joinBlocks(v_a_1663_);
lean_dec(v_a_1663_);
v___x_1689_ = l_Array_append___redArg(v___x_1682_, v___x_1688_);
lean_dec_ref(v___x_1688_);
v___y_1668_ = v___x_1689_;
goto v___jp_1667_;
}
v___jp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1669_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1670_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1671_ = l_Lean_Doc_prefixListLines(v___x_1669_, v___x_1670_, v___y_1668_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1671_);
v___x_1673_ = v___x_1665_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_a_1657_);
lean_dec_ref(v_desc_1654_);
v_a_1691_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1662_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1662_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
else
{
lean_dec_ref(v_desc_1654_);
lean_dec_ref(v___x_1646_);
lean_dec_ref(v_inst_1645_);
lean_dec_ref(v_inst_1644_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v___x_1701_, lean_object* v_item_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1699_, v_inst_1700_, v___x_1701_, v_item_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_x_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1716_; lean_object* v_toApplicative_1717_; lean_object* v_toFunctor_1718_; lean_object* v_toSeq_1719_; lean_object* v_toSeqLeft_1720_; lean_object* v_toSeqRight_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___x_1726_; lean_object* v___f_1727_; lean_object* v___f_1728_; lean_object* v___f_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1716_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1717_ = lean_ctor_get(v___x_1716_, 0);
v_toFunctor_1718_ = lean_ctor_get(v_toApplicative_1717_, 0);
v_toSeq_1719_ = lean_ctor_get(v_toApplicative_1717_, 2);
v_toSeqLeft_1720_ = lean_ctor_get(v_toApplicative_1717_, 3);
v_toSeqRight_1721_ = lean_ctor_get(v_toApplicative_1717_, 4);
v___f_1722_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1723_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1718_, 2);
v___f_1724_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1724_, 0, v_toFunctor_1718_);
v___f_1725_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1725_, 0, v_toFunctor_1718_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___f_1724_);
lean_ctor_set(v___x_1726_, 1, v___f_1725_);
lean_inc(v_toSeqRight_1721_);
v___f_1727_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1727_, 0, v_toSeqRight_1721_);
lean_inc(v_toSeqLeft_1720_);
v___f_1728_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1728_, 0, v_toSeqLeft_1720_);
lean_inc(v_toSeq_1719_);
v___f_1729_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1729_, 0, v_toSeq_1719_);
v___x_1730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1726_);
lean_ctor_set(v___x_1730_, 1, v___f_1722_);
lean_ctor_set(v___x_1730_, 2, v___f_1729_);
lean_ctor_set(v___x_1730_, 3, v___f_1728_);
lean_ctor_set(v___x_1730_, 4, v___f_1727_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
lean_ctor_set(v___x_1731_, 1, v___f_1723_);
v___x_1732_ = l_StateRefT_x27_instMonad___redArg(v___x_1731_);
switch(lean_obj_tag(v_x_1711_))
{
case 0:
{
lean_object* v_contents_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref(v___x_1732_);
lean_dec_ref(v_inst_1710_);
v_contents_1733_ = lean_ctor_get(v_x_1711_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_x_1711_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1735_ = v_x_1711_;
v_isShared_1736_ = v_isSharedCheck_1742_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_contents_1733_);
lean_dec(v_x_1711_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1742_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1737_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 9);
v___x_1739_ = v___x_1735_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_contents_1733_);
v___x_1739_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1740_; 
v___x_1740_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1709_, v___x_1737_, v___x_1739_, v_a_1712_, v_a_1713_, v_a_1714_);
return v___x_1740_;
}
}
}
case 1:
{
lean_object* v_content_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1751_; 
lean_dec_ref(v___x_1732_);
lean_dec_ref(v_inst_1710_);
lean_dec_ref(v_inst_1709_);
v_content_1743_ = lean_ctor_get(v_x_1711_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_x_1711_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1745_ = v_x_1711_;
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_content_1743_);
lean_dec(v_x_1711_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_1743_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set_tag(v___x_1745_, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1747_);
v___x_1749_ = v___x_1745_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
case 2:
{
lean_object* v_items_1752_; lean_object* v___f_1753_; size_t v_sz_1754_; size_t v___x_1755_; lean_object* v___x_2592__overap_1756_; lean_object* v___x_1757_; 
v_items_1752_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_items_1752_);
lean_dec_ref_known(v_x_1711_, 1);
lean_inc_ref(v___x_1732_);
v___f_1753_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1753_, 0, v_inst_1709_);
lean_closure_set(v___f_1753_, 1, v_inst_1710_);
lean_closure_set(v___f_1753_, 2, v___x_1732_);
v_sz_1754_ = lean_array_size(v_items_1752_);
v___x_1755_ = ((size_t)0ULL);
v___x_2592__overap_1756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1732_, v___f_1753_, v_sz_1754_, v___x_1755_, v_items_1752_);
lean_inc(v_a_1714_);
lean_inc_ref(v_a_1713_);
lean_inc(v_a_1712_);
v___x_1757_ = lean_apply_4(v___x_2592__overap_1756_, v_a_1712_, v_a_1713_, v_a_1714_, lean_box(0));
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1766_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = l_Lean_Doc_joinBlocks(v_a_1758_);
lean_dec(v_a_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_a_1767_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1757_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1757_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
case 3:
{
lean_object* v_start_1775_; lean_object* v_items_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1812_; 
v_start_1775_ = lean_ctor_get(v_x_1711_, 0);
v_items_1776_ = lean_ctor_get(v_x_1711_, 1);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_x_1711_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1778_ = v_x_1711_;
v_isShared_1779_ = v_isSharedCheck_1812_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_items_1776_);
lean_inc(v_start_1775_);
lean_dec(v_x_1711_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1812_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v_out_1780_; lean_object* v___x_1781_; lean_object* v___f_1782_; lean_object* v___y_1784_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v_out_1780_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1781_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_1732_);
v___f_1782_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1782_, 0, v_inst_1709_);
lean_closure_set(v___f_1782_, 1, v_inst_1710_);
lean_closure_set(v___f_1782_, 2, v___x_1732_);
lean_closure_set(v___f_1782_, 3, v___x_1781_);
v___x_1810_ = l_Int_toNat(v_start_1775_);
lean_dec(v_start_1775_);
v___x_1811_ = lean_nat_dec_le(v___x_1781_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_dec(v___x_1810_);
v___y_1784_ = v___x_1781_;
goto v___jp_1783_;
}
else
{
v___y_1784_ = v___x_1810_;
goto v___jp_1783_;
}
v___jp_1783_:
{
lean_object* v___x_1786_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 0);
lean_ctor_set(v___x_1778_, 1, v___y_1784_);
lean_ctor_set(v___x_1778_, 0, v_out_1780_);
v___x_1786_ = v___x_1778_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_out_1780_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v___y_1784_);
v___x_1786_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
size_t v_sz_1787_; size_t v___x_1788_; lean_object* v___x_2406__overap_1789_; lean_object* v___x_1790_; 
v_sz_1787_ = lean_array_size(v_items_1776_);
v___x_1788_ = ((size_t)0ULL);
v___x_2406__overap_1789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1732_, v_items_1776_, v___f_1782_, v_sz_1787_, v___x_1788_, v___x_1786_);
lean_inc(v_a_1714_);
lean_inc_ref(v_a_1713_);
lean_inc(v_a_1712_);
v___x_1790_ = lean_apply_4(v___x_2406__overap_1789_, v_a_1712_, v_a_1713_, v_a_1714_, lean_box(0));
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1800_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1800_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1800_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v_fst_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v_fst_1795_ = lean_ctor_get(v_a_1791_, 0);
lean_inc(v_fst_1795_);
lean_dec(v_a_1791_);
v___x_1796_ = l_Lean_Doc_joinBlocks(v_fst_1795_);
lean_dec(v_fst_1795_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1796_);
v___x_1798_ = v___x_1793_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v_a_1801_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1790_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1790_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_1813_; lean_object* v___f_1814_; size_t v_sz_1815_; size_t v___x_1816_; lean_object* v___x_2598__overap_1817_; lean_object* v___x_1818_; 
v_items_1813_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_items_1813_);
lean_dec_ref_known(v_x_1711_, 1);
lean_inc_ref(v___x_1732_);
v___f_1814_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 8, 3);
lean_closure_set(v___f_1814_, 0, v_inst_1709_);
lean_closure_set(v___f_1814_, 1, v_inst_1710_);
lean_closure_set(v___f_1814_, 2, v___x_1732_);
v_sz_1815_ = lean_array_size(v_items_1813_);
v___x_1816_ = ((size_t)0ULL);
v___x_2598__overap_1817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1732_, v___f_1814_, v_sz_1815_, v___x_1816_, v_items_1813_);
lean_inc(v_a_1714_);
lean_inc_ref(v_a_1713_);
lean_inc(v_a_1712_);
v___x_1818_ = lean_apply_4(v___x_2598__overap_1817_, v_a_1712_, v_a_1713_, v_a_1714_, lean_box(0));
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1827_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = l_Lean_Doc_joinBlocks(v_a_1819_);
lean_dec(v_a_1819_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
v_a_1828_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1818_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1818_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
case 5:
{
lean_object* v_items_1836_; lean_object* v___x_1837_; size_t v_sz_1838_; size_t v___x_1839_; lean_object* v___x_2601__overap_1840_; lean_object* v___x_1841_; 
v_items_1836_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_items_1836_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_1837_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1837_, 0, v_inst_1709_);
lean_closure_set(v___x_1837_, 1, v_inst_1710_);
v_sz_1838_ = lean_array_size(v_items_1836_);
v___x_1839_ = ((size_t)0ULL);
v___x_2601__overap_1840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1732_, v___x_1837_, v_sz_1838_, v___x_1839_, v_items_1836_);
lean_inc(v_a_1714_);
lean_inc_ref(v_a_1713_);
lean_inc(v_a_1712_);
v___x_1841_ = lean_apply_4(v___x_2601__overap_1840_, v_a_1712_, v_a_1713_, v_a_1714_, lean_box(0));
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1852_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1846_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_1847_ = l_Lean_Doc_joinBlocks(v_a_1842_);
lean_dec(v_a_1842_);
v___x_1848_ = l_Lean_Doc_prefixLines(v___x_1846_, v___x_1847_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1848_);
v___x_1850_ = v___x_1844_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
v_a_1853_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1841_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1841_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
case 6:
{
lean_object* v_content_1861_; lean_object* v___x_1862_; size_t v_sz_1863_; size_t v___x_1864_; lean_object* v___x_2604__overap_1865_; lean_object* v___x_1866_; 
v_content_1861_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_content_1861_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_1862_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1862_, 0, v_inst_1709_);
lean_closure_set(v___x_1862_, 1, v_inst_1710_);
v_sz_1863_ = lean_array_size(v_content_1861_);
v___x_1864_ = ((size_t)0ULL);
v___x_2604__overap_1865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1732_, v___x_1862_, v_sz_1863_, v___x_1864_, v_content_1861_);
lean_inc(v_a_1714_);
lean_inc_ref(v_a_1713_);
lean_inc(v_a_1712_);
v___x_1866_ = lean_apply_4(v___x_2604__overap_1865_, v_a_1712_, v_a_1713_, v_a_1714_, lean_box(0));
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1875_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1875_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1875_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1871_ = l_Lean_Doc_joinBlocks(v_a_1867_);
lean_dec(v_a_1867_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1871_);
v___x_1873_ = v___x_1869_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
v_a_1876_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1866_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1866_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
default: 
{
lean_object* v_container_1884_; lean_object* v_content_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec_ref(v___x_1732_);
v_container_1884_ = lean_ctor_get(v_x_1711_, 0);
lean_inc(v_container_1884_);
v_content_1885_ = lean_ctor_get(v_x_1711_, 1);
lean_inc_ref(v_content_1885_);
lean_dec_ref_known(v_x_1711_, 2);
v___x_1886_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc_ref(v_inst_1709_);
v___x_1887_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed), 8, 3);
lean_closure_set(v___x_1887_, 0, lean_box(0));
lean_closure_set(v___x_1887_, 1, v_inst_1709_);
lean_closure_set(v___x_1887_, 2, v___x_1886_);
lean_inc_ref(v_inst_1710_);
v___x_1888_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1888_, 0, v_inst_1709_);
lean_closure_set(v___x_1888_, 1, v_inst_1710_);
lean_inc(v_a_1714_);
lean_inc_ref(v_a_1713_);
lean_inc(v_a_1712_);
v___x_1889_ = lean_apply_8(v_inst_1710_, v___x_1887_, v___x_1888_, v_container_1884_, v_content_1885_, v_a_1712_, v_a_1713_, v_a_1714_, lean_box(0));
return v___x_1889_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed(lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_x_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1890_, v_inst_1891_, v_x_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v_inst_1898_, lean_object* v_inst_1899_, lean_object* v___x_1900_, lean_object* v_item_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; size_t v_sz_1907_; size_t v___x_1908_; lean_object* v___x_2631__overap_1909_; lean_object* v___x_1910_; 
v___x_1906_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1906_, 0, v_inst_1898_);
lean_closure_set(v___x_1906_, 1, v_inst_1899_);
v_sz_1907_ = lean_array_size(v_item_1901_);
v___x_1908_ = ((size_t)0ULL);
v___x_2631__overap_1909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1900_, v___x_1906_, v_sz_1907_, v___x_1908_, v_item_1901_);
lean_inc(v___y_1904_);
lean_inc_ref(v___y_1903_);
lean_inc(v___y_1902_);
v___x_1910_ = lean_apply_4(v___x_2631__overap_1909_, v___y_1902_, v___y_1903_, v___y_1904_, lean_box(0));
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1922_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1922_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1922_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1915_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1916_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1917_ = l_Lean_Doc_joinBlocks(v_a_1911_);
lean_dec(v_a_1911_);
v___x_1918_ = l_Lean_Doc_prefixListLines(v___x_1915_, v___x_1916_, v___x_1917_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1918_);
v___x_1920_ = v___x_1913_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
v_a_1923_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1910_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1910_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1931_, lean_object* v_b_1932_, lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_x_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1933_, v_inst_1934_, v_x_1935_, v_a_1936_, v_a_1937_, v_a_1938_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object* v_i_1941_, lean_object* v_b_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_x_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(v_i_1941_, v_b_1942_, v_inst_1943_, v_inst_1944_, v_x_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1951_, v_inst_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1959_, v_inst_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1967_, lean_object* v_b_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1969_, v_inst_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1977_, lean_object* v_b_1978_, lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1977_, v_b_1978_, v_inst_1979_, v_inst_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec(v_a_1982_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1987_, lean_object* v_inst_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_1989_, 0, lean_box(0));
lean_closure_set(v___x_1989_, 1, lean_box(0));
lean_closure_set(v___x_1989_, 2, v_inst_1987_);
lean_closure_set(v___x_1989_, 3, v_inst_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1990_, lean_object* v_b_1991_, lean_object* v_inst_1992_, lean_object* v_inst_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_1994_, 0, lean_box(0));
lean_closure_set(v___x_1994_, 1, lean_box(0));
lean_closure_set(v___x_1994_, 2, v_inst_1992_);
lean_closure_set(v___x_1994_, 3, v_inst_1993_);
return v___x_1994_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = 35;
v___x_1996_ = lean_box_uint32(v___x_1995_);
return v___x_1996_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___f_1998_; 
v___x_1997_ = l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1998_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1998_, 0, v___x_1997_);
return v___f_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_level_2001_, lean_object* v_part_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Doc_partMarkdown___redArg(v_inst_1999_, v_inst_2000_, v_level_2001_, v_part_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec(v_level_2001_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg(lean_object* v_inst_2008_, lean_object* v_inst_2009_, lean_object* v_level_2010_, lean_object* v_part_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___x_2016_; lean_object* v_toApplicative_2017_; lean_object* v_toFunctor_2018_; lean_object* v_toSeq_2019_; lean_object* v_toSeqLeft_2020_; lean_object* v_toSeqRight_2021_; lean_object* v___f_2022_; lean_object* v___f_2023_; lean_object* v___f_2024_; lean_object* v___f_2025_; lean_object* v___x_2026_; lean_object* v___f_2027_; lean_object* v___f_2028_; lean_object* v___f_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v_title_2033_; lean_object* v_content_2034_; lean_object* v_subParts_2035_; lean_object* v___x_2036_; size_t v_sz_2037_; size_t v___x_2038_; lean_object* v___x_680__overap_2039_; lean_object* v___x_2040_; 
v___x_2016_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2017_ = lean_ctor_get(v___x_2016_, 0);
v_toFunctor_2018_ = lean_ctor_get(v_toApplicative_2017_, 0);
v_toSeq_2019_ = lean_ctor_get(v_toApplicative_2017_, 2);
v_toSeqLeft_2020_ = lean_ctor_get(v_toApplicative_2017_, 3);
v_toSeqRight_2021_ = lean_ctor_get(v_toApplicative_2017_, 4);
v___f_2022_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2023_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2018_, 2);
v___f_2024_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2024_, 0, v_toFunctor_2018_);
v___f_2025_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2025_, 0, v_toFunctor_2018_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___f_2024_);
lean_ctor_set(v___x_2026_, 1, v___f_2025_);
lean_inc(v_toSeqRight_2021_);
v___f_2027_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2027_, 0, v_toSeqRight_2021_);
lean_inc(v_toSeqLeft_2020_);
v___f_2028_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2028_, 0, v_toSeqLeft_2020_);
lean_inc(v_toSeq_2019_);
v___f_2029_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2029_, 0, v_toSeq_2019_);
v___x_2030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2026_);
lean_ctor_set(v___x_2030_, 1, v___f_2022_);
lean_ctor_set(v___x_2030_, 2, v___f_2029_);
lean_ctor_set(v___x_2030_, 3, v___f_2028_);
lean_ctor_set(v___x_2030_, 4, v___f_2027_);
v___x_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
lean_ctor_set(v___x_2031_, 1, v___f_2023_);
v___x_2032_ = l_StateRefT_x27_instMonad___redArg(v___x_2031_);
v_title_2033_ = lean_ctor_get(v_part_2011_, 0);
lean_inc_ref(v_title_2033_);
v_content_2034_ = lean_ctor_get(v_part_2011_, 3);
lean_inc_ref(v_content_2034_);
v_subParts_2035_ = lean_ctor_get(v_part_2011_, 4);
lean_inc_ref(v_subParts_2035_);
lean_dec_ref(v_part_2011_);
lean_inc_ref(v_inst_2008_);
v___x_2036_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_2036_, 0, lean_box(0));
lean_closure_set(v___x_2036_, 1, v_inst_2008_);
v_sz_2037_ = lean_array_size(v_title_2033_);
v___x_2038_ = ((size_t)0ULL);
lean_inc_ref(v___x_2032_);
v___x_680__overap_2039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2032_, v___x_2036_, v_sz_2037_, v___x_2038_, v_title_2033_);
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
lean_inc(v_a_2012_);
v___x_2040_ = lean_apply_4(v___x_680__overap_2039_, v_a_2012_, v_a_2013_, v_a_2014_, lean_box(0));
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2042_; size_t v_sz_2043_; lean_object* v___x_683__overap_2044_; lean_object* v___x_2045_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
lean_inc_ref(v_inst_2009_);
lean_inc_ref(v_inst_2008_);
v___x_2042_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_2042_, 0, lean_box(0));
lean_closure_set(v___x_2042_, 1, lean_box(0));
lean_closure_set(v___x_2042_, 2, v_inst_2008_);
lean_closure_set(v___x_2042_, 3, v_inst_2009_);
v_sz_2043_ = lean_array_size(v_content_2034_);
lean_inc_ref(v___x_2032_);
v___x_683__overap_2044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2032_, v___x_2042_, v_sz_2043_, v___x_2038_, v_content_2034_);
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
lean_inc(v_a_2012_);
v___x_2045_ = lean_apply_4(v___x_683__overap_2044_, v_a_2012_, v_a_2013_, v_a_2014_, lean_box(0));
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; lean_object* v___f_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; size_t v_sz_2053_; lean_object* v___x_686__overap_2054_; lean_object* v___x_2055_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_2048_ = lean_obj_once(&l_Lean_Doc_partMarkdown___redArg___closed__0, &l_Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_partMarkdown___redArg___closed__0);
v___x_2049_ = lean_unsigned_to_nat(1u);
v___x_2050_ = lean_nat_add(v_level_2010_, v___x_2049_);
lean_inc(v___x_2050_);
v___x_2051_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_2048_, v___x_2050_, v___x_2047_);
v___x_2052_ = lean_alloc_closure((void*)(l_Lean_Doc_partMarkdown___redArg___boxed), 8, 3);
lean_closure_set(v___x_2052_, 0, v_inst_2008_);
lean_closure_set(v___x_2052_, 1, v_inst_2009_);
lean_closure_set(v___x_2052_, 2, v___x_2050_);
v_sz_2053_ = lean_array_size(v_subParts_2035_);
v___x_686__overap_2054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2032_, v___x_2052_, v_sz_2053_, v___x_2038_, v_subParts_2035_);
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
lean_inc(v_a_2012_);
v___x_2055_ = lean_apply_4(v___x_686__overap_2054_, v_a_2012_, v_a_2013_, v_a_2014_, lean_box(0));
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2074_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2074_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2074_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2060_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_2061_ = lean_string_append(v___x_2051_, v___x_2060_);
v___x_2062_ = lean_mk_empty_array_with_capacity(v___x_2049_);
lean_inc_ref_n(v___x_2062_, 2);
v___x_2063_ = lean_array_push(v___x_2062_, v___x_2061_);
v___x_2064_ = lean_array_push(v___x_2062_, v___x_2063_);
v___x_2065_ = l_Array_append___redArg(v___x_2064_, v_a_2041_);
lean_dec(v_a_2041_);
v___x_2066_ = l_Lean_Doc_joinInlines(v___x_2065_);
lean_dec_ref(v___x_2065_);
v___x_2067_ = lean_array_push(v___x_2062_, v___x_2066_);
v___x_2068_ = l_Array_append___redArg(v___x_2067_, v_a_2046_);
lean_dec(v_a_2046_);
v___x_2069_ = l_Array_append___redArg(v___x_2068_, v_a_2056_);
lean_dec(v_a_2056_);
v___x_2070_ = l_Lean_Doc_joinBlocks(v___x_2069_);
lean_dec_ref(v___x_2069_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2070_);
v___x_2072_ = v___x_2058_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v___x_2051_);
lean_dec(v_a_2046_);
lean_dec(v_a_2041_);
v_a_2075_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2055_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2055_);
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
lean_dec(v_a_2041_);
lean_dec_ref(v_subParts_2035_);
lean_dec_ref(v___x_2032_);
lean_dec_ref(v_inst_2009_);
lean_dec_ref(v_inst_2008_);
v_a_2083_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2045_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2045_);
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
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref(v_subParts_2035_);
lean_dec_ref(v_content_2034_);
lean_dec_ref(v___x_2032_);
lean_dec_ref(v_inst_2009_);
lean_dec_ref(v_inst_2008_);
v_a_2091_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2040_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2040_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown(lean_object* v_i_2099_, lean_object* v_b_2100_, lean_object* v_p_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_level_2104_, lean_object* v_part_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2102_, v_inst_2103_, v_level_2104_, v_part_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___boxed(lean_object* v_i_2111_, lean_object* v_b_2112_, lean_object* v_p_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_level_2116_, lean_object* v_part_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Doc_partMarkdown(v_i_2111_, v_b_2112_, v_p_2113_, v_inst_2114_, v_inst_2115_, v_level_2116_, v_part_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec(v_level_2116_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_2123_, lean_object* v_inst_2124_, lean_object* v_part_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2123_, v_inst_2124_, v___x_2130_, v_part_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_part_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_2132_, v_inst_2133_, v_part_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_2140_, lean_object* v_inst_2141_){
_start:
{
lean_object* v___f_2142_; 
v___f_2142_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2142_, 0, v_inst_2140_);
lean_closure_set(v___f_2142_, 1, v_inst_2141_);
return v___f_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_2143_, lean_object* v_b_2144_, lean_object* v_p_2145_, lean_object* v_inst_2146_, lean_object* v_inst_2147_){
_start:
{
lean_object* v___f_2148_; 
v___f_2148_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2148_, 0, v_inst_2146_);
lean_closure_set(v___f_2148_, 1, v_inst_2147_);
return v___f_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg(lean_object* v_inst_2149_, lean_object* v_f_2150_, lean_object* v_go_2151_, lean_object* v_val_2152_, lean_object* v_content_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___x_2158_; lean_object* v_toApplicative_2159_; lean_object* v_toFunctor_2160_; lean_object* v_toSeq_2161_; lean_object* v_toSeqLeft_2162_; lean_object* v_toSeqRight_2163_; lean_object* v___f_2164_; lean_object* v___f_2165_; lean_object* v___f_2166_; lean_object* v___f_2167_; lean_object* v___x_2168_; lean_object* v___f_2169_; lean_object* v___f_2170_; lean_object* v___f_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2158_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2159_ = lean_ctor_get(v___x_2158_, 0);
v_toFunctor_2160_ = lean_ctor_get(v_toApplicative_2159_, 0);
v_toSeq_2161_ = lean_ctor_get(v_toApplicative_2159_, 2);
v_toSeqLeft_2162_ = lean_ctor_get(v_toApplicative_2159_, 3);
v_toSeqRight_2163_ = lean_ctor_get(v_toApplicative_2159_, 4);
v___f_2164_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2165_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2160_, 2);
v___f_2166_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2166_, 0, v_toFunctor_2160_);
v___f_2167_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2167_, 0, v_toFunctor_2160_);
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___f_2166_);
lean_ctor_set(v___x_2168_, 1, v___f_2167_);
lean_inc(v_toSeqRight_2163_);
v___f_2169_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2169_, 0, v_toSeqRight_2163_);
lean_inc(v_toSeqLeft_2162_);
v___f_2170_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2170_, 0, v_toSeqLeft_2162_);
lean_inc(v_toSeq_2161_);
v___f_2171_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2171_, 0, v_toSeq_2161_);
v___x_2172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2168_);
lean_ctor_set(v___x_2172_, 1, v___f_2164_);
lean_ctor_set(v___x_2172_, 2, v___f_2171_);
lean_ctor_set(v___x_2172_, 3, v___f_2170_);
lean_ctor_set(v___x_2172_, 4, v___f_2169_);
v___x_2173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
lean_ctor_set(v___x_2173_, 1, v___f_2165_);
v___x_2174_ = l_StateRefT_x27_instMonad___redArg(v___x_2173_);
v___x_2175_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2152_, v_inst_2149_);
if (lean_obj_tag(v___x_2175_) == 0)
{
size_t v_sz_2176_; size_t v___x_2177_; lean_object* v___x_288__overap_2178_; lean_object* v___x_2179_; 
lean_dec_ref(v_f_2150_);
v_sz_2176_ = lean_array_size(v_content_2153_);
v___x_2177_ = ((size_t)0ULL);
v___x_288__overap_2178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2174_, v_go_2151_, v_sz_2176_, v___x_2177_, v_content_2153_);
lean_inc(v_a_2156_);
lean_inc_ref(v_a_2155_);
lean_inc(v_a_2154_);
v___x_2179_ = lean_apply_4(v___x_288__overap_2178_, v_a_2154_, v_a_2155_, v_a_2156_, lean_box(0));
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2188_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2184_ = l_Lean_Doc_joinInlines(v_a_2180_);
lean_dec(v_a_2180_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2184_);
v___x_2186_ = v___x_2182_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
v_a_2189_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2179_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2179_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_val_2197_; lean_object* v___x_2198_; 
lean_dec_ref(v___x_2174_);
v_val_2197_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_val_2197_);
lean_dec_ref_known(v___x_2175_, 1);
lean_inc(v_a_2156_);
lean_inc_ref(v_a_2155_);
lean_inc(v_a_2154_);
v___x_2198_ = lean_apply_7(v_f_2150_, v_go_2151_, v_val_2197_, v_content_2153_, v_a_2154_, v_a_2155_, v_a_2156_, lean_box(0));
return v___x_2198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg___boxed(lean_object* v_inst_2199_, lean_object* v_f_2200_, lean_object* v_go_2201_, lean_object* v_val_2202_, lean_object* v_content_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2199_, v_f_2200_, v_go_2201_, v_val_2202_, v_content_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec(v_val_2202_);
lean_dec(v_inst_2199_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer(lean_object* v_00_u03b1_2209_, lean_object* v_inst_2210_, lean_object* v_f_2211_, lean_object* v_go_2212_, lean_object* v_val_2213_, lean_object* v_content_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2210_, v_f_2211_, v_go_2212_, v_val_2213_, v_content_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___boxed(lean_object* v_00_u03b1_2220_, lean_object* v_inst_2221_, lean_object* v_f_2222_, lean_object* v_go_2223_, lean_object* v_val_2224_, lean_object* v_content_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_Doc_mkInlineMdRenderer(v_00_u03b1_2220_, v_inst_2221_, v_f_2222_, v_go_2223_, v_val_2224_, v_content_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec(v_a_2226_);
lean_dec(v_val_2224_);
lean_dec(v_inst_2221_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg(lean_object* v_inst_2231_, lean_object* v_f_2232_, lean_object* v_goI_2233_, lean_object* v_goB_2234_, lean_object* v_val_2235_, lean_object* v_content_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v___x_2241_; lean_object* v_toApplicative_2242_; lean_object* v_toFunctor_2243_; lean_object* v_toSeq_2244_; lean_object* v_toSeqLeft_2245_; lean_object* v_toSeqRight_2246_; lean_object* v___f_2247_; lean_object* v___f_2248_; lean_object* v___f_2249_; lean_object* v___f_2250_; lean_object* v___x_2251_; lean_object* v___f_2252_; lean_object* v___f_2253_; lean_object* v___f_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2241_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2242_ = lean_ctor_get(v___x_2241_, 0);
v_toFunctor_2243_ = lean_ctor_get(v_toApplicative_2242_, 0);
v_toSeq_2244_ = lean_ctor_get(v_toApplicative_2242_, 2);
v_toSeqLeft_2245_ = lean_ctor_get(v_toApplicative_2242_, 3);
v_toSeqRight_2246_ = lean_ctor_get(v_toApplicative_2242_, 4);
v___f_2247_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2248_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2243_, 2);
v___f_2249_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2249_, 0, v_toFunctor_2243_);
v___f_2250_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2250_, 0, v_toFunctor_2243_);
v___x_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___f_2249_);
lean_ctor_set(v___x_2251_, 1, v___f_2250_);
lean_inc(v_toSeqRight_2246_);
v___f_2252_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2252_, 0, v_toSeqRight_2246_);
lean_inc(v_toSeqLeft_2245_);
v___f_2253_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2253_, 0, v_toSeqLeft_2245_);
lean_inc(v_toSeq_2244_);
v___f_2254_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2254_, 0, v_toSeq_2244_);
v___x_2255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2251_);
lean_ctor_set(v___x_2255_, 1, v___f_2247_);
lean_ctor_set(v___x_2255_, 2, v___f_2254_);
lean_ctor_set(v___x_2255_, 3, v___f_2253_);
lean_ctor_set(v___x_2255_, 4, v___f_2252_);
v___x_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
lean_ctor_set(v___x_2256_, 1, v___f_2248_);
v___x_2257_ = l_StateRefT_x27_instMonad___redArg(v___x_2256_);
v___x_2258_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2235_, v_inst_2231_);
if (lean_obj_tag(v___x_2258_) == 0)
{
size_t v_sz_2259_; size_t v___x_2260_; lean_object* v___x_288__overap_2261_; lean_object* v___x_2262_; 
lean_dec_ref(v_goI_2233_);
lean_dec_ref(v_f_2232_);
v_sz_2259_ = lean_array_size(v_content_2236_);
v___x_2260_ = ((size_t)0ULL);
v___x_288__overap_2261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2257_, v_goB_2234_, v_sz_2259_, v___x_2260_, v_content_2236_);
lean_inc(v_a_2239_);
lean_inc_ref(v_a_2238_);
lean_inc(v_a_2237_);
v___x_2262_ = lean_apply_4(v___x_288__overap_2261_, v_a_2237_, v_a_2238_, v_a_2239_, lean_box(0));
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2271_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2267_ = l_Lean_Doc_joinBlocks(v_a_2263_);
lean_dec(v_a_2263_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2267_);
v___x_2269_ = v___x_2265_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
v_a_2272_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2262_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2262_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_object* v_val_2280_; lean_object* v___x_2281_; 
lean_dec_ref(v___x_2257_);
v_val_2280_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_val_2280_);
lean_dec_ref_known(v___x_2258_, 1);
lean_inc(v_a_2239_);
lean_inc_ref(v_a_2238_);
lean_inc(v_a_2237_);
v___x_2281_ = lean_apply_8(v_f_2232_, v_goI_2233_, v_goB_2234_, v_val_2280_, v_content_2236_, v_a_2237_, v_a_2238_, v_a_2239_, lean_box(0));
return v___x_2281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg___boxed(lean_object* v_inst_2282_, lean_object* v_f_2283_, lean_object* v_goI_2284_, lean_object* v_goB_2285_, lean_object* v_val_2286_, lean_object* v_content_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2282_, v_f_2283_, v_goI_2284_, v_goB_2285_, v_val_2286_, v_content_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec(v_val_2286_);
lean_dec(v_inst_2282_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer(lean_object* v_00_u03b1_2293_, lean_object* v_inst_2294_, lean_object* v_f_2295_, lean_object* v_goI_2296_, lean_object* v_goB_2297_, lean_object* v_val_2298_, lean_object* v_content_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2294_, v_f_2295_, v_goI_2296_, v_goB_2297_, v_val_2298_, v_content_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___boxed(lean_object* v_00_u03b1_2305_, lean_object* v_inst_2306_, lean_object* v_f_2307_, lean_object* v_goI_2308_, lean_object* v_goB_2309_, lean_object* v_val_2310_, lean_object* v_content_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_Doc_mkBlockMdRenderer(v_00_u03b1_2305_, v_inst_2306_, v_f_2307_, v_goI_2308_, v_goB_2309_, v_val_2310_, v_content_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec(v_val_2310_);
lean_dec(v_inst_2306_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(lean_object* v_as_2321_, size_t v_i_2322_, size_t v_stop_2323_, lean_object* v_b_2324_){
_start:
{
uint8_t v___x_2325_; 
v___x_2325_ = lean_usize_dec_eq(v_i_2322_, v_stop_2323_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; lean_object* v_fst_2327_; lean_object* v_snd_2328_; lean_object* v___x_2329_; size_t v___x_2330_; size_t v___x_2331_; 
v___x_2326_ = lean_array_uget_borrowed(v_as_2321_, v_i_2322_);
v_fst_2327_ = lean_ctor_get(v___x_2326_, 0);
v_snd_2328_ = lean_ctor_get(v___x_2326_, 1);
lean_inc(v_snd_2328_);
lean_inc(v_fst_2327_);
v___x_2329_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2327_, v_snd_2328_, v_b_2324_);
v___x_2330_ = ((size_t)1ULL);
v___x_2331_ = lean_usize_add(v_i_2322_, v___x_2330_);
v_i_2322_ = v___x_2331_;
v_b_2324_ = v___x_2329_;
goto _start;
}
else
{
return v_b_2324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0___boxed(lean_object* v_as_2333_, lean_object* v_i_2334_, lean_object* v_stop_2335_, lean_object* v_b_2336_){
_start:
{
size_t v_i_boxed_2337_; size_t v_stop_boxed_2338_; lean_object* v_res_2339_; 
v_i_boxed_2337_ = lean_unbox_usize(v_i_2334_);
lean_dec(v_i_2334_);
v_stop_boxed_2338_ = lean_unbox_usize(v_stop_2335_);
lean_dec(v_stop_2335_);
v_res_2339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v_as_2333_, v_i_boxed_2337_, v_stop_boxed_2338_, v_b_2336_);
lean_dec_ref(v_as_2333_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(lean_object* v_as_2340_, size_t v_i_2341_, size_t v_stop_2342_, lean_object* v_b_2343_){
_start:
{
lean_object* v___y_2345_; uint8_t v___x_2349_; 
v___x_2349_ = lean_usize_dec_eq(v_i_2341_, v_stop_2342_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2350_ = lean_array_uget_borrowed(v_as_2340_, v_i_2341_);
v___x_2351_ = lean_unsigned_to_nat(0u);
v___x_2352_ = lean_array_get_size(v___x_2350_);
v___x_2353_ = lean_nat_dec_lt(v___x_2351_, v___x_2352_);
if (v___x_2353_ == 0)
{
v___y_2345_ = v_b_2343_;
goto v___jp_2344_;
}
else
{
uint8_t v___x_2354_; 
v___x_2354_ = lean_nat_dec_le(v___x_2352_, v___x_2352_);
if (v___x_2354_ == 0)
{
if (v___x_2353_ == 0)
{
v___y_2345_ = v_b_2343_;
goto v___jp_2344_;
}
else
{
size_t v___x_2355_; size_t v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = ((size_t)0ULL);
v___x_2356_ = lean_usize_of_nat(v___x_2352_);
v___x_2357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2350_, v___x_2355_, v___x_2356_, v_b_2343_);
v___y_2345_ = v___x_2357_;
goto v___jp_2344_;
}
}
else
{
size_t v___x_2358_; size_t v___x_2359_; lean_object* v___x_2360_; 
v___x_2358_ = ((size_t)0ULL);
v___x_2359_ = lean_usize_of_nat(v___x_2352_);
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2350_, v___x_2358_, v___x_2359_, v_b_2343_);
v___y_2345_ = v___x_2360_;
goto v___jp_2344_;
}
}
}
else
{
return v_b_2343_;
}
v___jp_2344_:
{
size_t v___x_2346_; size_t v___x_2347_; 
v___x_2346_ = ((size_t)1ULL);
v___x_2347_ = lean_usize_add(v_i_2341_, v___x_2346_);
v_i_2341_ = v___x_2347_;
v_b_2343_ = v___y_2345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1___boxed(lean_object* v_as_2361_, lean_object* v_i_2362_, lean_object* v_stop_2363_, lean_object* v_b_2364_){
_start:
{
size_t v_i_boxed_2365_; size_t v_stop_boxed_2366_; lean_object* v_res_2367_; 
v_i_boxed_2365_ = lean_unbox_usize(v_i_2362_);
lean_dec(v_i_2362_);
v_stop_boxed_2366_ = lean_unbox_usize(v_stop_2363_);
lean_dec(v_stop_2363_);
v_res_2367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_as_2361_, v_i_boxed_2365_, v_stop_boxed_2366_, v_b_2364_);
lean_dec_ref(v_as_2361_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(lean_object* v_init_2368_, lean_object* v_es_2369_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2370_ = lean_unsigned_to_nat(0u);
v___x_2371_ = lean_array_get_size(v_es_2369_);
v___x_2372_ = lean_nat_dec_lt(v___x_2370_, v___x_2371_);
if (v___x_2372_ == 0)
{
return v_init_2368_;
}
else
{
uint8_t v___x_2373_; 
v___x_2373_ = lean_nat_dec_le(v___x_2371_, v___x_2371_);
if (v___x_2373_ == 0)
{
if (v___x_2372_ == 0)
{
return v_init_2368_;
}
else
{
size_t v___x_2374_; size_t v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = ((size_t)0ULL);
v___x_2375_ = lean_usize_of_nat(v___x_2371_);
v___x_2376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2369_, v___x_2374_, v___x_2375_, v_init_2368_);
return v___x_2376_;
}
}
else
{
size_t v___x_2377_; size_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = ((size_t)0ULL);
v___x_2378_ = lean_usize_of_nat(v___x_2371_);
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2369_, v___x_2377_, v___x_2378_, v_init_2368_);
return v___x_2379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries___boxed(lean_object* v_init_2380_, lean_object* v_es_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v_init_2380_, v_es_2381_);
lean_dec_ref(v_es_2381_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_2383_, lean_object* v_x_2384_){
_start:
{
if (lean_obj_tag(v_x_2384_) == 0)
{
lean_object* v_k_2385_; lean_object* v_v_2386_; lean_object* v_l_2387_; lean_object* v_r_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v_k_2385_ = lean_ctor_get(v_x_2384_, 1);
v_v_2386_ = lean_ctor_get(v_x_2384_, 2);
v_l_2387_ = lean_ctor_get(v_x_2384_, 3);
v_r_2388_ = lean_ctor_get(v_x_2384_, 4);
v___x_2389_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2383_, v_l_2387_);
lean_inc(v_v_2386_);
lean_inc(v_k_2385_);
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v_k_2385_);
lean_ctor_set(v___x_2390_, 1, v_v_2386_);
v___x_2391_ = lean_array_push(v___x_2389_, v___x_2390_);
v_init_2383_ = v___x_2391_;
v_x_2384_ = v_r_2388_;
goto _start;
}
else
{
return v_init_2383_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_2393_, lean_object* v_x_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2393_, v_x_2394_);
lean_dec(v_x_2394_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2398_){
_start:
{
lean_object* v_current_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_current_2399_ = lean_ctor_get(v_s_2398_, 1);
v___x_2400_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2401_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2400_, v_current_2399_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_s_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_s_2402_);
lean_dec_ref(v_s_2402_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2404_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = lean_box(0);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2406_);
lean_dec_ref(v_x_2406_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2408_, lean_object* v_s_2409_){
_start:
{
lean_object* v_current_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_current_2410_ = lean_ctor_get(v_s_2409_, 1);
v___x_2411_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2412_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2411_, v_current_2410_);
lean_inc_ref_n(v___x_2412_, 2);
v___x_2413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
lean_ctor_set(v___x_2413_, 2, v___x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2414_, lean_object* v_s_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2414_, v_s_2415_);
lean_dec_ref(v_s_2415_);
lean_dec_ref(v_x_2414_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2417_, lean_object* v_x_2418_){
_start:
{
lean_object* v_fst_2419_; lean_object* v_snd_2420_; lean_object* v_imported_2421_; lean_object* v_current_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2430_; 
v_fst_2419_ = lean_ctor_get(v_x_2418_, 0);
lean_inc(v_fst_2419_);
v_snd_2420_ = lean_ctor_get(v_x_2418_, 1);
lean_inc(v_snd_2420_);
lean_dec_ref(v_x_2418_);
v_imported_2421_ = lean_ctor_get(v_s_2417_, 0);
v_current_2422_ = lean_ctor_get(v_s_2417_, 1);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_s_2417_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2424_ = v_s_2417_;
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_current_2422_);
lean_inc(v_imported_2421_);
lean_dec(v_s_2417_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2426_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2419_, v_snd_2420_, v_current_2422_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 1, v___x_2426_);
v___x_2428_ = v___x_2424_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_imported_2421_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2431_, lean_object* v_es_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_inc(v___x_2431_);
v___x_2435_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v___x_2431_, v_es_2432_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v___x_2431_);
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2438_, lean_object* v_es_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2438_, v_es_2439_, v___y_2440_);
lean_dec_ref(v___y_2440_);
lean_dec_ref(v_es_2439_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2443_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2446_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2478_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_();
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(lean_object* v_init_2481_, lean_object* v_t_2482_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2481_, v_t_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_2484_, lean_object* v_t_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(v_init_2484_, v_t_2485_);
lean_dec(v_t_2485_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_));
v___x_2506_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2____boxed(lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_();
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_box(1);
v___x_2511_ = lean_st_mk_ref(v___x_2510_);
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2____boxed(lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_();
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = lean_box(1);
v___x_2517_ = lean_st_mk_ref(v___x_2516_);
v___x_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2____boxed(lean_object* v_a_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_();
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer(lean_object* v_type_2521_, lean_object* v_r_2522_){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2524_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2525_ = lean_st_ref_take(v___x_2524_);
v___x_2526_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2521_, v_r_2522_, v___x_2525_);
v___x_2527_ = lean_st_ref_set(v___x_2524_, v___x_2526_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer___boxed(lean_object* v_type_2529_, lean_object* v_r_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Doc_addBuiltinInlineMdRenderer(v_type_2529_, v_r_2530_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer(lean_object* v_type_2533_, lean_object* v_r_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2536_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2537_ = lean_st_ref_take(v___x_2536_);
v___x_2538_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2533_, v_r_2534_, v___x_2537_);
v___x_2539_ = lean_st_ref_set(v___x_2536_, v___x_2538_);
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer___boxed(lean_object* v_type_2541_, lean_object* v_r_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Doc_addBuiltinBlockMdRenderer(v_type_2541_, v_r_2542_);
return v_res_2544_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2545_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
lean_ctor_set(v___x_2550_, 2, v___x_2549_);
lean_ctor_set(v___x_2550_, 3, v___x_2549_);
lean_ctor_set(v___x_2550_, 4, v___x_2548_);
lean_ctor_set(v___x_2550_, 5, v___x_2548_);
lean_ctor_set(v___x_2550_, 6, v___x_2548_);
lean_ctor_set(v___x_2550_, 7, v___x_2548_);
lean_ctor_set(v___x_2550_, 8, v___x_2548_);
lean_ctor_set(v___x_2550_, 9, v___x_2548_);
return v___x_2550_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2551_ = lean_unsigned_to_nat(32u);
v___x_2552_ = lean_mk_empty_array_with_capacity(v___x_2551_);
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
return v___x_2553_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2554_ = ((size_t)5ULL);
v___x_2555_ = lean_unsigned_to_nat(0u);
v___x_2556_ = lean_unsigned_to_nat(32u);
v___x_2557_ = lean_mk_empty_array_with_capacity(v___x_2556_);
v___x_2558_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_2559_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v___x_2557_);
lean_ctor_set(v___x_2559_, 2, v___x_2555_);
lean_ctor_set(v___x_2559_, 3, v___x_2555_);
lean_ctor_set_usize(v___x_2559_, 4, v___x_2554_);
return v___x_2559_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2560_ = lean_box(1);
v___x_2561_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_2562_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
lean_ctor_set(v___x_2563_, 1, v___x_2561_);
lean_ctor_set(v___x_2563_, 2, v___x_2560_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v___x_2568_; lean_object* v_env_2569_; lean_object* v_options_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2568_ = lean_st_ref_get(v___y_2566_);
v_env_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc_ref(v_env_2569_);
lean_dec(v___x_2568_);
v_options_2570_ = lean_ctor_get(v___y_2565_, 2);
v___x_2571_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_2572_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_2570_);
v___x_2573_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2573_, 0, v_env_2569_);
lean_ctor_set(v___x_2573_, 1, v___x_2571_);
lean_ctor_set(v___x_2573_, 2, v___x_2572_);
lean_ctor_set(v___x_2573_, 3, v_options_2570_);
v___x_2574_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
lean_ctor_set(v___x_2574_, 1, v_msgData_2564_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_2576_, v___y_2577_, v___y_2578_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_ref_2585_; lean_object* v___x_2586_; lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2595_; 
v_ref_2585_ = lean_ctor_get(v___y_2582_, 5);
v___x_2586_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_2581_, v___y_2582_, v___y_2583_);
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2595_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2595_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
lean_inc(v_ref_2585_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_ref_2585_);
lean_ctor_set(v___x_2591_, 1, v_a_2587_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set_tag(v___x_2589_, 1);
lean_ctor_set(v___x_2589_, 0, v___x_2591_);
v___x_2593_ = v___x_2589_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(lean_object* v_x_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
if (lean_obj_tag(v_x_2601_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v_a_2605_ = lean_ctor_get(v_x_2601_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v_x_2601_, 1);
v___x_2606_ = l_Lean_stringToMessageData(v_a_2605_);
v___x_2607_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v___x_2606_, v___y_2602_, v___y_2603_);
return v___x_2607_;
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
v_a_2608_ = lean_ctor_get(v_x_2601_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_x_2601_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v_x_2601_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v_x_2601_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set_tag(v___x_2610_, 0);
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
return v_res_2620_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = lean_box(0);
v___x_2622_ = l_Lean_Elab_abortCommandExceptionId;
v___x_2623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v___x_2621_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(lean_object* v_constName_2629_, uint8_t v_checkMeta_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; lean_object* v_env_2635_; uint8_t v___x_2636_; 
v___x_2634_ = lean_st_ref_get(v___y_2632_);
v_env_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc_ref(v_env_2635_);
lean_dec(v___x_2634_);
lean_inc(v_constName_2629_);
v___x_2636_ = lean_has_compile_error(v_env_2635_, v_constName_2629_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; lean_object* v_env_2638_; lean_object* v_options_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2637_ = lean_st_ref_get(v___y_2632_);
v_env_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc_ref(v_env_2638_);
lean_dec(v___x_2637_);
v_options_2639_ = lean_ctor_get(v___y_2631_, 2);
v___x_2640_ = l_Lean_Environment_evalConst___redArg(v_env_2638_, v_options_2639_, v_constName_2629_, v_checkMeta_2630_);
lean_dec(v_constName_2629_);
lean_dec_ref(v_env_2638_);
v___x_2641_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2640_, v___y_2631_, v___y_2632_);
return v___x_2641_;
}
else
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v___x_2643_; lean_object* v_env_2644_; lean_object* v_options_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_dec_ref_known(v___x_2642_, 1);
v___x_2643_ = lean_st_ref_get(v___y_2632_);
v_env_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc_ref(v_env_2644_);
lean_dec(v___x_2643_);
v_options_2645_ = lean_ctor_get(v___y_2631_, 2);
v___x_2646_ = l_Lean_Environment_evalConst___redArg(v_env_2644_, v_options_2645_, v_constName_2629_, v_checkMeta_2630_);
lean_dec(v_constName_2629_);
lean_dec_ref(v_env_2644_);
v___x_2647_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2646_, v___y_2631_, v___y_2632_);
return v___x_2647_;
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_dec(v_constName_2629_);
v_a_2648_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2642_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2642_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg___boxed(lean_object* v_constName_2656_, lean_object* v_checkMeta_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
uint8_t v_checkMeta_boxed_2661_; lean_object* v_res_2662_; 
v_checkMeta_boxed_2661_ = lean_unbox(v_checkMeta_2657_);
v_res_2662_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2656_, v_checkMeta_boxed_2661_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(lean_object* v_type_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v___x_2667_; lean_object* v___y_2669_; lean_object* v_env_2700_; lean_object* v___x_2701_; lean_object* v_toEnvExtension_2702_; lean_object* v_asyncMode_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v_imported_2707_; lean_object* v_current_2708_; lean_object* v___x_2709_; 
v___x_2667_ = lean_st_ref_get(v_a_2665_);
v_env_2700_ = lean_ctor_get(v___x_2667_, 0);
lean_inc_ref(v_env_2700_);
lean_dec(v___x_2667_);
v___x_2701_ = l_Lean_Doc_docInlineMdExt;
v_toEnvExtension_2702_ = lean_ctor_get(v___x_2701_, 0);
v_asyncMode_2703_ = lean_ctor_get(v_toEnvExtension_2702_, 2);
v___x_2704_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2705_ = lean_box(0);
v___x_2706_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2704_, v___x_2701_, v_env_2700_, v_asyncMode_2703_, v___x_2705_);
v_imported_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_imported_2707_);
v_current_2708_ = lean_ctor_get(v___x_2706_, 1);
lean_inc(v_current_2708_);
lean_dec(v___x_2706_);
v___x_2709_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2708_, v_type_2663_);
lean_dec(v_current_2708_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2707_, v_type_2663_);
lean_dec(v_imported_2707_);
v___y_2669_ = v___x_2710_;
goto v___jp_2668_;
}
else
{
lean_dec(v_imported_2707_);
v___y_2669_ = v___x_2709_;
goto v___jp_2668_;
}
v___jp_2668_:
{
if (lean_obj_tag(v___y_2669_) == 0)
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2670_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2671_ = lean_st_ref_get(v___x_2670_);
v___x_2672_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2671_, v_type_2663_);
lean_dec(v___x_2671_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
return v___x_2673_;
}
else
{
lean_object* v_val_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2699_; 
v_val_2674_ = lean_ctor_get(v___y_2669_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___y_2669_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2676_ = v___y_2669_;
v_isShared_2677_ = v_isSharedCheck_2699_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_val_2674_);
lean_dec(v___y_2669_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2699_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
uint8_t v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = 1;
v___x_2679_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2674_, v___x_2678_, v_a_2664_, v_a_2665_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2690_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2682_ = v___x_2679_;
v_isShared_2683_ = v_isSharedCheck_2690_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2679_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2690_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v_a_2680_);
v___x_2685_ = v___x_2676_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2687_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v___x_2685_);
v___x_2687_ = v___x_2682_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
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
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_del_object(v___x_2676_);
v_a_2691_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2679_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2679_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe___boxed(lean_object* v_type_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v_type_2711_, v_a_2712_, v_a_2713_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_type_2711_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(v_00_u03b1_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(lean_object* v_00_u03b1_2726_, lean_object* v_constName_2727_, uint8_t v_checkMeta_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2727_, v_checkMeta_2728_, v___y_2729_, v___y_2730_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___boxed(lean_object* v_00_u03b1_2733_, lean_object* v_constName_2734_, lean_object* v_checkMeta_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
uint8_t v_checkMeta_boxed_2739_; lean_object* v_res_2740_; 
v_checkMeta_boxed_2739_ = lean_unbox(v_checkMeta_2735_);
v_res_2740_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(v_00_u03b1_2733_, v_constName_2734_, v_checkMeta_boxed_2739_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_2741_, lean_object* v_x_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2742_, v___y_2743_, v___y_2744_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2747_, lean_object* v_x_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(v_00_u03b1_2747_, v_x_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2753_, lean_object* v_msg_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2754_, v___y_2755_, v___y_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2759_, lean_object* v_msg_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_2759_, v_msg_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(lean_object* v_typeName_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v___x_2769_; lean_object* v___y_2771_; lean_object* v_env_2802_; lean_object* v___x_2803_; lean_object* v_toEnvExtension_2804_; lean_object* v_asyncMode_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v_imported_2809_; lean_object* v_current_2810_; lean_object* v___x_2811_; 
v___x_2769_ = lean_st_ref_get(v_a_2767_);
v_env_2802_ = lean_ctor_get(v___x_2769_, 0);
lean_inc_ref(v_env_2802_);
lean_dec(v___x_2769_);
v___x_2803_ = l_Lean_Doc_docBlockMdExt;
v_toEnvExtension_2804_ = lean_ctor_get(v___x_2803_, 0);
v_asyncMode_2805_ = lean_ctor_get(v_toEnvExtension_2804_, 2);
v___x_2806_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2807_ = lean_box(0);
v___x_2808_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2806_, v___x_2803_, v_env_2802_, v_asyncMode_2805_, v___x_2807_);
v_imported_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_imported_2809_);
v_current_2810_ = lean_ctor_get(v___x_2808_, 1);
lean_inc(v_current_2810_);
lean_dec(v___x_2808_);
v___x_2811_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2810_, v_typeName_2765_);
lean_dec(v_current_2810_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2809_, v_typeName_2765_);
lean_dec(v_imported_2809_);
v___y_2771_ = v___x_2812_;
goto v___jp_2770_;
}
else
{
lean_dec(v_imported_2809_);
v___y_2771_ = v___x_2811_;
goto v___jp_2770_;
}
v___jp_2770_:
{
if (lean_obj_tag(v___y_2771_) == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2772_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2773_ = lean_st_ref_get(v___x_2772_);
v___x_2774_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2773_, v_typeName_2765_);
lean_dec(v___x_2773_);
v___x_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
return v___x_2775_;
}
else
{
lean_object* v_val_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2801_; 
v_val_2776_ = lean_ctor_get(v___y_2771_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___y_2771_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2778_ = v___y_2771_;
v_isShared_2779_ = v_isSharedCheck_2801_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_val_2776_);
lean_dec(v___y_2771_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2801_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
uint8_t v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = 1;
v___x_2781_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2776_, v___x_2780_, v_a_2766_, v_a_2767_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2792_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2792_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2792_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v_a_2782_);
v___x_2787_ = v___x_2778_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2789_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2787_);
v___x_2789_ = v___x_2784_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
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
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_del_object(v___x_2778_);
v_a_2793_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2781_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2781_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe___boxed(lean_object* v_typeName_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v_typeName_2813_, v_a_2814_, v_a_2815_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_typeName_2813_);
return v_res_2817_;
}
}
static lean_object* _init_l_Lean_Doc_mdRendererHeartbeats(void){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_unsigned_to_nat(200000u);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg(lean_object* v_x_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v___x_2824_; lean_object* v_fileName_2825_; lean_object* v_fileMap_2826_; lean_object* v_options_2827_; lean_object* v_currRecDepth_2828_; lean_object* v_maxRecDepth_2829_; lean_object* v_ref_2830_; lean_object* v_currNamespace_2831_; lean_object* v_openDecls_2832_; lean_object* v_quotContext_2833_; lean_object* v_currMacroScope_2834_; uint8_t v_diag_2835_; lean_object* v_cancelTk_x3f_2836_; uint8_t v_suppressElabErrors_2837_; lean_object* v_inheritedTraceOptions_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2824_ = lean_io_get_num_heartbeats();
v_fileName_2825_ = lean_ctor_get(v_a_2821_, 0);
v_fileMap_2826_ = lean_ctor_get(v_a_2821_, 1);
v_options_2827_ = lean_ctor_get(v_a_2821_, 2);
v_currRecDepth_2828_ = lean_ctor_get(v_a_2821_, 3);
v_maxRecDepth_2829_ = lean_ctor_get(v_a_2821_, 4);
v_ref_2830_ = lean_ctor_get(v_a_2821_, 5);
v_currNamespace_2831_ = lean_ctor_get(v_a_2821_, 6);
v_openDecls_2832_ = lean_ctor_get(v_a_2821_, 7);
v_quotContext_2833_ = lean_ctor_get(v_a_2821_, 10);
v_currMacroScope_2834_ = lean_ctor_get(v_a_2821_, 11);
v_diag_2835_ = lean_ctor_get_uint8(v_a_2821_, sizeof(void*)*14);
v_cancelTk_x3f_2836_ = lean_ctor_get(v_a_2821_, 12);
v_suppressElabErrors_2837_ = lean_ctor_get_uint8(v_a_2821_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2838_ = lean_ctor_get(v_a_2821_, 13);
v___x_2839_ = lean_unsigned_to_nat(200000u);
lean_inc_ref(v_inheritedTraceOptions_2838_);
lean_inc(v_cancelTk_x3f_2836_);
lean_inc(v_currMacroScope_2834_);
lean_inc(v_quotContext_2833_);
lean_inc(v_openDecls_2832_);
lean_inc(v_currNamespace_2831_);
lean_inc(v_ref_2830_);
lean_inc(v_maxRecDepth_2829_);
lean_inc(v_currRecDepth_2828_);
lean_inc_ref(v_options_2827_);
lean_inc_ref(v_fileMap_2826_);
lean_inc_ref(v_fileName_2825_);
v___x_2840_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2840_, 0, v_fileName_2825_);
lean_ctor_set(v___x_2840_, 1, v_fileMap_2826_);
lean_ctor_set(v___x_2840_, 2, v_options_2827_);
lean_ctor_set(v___x_2840_, 3, v_currRecDepth_2828_);
lean_ctor_set(v___x_2840_, 4, v_maxRecDepth_2829_);
lean_ctor_set(v___x_2840_, 5, v_ref_2830_);
lean_ctor_set(v___x_2840_, 6, v_currNamespace_2831_);
lean_ctor_set(v___x_2840_, 7, v_openDecls_2832_);
lean_ctor_set(v___x_2840_, 8, v___x_2824_);
lean_ctor_set(v___x_2840_, 9, v___x_2839_);
lean_ctor_set(v___x_2840_, 10, v_quotContext_2833_);
lean_ctor_set(v___x_2840_, 11, v_currMacroScope_2834_);
lean_ctor_set(v___x_2840_, 12, v_cancelTk_x3f_2836_);
lean_ctor_set(v___x_2840_, 13, v_inheritedTraceOptions_2838_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*14, v_diag_2835_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*14 + 1, v_suppressElabErrors_2837_);
lean_inc(v_a_2822_);
lean_inc(v_a_2820_);
v___x_2841_ = lean_apply_4(v_x_2819_, v_a_2820_, v___x_2840_, v_a_2822_, lean_box(0));
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg___boxed(lean_object* v_x_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec(v_a_2843_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget(lean_object* v_00_u03b1_2848_, lean_object* v_x_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___boxed(lean_object* v_00_u03b1_2855_, lean_object* v_x_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_Doc_withMdRendererBudget(v_00_u03b1_2855_, v_x_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
lean_dec(v_a_2857_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback(lean_object* v_fallback_2862_, lean_object* v_act_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = lean_st_ref_get(v_a_2864_);
v___x_2869_ = l_Lean_Doc_withMdRendererBudget___redArg(v_act_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_dec(v___x_2868_);
lean_dec_ref(v_fallback_2862_);
return v___x_2869_;
}
else
{
lean_object* v_a_2870_; uint8_t v___x_2871_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
v___x_2871_ = l_Lean_Exception_isInterrupt(v_a_2870_);
lean_dec(v_a_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec_ref_known(v___x_2869_, 1);
v___x_2872_ = lean_st_ref_set(v_a_2864_, v___x_2868_);
lean_inc(v_a_2866_);
lean_inc_ref(v_a_2865_);
lean_inc(v_a_2864_);
v___x_2873_ = lean_apply_4(v_fallback_2862_, v_a_2864_, v_a_2865_, v_a_2866_, lean_box(0));
return v___x_2873_;
}
else
{
lean_dec(v___x_2868_);
lean_dec_ref(v_fallback_2862_);
return v___x_2869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback___boxed(lean_object* v_fallback_2874_, lean_object* v_act_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Lean_Doc_withRendererFallback(v_fallback_2874_, v_act_2875_, v_a_2876_, v_a_2877_, v_a_2878_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
lean_dec(v_a_2876_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0(lean_object* v_____do__lift_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = l_Lean_Doc_joinInlines(v_____do__lift_2881_);
v___x_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0___boxed(lean_object* v_____do__lift_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__0(v_____do__lift_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v_____do__lift_2888_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1(lean_object* v___x_2894_, lean_object* v___f_2895_, lean_object* v___x_2896_, lean_object* v_go_2897_, lean_object* v_container_2898_, lean_object* v_content_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
if (lean_obj_tag(v_container_2898_) == 0)
{
lean_object* v_val_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_val_2904_ = lean_ctor_get(v_container_2898_, 0);
lean_inc(v_val_2904_);
lean_dec_ref_known(v_container_2898_, 1);
v___x_2905_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2904_);
v___x_2906_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_2905_, v___y_2901_, v___y_2902_);
lean_dec(v___x_2905_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
lean_dec_ref_known(v___x_2906_, 1);
if (lean_obj_tag(v_a_2907_) == 0)
{
size_t v_sz_2908_; size_t v___x_2909_; lean_object* v___x_541__overap_2910_; lean_object* v___x_2911_; 
lean_dec(v_val_2904_);
lean_dec_ref(v___x_2896_);
v_sz_2908_ = lean_array_size(v_content_2899_);
v___x_2909_ = ((size_t)0ULL);
v___x_541__overap_2910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2894_, v_go_2897_, v_sz_2908_, v___x_2909_, v_content_2899_);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
lean_inc(v___y_2900_);
v___x_2911_ = lean_apply_4(v___x_541__overap_2910_, v___y_2900_, v___y_2901_, v___y_2902_, lean_box(0));
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2913_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
lean_inc(v___y_2900_);
v___x_2913_ = lean_apply_5(v___f_2895_, v_a_2912_, v___y_2900_, v___y_2901_, v___y_2902_, lean_box(0));
return v___x_2913_;
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v___f_2895_);
v_a_2914_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2911_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2911_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
else
{
lean_object* v_val_2922_; size_t v_sz_2923_; size_t v___x_2924_; lean_object* v___x_2925_; lean_object* v_fallback_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v_val_2922_ = lean_ctor_get(v_a_2907_, 0);
lean_inc(v_val_2922_);
lean_dec_ref_known(v_a_2907_, 1);
v_sz_2923_ = lean_array_size(v_content_2899_);
v___x_2924_ = ((size_t)0ULL);
lean_inc_ref(v_content_2899_);
lean_inc_ref(v_go_2897_);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2894_, v_go_2897_, v_sz_2923_, v___x_2924_, v_content_2899_);
v_fallback_2926_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_2926_, 0, lean_box(0));
lean_closure_set(v_fallback_2926_, 1, lean_box(0));
lean_closure_set(v_fallback_2926_, 2, v___x_2896_);
lean_closure_set(v_fallback_2926_, 3, lean_box(0));
lean_closure_set(v_fallback_2926_, 4, lean_box(0));
lean_closure_set(v_fallback_2926_, 5, v___x_2925_);
lean_closure_set(v_fallback_2926_, 6, v___f_2895_);
v___x_2927_ = lean_apply_3(v_val_2922_, v_go_2897_, v_val_2904_, v_content_2899_);
v___x_2928_ = l_Lean_Doc_withRendererFallback(v_fallback_2926_, v___x_2927_, v___y_2900_, v___y_2901_, v___y_2902_);
return v___x_2928_;
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v_val_2904_);
lean_dec_ref(v_content_2899_);
lean_dec_ref(v_go_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___f_2895_);
lean_dec_ref(v___x_2894_);
v_a_2929_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2906_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2906_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
else
{
size_t v_sz_2937_; size_t v___x_2938_; lean_object* v___x_558__overap_2939_; lean_object* v___x_2940_; 
lean_dec_ref_known(v_container_2898_, 1);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___f_2895_);
v_sz_2937_ = lean_array_size(v_content_2899_);
v___x_2938_ = ((size_t)0ULL);
v___x_558__overap_2939_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2894_, v_go_2897_, v_sz_2937_, v___x_2938_, v_content_2899_);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
lean_inc(v___y_2900_);
v___x_2940_ = lean_apply_4(v___x_558__overap_2939_, v___y_2900_, v___y_2901_, v___y_2902_, lean_box(0));
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2949_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2949_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2949_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2945_ = l_Lean_Doc_joinInlines(v_a_2941_);
lean_dec(v_a_2941_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2945_);
v___x_2947_ = v___x_2943_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
v_a_2950_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2940_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2940_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed(lean_object* v___x_2958_, lean_object* v___f_2959_, lean_object* v___x_2960_, lean_object* v_go_2961_, lean_object* v_container_2962_, lean_object* v_content_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__1(v___x_2958_, v___f_2959_, v___x_2960_, v_go_2961_, v_container_2962_, v_content_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
return v_res_2968_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownInlineElabInline(void){
_start:
{
lean_object* v___x_2970_; lean_object* v_toApplicative_2971_; lean_object* v_toFunctor_2972_; lean_object* v_toSeq_2973_; lean_object* v_toSeqLeft_2974_; lean_object* v_toSeqRight_2975_; lean_object* v___f_2976_; lean_object* v___f_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; lean_object* v___f_2980_; lean_object* v___x_2981_; lean_object* v___f_2982_; lean_object* v___f_2983_; lean_object* v___f_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___f_2988_; 
v___x_2970_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2971_ = lean_ctor_get(v___x_2970_, 0);
v_toFunctor_2972_ = lean_ctor_get(v_toApplicative_2971_, 0);
v_toSeq_2973_ = lean_ctor_get(v_toApplicative_2971_, 2);
v_toSeqLeft_2974_ = lean_ctor_get(v_toApplicative_2971_, 3);
v_toSeqRight_2975_ = lean_ctor_get(v_toApplicative_2971_, 4);
v___f_2976_ = ((lean_object*)(l_Lean_Doc_instMarkdownInlineElabInline___closed__0));
v___f_2977_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2978_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2972_, 2);
v___f_2979_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2979_, 0, v_toFunctor_2972_);
v___f_2980_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2980_, 0, v_toFunctor_2972_);
v___x_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___f_2979_);
lean_ctor_set(v___x_2981_, 1, v___f_2980_);
lean_inc(v_toSeqRight_2975_);
v___f_2982_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2982_, 0, v_toSeqRight_2975_);
lean_inc(v_toSeqLeft_2974_);
v___f_2983_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2983_, 0, v_toSeqLeft_2974_);
lean_inc(v_toSeq_2973_);
v___f_2984_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2984_, 0, v_toSeq_2973_);
v___x_2985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2981_);
lean_ctor_set(v___x_2985_, 1, v___f_2977_);
lean_ctor_set(v___x_2985_, 2, v___f_2984_);
lean_ctor_set(v___x_2985_, 3, v___f_2983_);
lean_ctor_set(v___x_2985_, 4, v___f_2982_);
v___x_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
lean_ctor_set(v___x_2986_, 1, v___f_2978_);
lean_inc_ref(v___x_2986_);
v___x_2987_ = l_StateRefT_x27_instMonad___redArg(v___x_2986_);
v___f_2988_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2988_, 0, v___x_2987_);
lean_closure_set(v___f_2988_, 1, v___f_2976_);
lean_closure_set(v___f_2988_, 2, v___x_2986_);
return v___f_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v_____do__lift_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = l_Lean_Doc_joinBlocks(v_____do__lift_2989_);
v___x_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object* v_____do__lift_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(v_____do__lift_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v_____do__lift_2996_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object* v___x_3002_, lean_object* v___f_3003_, lean_object* v___x_3004_, lean_object* v_goI_3005_, lean_object* v_goB_3006_, lean_object* v_container_3007_, lean_object* v_content_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
if (lean_obj_tag(v_container_3007_) == 0)
{
lean_object* v_val_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_val_3013_ = lean_ctor_get(v_container_3007_, 0);
lean_inc(v_val_3013_);
lean_dec_ref_known(v_container_3007_, 1);
v___x_3014_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3013_);
v___x_3015_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_3014_, v___y_3010_, v___y_3011_);
lean_dec(v___x_3014_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
if (lean_obj_tag(v_a_3016_) == 0)
{
size_t v_sz_3017_; size_t v___x_3018_; lean_object* v___x_541__overap_3019_; lean_object* v___x_3020_; 
lean_dec(v_val_3013_);
lean_dec_ref(v_goI_3005_);
lean_dec_ref(v___x_3004_);
v_sz_3017_ = lean_array_size(v_content_3008_);
v___x_3018_ = ((size_t)0ULL);
v___x_541__overap_3019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3002_, v_goB_3006_, v_sz_3017_, v___x_3018_, v_content_3008_);
lean_inc(v___y_3011_);
lean_inc_ref(v___y_3010_);
lean_inc(v___y_3009_);
v___x_3020_ = lean_apply_4(v___x_541__overap_3019_, v___y_3009_, v___y_3010_, v___y_3011_, lean_box(0));
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
lean_inc(v___y_3011_);
lean_inc_ref(v___y_3010_);
lean_inc(v___y_3009_);
v___x_3022_ = lean_apply_5(v___f_3003_, v_a_3021_, v___y_3009_, v___y_3010_, v___y_3011_, lean_box(0));
return v___x_3022_;
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref(v___f_3003_);
v_a_3023_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3020_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3020_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_object* v_val_3031_; size_t v_sz_3032_; size_t v___x_3033_; lean_object* v___x_3034_; lean_object* v_fallback_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_val_3031_ = lean_ctor_get(v_a_3016_, 0);
lean_inc(v_val_3031_);
lean_dec_ref_known(v_a_3016_, 1);
v_sz_3032_ = lean_array_size(v_content_3008_);
v___x_3033_ = ((size_t)0ULL);
lean_inc_ref(v_content_3008_);
lean_inc_ref(v_goB_3006_);
v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3002_, v_goB_3006_, v_sz_3032_, v___x_3033_, v_content_3008_);
v_fallback_3035_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_3035_, 0, lean_box(0));
lean_closure_set(v_fallback_3035_, 1, lean_box(0));
lean_closure_set(v_fallback_3035_, 2, v___x_3004_);
lean_closure_set(v_fallback_3035_, 3, lean_box(0));
lean_closure_set(v_fallback_3035_, 4, lean_box(0));
lean_closure_set(v_fallback_3035_, 5, v___x_3034_);
lean_closure_set(v_fallback_3035_, 6, v___f_3003_);
v___x_3036_ = lean_apply_4(v_val_3031_, v_goI_3005_, v_goB_3006_, v_val_3013_, v_content_3008_);
v___x_3037_ = l_Lean_Doc_withRendererFallback(v_fallback_3035_, v___x_3036_, v___y_3009_, v___y_3010_, v___y_3011_);
return v___x_3037_;
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec(v_val_3013_);
lean_dec_ref(v_content_3008_);
lean_dec_ref(v_goB_3006_);
lean_dec_ref(v_goI_3005_);
lean_dec_ref(v___x_3004_);
lean_dec_ref(v___f_3003_);
lean_dec_ref(v___x_3002_);
v_a_3038_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3015_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3015_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
size_t v_sz_3046_; size_t v___x_3047_; lean_object* v___x_558__overap_3048_; lean_object* v___x_3049_; 
lean_dec_ref_known(v_container_3007_, 1);
lean_dec_ref(v_goI_3005_);
lean_dec_ref(v___x_3004_);
lean_dec_ref(v___f_3003_);
v_sz_3046_ = lean_array_size(v_content_3008_);
v___x_3047_ = ((size_t)0ULL);
v___x_558__overap_3048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3002_, v_goB_3006_, v_sz_3046_, v___x_3047_, v_content_3008_);
lean_inc(v___y_3011_);
lean_inc_ref(v___y_3010_);
lean_inc(v___y_3009_);
v___x_3049_ = lean_apply_4(v___x_558__overap_3048_, v___y_3009_, v___y_3010_, v___y_3011_, lean_box(0));
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3058_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3052_ = v___x_3049_;
v_isShared_3053_ = v_isSharedCheck_3058_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3058_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3054_ = l_Lean_Doc_joinBlocks(v_a_3050_);
lean_dec(v_a_3050_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v___x_3054_);
v___x_3056_ = v___x_3052_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
v_a_3059_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3049_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3049_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object* v___x_3067_, lean_object* v___f_3068_, lean_object* v___x_3069_, lean_object* v_goI_3070_, lean_object* v_goB_3071_, lean_object* v_container_3072_, lean_object* v_content_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_3067_, v___f_3068_, v___x_3069_, v_goI_3070_, v_goB_3071_, v_container_3072_, v_content_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
return v_res_3078_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownBlockElabInlineElabBlock(void){
_start:
{
lean_object* v___x_3080_; lean_object* v_toApplicative_3081_; lean_object* v_toFunctor_3082_; lean_object* v_toSeq_3083_; lean_object* v_toSeqLeft_3084_; lean_object* v_toSeqRight_3085_; lean_object* v___f_3086_; lean_object* v___f_3087_; lean_object* v___f_3088_; lean_object* v___f_3089_; lean_object* v___f_3090_; lean_object* v___x_3091_; lean_object* v___f_3092_; lean_object* v___f_3093_; lean_object* v___f_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___f_3098_; 
v___x_3080_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3081_ = lean_ctor_get(v___x_3080_, 0);
v_toFunctor_3082_ = lean_ctor_get(v_toApplicative_3081_, 0);
v_toSeq_3083_ = lean_ctor_get(v_toApplicative_3081_, 2);
v_toSeqLeft_3084_ = lean_ctor_get(v_toApplicative_3081_, 3);
v_toSeqRight_3085_ = lean_ctor_get(v_toApplicative_3081_, 4);
v___f_3086_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___closed__0));
v___f_3087_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3088_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3082_, 2);
v___f_3089_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3089_, 0, v_toFunctor_3082_);
v___f_3090_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3090_, 0, v_toFunctor_3082_);
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___f_3089_);
lean_ctor_set(v___x_3091_, 1, v___f_3090_);
lean_inc(v_toSeqRight_3085_);
v___f_3092_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3092_, 0, v_toSeqRight_3085_);
lean_inc(v_toSeqLeft_3084_);
v___f_3093_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3093_, 0, v_toSeqLeft_3084_);
lean_inc(v_toSeq_3083_);
v___f_3094_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3094_, 0, v_toSeq_3083_);
v___x_3095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3091_);
lean_ctor_set(v___x_3095_, 1, v___f_3087_);
lean_ctor_set(v___x_3095_, 2, v___f_3094_);
lean_ctor_set(v___x_3095_, 3, v___f_3093_);
lean_ctor_set(v___x_3095_, 4, v___f_3092_);
v___x_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
lean_ctor_set(v___x_3096_, 1, v___f_3088_);
lean_inc_ref(v___x_3096_);
v___x_3097_ = l_StateRefT_x27_instMonad___redArg(v___x_3096_);
v___f_3098_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3098_, 0, v___x_3097_);
lean_closure_set(v___f_3098_, 1, v___f_3086_);
lean_closure_set(v___f_3098_, 2, v___x_3096_);
return v___f_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0(lean_object* v___x_3099_, lean_object* v___x_3100_, lean_object* v_part_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = lean_unsigned_to_nat(0u);
v___x_3107_ = l_Lean_Doc_partMarkdown___redArg(v___x_3099_, v___x_3100_, v___x_3106_, v_part_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed(lean_object* v___x_3108_, lean_object* v___x_3109_, lean_object* v_part_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__0(v___x_3108_, v___x_3109_, v_part_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1(lean_object* v___x_3116_, lean_object* v___x_3117_, lean_object* v___x_3118_, lean_object* v___f_3119_, lean_object* v_x_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_text_3125_; lean_object* v_subsections_3126_; lean_object* v___x_3127_; size_t v_sz_3128_; size_t v___x_3129_; lean_object* v___x_440__overap_3130_; lean_object* v___x_3131_; 
v_text_3125_ = lean_ctor_get(v_x_3120_, 0);
lean_inc_ref(v_text_3125_);
v_subsections_3126_ = lean_ctor_get(v_x_3120_, 1);
lean_inc_ref(v_subsections_3126_);
lean_dec_ref(v_x_3120_);
v___x_3127_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3127_, 0, lean_box(0));
lean_closure_set(v___x_3127_, 1, lean_box(0));
lean_closure_set(v___x_3127_, 2, v___x_3116_);
lean_closure_set(v___x_3127_, 3, v___x_3117_);
v_sz_3128_ = lean_array_size(v_text_3125_);
v___x_3129_ = ((size_t)0ULL);
lean_inc_ref(v___x_3118_);
v___x_440__overap_3130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3118_, v___x_3127_, v_sz_3128_, v___x_3129_, v_text_3125_);
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
lean_inc(v___y_3121_);
v___x_3131_ = lean_apply_4(v___x_440__overap_3130_, v___y_3121_, v___y_3122_, v___y_3123_, lean_box(0));
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; size_t v_sz_3133_; lean_object* v___x_443__overap_3134_; lean_object* v___x_3135_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3131_, 1);
v_sz_3133_ = lean_array_size(v_subsections_3126_);
v___x_443__overap_3134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3118_, v___f_3119_, v_sz_3133_, v___x_3129_, v_subsections_3126_);
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
lean_inc(v___y_3121_);
v___x_3135_ = lean_apply_4(v___x_443__overap_3134_, v___y_3121_, v___y_3122_, v___y_3123_, lean_box(0));
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3145_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3145_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3145_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3140_ = l_Array_append___redArg(v_a_3132_, v_a_3136_);
lean_dec(v_a_3136_);
v___x_3141_ = l_Lean_Doc_joinBlocks(v___x_3140_);
lean_dec_ref(v___x_3140_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3141_);
v___x_3143_ = v___x_3138_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec(v_a_3132_);
v_a_3146_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3135_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3135_);
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
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec_ref(v_subsections_3126_);
lean_dec_ref(v___f_3119_);
lean_dec_ref(v___x_3118_);
v_a_3154_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3131_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3131_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed(lean_object* v___x_3162_, lean_object* v___x_3163_, lean_object* v___x_3164_, lean_object* v___f_3165_, lean_object* v_x_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__1(v___x_3162_, v___x_3163_, v___x_3164_, v___f_3165_, v_x_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
return v_res_3171_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___f_3174_; 
v___x_3172_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3173_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3174_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3174_, 0, v___x_3173_);
lean_closure_set(v___f_3174_, 1, v___x_3172_);
return v___f_3174_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString(void){
_start:
{
lean_object* v___x_3175_; lean_object* v_toApplicative_3176_; lean_object* v_toFunctor_3177_; lean_object* v_toSeq_3178_; lean_object* v_toSeqLeft_3179_; lean_object* v_toSeqRight_3180_; lean_object* v___f_3181_; lean_object* v___f_3182_; lean_object* v___f_3183_; lean_object* v___f_3184_; lean_object* v___x_3185_; lean_object* v___f_3186_; lean_object* v___f_3187_; lean_object* v___f_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___f_3194_; lean_object* v___f_3195_; 
v___x_3175_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3176_ = lean_ctor_get(v___x_3175_, 0);
v_toFunctor_3177_ = lean_ctor_get(v_toApplicative_3176_, 0);
v_toSeq_3178_ = lean_ctor_get(v_toApplicative_3176_, 2);
v_toSeqLeft_3179_ = lean_ctor_get(v_toApplicative_3176_, 3);
v_toSeqRight_3180_ = lean_ctor_get(v_toApplicative_3176_, 4);
v___f_3181_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3182_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3177_, 2);
v___f_3183_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3183_, 0, v_toFunctor_3177_);
v___f_3184_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3184_, 0, v_toFunctor_3177_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___f_3183_);
lean_ctor_set(v___x_3185_, 1, v___f_3184_);
lean_inc(v_toSeqRight_3180_);
v___f_3186_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3186_, 0, v_toSeqRight_3180_);
lean_inc(v_toSeqLeft_3179_);
v___f_3187_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3187_, 0, v_toSeqLeft_3179_);
lean_inc(v_toSeq_3178_);
v___f_3188_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3188_, 0, v_toSeq_3178_);
v___x_3189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3185_);
lean_ctor_set(v___x_3189_, 1, v___f_3181_);
lean_ctor_set(v___x_3189_, 2, v___f_3188_);
lean_ctor_set(v___x_3189_, 3, v___f_3187_);
lean_ctor_set(v___x_3189_, 4, v___f_3186_);
v___x_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_ctor_set(v___x_3190_, 1, v___f_3182_);
v___x_3191_ = l_StateRefT_x27_instMonad___redArg(v___x_3190_);
v___x_3192_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3193_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3194_ = lean_obj_once(&l_Lean_Doc_instToMarkdownVersoDocString___closed__0, &l_Lean_Doc_instToMarkdownVersoDocString___closed__0_once, _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0);
v___f_3195_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3195_, 0, v___x_3192_);
lean_closure_set(v___f_3195_, 1, v___x_3193_);
lean_closure_set(v___f_3195_, 2, v___x_3191_);
lean_closure_set(v___f_3195_, 3, v___f_3194_);
return v___f_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0(lean_object* v___x_3196_, lean_object* v___x_3197_, lean_object* v_x_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_snd_3203_; lean_object* v_fst_3204_; lean_object* v_snd_3205_; lean_object* v___x_3206_; 
v_snd_3203_ = lean_ctor_get(v_x_3198_, 1);
lean_inc(v_snd_3203_);
v_fst_3204_ = lean_ctor_get(v_x_3198_, 0);
lean_inc(v_fst_3204_);
lean_dec_ref(v_x_3198_);
v_snd_3205_ = lean_ctor_get(v_snd_3203_, 1);
lean_inc(v_snd_3205_);
lean_dec(v_snd_3203_);
v___x_3206_ = l_Lean_Doc_partMarkdown___redArg(v___x_3196_, v___x_3197_, v_fst_3204_, v_snd_3205_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec(v_fst_3204_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_3207_, lean_object* v___x_3208_, lean_object* v_x_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_Doc_instToMarkdownSnippet___lam__0(v___x_3207_, v___x_3208_, v_x_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1(lean_object* v___x_3215_, lean_object* v___x_3216_, lean_object* v___x_3217_, lean_object* v___f_3218_, lean_object* v_x_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_text_3224_; lean_object* v_sections_3225_; lean_object* v___x_3226_; size_t v_sz_3227_; size_t v___x_3228_; lean_object* v___x_487__overap_3229_; lean_object* v___x_3230_; 
v_text_3224_ = lean_ctor_get(v_x_3219_, 0);
lean_inc_ref(v_text_3224_);
v_sections_3225_ = lean_ctor_get(v_x_3219_, 1);
lean_inc_ref(v_sections_3225_);
lean_dec_ref(v_x_3219_);
v___x_3226_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3226_, 0, lean_box(0));
lean_closure_set(v___x_3226_, 1, lean_box(0));
lean_closure_set(v___x_3226_, 2, v___x_3215_);
lean_closure_set(v___x_3226_, 3, v___x_3216_);
v_sz_3227_ = lean_array_size(v_text_3224_);
v___x_3228_ = ((size_t)0ULL);
lean_inc_ref(v___x_3217_);
v___x_487__overap_3229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3217_, v___x_3226_, v_sz_3227_, v___x_3228_, v_text_3224_);
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
lean_inc(v___y_3220_);
v___x_3230_ = lean_apply_4(v___x_487__overap_3229_, v___y_3220_, v___y_3221_, v___y_3222_, lean_box(0));
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; size_t v_sz_3232_; lean_object* v___x_490__overap_3233_; lean_object* v___x_3234_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v_sz_3232_ = lean_array_size(v_sections_3225_);
v___x_490__overap_3233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3217_, v___f_3218_, v_sz_3232_, v___x_3228_, v_sections_3225_);
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
lean_inc(v___y_3220_);
v___x_3234_ = lean_apply_4(v___x_490__overap_3233_, v___y_3220_, v___y_3221_, v___y_3222_, lean_box(0));
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3244_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3244_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3244_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3239_ = l_Array_append___redArg(v_a_3231_, v_a_3235_);
lean_dec(v_a_3235_);
v___x_3240_ = l_Lean_Doc_joinBlocks(v___x_3239_);
lean_dec_ref(v___x_3239_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3240_);
v___x_3242_ = v___x_3237_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec(v_a_3231_);
v_a_3245_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3234_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3234_);
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
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v_sections_3225_);
lean_dec_ref(v___f_3218_);
lean_dec_ref(v___x_3217_);
v_a_3253_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3230_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3230_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_3261_, lean_object* v___x_3262_, lean_object* v___x_3263_, lean_object* v___f_3264_, lean_object* v_x_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_Doc_instToMarkdownSnippet___lam__1(v___x_3261_, v___x_3262_, v___x_3263_, v___f_3264_, v_x_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
return v_res_3270_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___f_3273_; 
v___x_3271_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3272_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3273_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3273_, 0, v___x_3272_);
lean_closure_set(v___f_3273_, 1, v___x_3271_);
return v___f_3273_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet(void){
_start:
{
lean_object* v___x_3274_; lean_object* v_toApplicative_3275_; lean_object* v_toFunctor_3276_; lean_object* v_toSeq_3277_; lean_object* v_toSeqLeft_3278_; lean_object* v_toSeqRight_3279_; lean_object* v___f_3280_; lean_object* v___f_3281_; lean_object* v___f_3282_; lean_object* v___f_3283_; lean_object* v___x_3284_; lean_object* v___f_3285_; lean_object* v___f_3286_; lean_object* v___f_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___f_3293_; lean_object* v___f_3294_; 
v___x_3274_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3275_ = lean_ctor_get(v___x_3274_, 0);
v_toFunctor_3276_ = lean_ctor_get(v_toApplicative_3275_, 0);
v_toSeq_3277_ = lean_ctor_get(v_toApplicative_3275_, 2);
v_toSeqLeft_3278_ = lean_ctor_get(v_toApplicative_3275_, 3);
v_toSeqRight_3279_ = lean_ctor_get(v_toApplicative_3275_, 4);
v___f_3280_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3281_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3276_, 2);
v___f_3282_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3282_, 0, v_toFunctor_3276_);
v___f_3283_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3283_, 0, v_toFunctor_3276_);
v___x_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___f_3282_);
lean_ctor_set(v___x_3284_, 1, v___f_3283_);
lean_inc(v_toSeqRight_3279_);
v___f_3285_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3285_, 0, v_toSeqRight_3279_);
lean_inc(v_toSeqLeft_3278_);
v___f_3286_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3286_, 0, v_toSeqLeft_3278_);
lean_inc(v_toSeq_3277_);
v___f_3287_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3287_, 0, v_toSeq_3277_);
v___x_3288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3284_);
lean_ctor_set(v___x_3288_, 1, v___f_3280_);
lean_ctor_set(v___x_3288_, 2, v___f_3287_);
lean_ctor_set(v___x_3288_, 3, v___f_3286_);
lean_ctor_set(v___x_3288_, 4, v___f_3285_);
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
lean_ctor_set(v___x_3289_, 1, v___f_3281_);
v___x_3290_ = l_StateRefT_x27_instMonad___redArg(v___x_3289_);
v___x_3291_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3292_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3293_ = lean_obj_once(&l_Lean_Doc_instToMarkdownSnippet___closed__0, &l_Lean_Doc_instToMarkdownSnippet___closed__0_once, _init_l_Lean_Doc_instToMarkdownSnippet___closed__0);
v___f_3294_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3294_, 0, v___x_3291_);
lean_closure_set(v___f_3294_, 1, v___x_3292_);
lean_closure_set(v___f_3294_, 2, v___x_3290_);
lean_closure_set(v___f_3294_, 3, v___f_3293_);
return v___f_3294_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(lean_object* v_opts_3295_, lean_object* v_opt_3296_){
_start:
{
lean_object* v_name_3297_; lean_object* v_defValue_3298_; lean_object* v_map_3299_; lean_object* v___x_3300_; 
v_name_3297_ = lean_ctor_get(v_opt_3296_, 0);
v_defValue_3298_ = lean_ctor_get(v_opt_3296_, 1);
v_map_3299_ = lean_ctor_get(v_opts_3295_, 0);
v___x_3300_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3299_, v_name_3297_);
if (lean_obj_tag(v___x_3300_) == 0)
{
uint8_t v___x_3301_; 
v___x_3301_ = lean_unbox(v_defValue_3298_);
return v___x_3301_;
}
else
{
lean_object* v_val_3302_; 
v_val_3302_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_val_3302_);
lean_dec_ref_known(v___x_3300_, 1);
if (lean_obj_tag(v_val_3302_) == 1)
{
uint8_t v_v_3303_; 
v_v_3303_ = lean_ctor_get_uint8(v_val_3302_, 0);
lean_dec_ref_known(v_val_3302_, 0);
return v_v_3303_;
}
else
{
uint8_t v___x_3304_; 
lean_dec(v_val_3302_);
v___x_3304_ = lean_unbox(v_defValue_3298_);
return v___x_3304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0___boxed(lean_object* v_opts_3305_, lean_object* v_opt_3306_){
_start:
{
uint8_t v_res_3307_; lean_object* v_r_3308_; 
v_res_3307_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_opts_3305_, v_opt_3306_);
lean_dec_ref(v_opt_3306_);
lean_dec_ref(v_opts_3305_);
v_r_3308_ = lean_box(v_res_3307_);
return v_r_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(lean_object* v_opts_3309_, lean_object* v_opt_3310_){
_start:
{
lean_object* v_name_3311_; lean_object* v_defValue_3312_; lean_object* v_map_3313_; lean_object* v___x_3314_; 
v_name_3311_ = lean_ctor_get(v_opt_3310_, 0);
v_defValue_3312_ = lean_ctor_get(v_opt_3310_, 1);
v_map_3313_ = lean_ctor_get(v_opts_3309_, 0);
v___x_3314_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3313_, v_name_3311_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_inc(v_defValue_3312_);
return v_defValue_3312_;
}
else
{
lean_object* v_val_3315_; 
v_val_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_val_3315_);
lean_dec_ref_known(v___x_3314_, 1);
if (lean_obj_tag(v_val_3315_) == 3)
{
lean_object* v_v_3316_; 
v_v_3316_ = lean_ctor_get(v_val_3315_, 0);
lean_inc(v_v_3316_);
lean_dec_ref_known(v_val_3315_, 1);
return v_v_3316_;
}
else
{
lean_dec(v_val_3315_);
lean_inc(v_defValue_3312_);
return v_defValue_3312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1___boxed(lean_object* v_opts_3317_, lean_object* v_opt_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(v_opts_3317_, v_opt_3318_);
lean_dec_ref(v_opt_3318_);
lean_dec_ref(v_opts_3317_);
return v_res_3319_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3320_ = lean_unsigned_to_nat(32u);
v___x_3321_ = lean_mk_empty_array_with_capacity(v___x_3320_);
v___x_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__1(void){
_start:
{
size_t v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3323_ = ((size_t)5ULL);
v___x_3324_ = lean_unsigned_to_nat(0u);
v___x_3325_ = lean_unsigned_to_nat(32u);
v___x_3326_ = lean_mk_empty_array_with_capacity(v___x_3325_);
v___x_3327_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__0, &l_Lean_Doc_runMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__0);
v___x_3328_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
lean_ctor_set(v___x_3328_, 1, v___x_3326_);
lean_ctor_set(v___x_3328_, 2, v___x_3324_);
lean_ctor_set(v___x_3328_, 3, v___x_3324_);
lean_ctor_set_usize(v___x_3328_, 4, v___x_3323_);
return v___x_3328_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__2(void){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3329_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__3(void){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__2, &l_Lean_Doc_runMarkdown___redArg___closed__2_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__2);
v___x_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
return v___x_3331_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__4(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__3, &l_Lean_Doc_runMarkdown___redArg___closed__3_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__3);
v___x_3333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
return v___x_3333_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__5(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3334_ = l_Lean_NameSet_empty;
v___x_3335_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
lean_ctor_set(v___x_3336_, 2, v___x_3334_);
return v___x_3336_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__6(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = lean_unsigned_to_nat(1u);
v___x_3338_ = l_Lean_firstFrontendMacroScope;
v___x_3339_ = lean_nat_add(v___x_3338_, v___x_3337_);
return v___x_3339_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__11(void){
_start:
{
lean_object* v___x_3350_; uint64_t v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3351_ = 0ULL;
v___x_3352_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set_uint64(v___x_3352_, sizeof(void*)*1, v___x_3351_);
return v___x_3352_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__12(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; 
v___x_3353_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3354_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__3, &l_Lean_Doc_runMarkdown___redArg___closed__3_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__3);
v___x_3355_ = 1;
v___x_3356_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3356_, 0, v___x_3354_);
lean_ctor_set(v___x_3356_, 1, v___x_3354_);
lean_ctor_set(v___x_3356_, 2, v___x_3353_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*3, v___x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg(lean_object* v_env_3363_, lean_object* v_act_3364_, lean_object* v_options_3365_, lean_object* v_currNamespace_3366_, lean_object* v_openDecls_3367_, lean_object* v_cancelTk_x3f_3368_){
_start:
{
lean_object* v_a_3371_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v_env_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; lean_object* v_fileName_3401_; lean_object* v_fileMap_3402_; lean_object* v_currRecDepth_3403_; lean_object* v_ref_3404_; lean_object* v_currNamespace_3405_; lean_object* v_openDecls_3406_; lean_object* v_initHeartbeats_3407_; lean_object* v_maxHeartbeats_3408_; lean_object* v_quotContext_3409_; lean_object* v_currMacroScope_3410_; lean_object* v_cancelTk_x3f_3411_; uint8_t v_suppressElabErrors_3412_; lean_object* v_inheritedTraceOptions_3413_; lean_object* v___y_3414_; uint8_t v___y_3451_; uint8_t v___x_3472_; 
v___x_3374_ = lean_unsigned_to_nat(0u);
v___x_3375_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__4, &l_Lean_Doc_runMarkdown___redArg___closed__4_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__4);
v___x_3376_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__5, &l_Lean_Doc_runMarkdown___redArg___closed__5_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__5);
v___x_3377_ = lean_io_get_num_heartbeats();
v___x_3378_ = l_Lean_firstFrontendMacroScope;
v___x_3379_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__6, &l_Lean_Doc_runMarkdown___redArg___closed__6_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__6);
v___x_3380_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__9));
v___x_3381_ = lean_box(0);
v___x_3382_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__10));
v___x_3383_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__11, &l_Lean_Doc_runMarkdown___redArg___closed__11_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__11);
v___x_3384_ = 1;
v___x_3385_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__12, &l_Lean_Doc_runMarkdown___redArg___closed__12_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__12);
v___x_3386_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__13));
v___x_3387_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3387_, 0, v_env_3363_);
lean_ctor_set(v___x_3387_, 1, v___x_3379_);
lean_ctor_set(v___x_3387_, 2, v___x_3380_);
lean_ctor_set(v___x_3387_, 3, v___x_3382_);
lean_ctor_set(v___x_3387_, 4, v___x_3383_);
lean_ctor_set(v___x_3387_, 5, v___x_3375_);
lean_ctor_set(v___x_3387_, 6, v___x_3376_);
lean_ctor_set(v___x_3387_, 7, v___x_3385_);
lean_ctor_set(v___x_3387_, 8, v___x_3386_);
v___x_3388_ = lean_st_mk_ref(v___x_3387_);
v___x_3389_ = l_Lean_inheritedTraceOptions;
v___x_3390_ = lean_st_ref_get(v___x_3389_);
v___x_3391_ = lean_st_ref_get(v___x_3388_);
v_env_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc_ref(v_env_3392_);
lean_dec(v___x_3391_);
v___x_3393_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__14));
v___x_3394_ = l_Lean_instInhabitedFileMap_default;
v___x_3395_ = lean_box(0);
v___x_3396_ = l_Lean_Core_getMaxHeartbeats(v_options_3365_);
v___x_3397_ = 0;
v___x_3398_ = l_Lean_diagnostics;
v___x_3399_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_options_3365_, v___x_3398_);
v___x_3472_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3392_);
lean_dec_ref(v_env_3392_);
if (v___x_3472_ == 0)
{
if (v___x_3399_ == 0)
{
v___y_3451_ = v___x_3384_;
goto v___jp_3450_;
}
else
{
v___y_3451_ = v___x_3472_;
goto v___jp_3450_;
}
}
else
{
v___y_3451_ = v___x_3399_;
goto v___jp_3450_;
}
v___jp_3370_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = lean_mk_io_user_error(v_a_3371_);
v___x_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
return v___x_3373_;
}
v___jp_3400_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3415_ = l_Lean_maxRecDepth;
v___x_3416_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__1(v_options_3365_, v___x_3415_);
lean_inc(v_currMacroScope_3410_);
lean_inc(v_quotContext_3409_);
lean_inc(v_ref_3404_);
lean_inc_ref(v_fileMap_3402_);
lean_inc_ref(v_fileName_3401_);
v___x_3417_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3417_, 0, v_fileName_3401_);
lean_ctor_set(v___x_3417_, 1, v_fileMap_3402_);
lean_ctor_set(v___x_3417_, 2, v_options_3365_);
lean_ctor_set(v___x_3417_, 3, v_currRecDepth_3403_);
lean_ctor_set(v___x_3417_, 4, v___x_3416_);
lean_ctor_set(v___x_3417_, 5, v_ref_3404_);
lean_ctor_set(v___x_3417_, 6, v_currNamespace_3405_);
lean_ctor_set(v___x_3417_, 7, v_openDecls_3406_);
lean_ctor_set(v___x_3417_, 8, v_initHeartbeats_3407_);
lean_ctor_set(v___x_3417_, 9, v_maxHeartbeats_3408_);
lean_ctor_set(v___x_3417_, 10, v_quotContext_3409_);
lean_ctor_set(v___x_3417_, 11, v_currMacroScope_3410_);
lean_ctor_set(v___x_3417_, 12, v_cancelTk_x3f_3411_);
lean_ctor_set(v___x_3417_, 13, v_inheritedTraceOptions_3413_);
lean_ctor_set_uint8(v___x_3417_, sizeof(void*)*14, v___x_3399_);
lean_ctor_set_uint8(v___x_3417_, sizeof(void*)*14 + 1, v_suppressElabErrors_3412_);
v___x_3418_ = lean_apply_3(v_act_3364_, v___x_3417_, v___y_3414_, lean_box(0));
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3427_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3427_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3427_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3423_ = lean_st_ref_get(v___x_3388_);
lean_dec(v___x_3388_);
lean_dec(v___x_3423_);
if (v_isShared_3422_ == 0)
{
v___x_3425_ = v___x_3421_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3419_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3449_; 
lean_dec(v___x_3388_);
v_a_3428_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3430_ = v___x_3418_;
v_isShared_3431_ = v_isSharedCheck_3449_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3418_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3449_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
if (lean_obj_tag(v_a_3428_) == 0)
{
lean_object* v_msg_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
v_msg_3432_ = lean_ctor_get(v_a_3428_, 1);
lean_inc_ref(v_msg_3432_);
lean_dec_ref_known(v_a_3428_, 2);
v___x_3433_ = l_Lean_MessageData_toString(v_msg_3432_);
v___x_3434_ = lean_mk_io_user_error(v___x_3433_);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3434_);
v___x_3436_ = v___x_3430_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
else
{
lean_object* v_id_3438_; lean_object* v___x_3439_; 
lean_del_object(v___x_3430_);
v_id_3438_ = lean_ctor_get(v_a_3428_, 0);
lean_inc(v_id_3438_);
lean_dec_ref_known(v_a_3428_, 2);
v___x_3439_ = l_Lean_InternalExceptionId_getName(v_id_3438_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_dec(v_id_3438_);
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3439_, 1);
v___x_3441_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__15));
v___x_3442_ = l_Lean_Name_toString(v_a_3440_, v___x_3384_);
v___x_3443_ = lean_string_append(v___x_3441_, v___x_3442_);
lean_dec_ref(v___x_3442_);
v_a_3371_ = v___x_3443_;
goto v___jp_3370_;
}
else
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_dec_ref_known(v___x_3439_, 1);
v___x_3444_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__16));
v___x_3445_ = l_Nat_reprFast(v_id_3438_);
v___x_3446_ = lean_string_append(v___x_3444_, v___x_3445_);
lean_dec_ref(v___x_3445_);
v___x_3447_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__17));
v___x_3448_ = lean_string_append(v___x_3446_, v___x_3447_);
v_a_3371_ = v___x_3448_;
goto v___jp_3370_;
}
}
}
}
}
v___jp_3450_:
{
uint8_t v___x_3452_; 
v___x_3452_ = lean_bool_not(v___y_3451_);
if (v___x_3452_ == 0)
{
lean_inc(v___x_3388_);
v_fileName_3401_ = v___x_3393_;
v_fileMap_3402_ = v___x_3394_;
v_currRecDepth_3403_ = v___x_3374_;
v_ref_3404_ = v___x_3395_;
v_currNamespace_3405_ = v_currNamespace_3366_;
v_openDecls_3406_ = v_openDecls_3367_;
v_initHeartbeats_3407_ = v___x_3377_;
v_maxHeartbeats_3408_ = v___x_3396_;
v_quotContext_3409_ = v___x_3381_;
v_currMacroScope_3410_ = v___x_3378_;
v_cancelTk_x3f_3411_ = v_cancelTk_x3f_3368_;
v_suppressElabErrors_3412_ = v___x_3397_;
v_inheritedTraceOptions_3413_ = v___x_3390_;
v___y_3414_ = v___x_3388_;
goto v___jp_3400_;
}
else
{
lean_object* v___x_3453_; lean_object* v_env_3454_; lean_object* v_nextMacroScope_3455_; lean_object* v_ngen_3456_; lean_object* v_auxDeclNGen_3457_; lean_object* v_traceState_3458_; lean_object* v_messages_3459_; lean_object* v_infoState_3460_; lean_object* v_snapshotTasks_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3470_; 
v___x_3453_ = lean_st_ref_take(v___x_3388_);
v_env_3454_ = lean_ctor_get(v___x_3453_, 0);
v_nextMacroScope_3455_ = lean_ctor_get(v___x_3453_, 1);
v_ngen_3456_ = lean_ctor_get(v___x_3453_, 2);
v_auxDeclNGen_3457_ = lean_ctor_get(v___x_3453_, 3);
v_traceState_3458_ = lean_ctor_get(v___x_3453_, 4);
v_messages_3459_ = lean_ctor_get(v___x_3453_, 6);
v_infoState_3460_ = lean_ctor_get(v___x_3453_, 7);
v_snapshotTasks_3461_ = lean_ctor_get(v___x_3453_, 8);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3470_ == 0)
{
lean_object* v_unused_3471_; 
v_unused_3471_ = lean_ctor_get(v___x_3453_, 5);
lean_dec(v_unused_3471_);
v___x_3463_ = v___x_3453_;
v_isShared_3464_ = v_isSharedCheck_3470_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_snapshotTasks_3461_);
lean_inc(v_infoState_3460_);
lean_inc(v_messages_3459_);
lean_inc(v_traceState_3458_);
lean_inc(v_auxDeclNGen_3457_);
lean_inc(v_ngen_3456_);
lean_inc(v_nextMacroScope_3455_);
lean_inc(v_env_3454_);
lean_dec(v___x_3453_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3470_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3465_ = l_Lean_Kernel_enableDiag(v_env_3454_, v___x_3399_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 5, v___x_3375_);
lean_ctor_set(v___x_3463_, 0, v___x_3465_);
v___x_3467_ = v___x_3463_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_nextMacroScope_3455_);
lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_ngen_3456_);
lean_ctor_set(v_reuseFailAlloc_3469_, 3, v_auxDeclNGen_3457_);
lean_ctor_set(v_reuseFailAlloc_3469_, 4, v_traceState_3458_);
lean_ctor_set(v_reuseFailAlloc_3469_, 5, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3469_, 6, v_messages_3459_);
lean_ctor_set(v_reuseFailAlloc_3469_, 7, v_infoState_3460_);
lean_ctor_set(v_reuseFailAlloc_3469_, 8, v_snapshotTasks_3461_);
v___x_3467_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3468_; 
v___x_3468_ = lean_st_ref_set(v___x_3388_, v___x_3467_);
lean_inc(v___x_3388_);
v_fileName_3401_ = v___x_3393_;
v_fileMap_3402_ = v___x_3394_;
v_currRecDepth_3403_ = v___x_3374_;
v_ref_3404_ = v___x_3395_;
v_currNamespace_3405_ = v_currNamespace_3366_;
v_openDecls_3406_ = v_openDecls_3367_;
v_initHeartbeats_3407_ = v___x_3377_;
v_maxHeartbeats_3408_ = v___x_3396_;
v_quotContext_3409_ = v___x_3381_;
v_currMacroScope_3410_ = v___x_3378_;
v_cancelTk_x3f_3411_ = v_cancelTk_x3f_3368_;
v_suppressElabErrors_3412_ = v___x_3397_;
v_inheritedTraceOptions_3413_ = v___x_3390_;
v___y_3414_ = v___x_3388_;
goto v___jp_3400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg___boxed(lean_object* v_env_3473_, lean_object* v_act_3474_, lean_object* v_options_3475_, lean_object* v_currNamespace_3476_, lean_object* v_openDecls_3477_, lean_object* v_cancelTk_x3f_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_Doc_runMarkdown___redArg(v_env_3473_, v_act_3474_, v_options_3475_, v_currNamespace_3476_, v_openDecls_3477_, v_cancelTk_x3f_3478_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown(lean_object* v_00_u03b1_3481_, lean_object* v_env_3482_, lean_object* v_act_3483_, lean_object* v_options_3484_, lean_object* v_currNamespace_3485_, lean_object* v_openDecls_3486_, lean_object* v_cancelTk_x3f_3487_){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = l_Lean_Doc_runMarkdown___redArg(v_env_3482_, v_act_3483_, v_options_3484_, v_currNamespace_3485_, v_openDecls_3486_, v_cancelTk_x3f_3487_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___boxed(lean_object* v_00_u03b1_3490_, lean_object* v_env_3491_, lean_object* v_act_3492_, lean_object* v_options_3493_, lean_object* v_currNamespace_3494_, lean_object* v_openDecls_3495_, lean_object* v_cancelTk_x3f_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Lean_Doc_runMarkdown(v_00_u03b1_3490_, v_env_3491_, v_act_3492_, v_options_3493_, v_currNamespace_3494_, v_openDecls_3495_, v_cancelTk_x3f_3496_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(lean_object* v_x_3499_, size_t v_sz_3500_, size_t v_i_3501_, lean_object* v_bs_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
uint8_t v___x_3507_; 
v___x_3507_ = lean_usize_dec_lt(v_i_3501_, v_sz_3500_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
lean_dec_ref(v_x_3499_);
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_bs_3502_);
return v___x_3508_;
}
else
{
lean_object* v_v_3509_; lean_object* v___x_3510_; 
v_v_3509_ = lean_array_uget_borrowed(v_bs_3502_, v_i_3501_);
lean_inc(v_v_3509_);
lean_inc_ref(v_x_3499_);
v___x_3510_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3499_, v_v_3509_, v___y_3503_, v___y_3504_, v___y_3505_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___x_3512_; lean_object* v_bs_x27_3513_; size_t v___x_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v___x_3510_, 1);
v___x_3512_ = lean_unsigned_to_nat(0u);
v_bs_x27_3513_ = lean_array_uset(v_bs_3502_, v_i_3501_, v___x_3512_);
v___x_3514_ = ((size_t)1ULL);
v___x_3515_ = lean_usize_add(v_i_3501_, v___x_3514_);
v___x_3516_ = lean_array_uset(v_bs_x27_3513_, v_i_3501_, v_a_3511_);
v_i_3501_ = v___x_3515_;
v_bs_3502_ = v___x_3516_;
goto _start;
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v_bs_3502_);
lean_dec_ref(v_x_3499_);
v_a_3518_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3510_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3510_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed(lean_object* v_x_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(v_x_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(lean_object* v_x_3535_, size_t v_sz_3536_, size_t v___x_3537_, lean_object* v_content_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3535_, v_sz_3536_, v___x_3537_, v_content_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3552_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3546_ = v___x_3543_;
v_isShared_3547_ = v_isSharedCheck_3552_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3552_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3548_; lean_object* v___x_3550_; 
v___x_3548_ = l_Lean_Doc_joinInlines(v_a_3544_);
lean_dec(v_a_3544_);
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 0, v___x_3548_);
v___x_3550_ = v___x_3546_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
v_a_3553_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3543_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3543_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed(lean_object* v_x_3561_, lean_object* v_sz_3562_, lean_object* v___x_3563_, lean_object* v_content_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
size_t v_sz_boxed_3569_; size_t v___x_3977__boxed_3570_; lean_object* v_res_3571_; 
v_sz_boxed_3569_ = lean_unbox_usize(v_sz_3562_);
lean_dec(v_sz_3562_);
v___x_3977__boxed_3570_ = lean_unbox_usize(v___x_3563_);
lean_dec(v___x_3563_);
v_res_3571_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(v_x_3561_, v_sz_boxed_3569_, v___x_3977__boxed_3570_, v_content_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(lean_object* v_x_3572_, lean_object* v_x_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v_pieces_3579_; lean_object* v_pieces_3583_; 
switch(lean_obj_tag(v_x_3573_))
{
case 0:
{
lean_object* v_string_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
lean_dec_ref(v_x_3572_);
v_string_3586_ = lean_ctor_get(v_x_3573_, 0);
lean_inc_ref(v_string_3586_);
lean_dec_ref_known(v_x_3573_, 1);
v___x_3587_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_3586_);
lean_dec_ref(v_string_3586_);
v___x_3588_ = lean_unsigned_to_nat(1u);
v___x_3589_ = lean_mk_empty_array_with_capacity(v___x_3588_);
v___x_3590_ = lean_array_push(v___x_3589_, v___x_3587_);
v___x_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3590_);
return v___x_3591_;
}
case 1:
{
lean_object* v_content_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3651_; 
v_content_3592_ = lean_ctor_get(v_x_3573_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v_x_3573_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3594_ = v_x_3573_;
v_isShared_3595_ = v_isSharedCheck_3651_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_content_3592_);
lean_dec(v_x_3573_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3651_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set_tag(v___x_3594_, 9);
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_content_3592_);
v___x_3597_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; lean_object* v_snd_3599_; lean_object* v_fst_3600_; lean_object* v_fst_3601_; lean_object* v_snd_3602_; lean_object* v_pieces_3604_; uint8_t v_inEmph_3613_; uint8_t v_inBold_3614_; uint8_t v_inLink_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3649_; 
v___x_3598_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3597_);
v_snd_3599_ = lean_ctor_get(v___x_3598_, 1);
lean_inc(v_snd_3599_);
v_fst_3600_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_fst_3600_);
lean_dec_ref(v___x_3598_);
v_fst_3601_ = lean_ctor_get(v_snd_3599_, 0);
lean_inc(v_fst_3601_);
v_snd_3602_ = lean_ctor_get(v_snd_3599_, 1);
lean_inc(v_snd_3602_);
lean_dec(v_snd_3599_);
v_inEmph_3613_ = lean_ctor_get_uint8(v_x_3572_, 0);
v_inBold_3614_ = lean_ctor_get_uint8(v_x_3572_, 1);
v_inLink_3615_ = lean_ctor_get_uint8(v_x_3572_, 2);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_x_3572_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3617_ = v_x_3572_;
v_isShared_3618_ = v_isSharedCheck_3649_;
goto v_resetjp_3616_;
}
else
{
lean_dec(v_x_3572_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3649_;
goto v_resetjp_3616_;
}
v___jp_3603_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; uint8_t v___x_3608_; 
v___x_3605_ = lean_string_utf8_byte_size(v_snd_3602_);
v___x_3606_ = lean_unsigned_to_nat(0u);
v___x_3607_ = lean_nat_dec_eq(v___x_3605_, v___x_3606_);
v___x_3608_ = lean_bool_not(v___x_3607_);
if (v___x_3608_ == 0)
{
lean_dec(v_snd_3602_);
v_pieces_3583_ = v_pieces_3604_;
goto v___jp_3582_;
}
else
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3609_ = lean_unsigned_to_nat(1u);
v___x_3610_ = lean_mk_empty_array_with_capacity(v___x_3609_);
v___x_3611_ = lean_array_push(v___x_3610_, v_snd_3602_);
v___x_3612_ = lean_array_push(v_pieces_3604_, v___x_3611_);
v_pieces_3583_ = v___x_3612_;
goto v___jp_3582_;
}
}
v_resetjp_3616_:
{
uint8_t v___x_3619_; lean_object* v___x_3621_; 
v___x_3619_ = 1;
if (v_isShared_3618_ == 0)
{
v___x_3621_ = v___x_3617_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3648_, 1, v_inBold_3614_);
lean_ctor_set_uint8(v_reuseFailAlloc_3648_, 2, v_inLink_3615_);
v___x_3621_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3622_; 
lean_ctor_set_uint8(v___x_3621_, 0, v___x_3619_);
v___x_3622_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3621_, v_fst_3601_, v_a_3574_, v_a_3575_, v_a_3576_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v_pieces_3625_; lean_object* v_pieces_3633_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; uint8_t v___x_3643_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3622_, 1);
v___x_3639_ = lean_unsigned_to_nat(0u);
v___x_3640_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3641_ = lean_string_utf8_byte_size(v_fst_3600_);
v___x_3642_ = lean_nat_dec_eq(v___x_3641_, v___x_3639_);
v___x_3643_ = lean_bool_not(v___x_3642_);
if (v___x_3643_ == 0)
{
lean_dec(v_fst_3600_);
v_pieces_3633_ = v___x_3640_;
goto v___jp_3632_;
}
else
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3644_ = lean_unsigned_to_nat(1u);
v___x_3645_ = lean_mk_empty_array_with_capacity(v___x_3644_);
v___x_3646_ = lean_array_push(v___x_3645_, v_fst_3600_);
v___x_3647_ = lean_array_push(v___x_3640_, v___x_3646_);
v_pieces_3633_ = v___x_3647_;
goto v___jp_3632_;
}
v___jp_3624_:
{
lean_object* v___x_3626_; uint8_t v___x_3627_; 
v___x_3626_ = lean_array_push(v_pieces_3625_, v_a_3623_);
v___x_3627_ = lean_bool_not(v_inEmph_3613_);
if (v___x_3627_ == 0)
{
v_pieces_3604_ = v___x_3626_;
goto v___jp_3603_;
}
else
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3628_ = lean_unsigned_to_nat(1u);
v___x_3629_ = lean_mk_empty_array_with_capacity(v___x_3628_);
lean_dec_ref(v___x_3629_);
v___x_3630_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3631_ = lean_array_push(v___x_3626_, v___x_3630_);
v_pieces_3604_ = v___x_3631_;
goto v___jp_3603_;
}
}
v___jp_3632_:
{
uint8_t v___x_3634_; 
v___x_3634_ = lean_bool_not(v_inEmph_3613_);
if (v___x_3634_ == 0)
{
v_pieces_3625_ = v_pieces_3633_;
goto v___jp_3624_;
}
else
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3635_ = lean_unsigned_to_nat(1u);
v___x_3636_ = lean_mk_empty_array_with_capacity(v___x_3635_);
lean_dec_ref(v___x_3636_);
v___x_3637_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3638_ = lean_array_push(v_pieces_3633_, v___x_3637_);
v_pieces_3625_ = v___x_3638_;
goto v___jp_3624_;
}
}
}
else
{
lean_dec(v_snd_3602_);
lean_dec(v_fst_3600_);
return v___x_3622_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3711_; 
v_content_3652_ = lean_ctor_get(v_x_3573_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_x_3573_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3654_ = v_x_3573_;
v_isShared_3655_ = v_isSharedCheck_3711_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_content_3652_);
lean_dec(v_x_3573_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3711_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set_tag(v___x_3654_, 9);
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_content_3652_);
v___x_3657_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3658_; lean_object* v_snd_3659_; lean_object* v_fst_3660_; lean_object* v_fst_3661_; lean_object* v_snd_3662_; lean_object* v_pieces_3664_; uint8_t v_inEmph_3673_; uint8_t v_inBold_3674_; uint8_t v_inLink_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3709_; 
v___x_3658_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3657_);
v_snd_3659_ = lean_ctor_get(v___x_3658_, 1);
lean_inc(v_snd_3659_);
v_fst_3660_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_fst_3660_);
lean_dec_ref(v___x_3658_);
v_fst_3661_ = lean_ctor_get(v_snd_3659_, 0);
lean_inc(v_fst_3661_);
v_snd_3662_ = lean_ctor_get(v_snd_3659_, 1);
lean_inc(v_snd_3662_);
lean_dec(v_snd_3659_);
v_inEmph_3673_ = lean_ctor_get_uint8(v_x_3572_, 0);
v_inBold_3674_ = lean_ctor_get_uint8(v_x_3572_, 1);
v_inLink_3675_ = lean_ctor_get_uint8(v_x_3572_, 2);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_x_3572_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3677_ = v_x_3572_;
v_isShared_3678_ = v_isSharedCheck_3709_;
goto v_resetjp_3676_;
}
else
{
lean_dec(v_x_3572_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3709_;
goto v_resetjp_3676_;
}
v___jp_3663_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; uint8_t v___x_3668_; 
v___x_3665_ = lean_string_utf8_byte_size(v_snd_3662_);
v___x_3666_ = lean_unsigned_to_nat(0u);
v___x_3667_ = lean_nat_dec_eq(v___x_3665_, v___x_3666_);
v___x_3668_ = lean_bool_not(v___x_3667_);
if (v___x_3668_ == 0)
{
lean_dec(v_snd_3662_);
v_pieces_3579_ = v_pieces_3664_;
goto v___jp_3578_;
}
else
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3669_ = lean_unsigned_to_nat(1u);
v___x_3670_ = lean_mk_empty_array_with_capacity(v___x_3669_);
v___x_3671_ = lean_array_push(v___x_3670_, v_snd_3662_);
v___x_3672_ = lean_array_push(v_pieces_3664_, v___x_3671_);
v_pieces_3579_ = v___x_3672_;
goto v___jp_3578_;
}
}
v_resetjp_3676_:
{
uint8_t v___x_3679_; lean_object* v___x_3681_; 
v___x_3679_ = 1;
if (v_isShared_3678_ == 0)
{
v___x_3681_ = v___x_3677_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3708_, 0, v_inEmph_3673_);
lean_ctor_set_uint8(v_reuseFailAlloc_3708_, 2, v_inLink_3675_);
v___x_3681_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3682_; 
lean_ctor_set_uint8(v___x_3681_, 1, v___x_3679_);
v___x_3682_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3681_, v_fst_3661_, v_a_3574_, v_a_3575_, v_a_3576_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v_pieces_3685_; lean_object* v_pieces_3693_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; uint8_t v___x_3702_; uint8_t v___x_3703_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
lean_dec_ref_known(v___x_3682_, 1);
v___x_3699_ = lean_unsigned_to_nat(0u);
v___x_3700_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3701_ = lean_string_utf8_byte_size(v_fst_3660_);
v___x_3702_ = lean_nat_dec_eq(v___x_3701_, v___x_3699_);
v___x_3703_ = lean_bool_not(v___x_3702_);
if (v___x_3703_ == 0)
{
lean_dec(v_fst_3660_);
v_pieces_3693_ = v___x_3700_;
goto v___jp_3692_;
}
else
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3704_ = lean_unsigned_to_nat(1u);
v___x_3705_ = lean_mk_empty_array_with_capacity(v___x_3704_);
v___x_3706_ = lean_array_push(v___x_3705_, v_fst_3660_);
v___x_3707_ = lean_array_push(v___x_3700_, v___x_3706_);
v_pieces_3693_ = v___x_3707_;
goto v___jp_3692_;
}
v___jp_3684_:
{
lean_object* v___x_3686_; uint8_t v___x_3687_; 
v___x_3686_ = lean_array_push(v_pieces_3685_, v_a_3683_);
v___x_3687_ = lean_bool_not(v_inBold_3674_);
if (v___x_3687_ == 0)
{
v_pieces_3664_ = v___x_3686_;
goto v___jp_3663_;
}
else
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3688_ = lean_unsigned_to_nat(1u);
v___x_3689_ = lean_mk_empty_array_with_capacity(v___x_3688_);
lean_dec_ref(v___x_3689_);
v___x_3690_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3691_ = lean_array_push(v___x_3686_, v___x_3690_);
v_pieces_3664_ = v___x_3691_;
goto v___jp_3663_;
}
}
v___jp_3692_:
{
uint8_t v___x_3694_; 
v___x_3694_ = lean_bool_not(v_inBold_3674_);
if (v___x_3694_ == 0)
{
v_pieces_3685_ = v_pieces_3693_;
goto v___jp_3684_;
}
else
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3695_ = lean_unsigned_to_nat(1u);
v___x_3696_ = lean_mk_empty_array_with_capacity(v___x_3695_);
lean_dec_ref(v___x_3696_);
v___x_3697_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3698_ = lean_array_push(v_pieces_3693_, v___x_3697_);
v_pieces_3685_ = v___x_3698_;
goto v___jp_3684_;
}
}
}
else
{
lean_dec(v_snd_3662_);
lean_dec(v_fst_3660_);
return v___x_3682_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
lean_dec_ref(v_x_3572_);
v_string_3712_ = lean_ctor_get(v_x_3573_, 0);
lean_inc_ref(v_string_3712_);
lean_dec_ref_known(v_x_3573_, 1);
v___x_3713_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_3712_);
v___x_3714_ = lean_unsigned_to_nat(1u);
v___x_3715_ = lean_mk_empty_array_with_capacity(v___x_3714_);
v___x_3716_ = lean_array_push(v___x_3715_, v___x_3713_);
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
return v___x_3717_;
}
case 4:
{
uint8_t v_mode_3718_; 
lean_dec_ref(v_x_3572_);
v_mode_3718_ = lean_ctor_get_uint8(v_x_3573_, sizeof(void*)*1);
if (v_mode_3718_ == 0)
{
lean_object* v_string_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v_string_3719_ = lean_ctor_get(v_x_3573_, 0);
lean_inc_ref(v_string_3719_);
lean_dec_ref_known(v_x_3573_, 1);
v___x_3720_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_3721_ = lean_string_append(v___x_3720_, v_string_3719_);
lean_dec_ref(v_string_3719_);
v___x_3722_ = lean_string_append(v___x_3721_, v___x_3720_);
v___x_3723_ = lean_unsigned_to_nat(1u);
v___x_3724_ = lean_mk_empty_array_with_capacity(v___x_3723_);
v___x_3725_ = lean_array_push(v___x_3724_, v___x_3722_);
v___x_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
return v___x_3726_;
}
else
{
lean_object* v_string_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v_string_3727_ = lean_ctor_get(v_x_3573_, 0);
lean_inc_ref(v_string_3727_);
lean_dec_ref_known(v_x_3573_, 1);
v___x_3728_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_3729_ = lean_string_append(v___x_3728_, v_string_3727_);
lean_dec_ref(v_string_3727_);
v___x_3730_ = lean_string_append(v___x_3729_, v___x_3728_);
v___x_3731_ = lean_unsigned_to_nat(1u);
v___x_3732_ = lean_mk_empty_array_with_capacity(v___x_3731_);
v___x_3733_ = lean_array_push(v___x_3732_, v___x_3730_);
v___x_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
return v___x_3734_;
}
}
case 5:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
lean_dec_ref_known(v_x_3573_, 1);
lean_dec_ref(v_x_3572_);
v___x_3735_ = lean_unsigned_to_nat(2u);
v___x_3736_ = lean_mk_empty_array_with_capacity(v___x_3735_);
lean_dec_ref(v___x_3736_);
v___x_3737_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
return v___x_3738_;
}
case 6:
{
uint8_t v_inLink_3739_; 
v_inLink_3739_ = lean_ctor_get_uint8(v_x_3572_, 2);
if (v_inLink_3739_ == 0)
{
lean_object* v_content_3740_; lean_object* v_url_3741_; uint8_t v_inEmph_3742_; uint8_t v_inBold_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3774_; 
v_content_3740_ = lean_ctor_get(v_x_3573_, 0);
lean_inc_ref(v_content_3740_);
v_url_3741_ = lean_ctor_get(v_x_3573_, 1);
lean_inc_ref(v_url_3741_);
lean_dec_ref_known(v_x_3573_, 2);
v_inEmph_3742_ = lean_ctor_get_uint8(v_x_3572_, 0);
v_inBold_3743_ = lean_ctor_get_uint8(v_x_3572_, 1);
v_isSharedCheck_3774_ = !lean_is_exclusive(v_x_3572_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3745_ = v_x_3572_;
v_isShared_3746_ = v_isSharedCheck_3774_;
goto v_resetjp_3744_;
}
else
{
lean_dec(v_x_3572_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3774_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
uint8_t v___x_3747_; lean_object* v___x_3749_; 
v___x_3747_ = 1;
if (v_isShared_3746_ == 0)
{
v___x_3749_ = v___x_3745_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 0, v_inEmph_3742_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 1, v_inBold_3743_);
v___x_3749_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
lean_ctor_set_uint8(v___x_3749_, 2, v___x_3747_);
v___x_3750_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3750_, 0, v_content_3740_);
v___x_3751_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3749_, v___x_3750_, v_a_3574_, v_a_3575_, v_a_3576_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3772_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_3772_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3772_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
v___x_3756_ = lean_unsigned_to_nat(1u);
v___x_3757_ = lean_mk_empty_array_with_capacity(v___x_3756_);
v___x_3758_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3759_ = lean_string_append(v___x_3758_, v_url_3741_);
lean_dec_ref(v_url_3741_);
v___x_3760_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3761_ = lean_string_append(v___x_3759_, v___x_3760_);
v___x_3762_ = lean_array_push(v___x_3757_, v___x_3761_);
v___x_3763_ = lean_unsigned_to_nat(3u);
v___x_3764_ = lean_mk_empty_array_with_capacity(v___x_3763_);
lean_dec_ref(v___x_3764_);
v___x_3765_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_3766_ = lean_array_push(v___x_3765_, v_a_3752_);
v___x_3767_ = lean_array_push(v___x_3766_, v___x_3762_);
v___x_3768_ = l_Lean_Doc_joinInlines(v___x_3767_);
lean_dec_ref(v___x_3767_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v___x_3768_);
v___x_3770_ = v___x_3754_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
else
{
lean_dec_ref(v_url_3741_);
return v___x_3751_;
}
}
}
}
else
{
lean_object* v_content_3775_; size_t v_sz_3776_; size_t v___x_3777_; lean_object* v___x_3778_; 
v_content_3775_ = lean_ctor_get(v_x_3573_, 0);
lean_inc_ref(v_content_3775_);
lean_dec_ref_known(v_x_3573_, 2);
v_sz_3776_ = lean_array_size(v_content_3775_);
v___x_3777_ = ((size_t)0ULL);
v___x_3778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3572_, v_sz_3776_, v___x_3777_, v_content_3775_, v_a_3574_, v_a_3575_, v_a_3576_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3787_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3781_ = v___x_3778_;
v_isShared_3782_ = v_isSharedCheck_3787_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3778_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3787_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___x_3783_ = l_Lean_Doc_joinInlines(v_a_3779_);
lean_dec(v_a_3779_);
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v___x_3783_);
v___x_3785_ = v___x_3781_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3783_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
v_a_3788_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3778_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3778_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
case 7:
{
lean_object* v_name_3796_; lean_object* v_content_3797_; size_t v_sz_3798_; size_t v___x_3799_; lean_object* v___x_3800_; 
v_name_3796_ = lean_ctor_get(v_x_3573_, 0);
lean_inc_ref(v_name_3796_);
v_content_3797_ = lean_ctor_get(v_x_3573_, 1);
lean_inc_ref(v_content_3797_);
lean_dec_ref_known(v_x_3573_, 2);
v_sz_3798_ = lean_array_size(v_content_3797_);
v___x_3799_ = ((size_t)0ULL);
v___x_3800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3572_, v_sz_3798_, v___x_3799_, v_content_3797_, v_a_3574_, v_a_3575_, v_a_3576_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_a_3801_);
lean_dec_ref_known(v___x_3800_, 1);
v___x_3802_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_3803_ = l_Lean_Doc_joinInlines(v_a_3801_);
lean_dec(v_a_3801_);
v___x_3804_ = lean_array_to_list(v___x_3803_);
v___x_3805_ = l_String_intercalate(v___x_3802_, v___x_3804_);
lean_inc_ref(v_name_3796_);
v___x_3806_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_3796_, v___x_3805_, v_a_3574_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3820_; 
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3820_ == 0)
{
lean_object* v_unused_3821_; 
v_unused_3821_ = lean_ctor_get(v___x_3806_, 0);
lean_dec(v_unused_3821_);
v___x_3808_ = v___x_3806_;
v_isShared_3809_ = v_isSharedCheck_3820_;
goto v_resetjp_3807_;
}
else
{
lean_dec(v___x_3806_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3820_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3818_; 
v___x_3810_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_3811_ = lean_string_append(v___x_3810_, v_name_3796_);
lean_dec_ref(v_name_3796_);
v___x_3812_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_3813_ = lean_string_append(v___x_3811_, v___x_3812_);
v___x_3814_ = lean_unsigned_to_nat(1u);
v___x_3815_ = lean_mk_empty_array_with_capacity(v___x_3814_);
v___x_3816_ = lean_array_push(v___x_3815_, v___x_3813_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 0, v___x_3816_);
v___x_3818_ = v___x_3808_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec_ref(v_name_3796_);
v_a_3822_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3806_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3806_);
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
else
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
lean_dec_ref(v_name_3796_);
v_a_3830_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3800_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3800_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
case 8:
{
lean_object* v_alt_3838_; lean_object* v_url_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
lean_dec_ref(v_x_3572_);
v_alt_3838_ = lean_ctor_get(v_x_3573_, 0);
lean_inc_ref(v_alt_3838_);
v_url_3839_ = lean_ctor_get(v_x_3573_, 1);
lean_inc_ref(v_url_3839_);
lean_dec_ref_known(v_x_3573_, 2);
v___x_3840_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_3841_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_3838_);
lean_dec_ref(v_alt_3838_);
v___x_3842_ = lean_string_append(v___x_3840_, v___x_3841_);
lean_dec_ref(v___x_3841_);
v___x_3843_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3844_ = lean_string_append(v___x_3842_, v___x_3843_);
v___x_3845_ = lean_string_append(v___x_3844_, v_url_3839_);
lean_dec_ref(v_url_3839_);
v___x_3846_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3847_ = lean_string_append(v___x_3845_, v___x_3846_);
v___x_3848_ = lean_unsigned_to_nat(1u);
v___x_3849_ = lean_mk_empty_array_with_capacity(v___x_3848_);
v___x_3850_ = lean_array_push(v___x_3849_, v___x_3847_);
v___x_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
return v___x_3851_;
}
case 9:
{
lean_object* v_content_3852_; size_t v_sz_3853_; size_t v___x_3854_; lean_object* v___x_3855_; 
v_content_3852_ = lean_ctor_get(v_x_3573_, 0);
lean_inc_ref(v_content_3852_);
lean_dec_ref_known(v_x_3573_, 1);
v_sz_3853_ = lean_array_size(v_content_3852_);
v___x_3854_ = ((size_t)0ULL);
v___x_3855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3572_, v_sz_3853_, v___x_3854_, v_content_3852_, v_a_3574_, v_a_3575_, v_a_3576_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3864_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3858_ = v___x_3855_;
v_isShared_3859_ = v_isSharedCheck_3864_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3855_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3864_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3860_; lean_object* v___x_3862_; 
v___x_3860_ = l_Lean_Doc_joinInlines(v_a_3856_);
lean_dec(v_a_3856_);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 0, v___x_3860_);
v___x_3862_ = v___x_3858_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3860_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
v_a_3865_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3855_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3855_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
default: 
{
lean_object* v_container_3873_; 
v_container_3873_ = lean_ctor_get(v_x_3573_, 0);
if (lean_obj_tag(v_container_3873_) == 0)
{
lean_object* v_content_3874_; lean_object* v_val_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
lean_inc_ref(v_container_3873_);
v_content_3874_ = lean_ctor_get(v_x_3573_, 1);
lean_inc_ref(v_content_3874_);
lean_dec_ref_known(v_x_3573_, 2);
v_val_3875_ = lean_ctor_get(v_container_3873_, 0);
lean_inc(v_val_3875_);
lean_dec_ref_known(v_container_3873_, 1);
v___x_3876_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3875_);
v___x_3877_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_3876_, v_a_3575_, v_a_3576_);
lean_dec(v___x_3876_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3877_, 1);
if (lean_obj_tag(v_a_3878_) == 0)
{
size_t v_sz_3879_; size_t v___x_3880_; lean_object* v___x_3881_; 
lean_dec(v_val_3875_);
v_sz_3879_ = lean_array_size(v_content_3874_);
v___x_3880_ = ((size_t)0ULL);
v___x_3881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3572_, v_sz_3879_, v___x_3880_, v_content_3874_, v_a_3574_, v_a_3575_, v_a_3576_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3890_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; lean_object* v___x_3888_; 
v___x_3886_ = l_Lean_Doc_joinInlines(v_a_3882_);
lean_dec(v_a_3882_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3886_);
v___x_3888_ = v___x_3884_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3886_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
v_a_3891_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3881_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3881_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
else
{
lean_object* v_val_3899_; lean_object* v___f_3900_; size_t v_sz_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v_fallback_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v_val_3899_ = lean_ctor_get(v_a_3878_, 0);
lean_inc(v_val_3899_);
lean_dec_ref_known(v_a_3878_, 1);
lean_inc_ref(v_x_3572_);
v___f_3900_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3900_, 0, v_x_3572_);
v_sz_3901_ = lean_array_size(v_content_3874_);
v___x_3902_ = lean_box_usize(v_sz_3901_);
v___x_3903_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
lean_inc_ref(v_content_3874_);
v_fallback_3904_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v_fallback_3904_, 0, v_x_3572_);
lean_closure_set(v_fallback_3904_, 1, v___x_3902_);
lean_closure_set(v_fallback_3904_, 2, v___x_3903_);
lean_closure_set(v_fallback_3904_, 3, v_content_3874_);
v___x_3905_ = lean_apply_3(v_val_3899_, v___f_3900_, v_val_3875_, v_content_3874_);
v___x_3906_ = l_Lean_Doc_withRendererFallback(v_fallback_3904_, v___x_3905_, v_a_3574_, v_a_3575_, v_a_3576_);
return v___x_3906_;
}
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec(v_val_3875_);
lean_dec_ref(v_content_3874_);
lean_dec_ref(v_x_3572_);
v_a_3907_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3877_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3877_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
else
{
lean_object* v_content_3915_; size_t v_sz_3916_; size_t v___x_3917_; lean_object* v___x_3918_; 
v_content_3915_ = lean_ctor_get(v_x_3573_, 1);
lean_inc_ref(v_content_3915_);
lean_dec_ref_known(v_x_3573_, 2);
v_sz_3916_ = lean_array_size(v_content_3915_);
v___x_3917_ = ((size_t)0ULL);
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3572_, v_sz_3916_, v___x_3917_, v_content_3915_, v_a_3574_, v_a_3575_, v_a_3576_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3927_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3921_ = v___x_3918_;
v_isShared_3922_ = v_isSharedCheck_3927_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3918_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3927_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; lean_object* v___x_3925_; 
v___x_3923_ = l_Lean_Doc_joinInlines(v_a_3919_);
lean_dec(v_a_3919_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 0, v___x_3923_);
v___x_3925_ = v___x_3921_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
v_a_3928_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3918_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3918_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
}
}
v___jp_3578_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = l_Lean_Doc_joinInlines(v_pieces_3579_);
lean_dec_ref(v_pieces_3579_);
v___x_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
return v___x_3581_;
}
v___jp_3582_:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = l_Lean_Doc_joinInlines(v_pieces_3583_);
lean_dec_ref(v_pieces_3583_);
v___x_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
return v___x_3585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(lean_object* v_x_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3943_, lean_object* v_sz_3944_, lean_object* v_i_3945_, lean_object* v_bs_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
size_t v_sz_boxed_3951_; size_t v_i_boxed_3952_; lean_object* v_res_3953_; 
v_sz_boxed_3951_ = lean_unbox_usize(v_sz_3944_);
lean_dec(v_sz_3944_);
v_i_boxed_3952_ = lean_unbox_usize(v_i_3945_);
lean_dec(v_i_3945_);
v_res_3953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3943_, v_sz_boxed_3951_, v_i_boxed_3952_, v_bs_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed(lean_object* v_x_3954_, lean_object* v_x_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3954_, v_x_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
lean_dec(v_a_3956_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(lean_object* v___x_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v___x_3967_; 
v___x_3967_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0___boxed(lean_object* v___x_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(v___x_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(lean_object* v_x_3975_, lean_object* v_x_3976_){
_start:
{
lean_object* v_zero_3977_; uint8_t v_isZero_3978_; 
v_zero_3977_ = lean_unsigned_to_nat(0u);
v_isZero_3978_ = lean_nat_dec_eq(v_x_3975_, v_zero_3977_);
if (v_isZero_3978_ == 1)
{
lean_dec(v_x_3975_);
return v_x_3976_;
}
else
{
uint32_t v___x_3979_; lean_object* v_one_3980_; lean_object* v_n_3981_; lean_object* v___x_3982_; 
v___x_3979_ = 32;
v_one_3980_ = lean_unsigned_to_nat(1u);
v_n_3981_ = lean_nat_sub(v_x_3975_, v_one_3980_);
lean_dec(v_x_3975_);
v___x_3982_ = lean_string_push(v_x_3976_, v___x_3979_);
v_x_3975_ = v_n_3981_;
v_x_3976_ = v___x_3982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(size_t v_sz_3984_, size_t v_i_3985_, lean_object* v_bs_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
uint8_t v___x_3991_; 
v___x_3991_ = lean_usize_dec_lt(v_i_3985_, v_sz_3984_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; 
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v_bs_3986_);
return v___x_3992_;
}
else
{
lean_object* v_v_3993_; size_t v_sz_3994_; size_t v___x_3995_; lean_object* v___x_3996_; 
v_v_3993_ = lean_array_uget_borrowed(v_bs_3986_, v_i_3985_);
v_sz_3994_ = lean_array_size(v_v_3993_);
v___x_3995_ = ((size_t)0ULL);
lean_inc(v_v_3993_);
v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_3994_, v___x_3995_, v_v_3993_, v___y_3987_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3998_; lean_object* v_bs_x27_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; size_t v___x_4004_; size_t v___x_4005_; lean_object* v___x_4006_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref_known(v___x_3996_, 1);
v___x_3998_ = lean_unsigned_to_nat(0u);
v_bs_x27_3999_ = lean_array_uset(v_bs_3986_, v_i_3985_, v___x_3998_);
v___x_4000_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_4001_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_4002_ = l_Lean_Doc_joinBlocks(v_a_3997_);
lean_dec(v_a_3997_);
v___x_4003_ = l_Lean_Doc_prefixListLines(v___x_4000_, v___x_4001_, v___x_4002_);
v___x_4004_ = ((size_t)1ULL);
v___x_4005_ = lean_usize_add(v_i_3985_, v___x_4004_);
v___x_4006_ = lean_array_uset(v_bs_x27_3999_, v_i_3985_, v___x_4003_);
v_i_3985_ = v___x_4005_;
v_bs_3986_ = v___x_4006_;
goto _start;
}
else
{
lean_dec_ref(v_bs_3986_);
return v___x_3996_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(lean_object* v_as_4008_, size_t v_sz_4009_, size_t v_i_4010_, lean_object* v_b_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
uint8_t v___x_4016_; 
v___x_4016_ = lean_usize_dec_lt(v_i_4010_, v_sz_4009_);
if (v___x_4016_ == 0)
{
lean_object* v___x_4017_; 
v___x_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4017_, 0, v_b_4011_);
return v___x_4017_;
}
else
{
lean_object* v_a_4018_; size_t v_sz_4019_; size_t v___x_4020_; lean_object* v___x_4021_; 
v_a_4018_ = lean_array_uget_borrowed(v_as_4008_, v_i_4010_);
v_sz_4019_ = lean_array_size(v_a_4018_);
v___x_4020_ = ((size_t)0ULL);
lean_inc(v_a_4018_);
v___x_4021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4019_, v___x_4020_, v_a_4018_, v___y_4012_, v___y_4013_, v___y_4014_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v_fst_4023_; lean_object* v_snd_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4045_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v___x_4021_, 1);
v_fst_4023_ = lean_ctor_get(v_b_4011_, 0);
v_snd_4024_ = lean_ctor_get(v_b_4011_, 1);
v_isSharedCheck_4045_ = !lean_is_exclusive(v_b_4011_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4026_ = v_b_4011_;
v_isShared_4027_ = v_isSharedCheck_4045_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_snd_4024_);
lean_inc(v_fst_4023_);
lean_dec(v_b_4011_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4045_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4040_; 
v___x_4028_ = lean_unsigned_to_nat(1u);
lean_inc(v_snd_4024_);
v___x_4029_ = l_Nat_reprFast(v_snd_4024_);
v___x_4030_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_4031_ = lean_string_append(v___x_4029_, v___x_4030_);
v___x_4032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4033_ = lean_string_utf8_byte_size(v___x_4031_);
v___x_4034_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(v___x_4033_, v___x_4032_);
v___x_4035_ = l_Lean_Doc_joinBlocks(v_a_4022_);
lean_dec(v_a_4022_);
v___x_4036_ = l_Lean_Doc_prefixListLines(v___x_4031_, v___x_4034_, v___x_4035_);
v___x_4037_ = lean_array_push(v_fst_4023_, v___x_4036_);
v___x_4038_ = lean_nat_add(v_snd_4024_, v___x_4028_);
lean_dec(v_snd_4024_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4038_);
lean_ctor_set(v___x_4026_, 0, v___x_4037_);
v___x_4040_ = v___x_4026_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4037_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v___x_4038_);
v___x_4040_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
size_t v___x_4041_; size_t v___x_4042_; 
v___x_4041_ = ((size_t)1ULL);
v___x_4042_ = lean_usize_add(v_i_4010_, v___x_4041_);
v_i_4010_ = v___x_4042_;
v_b_4011_ = v___x_4040_;
goto _start;
}
}
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_dec_ref(v_b_4011_);
v_a_4046_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4021_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4021_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(size_t v_sz_4054_, size_t v_i_4055_, lean_object* v_bs_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
uint8_t v___x_4061_; 
v___x_4061_ = lean_usize_dec_lt(v_i_4055_, v_sz_4054_);
if (v___x_4061_ == 0)
{
lean_object* v___x_4062_; 
v___x_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4062_, 0, v_bs_4056_);
return v___x_4062_;
}
else
{
lean_object* v_v_4063_; lean_object* v___x_4064_; lean_object* v_term_4065_; lean_object* v_desc_4066_; lean_object* v___x_4067_; lean_object* v_bs_x27_4068_; lean_object* v_a_4070_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v_v_4063_ = lean_array_uget_borrowed(v_bs_4056_, v_i_4055_);
v___x_4064_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_4065_ = lean_ctor_get(v_v_4063_, 0);
lean_inc_ref(v_term_4065_);
v_desc_4066_ = lean_ctor_get(v_v_4063_, 1);
lean_inc_ref(v_desc_4066_);
v___x_4067_ = lean_unsigned_to_nat(0u);
v_bs_x27_4068_ = lean_array_uset(v_bs_4056_, v_i_4055_, v___x_4067_);
v___x_4075_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4075_, 0, v_term_4065_);
v___x_4076_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4064_, v___x_4075_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; size_t v_sz_4078_; size_t v___x_4079_; lean_object* v___x_4080_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v___x_4076_, 1);
v_sz_4078_ = lean_array_size(v_desc_4066_);
v___x_4079_ = ((size_t)0ULL);
lean_inc_ref(v_desc_4066_);
v___x_4080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4078_, v___x_4079_, v_desc_4066_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v___y_4083_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; uint8_t v___x_4096_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4080_, 1);
v___x_4087_ = lean_unsigned_to_nat(1u);
v___x_4088_ = lean_mk_empty_array_with_capacity(v___x_4087_);
v___x_4089_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_4090_ = lean_unsigned_to_nat(2u);
v___x_4091_ = lean_mk_empty_array_with_capacity(v___x_4090_);
v___x_4092_ = lean_array_push(v___x_4091_, v_a_4077_);
v___x_4093_ = lean_array_push(v___x_4092_, v___x_4089_);
v___x_4094_ = l_Lean_Doc_joinInlines(v___x_4093_);
lean_dec_ref(v___x_4093_);
v___x_4095_ = lean_array_get_size(v_desc_4066_);
lean_dec_ref(v_desc_4066_);
v___x_4096_ = lean_nat_dec_le(v___x_4095_, v___x_4087_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4097_ = lean_array_push(v___x_4088_, v___x_4094_);
v___x_4098_ = l_Array_append___redArg(v___x_4097_, v_a_4081_);
lean_dec(v_a_4081_);
v___x_4099_ = l_Lean_Doc_joinBlocks(v___x_4098_);
lean_dec_ref(v___x_4098_);
v___y_4083_ = v___x_4099_;
goto v___jp_4082_;
}
else
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
lean_dec_ref(v___x_4088_);
v___x_4100_ = l_Lean_Doc_joinBlocks(v_a_4081_);
lean_dec(v_a_4081_);
v___x_4101_ = l_Array_append___redArg(v___x_4094_, v___x_4100_);
lean_dec_ref(v___x_4100_);
v___y_4083_ = v___x_4101_;
goto v___jp_4082_;
}
v___jp_4082_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4084_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_4085_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_4086_ = l_Lean_Doc_prefixListLines(v___x_4084_, v___x_4085_, v___y_4083_);
v_a_4070_ = v___x_4086_;
goto v___jp_4069_;
}
}
else
{
lean_dec(v_a_4077_);
lean_dec_ref(v_bs_x27_4068_);
lean_dec_ref(v_desc_4066_);
return v___x_4080_;
}
}
else
{
lean_dec_ref(v_desc_4066_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4102_; 
v_a_4102_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v___x_4076_, 1);
v_a_4070_ = v_a_4102_;
goto v___jp_4069_;
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec_ref(v_bs_x27_4068_);
v_a_4103_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4076_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4076_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
v___jp_4069_:
{
size_t v___x_4071_; size_t v___x_4072_; lean_object* v___x_4073_; 
v___x_4071_ = ((size_t)1ULL);
v___x_4072_ = lean_usize_add(v_i_4055_, v___x_4071_);
v___x_4073_ = lean_array_uset(v_bs_x27_4068_, v_i_4055_, v_a_4070_);
v_i_4055_ = v___x_4072_;
v_bs_4056_ = v___x_4073_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed(lean_object* v_x_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_x_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
lean_dec(v_a_4114_);
lean_dec_ref(v_a_4113_);
lean_dec(v_a_4112_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed(lean_object* v_sz_4119_, lean_object* v___x_4120_, lean_object* v_content_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
size_t v_sz_boxed_4126_; size_t v___x_4849__boxed_4127_; lean_object* v_res_4128_; 
v_sz_boxed_4126_ = lean_unbox_usize(v_sz_4119_);
lean_dec(v_sz_4119_);
v___x_4849__boxed_4127_ = lean_unbox_usize(v___x_4120_);
lean_dec(v___x_4120_);
v_res_4128_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(v_sz_boxed_4126_, v___x_4849__boxed_4127_, v_content_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(lean_object* v_x_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
switch(lean_obj_tag(v_x_4129_))
{
case 0:
{
lean_object* v_contents_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4143_; 
v_contents_4134_ = lean_ctor_get(v_x_4129_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v_x_4129_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4136_ = v_x_4129_;
v_isShared_4137_ = v_isSharedCheck_4143_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_contents_4134_);
lean_dec(v_x_4129_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4143_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4138_; lean_object* v___x_4140_; 
v___x_4138_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_4137_ == 0)
{
lean_ctor_set_tag(v___x_4136_, 9);
v___x_4140_ = v___x_4136_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_contents_4134_);
v___x_4140_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
lean_object* v___x_4141_; 
v___x_4141_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4138_, v___x_4140_, v_a_4130_, v_a_4131_, v_a_4132_);
return v___x_4141_;
}
}
}
case 1:
{
lean_object* v_content_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4152_; 
v_content_4144_ = lean_ctor_get(v_x_4129_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v_x_4129_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4146_ = v_x_4129_;
v_isShared_4147_ = v_isSharedCheck_4152_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_content_4144_);
lean_dec(v_x_4129_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4152_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4148_; lean_object* v___x_4150_; 
v___x_4148_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_4144_);
if (v_isShared_4147_ == 0)
{
lean_ctor_set_tag(v___x_4146_, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4148_);
v___x_4150_ = v___x_4146_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v___x_4148_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
case 2:
{
lean_object* v_items_4153_; size_t v_sz_4154_; size_t v___x_4155_; lean_object* v___x_4156_; 
v_items_4153_ = lean_ctor_get(v_x_4129_, 0);
lean_inc_ref(v_items_4153_);
lean_dec_ref_known(v_x_4129_, 1);
v_sz_4154_ = lean_array_size(v_items_4153_);
v___x_4155_ = ((size_t)0ULL);
v___x_4156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_4154_, v___x_4155_, v_items_4153_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4165_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4159_ = v___x_4156_;
v_isShared_4160_ = v_isSharedCheck_4165_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4156_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4165_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4161_; lean_object* v___x_4163_; 
v___x_4161_ = l_Lean_Doc_joinBlocks(v_a_4157_);
lean_dec(v_a_4157_);
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 0, v___x_4161_);
v___x_4163_ = v___x_4159_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v___x_4161_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
v_a_4166_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4156_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4156_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
case 3:
{
lean_object* v_start_4174_; lean_object* v_items_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4209_; 
v_start_4174_ = lean_ctor_get(v_x_4129_, 0);
v_items_4175_ = lean_ctor_get(v_x_4129_, 1);
v_isSharedCheck_4209_ = !lean_is_exclusive(v_x_4129_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4177_ = v_x_4129_;
v_isShared_4178_ = v_isSharedCheck_4209_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_items_4175_);
lean_inc(v_start_4174_);
lean_dec(v_x_4129_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4209_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v_out_4179_; lean_object* v___y_4181_; lean_object* v___x_4206_; lean_object* v___x_4207_; uint8_t v___x_4208_; 
v_out_4179_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_4206_ = lean_unsigned_to_nat(1u);
v___x_4207_ = l_Int_toNat(v_start_4174_);
lean_dec(v_start_4174_);
v___x_4208_ = lean_nat_dec_le(v___x_4206_, v___x_4207_);
if (v___x_4208_ == 0)
{
lean_dec(v___x_4207_);
v___y_4181_ = v___x_4206_;
goto v___jp_4180_;
}
else
{
v___y_4181_ = v___x_4207_;
goto v___jp_4180_;
}
v___jp_4180_:
{
lean_object* v___x_4183_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set_tag(v___x_4177_, 0);
lean_ctor_set(v___x_4177_, 1, v___y_4181_);
lean_ctor_set(v___x_4177_, 0, v_out_4179_);
v___x_4183_ = v___x_4177_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_out_4179_);
lean_ctor_set(v_reuseFailAlloc_4205_, 1, v___y_4181_);
v___x_4183_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
size_t v_sz_4184_; size_t v___x_4185_; lean_object* v___x_4186_; 
v_sz_4184_ = lean_array_size(v_items_4175_);
v___x_4185_ = ((size_t)0ULL);
v___x_4186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_items_4175_, v_sz_4184_, v___x_4185_, v___x_4183_, v_a_4130_, v_a_4131_, v_a_4132_);
lean_dec_ref(v_items_4175_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4196_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4189_ = v___x_4186_;
v_isShared_4190_ = v_isSharedCheck_4196_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4186_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4196_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v_fst_4191_; lean_object* v___x_4192_; lean_object* v___x_4194_; 
v_fst_4191_ = lean_ctor_get(v_a_4187_, 0);
lean_inc(v_fst_4191_);
lean_dec(v_a_4187_);
v___x_4192_ = l_Lean_Doc_joinBlocks(v_fst_4191_);
lean_dec(v_fst_4191_);
if (v_isShared_4190_ == 0)
{
lean_ctor_set(v___x_4189_, 0, v___x_4192_);
v___x_4194_ = v___x_4189_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4192_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
else
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
v_a_4197_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4199_ = v___x_4186_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4186_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_4210_; size_t v_sz_4211_; size_t v___x_4212_; lean_object* v___x_4213_; 
v_items_4210_ = lean_ctor_get(v_x_4129_, 0);
lean_inc_ref(v_items_4210_);
lean_dec_ref_known(v_x_4129_, 1);
v_sz_4211_ = lean_array_size(v_items_4210_);
v___x_4212_ = ((size_t)0ULL);
v___x_4213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_4211_, v___x_4212_, v_items_4210_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4222_; 
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4216_ = v___x_4213_;
v_isShared_4217_ = v_isSharedCheck_4222_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4213_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4222_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4218_; lean_object* v___x_4220_; 
v___x_4218_ = l_Lean_Doc_joinBlocks(v_a_4214_);
lean_dec(v_a_4214_);
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 0, v___x_4218_);
v___x_4220_ = v___x_4216_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4218_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
v_a_4223_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4213_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4213_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
case 5:
{
lean_object* v_items_4231_; size_t v_sz_4232_; size_t v___x_4233_; lean_object* v___x_4234_; 
v_items_4231_ = lean_ctor_get(v_x_4129_, 0);
lean_inc_ref(v_items_4231_);
lean_dec_ref_known(v_x_4129_, 1);
v_sz_4232_ = lean_array_size(v_items_4231_);
v___x_4233_ = ((size_t)0ULL);
v___x_4234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4232_, v___x_4233_, v_items_4231_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4245_; 
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4237_ = v___x_4234_;
v_isShared_4238_ = v_isSharedCheck_4245_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4234_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4245_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4239_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_4240_ = l_Lean_Doc_joinBlocks(v_a_4235_);
lean_dec(v_a_4235_);
v___x_4241_ = l_Lean_Doc_prefixLines(v___x_4239_, v___x_4240_);
if (v_isShared_4238_ == 0)
{
lean_ctor_set(v___x_4237_, 0, v___x_4241_);
v___x_4243_ = v___x_4237_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
v_a_4246_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4234_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4234_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
case 6:
{
lean_object* v_content_4254_; size_t v_sz_4255_; size_t v___x_4256_; lean_object* v___x_4257_; 
v_content_4254_ = lean_ctor_get(v_x_4129_, 0);
lean_inc_ref(v_content_4254_);
lean_dec_ref_known(v_x_4129_, 1);
v_sz_4255_ = lean_array_size(v_content_4254_);
v___x_4256_ = ((size_t)0ULL);
v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4255_, v___x_4256_, v_content_4254_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4266_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4260_ = v___x_4257_;
v_isShared_4261_ = v_isSharedCheck_4266_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4257_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4266_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4262_; lean_object* v___x_4264_; 
v___x_4262_ = l_Lean_Doc_joinBlocks(v_a_4258_);
lean_dec(v_a_4258_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 0, v___x_4262_);
v___x_4264_ = v___x_4260_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4262_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
else
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
v_a_4267_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4257_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4257_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
default: 
{
lean_object* v_container_4275_; 
v_container_4275_ = lean_ctor_get(v_x_4129_, 0);
if (lean_obj_tag(v_container_4275_) == 0)
{
lean_object* v_content_4276_; lean_object* v_val_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
lean_inc_ref(v_container_4275_);
v_content_4276_ = lean_ctor_get(v_x_4129_, 1);
lean_inc_ref(v_content_4276_);
lean_dec_ref_known(v_x_4129_, 2);
v_val_4277_ = lean_ctor_get(v_container_4275_, 0);
lean_inc(v_val_4277_);
lean_dec_ref_known(v_container_4275_, 1);
v___x_4278_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_4277_);
v___x_4279_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_4278_, v_a_4131_, v_a_4132_);
lean_dec(v___x_4278_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
if (lean_obj_tag(v_a_4280_) == 0)
{
size_t v_sz_4281_; size_t v___x_4282_; lean_object* v___x_4283_; 
lean_dec(v_val_4277_);
v_sz_4281_ = lean_array_size(v_content_4276_);
v___x_4282_ = ((size_t)0ULL);
v___x_4283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4281_, v___x_4282_, v_content_4276_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4292_; 
v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4286_ = v___x_4283_;
v_isShared_4287_ = v_isSharedCheck_4292_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4283_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4292_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4288_; lean_object* v___x_4290_; 
v___x_4288_ = l_Lean_Doc_joinBlocks(v_a_4284_);
lean_dec(v_a_4284_);
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 0, v___x_4288_);
v___x_4290_ = v___x_4286_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4288_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
v_a_4293_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4283_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4283_);
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
lean_object* v_val_4301_; lean_object* v___f_4302_; lean_object* v___f_4303_; size_t v_sz_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v_fallback_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v_val_4301_ = lean_ctor_get(v_a_4280_, 0);
lean_inc(v_val_4301_);
lean_dec_ref_known(v_a_4280_, 1);
v___f_4302_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed), 5, 0);
v___f_4303_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___closed__0));
v_sz_4304_ = lean_array_size(v_content_4276_);
v___x_4305_ = lean_box_usize(v_sz_4304_);
v___x_4306_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
lean_inc_ref(v_content_4276_);
v_fallback_4307_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_fallback_4307_, 0, v___x_4305_);
lean_closure_set(v_fallback_4307_, 1, v___x_4306_);
lean_closure_set(v_fallback_4307_, 2, v_content_4276_);
v___x_4308_ = lean_apply_4(v_val_4301_, v___f_4303_, v___f_4302_, v_val_4277_, v_content_4276_);
v___x_4309_ = l_Lean_Doc_withRendererFallback(v_fallback_4307_, v___x_4308_, v_a_4130_, v_a_4131_, v_a_4132_);
return v___x_4309_;
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_dec(v_val_4277_);
lean_dec_ref(v_content_4276_);
v_a_4310_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4279_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4279_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
else
{
lean_object* v_content_4318_; size_t v_sz_4319_; size_t v___x_4320_; lean_object* v___x_4321_; 
v_content_4318_ = lean_ctor_get(v_x_4129_, 1);
lean_inc_ref(v_content_4318_);
lean_dec_ref_known(v_x_4129_, 2);
v_sz_4319_ = lean_array_size(v_content_4318_);
v___x_4320_ = ((size_t)0ULL);
v___x_4321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4319_, v___x_4320_, v_content_4318_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4330_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4324_ = v___x_4321_;
v_isShared_4325_ = v_isSharedCheck_4330_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4321_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4330_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4326_; lean_object* v___x_4328_; 
v___x_4326_ = l_Lean_Doc_joinBlocks(v_a_4322_);
lean_dec(v_a_4322_);
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 0, v___x_4326_);
v___x_4328_ = v___x_4324_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v___x_4326_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
v_a_4331_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4321_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4321_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(size_t v_sz_4339_, size_t v_i_4340_, lean_object* v_bs_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
uint8_t v___x_4346_; 
v___x_4346_ = lean_usize_dec_lt(v_i_4340_, v_sz_4339_);
if (v___x_4346_ == 0)
{
lean_object* v___x_4347_; 
v___x_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4347_, 0, v_bs_4341_);
return v___x_4347_;
}
else
{
lean_object* v_v_4348_; lean_object* v___x_4349_; 
v_v_4348_ = lean_array_uget_borrowed(v_bs_4341_, v_i_4340_);
lean_inc(v_v_4348_);
v___x_4349_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_v_4348_, v___y_4342_, v___y_4343_, v___y_4344_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4351_; lean_object* v_bs_x27_4352_; size_t v___x_4353_; size_t v___x_4354_; lean_object* v___x_4355_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___x_4349_, 1);
v___x_4351_ = lean_unsigned_to_nat(0u);
v_bs_x27_4352_ = lean_array_uset(v_bs_4341_, v_i_4340_, v___x_4351_);
v___x_4353_ = ((size_t)1ULL);
v___x_4354_ = lean_usize_add(v_i_4340_, v___x_4353_);
v___x_4355_ = lean_array_uset(v_bs_x27_4352_, v_i_4340_, v_a_4350_);
v_i_4340_ = v___x_4354_;
v_bs_4341_ = v___x_4355_;
goto _start;
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec_ref(v_bs_4341_);
v_a_4357_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4349_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4349_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(size_t v_sz_4365_, size_t v___x_4366_, lean_object* v_content_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4365_, v___x_4366_, v_content_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4381_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4375_ = v___x_4372_;
v_isShared_4376_ = v_isSharedCheck_4381_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4372_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4381_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4377_; lean_object* v___x_4379_; 
v___x_4377_ = l_Lean_Doc_joinBlocks(v_a_4373_);
lean_dec(v_a_4373_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 0, v___x_4377_);
v___x_4379_ = v___x_4375_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4377_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
v_a_4382_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4372_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4372_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2___boxed(lean_object* v_sz_4390_, lean_object* v_i_4391_, lean_object* v_bs_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
size_t v_sz_boxed_4397_; size_t v_i_boxed_4398_; lean_object* v_res_4399_; 
v_sz_boxed_4397_ = lean_unbox_usize(v_sz_4390_);
lean_dec(v_sz_4390_);
v_i_boxed_4398_ = lean_unbox_usize(v_i_4391_);
lean_dec(v_i_4391_);
v_res_4399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_boxed_4397_, v_i_boxed_4398_, v_bs_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec(v___y_4393_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5___boxed(lean_object* v_sz_4400_, lean_object* v_i_4401_, lean_object* v_bs_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
size_t v_sz_boxed_4407_; size_t v_i_boxed_4408_; lean_object* v_res_4409_; 
v_sz_boxed_4407_ = lean_unbox_usize(v_sz_4400_);
lean_dec(v_sz_4400_);
v_i_boxed_4408_ = lean_unbox_usize(v_i_4401_);
lean_dec(v_i_4401_);
v_res_4409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_boxed_4407_, v_i_boxed_4408_, v_bs_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7___boxed(lean_object* v_as_4410_, lean_object* v_sz_4411_, lean_object* v_i_4412_, lean_object* v_b_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
size_t v_sz_boxed_4418_; size_t v_i_boxed_4419_; lean_object* v_res_4420_; 
v_sz_boxed_4418_ = lean_unbox_usize(v_sz_4411_);
lean_dec(v_sz_4411_);
v_i_boxed_4419_ = lean_unbox_usize(v_i_4412_);
lean_dec(v_i_4412_);
v_res_4420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_as_4410_, v_sz_boxed_4418_, v_i_boxed_4419_, v_b_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v_as_4410_);
return v_res_4420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8___boxed(lean_object* v_sz_4421_, lean_object* v_i_4422_, lean_object* v_bs_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
size_t v_sz_boxed_4428_; size_t v_i_boxed_4429_; lean_object* v_res_4430_; 
v_sz_boxed_4428_ = lean_unbox_usize(v_sz_4421_);
lean_dec(v_sz_4421_);
v_i_boxed_4429_ = lean_unbox_usize(v_i_4422_);
lean_dec(v_i_4422_);
v_res_4430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_boxed_4428_, v_i_boxed_4429_, v_bs_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
return v_res_4430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(size_t v_sz_4431_, size_t v_i_4432_, lean_object* v_bs_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
uint8_t v___x_4438_; 
v___x_4438_ = lean_usize_dec_lt(v_i_4432_, v_sz_4431_);
if (v___x_4438_ == 0)
{
lean_object* v___x_4439_; 
v___x_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4439_, 0, v_bs_4433_);
return v___x_4439_;
}
else
{
lean_object* v_v_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v_v_4440_ = lean_array_uget_borrowed(v_bs_4433_, v_i_4432_);
v___x_4441_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc(v_v_4440_);
v___x_4442_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4441_, v_v_4440_, v___y_4434_, v___y_4435_, v___y_4436_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; lean_object* v___x_4444_; lean_object* v_bs_x27_4445_; size_t v___x_4446_; size_t v___x_4447_; lean_object* v___x_4448_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_a_4443_);
lean_dec_ref_known(v___x_4442_, 1);
v___x_4444_ = lean_unsigned_to_nat(0u);
v_bs_x27_4445_ = lean_array_uset(v_bs_4433_, v_i_4432_, v___x_4444_);
v___x_4446_ = ((size_t)1ULL);
v___x_4447_ = lean_usize_add(v_i_4432_, v___x_4446_);
v___x_4448_ = lean_array_uset(v_bs_x27_4445_, v_i_4432_, v_a_4443_);
v_i_4432_ = v___x_4447_;
v_bs_4433_ = v___x_4448_;
goto _start;
}
else
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_dec_ref(v_bs_4433_);
v_a_4450_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4442_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4442_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1___boxed(lean_object* v_sz_4458_, lean_object* v_i_4459_, lean_object* v_bs_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
size_t v_sz_boxed_4465_; size_t v_i_boxed_4466_; lean_object* v_res_4467_; 
v_sz_boxed_4465_ = lean_unbox_usize(v_sz_4458_);
lean_dec(v_sz_4458_);
v_i_boxed_4466_ = lean_unbox_usize(v_i_4459_);
lean_dec(v_i_4459_);
v_res_4467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_boxed_4465_, v_i_boxed_4466_, v_bs_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4462_);
lean_dec(v___y_4461_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(lean_object* v_x_4468_, lean_object* v_x_4469_){
_start:
{
lean_object* v_zero_4470_; uint8_t v_isZero_4471_; 
v_zero_4470_ = lean_unsigned_to_nat(0u);
v_isZero_4471_ = lean_nat_dec_eq(v_x_4468_, v_zero_4470_);
if (v_isZero_4471_ == 1)
{
lean_dec(v_x_4468_);
return v_x_4469_;
}
else
{
uint32_t v___x_4472_; lean_object* v_one_4473_; lean_object* v_n_4474_; lean_object* v___x_4475_; 
v___x_4472_ = 35;
v_one_4473_ = lean_unsigned_to_nat(1u);
v_n_4474_ = lean_nat_sub(v_x_4468_, v_one_4473_);
lean_dec(v_x_4468_);
v___x_4475_ = lean_string_push(v_x_4469_, v___x_4472_);
v_x_4468_ = v_n_4474_;
v_x_4469_ = v___x_4475_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(lean_object* v_level_4477_, lean_object* v_part_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v_title_4483_; lean_object* v_content_4484_; lean_object* v_subParts_4485_; size_t v_sz_4486_; size_t v___x_4487_; lean_object* v___x_4488_; 
v_title_4483_ = lean_ctor_get(v_part_4478_, 0);
lean_inc_ref(v_title_4483_);
v_content_4484_ = lean_ctor_get(v_part_4478_, 3);
lean_inc_ref(v_content_4484_);
v_subParts_4485_ = lean_ctor_get(v_part_4478_, 4);
lean_inc_ref(v_subParts_4485_);
lean_dec_ref(v_part_4478_);
v_sz_4486_ = lean_array_size(v_title_4483_);
v___x_4487_ = ((size_t)0ULL);
v___x_4488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_4486_, v___x_4487_, v_title_4483_, v_a_4479_, v_a_4480_, v_a_4481_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; size_t v_sz_4490_; lean_object* v___x_4491_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v___x_4488_, 1);
v_sz_4490_ = lean_array_size(v_content_4484_);
v___x_4491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4490_, v___x_4487_, v_content_4484_, v_a_4479_, v_a_4480_, v_a_4481_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; size_t v_sz_4497_; lean_object* v___x_4498_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
lean_dec_ref_known(v___x_4491_, 1);
v___x_4493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4494_ = lean_unsigned_to_nat(1u);
v___x_4495_ = lean_nat_add(v_level_4477_, v___x_4494_);
lean_inc(v___x_4495_);
v___x_4496_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(v___x_4495_, v___x_4493_);
v_sz_4497_ = lean_array_size(v_subParts_4485_);
v___x_4498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4495_, v_sz_4497_, v___x_4487_, v_subParts_4485_, v_a_4479_, v_a_4480_, v_a_4481_);
lean_dec(v___x_4495_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4517_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4501_ = v___x_4498_;
v_isShared_4502_ = v_isSharedCheck_4517_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4498_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4517_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4515_; 
v___x_4503_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_4504_ = lean_string_append(v___x_4496_, v___x_4503_);
v___x_4505_ = lean_mk_empty_array_with_capacity(v___x_4494_);
lean_inc_ref_n(v___x_4505_, 2);
v___x_4506_ = lean_array_push(v___x_4505_, v___x_4504_);
v___x_4507_ = lean_array_push(v___x_4505_, v___x_4506_);
v___x_4508_ = l_Array_append___redArg(v___x_4507_, v_a_4489_);
lean_dec(v_a_4489_);
v___x_4509_ = l_Lean_Doc_joinInlines(v___x_4508_);
lean_dec_ref(v___x_4508_);
v___x_4510_ = lean_array_push(v___x_4505_, v___x_4509_);
v___x_4511_ = l_Array_append___redArg(v___x_4510_, v_a_4492_);
lean_dec(v_a_4492_);
v___x_4512_ = l_Array_append___redArg(v___x_4511_, v_a_4499_);
lean_dec(v_a_4499_);
v___x_4513_ = l_Lean_Doc_joinBlocks(v___x_4512_);
lean_dec_ref(v___x_4512_);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 0, v___x_4513_);
v___x_4515_ = v___x_4501_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4513_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4525_; 
lean_dec_ref(v___x_4496_);
lean_dec(v_a_4492_);
lean_dec(v_a_4489_);
v_a_4518_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4520_ = v___x_4498_;
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4498_);
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
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
lean_dec(v_a_4489_);
lean_dec_ref(v_subParts_4485_);
v_a_4526_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4491_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4491_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
lean_dec_ref(v_subParts_4485_);
lean_dec_ref(v_content_4484_);
v_a_4534_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4488_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4488_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(lean_object* v___x_4542_, size_t v_sz_4543_, size_t v_i_4544_, lean_object* v_bs_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
uint8_t v___x_4550_; 
v___x_4550_ = lean_usize_dec_lt(v_i_4544_, v_sz_4543_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4551_; 
v___x_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4551_, 0, v_bs_4545_);
return v___x_4551_;
}
else
{
lean_object* v_v_4552_; lean_object* v___x_4553_; 
v_v_4552_ = lean_array_uget_borrowed(v_bs_4545_, v_i_4544_);
lean_inc(v_v_4552_);
v___x_4553_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4542_, v_v_4552_, v___y_4546_, v___y_4547_, v___y_4548_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; lean_object* v___x_4555_; lean_object* v_bs_x27_4556_; size_t v___x_4557_; size_t v___x_4558_; lean_object* v___x_4559_; 
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_a_4554_);
lean_dec_ref_known(v___x_4553_, 1);
v___x_4555_ = lean_unsigned_to_nat(0u);
v_bs_x27_4556_ = lean_array_uset(v_bs_4545_, v_i_4544_, v___x_4555_);
v___x_4557_ = ((size_t)1ULL);
v___x_4558_ = lean_usize_add(v_i_4544_, v___x_4557_);
v___x_4559_ = lean_array_uset(v_bs_x27_4556_, v_i_4544_, v_a_4554_);
v_i_4544_ = v___x_4558_;
v_bs_4545_ = v___x_4559_;
goto _start;
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
lean_dec_ref(v_bs_4545_);
v_a_4561_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___x_4553_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4553_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg___boxed(lean_object* v___x_4569_, lean_object* v_sz_4570_, lean_object* v_i_4571_, lean_object* v_bs_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
size_t v_sz_boxed_4577_; size_t v_i_boxed_4578_; lean_object* v_res_4579_; 
v_sz_boxed_4577_ = lean_unbox_usize(v_sz_4570_);
lean_dec(v_sz_4570_);
v_i_boxed_4578_ = lean_unbox_usize(v_i_4571_);
lean_dec(v_i_4571_);
v_res_4579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4569_, v_sz_boxed_4577_, v_i_boxed_4578_, v_bs_4572_, v___y_4573_, v___y_4574_, v___y_4575_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec(v___x_4569_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg___boxed(lean_object* v_level_4580_, lean_object* v_part_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4580_, v_part_4581_, v_a_4582_, v_a_4583_, v_a_4584_);
lean_dec(v_a_4584_);
lean_dec_ref(v_a_4583_);
lean_dec(v_a_4582_);
lean_dec(v_level_4580_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(size_t v_sz_4587_, size_t v_i_4588_, lean_object* v_bs_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_){
_start:
{
uint8_t v___x_4594_; 
v___x_4594_ = lean_usize_dec_lt(v_i_4588_, v_sz_4587_);
if (v___x_4594_ == 0)
{
lean_object* v___x_4595_; 
v___x_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4595_, 0, v_bs_4589_);
return v___x_4595_;
}
else
{
lean_object* v_v_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v_v_4596_ = lean_array_uget_borrowed(v_bs_4589_, v_i_4588_);
v___x_4597_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_4596_);
v___x_4598_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4597_, v_v_4596_, v___y_4590_, v___y_4591_, v___y_4592_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v_bs_x27_4600_; size_t v___x_4601_; size_t v___x_4602_; lean_object* v___x_4603_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_a_4599_);
lean_dec_ref_known(v___x_4598_, 1);
v_bs_x27_4600_ = lean_array_uset(v_bs_4589_, v_i_4588_, v___x_4597_);
v___x_4601_ = ((size_t)1ULL);
v___x_4602_ = lean_usize_add(v_i_4588_, v___x_4601_);
v___x_4603_ = lean_array_uset(v_bs_x27_4600_, v_i_4588_, v_a_4599_);
v_i_4588_ = v___x_4602_;
v_bs_4589_ = v___x_4603_;
goto _start;
}
else
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
lean_dec_ref(v_bs_4589_);
v_a_4605_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4598_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4598_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3___boxed(lean_object* v_sz_4613_, lean_object* v_i_4614_, lean_object* v_bs_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
size_t v_sz_boxed_4620_; size_t v_i_boxed_4621_; lean_object* v_res_4622_; 
v_sz_boxed_4620_ = lean_unbox_usize(v_sz_4613_);
lean_dec(v_sz_4613_);
v_i_boxed_4621_ = lean_unbox_usize(v_i_4614_);
lean_dec(v_i_4614_);
v_res_4622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_boxed_4620_, v_i_boxed_4621_, v_bs_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec(v___y_4616_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0(lean_object* v_val_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_){
_start:
{
lean_object* v_text_4628_; lean_object* v_subsections_4629_; size_t v_sz_4630_; size_t v___x_4631_; lean_object* v___x_4632_; 
v_text_4628_ = lean_ctor_get(v_val_4623_, 0);
lean_inc_ref(v_text_4628_);
v_subsections_4629_ = lean_ctor_get(v_val_4623_, 1);
lean_inc_ref(v_subsections_4629_);
lean_dec_ref(v_val_4623_);
v_sz_4630_ = lean_array_size(v_text_4628_);
v___x_4631_ = ((size_t)0ULL);
v___x_4632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4630_, v___x_4631_, v_text_4628_, v___y_4624_, v___y_4625_, v___y_4626_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v_a_4633_; size_t v_sz_4634_; lean_object* v___x_4635_; 
v_a_4633_ = lean_ctor_get(v___x_4632_, 0);
lean_inc(v_a_4633_);
lean_dec_ref_known(v___x_4632_, 1);
v_sz_4634_ = lean_array_size(v_subsections_4629_);
v___x_4635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_4634_, v___x_4631_, v_subsections_4629_, v___y_4624_, v___y_4625_, v___y_4626_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4645_; 
v_a_4636_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4638_ = v___x_4635_;
v_isShared_4639_ = v_isSharedCheck_4645_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4635_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4645_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4643_; 
v___x_4640_ = l_Array_append___redArg(v_a_4633_, v_a_4636_);
lean_dec(v_a_4636_);
v___x_4641_ = l_Lean_Doc_joinBlocks(v___x_4640_);
lean_dec_ref(v___x_4640_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 0, v___x_4641_);
v___x_4643_ = v___x_4638_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4641_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
return v___x_4643_;
}
}
}
else
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4653_; 
lean_dec(v_a_4633_);
v_a_4646_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4648_ = v___x_4635_;
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4635_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4651_; 
if (v_isShared_4649_ == 0)
{
v___x_4651_ = v___x_4648_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4646_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
lean_dec_ref(v_subsections_4629_);
v_a_4654_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4632_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4632_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0___boxed(lean_object* v_val_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_Lean_findSimpleDocString_x3f___lam__0(v_val_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_4668_, lean_object* v_declName_4669_, uint8_t v_includeBuiltin_4670_, lean_object* v_options_4671_, lean_object* v_currNamespace_4672_, lean_object* v_openDecls_4673_, lean_object* v_cancelTk_x3f_4674_){
_start:
{
lean_object* v___x_4676_; 
lean_inc_ref(v_env_4668_);
v___x_4676_ = l_Lean_findInternalDocString_x3f(v_env_4668_, v_declName_4669_, v_includeBuiltin_4670_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4720_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4679_ = v___x_4676_;
v_isShared_4680_ = v_isSharedCheck_4720_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4676_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4720_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
if (lean_obj_tag(v_a_4677_) == 0)
{
lean_object* v___x_4681_; lean_object* v___x_4683_; 
lean_dec(v_cancelTk_x3f_4674_);
lean_dec(v_openDecls_4673_);
lean_dec(v_currNamespace_4672_);
lean_dec_ref(v_options_4671_);
lean_dec_ref(v_env_4668_);
v___x_4681_ = lean_box(0);
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 0, v___x_4681_);
v___x_4683_ = v___x_4679_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v___x_4681_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
else
{
lean_object* v_val_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4719_; 
v_val_4685_ = lean_ctor_get(v_a_4677_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v_a_4677_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4687_ = v_a_4677_;
v_isShared_4688_ = v_isSharedCheck_4719_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_val_4685_);
lean_dec(v_a_4677_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4719_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
if (lean_obj_tag(v_val_4685_) == 0)
{
lean_object* v_val_4689_; lean_object* v___x_4691_; 
lean_dec(v_cancelTk_x3f_4674_);
lean_dec(v_openDecls_4673_);
lean_dec(v_currNamespace_4672_);
lean_dec_ref(v_options_4671_);
lean_dec_ref(v_env_4668_);
v_val_4689_ = lean_ctor_get(v_val_4685_, 0);
lean_inc(v_val_4689_);
lean_dec_ref_known(v_val_4685_, 1);
if (v_isShared_4688_ == 0)
{
lean_ctor_set(v___x_4687_, 0, v_val_4689_);
v___x_4691_ = v___x_4687_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_val_4689_);
v___x_4691_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
lean_object* v___x_4693_; 
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 0, v___x_4691_);
v___x_4693_ = v___x_4679_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4691_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
else
{
lean_object* v_val_4696_; lean_object* v___f_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
lean_del_object(v___x_4679_);
v_val_4696_ = lean_ctor_get(v_val_4685_, 0);
lean_inc(v_val_4696_);
lean_dec_ref_known(v_val_4685_, 1);
v___f_4697_ = lean_alloc_closure((void*)(l_Lean_findSimpleDocString_x3f___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4697_, 0, v_val_4696_);
v___x_4698_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_4698_, 0, v___f_4697_);
v___x_4699_ = l_Lean_Doc_runMarkdown___redArg(v_env_4668_, v___x_4698_, v_options_4671_, v_currNamespace_4672_, v_openDecls_4673_, v_cancelTk_x3f_4674_);
if (lean_obj_tag(v___x_4699_) == 0)
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4710_; 
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4702_ = v___x_4699_;
v_isShared_4703_ = v_isSharedCheck_4710_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4699_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4710_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4688_ == 0)
{
lean_ctor_set(v___x_4687_, 0, v_a_4700_);
v___x_4705_ = v___x_4687_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4700_);
v___x_4705_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
lean_object* v___x_4707_; 
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 0, v___x_4705_);
v___x_4707_ = v___x_4702_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4705_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
else
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
lean_del_object(v___x_4687_);
v_a_4711_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4713_ = v___x_4699_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4699_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4716_; 
if (v_isShared_4714_ == 0)
{
v___x_4716_ = v___x_4713_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4711_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
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
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
lean_dec(v_cancelTk_x3f_4674_);
lean_dec(v_openDecls_4673_);
lean_dec(v_currNamespace_4672_);
lean_dec_ref(v_options_4671_);
lean_dec_ref(v_env_4668_);
v_a_4721_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4676_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4676_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_4729_, lean_object* v_declName_4730_, lean_object* v_includeBuiltin_4731_, lean_object* v_options_4732_, lean_object* v_currNamespace_4733_, lean_object* v_openDecls_4734_, lean_object* v_cancelTk_x3f_4735_, lean_object* v_a_4736_){
_start:
{
uint8_t v_includeBuiltin_boxed_4737_; lean_object* v_res_4738_; 
v_includeBuiltin_boxed_4737_ = lean_unbox(v_includeBuiltin_4731_);
v_res_4738_ = l_Lean_findSimpleDocString_x3f(v_env_4729_, v_declName_4730_, v_includeBuiltin_boxed_4737_, v_options_4732_, v_currNamespace_4733_, v_openDecls_4734_, v_cancelTk_x3f_4735_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(lean_object* v_p_4739_, lean_object* v_level_4740_, lean_object* v_part_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v___x_4746_; 
v___x_4746_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4740_, v_part_4741_, v_a_4742_, v_a_4743_, v_a_4744_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___boxed(lean_object* v_p_4747_, lean_object* v_level_4748_, lean_object* v_part_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(v_p_4747_, v_level_4748_, v_part_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec(v_level_4748_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(lean_object* v_p_4755_, lean_object* v___x_4756_, size_t v_sz_4757_, size_t v_i_4758_, lean_object* v_bs_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_){
_start:
{
lean_object* v___x_4764_; 
v___x_4764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4756_, v_sz_4757_, v_i_4758_, v_bs_4759_, v___y_4760_, v___y_4761_, v___y_4762_);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___boxed(lean_object* v_p_4765_, lean_object* v___x_4766_, lean_object* v_sz_4767_, lean_object* v_i_4768_, lean_object* v_bs_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
size_t v_sz_boxed_4774_; size_t v_i_boxed_4775_; lean_object* v_res_4776_; 
v_sz_boxed_4774_ = lean_unbox_usize(v_sz_4767_);
lean_dec(v_sz_4767_);
v_i_boxed_4775_ = lean_unbox_usize(v_i_4768_);
lean_dec(v_i_4768_);
v_res_4776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(v_p_4765_, v___x_4766_, v_sz_boxed_4774_, v_i_boxed_4775_, v_bs_4769_, v___y_4770_, v___y_4771_, v___y_4772_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec(v___y_4770_);
lean_dec(v___x_4766_);
return v_res_4776_;
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
