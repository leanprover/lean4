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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Doc_Inline_empty___redArg();
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
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
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg();
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___boxed(lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_runMarkdown___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "<docstring>"};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__1;
static const lean_string_object l_Lean_Doc_runMarkdown___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Doc_runMarkdown___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Doc_runMarkdown___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__4 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Doc_runMarkdown___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__6;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__7;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__8;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__9;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__10;
static const lean_array_object l_Lean_Doc_runMarkdown___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__11 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__12;
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__13;
static const lean_string_object l_Lean_Doc_runMarkdown___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__14 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__14_value;
static const lean_string_object l_Lean_Doc_runMarkdown___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__15 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__15_value;
static const lean_string_object l_Lean_Doc_runMarkdown___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_Lean_Doc_runMarkdown___redArg___closed__16 = (const lean_object*)&l_Lean_Doc_runMarkdown___redArg___closed__16_value;
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
v___x_6_ = lean_box(0);
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v_name_1_);
lean_ctor_set(v___x_7_, 1, v_body_2_);
v___x_8_ = lean_array_push(v___x_5_, v___x_7_);
v___x_9_ = lean_st_ref_put(v_a_3_, v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_6_);
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
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0(lean_object* v_a_365_, lean_object* v_a_366_, uint8_t v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0___boxed(lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
uint8_t v_a_41__boxed_381_; lean_object* v_res_382_; 
v_a_41__boxed_381_ = lean_unbox(v_a_375_);
v_res_382_ = l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0(v_a_373_, v_a_374_, v_a_41__boxed_381_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec_ref(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg(){
_start:
{
lean_object* v___f_385_; 
v___f_385_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0));
return v___f_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___boxed(lean_object* v___dummy_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Doc_instMarkdownBlockEmpty___redArg();
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object* v_i_388_){
_start:
{
lean_object* v___f_389_; 
v___f_389_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0));
return v___f_389_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
if (lean_obj_tag(v_x_391_) == 0)
{
uint8_t v___x_392_; 
v___x_392_ = 1;
return v___x_392_;
}
else
{
uint8_t v___x_393_; 
v___x_393_ = 0;
return v___x_393_;
}
}
else
{
if (lean_obj_tag(v_x_391_) == 0)
{
uint8_t v___x_394_; 
v___x_394_ = 0;
return v___x_394_;
}
else
{
lean_object* v_val_395_; lean_object* v_val_396_; uint32_t v___x_397_; uint32_t v___x_398_; uint8_t v___x_399_; 
v_val_395_ = lean_ctor_get(v_x_390_, 0);
v_val_396_ = lean_ctor_get(v_x_391_, 0);
v___x_397_ = lean_unbox_uint32(v_val_395_);
v___x_398_ = lean_unbox_uint32(v_val_396_);
v___x_399_ = lean_uint32_dec_eq(v___x_397_, v___x_398_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1___boxed(lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_x_400_, v_x_401_);
lean_dec(v_x_401_);
lean_dec(v_x_400_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(lean_object* v_s_404_, uint32_t v_c_405_, lean_object* v_a_406_, uint8_t v_b_407_){
_start:
{
lean_object* v_str_408_; lean_object* v_startInclusive_409_; lean_object* v_endExclusive_410_; lean_object* v___x_411_; uint8_t v_decide_412_; 
v_str_408_ = lean_ctor_get(v_s_404_, 0);
v_startInclusive_409_ = lean_ctor_get(v_s_404_, 1);
v_endExclusive_410_ = lean_ctor_get(v_s_404_, 2);
v___x_411_ = lean_nat_sub(v_endExclusive_410_, v_startInclusive_409_);
v_decide_412_ = lean_nat_dec_eq(v_a_406_, v___x_411_);
lean_dec(v___x_411_);
if (v_decide_412_ == 0)
{
lean_object* v___x_413_; uint32_t v___x_414_; uint8_t v___x_415_; 
v___x_413_ = lean_nat_add(v_startInclusive_409_, v_a_406_);
lean_dec(v_a_406_);
v___x_414_ = lean_string_utf8_get_fast(v_str_408_, v___x_413_);
v___x_415_ = lean_uint32_dec_eq(v___x_414_, v_c_405_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_string_utf8_next_fast(v_str_408_, v___x_413_);
lean_dec(v___x_413_);
v___x_417_ = lean_nat_sub(v___x_416_, v_startInclusive_409_);
v_a_406_ = v___x_417_;
v_b_407_ = v___x_415_;
goto _start;
}
else
{
lean_dec(v___x_413_);
return v___x_415_;
}
}
else
{
lean_dec(v_a_406_);
return v_b_407_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg___boxed(lean_object* v_s_419_, lean_object* v_c_420_, lean_object* v_a_421_, lean_object* v_b_422_){
_start:
{
uint32_t v_c_boxed_423_; uint8_t v_b_boxed_424_; uint8_t v_res_425_; lean_object* v_r_426_; 
v_c_boxed_423_ = lean_unbox_uint32(v_c_420_);
lean_dec(v_c_420_);
v_b_boxed_424_ = lean_unbox(v_b_422_);
v_res_425_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_419_, v_c_boxed_423_, v_a_421_, v_b_boxed_424_);
lean_dec_ref(v_s_419_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(uint32_t v_c_427_, lean_object* v_s_428_){
_start:
{
lean_object* v_searcher_429_; uint8_t v___x_430_; uint8_t v___x_431_; 
v_searcher_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = 0;
v___x_431_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_428_, v_c_427_, v_searcher_429_, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0___boxed(lean_object* v_c_432_, lean_object* v_s_433_){
_start:
{
uint32_t v_c_boxed_434_; uint8_t v_res_435_; lean_object* v_r_436_; 
v_c_boxed_434_ = lean_unbox_uint32(v_c_432_);
lean_dec(v_c_432_);
v_res_435_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_boxed_434_, v_s_433_);
lean_dec_ref(v_s_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0));
v___x_439_ = lean_string_utf8_byte_size(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_440_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0));
v___x_443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
lean_ctor_set(v___x_443_, 1, v___x_441_);
lean_ctor_set(v___x_443_, 2, v___x_440_);
return v___x_443_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_444_; lean_object* v___x_445_; 
v___x_444_ = 91;
v___x_445_ = lean_box_uint32(v___x_444_);
return v___x_445_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1;
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(uint32_t v_c_448_, lean_object* v_next_x3f_449_){
_start:
{
uint32_t v___x_450_; uint8_t v___x_451_; 
v___x_450_ = 33;
v___x_451_ = lean_uint32_dec_eq(v_c_448_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2);
v___x_453_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_448_, v___x_452_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3);
v___x_455_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_449_, v___x_454_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___boxed(lean_object* v_c_456_, lean_object* v_next_x3f_457_){
_start:
{
uint32_t v_c_boxed_458_; uint8_t v_res_459_; lean_object* v_r_460_; 
v_c_boxed_458_ = lean_unbox_uint32(v_c_456_);
lean_dec(v_c_456_);
v_res_459_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_boxed_458_, v_next_x3f_457_);
lean_dec(v_next_x3f_457_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(lean_object* v_s_461_, uint32_t v_c_462_, lean_object* v_inst_463_, lean_object* v_R_464_, lean_object* v_a_465_, uint8_t v_b_466_, lean_object* v_c_467_){
_start:
{
uint8_t v___x_468_; 
v___x_468_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_461_, v_c_462_, v_a_465_, v_b_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___boxed(lean_object* v_s_469_, lean_object* v_c_470_, lean_object* v_inst_471_, lean_object* v_R_472_, lean_object* v_a_473_, lean_object* v_b_474_, lean_object* v_c_475_){
_start:
{
uint32_t v_c_boxed_476_; uint8_t v_b_boxed_477_; uint8_t v_res_478_; lean_object* v_r_479_; 
v_c_boxed_476_ = lean_unbox_uint32(v_c_470_);
lean_dec(v_c_470_);
v_b_boxed_477_ = lean_unbox(v_b_474_);
v_res_478_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(v_s_469_, v_c_boxed_476_, v_inst_471_, v_R_472_, v_a_473_, v_b_boxed_477_, v_c_475_);
lean_dec_ref(v_s_469_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_480_; lean_object* v___x_481_; 
v___x_480_ = 32;
v___x_481_ = lean_box_uint32(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(lean_object* v_prev_x3f_484_, uint32_t v_c_485_, lean_object* v_next_x3f_486_){
_start:
{
uint8_t v___y_488_; lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0);
v___x_506_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_486_, v___x_505_);
if (v___x_506_ == 0)
{
if (lean_obj_tag(v_next_x3f_486_) == 0)
{
uint8_t v___x_507_; 
v___x_507_ = 1;
v___y_488_ = v___x_507_;
goto v___jp_487_;
}
else
{
v___y_488_ = v___x_506_;
goto v___jp_487_;
}
}
else
{
v___y_488_ = v___x_506_;
goto v___jp_487_;
}
v___jp_487_:
{
uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 62;
v___x_490_ = lean_uint32_dec_eq(v_c_485_, v___x_489_);
if (v___x_490_ == 0)
{
uint32_t v___x_491_; uint8_t v___x_492_; 
v___x_491_ = 45;
v___x_492_ = lean_uint32_dec_eq(v_c_485_, v___x_491_);
if (v___x_492_ == 0)
{
uint32_t v___x_493_; uint8_t v___x_494_; 
v___x_493_ = 43;
v___x_494_ = lean_uint32_dec_eq(v_c_485_, v___x_493_);
if (v___x_494_ == 0)
{
uint32_t v___x_495_; uint8_t v___x_496_; 
v___x_495_ = 46;
v___x_496_ = lean_uint32_dec_eq(v_c_485_, v___x_495_);
if (v___x_496_ == 0)
{
uint8_t v___x_497_; 
v___x_497_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_485_, v_next_x3f_486_);
return v___x_497_;
}
else
{
if (lean_obj_tag(v_prev_x3f_484_) == 0)
{
return v___x_494_;
}
else
{
lean_object* v_val_498_; uint32_t v___x_499_; uint32_t v___x_500_; uint8_t v___x_501_; 
v_val_498_ = lean_ctor_get(v_prev_x3f_484_, 0);
v___x_499_ = 48;
v___x_500_ = lean_unbox_uint32(v_val_498_);
v___x_501_ = lean_uint32_dec_le(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
return v___x_501_;
}
else
{
uint32_t v___x_502_; uint32_t v___x_503_; uint8_t v___x_504_; 
v___x_502_ = 57;
v___x_503_ = lean_unbox_uint32(v_val_498_);
v___x_504_ = lean_uint32_dec_le(v___x_503_, v___x_502_);
if (v___x_504_ == 0)
{
return v___x_504_;
}
else
{
return v___y_488_;
}
}
}
}
}
else
{
return v___y_488_;
}
}
else
{
return v___y_488_;
}
}
else
{
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___boxed(lean_object* v_prev_x3f_508_, lean_object* v_c_509_, lean_object* v_next_x3f_510_){
_start:
{
uint32_t v_c_boxed_511_; uint8_t v_res_512_; lean_object* v_r_513_; 
v_c_boxed_511_ = lean_unbox_uint32(v_c_509_);
lean_dec(v_c_509_);
v_res_512_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_prev_x3f_508_, v_c_boxed_511_, v_next_x3f_510_);
lean_dec(v_next_x3f_510_);
lean_dec(v_prev_x3f_508_);
v_r_513_ = lean_box(v_res_512_);
return v_r_513_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0));
v___x_516_ = lean_string_utf8_byte_size(v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1);
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0));
v___x_520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v___x_518_);
lean_ctor_set(v___x_520_, 2, v___x_517_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(uint32_t v___x_521_, lean_object* v___x_522_, lean_object* v_____r_523_, lean_object* v_s_x27_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint32_t v___x_538_; uint8_t v___x_539_; 
v___x_525_ = lean_string_push(v_s_x27_524_, v___x_521_);
v___x_526_ = lean_box_uint32(v___x_521_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
v___x_538_ = 48;
v___x_539_ = lean_uint32_dec_le(v___x_538_, v___x_521_);
if (v___x_539_ == 0)
{
goto v___jp_532_;
}
else
{
uint32_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = 57;
v___x_541_ = lean_uint32_dec_le(v___x_521_, v___x_540_);
if (v___x_541_ == 0)
{
goto v___jp_532_;
}
else
{
goto v___jp_528_;
}
}
v___jp_528_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_522_);
lean_ctor_set(v___x_529_, 1, v___x_527_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_525_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
v___jp_532_:
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2);
v___x_534_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v___x_521_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_522_);
lean_ctor_set(v___x_535_, 1, v___x_527_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_525_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
else
{
goto v___jp_528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed(lean_object* v___x_542_, lean_object* v___x_543_, lean_object* v_____r_544_, lean_object* v_s_x27_545_){
_start:
{
uint32_t v___x_2058__boxed_546_; lean_object* v_res_547_; 
v___x_2058__boxed_546_ = lean_unbox_uint32(v___x_542_);
lean_dec(v___x_542_);
v_res_547_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_2058__boxed_546_, v___x_543_, v_____r_544_, v_s_x27_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(lean_object* v_s_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___y_551_; lean_object* v_snd_555_; lean_object* v_fst_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_594_; 
v_snd_555_ = lean_ctor_get(v_a_549_, 1);
v_fst_556_ = lean_ctor_get(v_a_549_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_a_549_);
if (v_isSharedCheck_594_ == 0)
{
v___x_558_ = v_a_549_;
v_isShared_559_ = v_isSharedCheck_594_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snd_555_);
lean_inc(v_fst_556_);
lean_dec(v_a_549_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_594_;
goto v_resetjp_557_;
}
v___jp_550_:
{
if (lean_obj_tag(v___y_551_) == 0)
{
lean_object* v_a_552_; 
v_a_552_ = lean_ctor_get(v___y_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___y_551_, 1);
return v_a_552_;
}
else
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v___y_551_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___y_551_, 1);
v_a_549_ = v_a_553_;
goto _start;
}
}
v_resetjp_557_:
{
lean_object* v_fst_560_; lean_object* v_snd_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_593_; 
v_fst_560_ = lean_ctor_get(v_snd_555_, 0);
v_snd_561_ = lean_ctor_get(v_snd_555_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_snd_555_);
if (v_isSharedCheck_593_ == 0)
{
v___x_563_ = v_snd_555_;
v_isShared_564_ = v_isSharedCheck_593_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_snd_561_);
lean_inc(v_fst_560_);
lean_dec(v_snd_555_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_593_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; uint8_t v_decide_566_; 
v___x_565_ = lean_string_utf8_byte_size(v_s_548_);
v_decide_566_ = lean_nat_dec_eq(v_fst_560_, v___x_565_);
if (v_decide_566_ == 0)
{
uint32_t v___x_567_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___f_580_; uint8_t v_decide_585_; 
lean_del_object(v___x_563_);
lean_del_object(v___x_558_);
v___x_567_ = lean_string_utf8_get_fast(v_s_548_, v_fst_560_);
v___x_578_ = lean_string_utf8_next_fast(v_s_548_, v_fst_560_);
lean_dec(v_fst_560_);
v___x_579_ = lean_box_uint32(v___x_567_);
v___f_580_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_580_, 0, v___x_579_);
lean_closure_set(v___f_580_, 1, v___x_578_);
v_decide_585_ = lean_nat_dec_eq(v___x_578_, v___x_565_);
if (v_decide_585_ == 0)
{
goto v___jp_581_;
}
else
{
if (v_decide_566_ == 0)
{
lean_object* v_prev_x3f_586_; 
v_prev_x3f_586_ = lean_box(0);
v___y_569_ = v___f_580_;
v___y_570_ = v_prev_x3f_586_;
goto v___jp_568_;
}
else
{
goto v___jp_581_;
}
}
v___jp_568_:
{
uint8_t v___x_571_; 
v___x_571_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_snd_561_, v___x_567_, v___y_570_);
lean_dec(v___y_570_);
lean_dec(v_snd_561_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_box(0);
v___x_573_ = lean_apply_2(v___y_569_, v___x_572_, v_fst_556_);
v___y_551_ = v___x_573_;
goto v___jp_550_;
}
else
{
uint32_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_574_ = 92;
v___x_575_ = lean_string_push(v_fst_556_, v___x_574_);
v___x_576_ = lean_box(0);
v___x_577_ = lean_apply_2(v___y_569_, v___x_576_, v___x_575_);
v___y_551_ = v___x_577_;
goto v___jp_550_;
}
}
v___jp_581_:
{
uint32_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_string_utf8_get_fast(v_s_548_, v___x_578_);
v___x_583_ = lean_box_uint32(v___x_582_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
v___y_569_ = v___f_580_;
v___y_570_ = v___x_584_;
goto v___jp_568_;
}
}
else
{
lean_object* v___x_588_; 
if (v_isShared_564_ == 0)
{
v___x_588_ = v___x_563_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_fst_560_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_snd_561_);
v___x_588_ = v_reuseFailAlloc_592_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_590_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v___x_588_);
v___x_590_ = v___x_558_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_fst_556_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___boxed(lean_object* v_s_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_595_, v_a_596_);
lean_dec_ref(v_s_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(uint32_t v___x_598_, lean_object* v___x_599_, lean_object* v_____r_600_, lean_object* v_s_x27_601_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_string_push(v_s_x27_601_, v___x_598_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v___x_599_);
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0___boxed(lean_object* v___x_605_, lean_object* v___x_606_, lean_object* v_____r_607_, lean_object* v_s_x27_608_){
_start:
{
uint32_t v___x_2188__boxed_609_; lean_object* v_res_610_; 
v___x_2188__boxed_609_ = lean_unbox_uint32(v___x_605_);
lean_dec(v___x_605_);
v_res_610_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_2188__boxed_609_, v___x_606_, v_____r_607_, v_s_x27_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(lean_object* v_s_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___y_614_; lean_object* v_fst_618_; lean_object* v_snd_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_644_; 
v_fst_618_ = lean_ctor_get(v_a_612_, 0);
v_snd_619_ = lean_ctor_get(v_a_612_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v_a_612_);
if (v_isSharedCheck_644_ == 0)
{
v___x_621_ = v_a_612_;
v_isShared_622_ = v_isSharedCheck_644_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_snd_619_);
lean_inc(v_fst_618_);
lean_dec(v_a_612_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_644_;
goto v_resetjp_620_;
}
v___jp_613_:
{
if (lean_obj_tag(v___y_614_) == 0)
{
lean_object* v_a_615_; 
v_a_615_ = lean_ctor_get(v___y_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___y_614_, 1);
return v_a_615_;
}
else
{
lean_object* v_a_616_; 
v_a_616_ = lean_ctor_get(v___y_614_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___y_614_, 1);
v_a_612_ = v_a_616_;
goto _start;
}
}
v_resetjp_620_:
{
lean_object* v___x_623_; uint8_t v_decide_624_; 
v___x_623_ = lean_string_utf8_byte_size(v_s_611_);
v_decide_624_ = lean_nat_dec_eq(v_snd_619_, v___x_623_);
if (v_decide_624_ == 0)
{
uint32_t v___x_625_; lean_object* v___x_626_; lean_object* v___y_628_; uint8_t v_decide_636_; 
lean_del_object(v___x_621_);
v___x_625_ = lean_string_utf8_get_fast(v_s_611_, v_snd_619_);
v___x_626_ = lean_string_utf8_next_fast(v_s_611_, v_snd_619_);
lean_dec(v_snd_619_);
v_decide_636_ = lean_nat_dec_eq(v___x_626_, v___x_623_);
if (v_decide_636_ == 0)
{
uint32_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_string_utf8_get_fast(v_s_611_, v___x_626_);
v___x_638_ = lean_box_uint32(v___x_637_);
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
v___y_628_ = v___x_639_;
goto v___jp_627_;
}
else
{
lean_object* v_prev_x3f_640_; 
v_prev_x3f_640_ = lean_box(0);
v___y_628_ = v_prev_x3f_640_;
goto v___jp_627_;
}
v___jp_627_:
{
uint8_t v___x_629_; 
v___x_629_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v___x_625_, v___y_628_);
lean_dec(v___y_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_box(0);
v___x_631_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_625_, v___x_626_, v___x_630_, v_fst_618_);
v___y_614_ = v___x_631_;
goto v___jp_613_;
}
else
{
uint32_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_632_ = 92;
v___x_633_ = lean_string_push(v_fst_618_, v___x_632_);
v___x_634_ = lean_box(0);
v___x_635_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_625_, v___x_626_, v___x_634_, v___x_633_);
v___y_614_ = v___x_635_;
goto v___jp_613_;
}
}
}
else
{
lean_object* v___x_642_; 
if (v_isShared_622_ == 0)
{
v___x_642_ = v___x_621_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_fst_618_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_snd_619_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___boxed(lean_object* v_s_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_645_, v_a_646_);
lean_dec_ref(v_s_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object* v_s_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_snd_657_; lean_object* v_fst_658_; lean_object* v_fst_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_668_; 
v___x_655_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1));
v___x_656_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_654_, v___x_655_);
v_snd_657_ = lean_ctor_get(v___x_656_, 1);
lean_inc(v_snd_657_);
v_fst_658_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_fst_658_);
lean_dec_ref(v___x_656_);
v_fst_659_ = lean_ctor_get(v_snd_657_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v_snd_657_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v_snd_657_, 1);
lean_dec(v_unused_669_);
v___x_661_ = v_snd_657_;
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_fst_659_);
lean_dec(v_snd_657_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v_fst_659_);
lean_ctor_set(v___x_661_, 0, v_fst_658_);
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_fst_658_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_fst_659_);
v___x_664_ = v_reuseFailAlloc_667_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; lean_object* v_fst_666_; 
v___x_665_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_654_, v___x_664_);
v_fst_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_fst_666_);
lean_dec_ref(v___x_665_);
return v_fst_666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object* v_s_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_670_);
lean_dec_ref(v_s_670_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object* v_s_672_, lean_object* v_inst_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_672_, v_a_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object* v_s_676_, lean_object* v_inst_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_676_, v_inst_677_, v_a_678_);
lean_dec_ref(v_s_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(lean_object* v_s_680_, lean_object* v_inst_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_680_, v_a_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___boxed(lean_object* v_s_684_, lean_object* v_inst_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(v_s_684_, v_inst_685_, v_a_686_);
lean_dec_ref(v_s_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v_str_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_snd_690_; lean_object* v_fst_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_733_; 
v_snd_690_ = lean_ctor_get(v_a_689_, 1);
v_fst_691_ = lean_ctor_get(v_a_689_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_a_689_);
if (v_isSharedCheck_733_ == 0)
{
v___x_693_ = v_a_689_;
v_isShared_694_ = v_isSharedCheck_733_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_snd_690_);
lean_inc(v_fst_691_);
lean_dec(v_a_689_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_733_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_fst_695_; lean_object* v_snd_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_732_; 
v_fst_695_ = lean_ctor_get(v_snd_690_, 0);
v_snd_696_ = lean_ctor_get(v_snd_690_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_snd_690_);
if (v_isSharedCheck_732_ == 0)
{
v___x_698_ = v_snd_690_;
v_isShared_699_ = v_isSharedCheck_732_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_snd_696_);
lean_inc(v_fst_695_);
lean_dec(v_snd_690_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_732_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; uint8_t v_decide_701_; 
v___x_700_ = lean_string_utf8_byte_size(v_str_688_);
v_decide_701_ = lean_nat_dec_eq(v_snd_696_, v___x_700_);
if (v_decide_701_ == 0)
{
uint32_t v___x_702_; lean_object* v___x_703_; uint32_t v___x_704_; uint8_t v___x_705_; 
v___x_702_ = lean_string_utf8_get_fast(v_str_688_, v_snd_696_);
v___x_703_ = lean_string_utf8_next_fast(v_str_688_, v_snd_696_);
lean_dec(v_snd_696_);
v___x_704_ = 96;
v___x_705_ = lean_uint32_dec_eq(v___x_702_, v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v_longest_706_; lean_object* v___y_708_; uint8_t v___x_716_; 
v_longest_706_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_nat_dec_le(v_fst_691_, v_fst_695_);
if (v___x_716_ == 0)
{
lean_dec(v_fst_695_);
v___y_708_ = v_fst_691_;
goto v___jp_707_;
}
else
{
lean_dec(v_fst_691_);
v___y_708_ = v_fst_695_;
goto v___jp_707_;
}
v___jp_707_:
{
lean_object* v___x_710_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_703_);
lean_ctor_set(v___x_698_, 0, v_longest_706_);
v___x_710_ = v___x_698_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_longest_706_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_703_);
v___x_710_ = v_reuseFailAlloc_715_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_712_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_710_);
lean_ctor_set(v___x_693_, 0, v___y_708_);
v___x_712_ = v___x_693_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___y_708_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_714_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
v_a_689_ = v___x_712_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = lean_nat_add(v_fst_695_, v___x_717_);
lean_dec(v_fst_695_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_703_);
lean_ctor_set(v___x_698_, 0, v___x_718_);
v___x_720_ = v___x_698_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_703_);
v___x_720_ = v_reuseFailAlloc_725_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_720_);
v___x_722_ = v___x_693_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_fst_691_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_724_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
v_a_689_ = v___x_722_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_727_; 
if (v_isShared_699_ == 0)
{
v___x_727_ = v___x_698_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_fst_695_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_snd_696_);
v___x_727_ = v_reuseFailAlloc_731_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_729_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_727_);
v___x_729_ = v___x_693_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_fst_691_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v_str_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_734_, v_a_735_);
lean_dec_ref(v_str_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(lean_object* v_str_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_snd_745_; lean_object* v_fst_746_; lean_object* v_fst_747_; uint8_t v___x_748_; 
v___x_743_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1));
v___x_744_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_742_, v___x_743_);
v_snd_745_ = lean_ctor_get(v___x_744_, 1);
lean_inc(v_snd_745_);
v_fst_746_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_fst_746_);
lean_dec_ref(v___x_744_);
v_fst_747_ = lean_ctor_get(v_snd_745_, 0);
lean_inc(v_fst_747_);
lean_dec(v_snd_745_);
v___x_748_ = lean_nat_dec_le(v_fst_746_, v_fst_747_);
if (v___x_748_ == 0)
{
lean_dec(v_fst_747_);
return v_fst_746_;
}
else
{
lean_dec(v_fst_746_);
return v_fst_747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___boxed(lean_object* v_str_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_749_);
lean_dec_ref(v_str_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(lean_object* v_str_751_, lean_object* v_inst_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_751_, v_a_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v_str_755_, lean_object* v_inst_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(v_str_755_, v_inst_756_, v_a_757_);
lean_dec_ref(v_str_755_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(lean_object* v_x_759_, lean_object* v_x_760_){
_start:
{
lean_object* v_zero_761_; uint8_t v_isZero_762_; 
v_zero_761_ = lean_unsigned_to_nat(0u);
v_isZero_762_ = lean_nat_dec_eq(v_x_759_, v_zero_761_);
if (v_isZero_762_ == 1)
{
lean_dec(v_x_759_);
return v_x_760_;
}
else
{
uint32_t v___x_763_; lean_object* v_one_764_; lean_object* v_n_765_; lean_object* v___x_766_; 
v___x_763_ = 96;
v_one_764_ = lean_unsigned_to_nat(1u);
v_n_765_ = lean_nat_sub(v_x_759_, v_one_764_);
lean_dec(v_x_759_);
v___x_766_ = lean_string_push(v_x_760_, v___x_763_);
v_x_759_ = v_n_765_;
v_x_760_ = v___x_766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(lean_object* v_atLeast_768_, lean_object* v_str_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___y_772_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_776_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_769_);
v___x_777_ = lean_nat_dec_le(v_atLeast_768_, v___x_776_);
if (v___x_777_ == 0)
{
lean_dec(v___x_776_);
v___y_772_ = v_atLeast_768_;
goto v___jp_771_;
}
else
{
lean_dec(v_atLeast_768_);
v___y_772_ = v___x_776_;
goto v___jp_771_;
}
v___jp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_add(v___y_772_, v___x_773_);
lean_dec(v___y_772_);
v___x_775_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(v___x_774_, v___x_770_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor___boxed(lean_object* v_atLeast_778_, lean_object* v_str_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v_atLeast_778_, v_str_779_);
lean_dec_ref(v_str_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object* v_str_782_){
_start:
{
lean_object* v___x_783_; lean_object* v_backticks_784_; lean_object* v___y_786_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_783_ = lean_unsigned_to_nat(0u);
v_backticks_784_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_783_, v_str_782_);
v___x_800_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1));
v___x_801_ = lean_string_utf8_byte_size(v_str_782_);
v___x_802_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2);
v___x_803_ = lean_nat_dec_le(v___x_802_, v___x_801_);
if (v___x_803_ == 0)
{
goto v___jp_793_;
}
else
{
uint8_t v___x_804_; 
v___x_804_ = lean_string_memcmp(v_str_782_, v___x_800_, v___x_783_, v___x_783_, v___x_802_);
if (v___x_804_ == 0)
{
goto v___jp_793_;
}
else
{
goto v___jp_789_;
}
}
v___jp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_inc_ref(v_backticks_784_);
v___x_787_ = lean_string_append(v_backticks_784_, v___y_786_);
lean_dec_ref(v___y_786_);
v___x_788_ = lean_string_append(v___x_787_, v_backticks_784_);
lean_dec_ref(v_backticks_784_);
return v___x_788_;
}
v___jp_789_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_791_ = lean_string_append(v___x_790_, v_str_782_);
lean_dec_ref(v_str_782_);
v___x_792_ = lean_string_append(v___x_791_, v___x_790_);
v___y_786_ = v___x_792_;
goto v___jp_785_;
}
v___jp_793_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_794_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1));
v___x_795_ = lean_string_utf8_byte_size(v_str_782_);
v___x_796_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2);
v___x_797_ = lean_nat_dec_le(v___x_796_, v___x_795_);
if (v___x_797_ == 0)
{
v___y_786_ = v_str_782_;
goto v___jp_785_;
}
else
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = lean_nat_sub(v___x_795_, v___x_796_);
v___x_799_ = lean_string_memcmp(v_str_782_, v___x_794_, v___x_798_, v___x_783_, v___x_796_);
lean_dec(v___x_798_);
if (v___x_799_ == 0)
{
v___y_786_ = v_str_782_;
goto v___jp_785_;
}
else
{
goto v___jp_789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg(){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___closed__0));
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___boxed(lean_object* v___dummy_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg();
return v_res_810_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg();
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(lean_object* v_s_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___boxed(lean_object* v_s_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v_s_814_);
lean_dec_ref(v_s_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(lean_object* v_str_816_, lean_object* v___x_817_, lean_object* v___x_818_, lean_object* v_a_819_, lean_object* v_b_820_){
_start:
{
lean_object* v_it_822_; lean_object* v_startInclusive_823_; lean_object* v_endExclusive_824_; 
if (lean_obj_tag(v_a_819_) == 0)
{
lean_object* v_currPos_828_; lean_object* v_searcher_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_852_; 
v_currPos_828_ = lean_ctor_get(v_a_819_, 0);
v_searcher_829_ = lean_ctor_get(v_a_819_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_a_819_);
if (v_isSharedCheck_852_ == 0)
{
v___x_831_ = v_a_819_;
v_isShared_832_ = v_isSharedCheck_852_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_searcher_829_);
lean_inc(v_currPos_828_);
lean_dec(v_a_819_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_852_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
uint8_t v_decide_833_; 
v_decide_833_ = lean_nat_dec_eq(v_searcher_829_, v___x_818_);
if (v_decide_833_ == 0)
{
uint32_t v___x_834_; uint32_t v___x_835_; uint8_t v___x_836_; 
v___x_834_ = 10;
v___x_835_ = lean_string_utf8_get_fast(v_str_816_, v_searcher_829_);
v___x_836_ = lean_uint32_dec_eq(v___x_835_, v___x_834_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_string_utf8_next_fast(v_str_816_, v_searcher_829_);
lean_dec(v_searcher_829_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_837_);
v___x_839_ = v___x_831_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_currPos_828_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_837_);
v___x_839_ = v_reuseFailAlloc_841_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
v_a_819_ = v___x_839_;
goto _start;
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v_slice_845_; lean_object* v_nextIt_847_; 
v___x_842_ = lean_string_utf8_next_fast(v_str_816_, v_searcher_829_);
v___x_843_ = lean_nat_sub(v___x_842_, v_searcher_829_);
v___x_844_ = lean_nat_add(v_searcher_829_, v___x_843_);
lean_dec(v___x_843_);
v_slice_845_ = l_String_Slice_subslice_x21(v___x_817_, v_currPos_828_, v_searcher_829_);
lean_inc(v___x_844_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_844_);
lean_ctor_set(v___x_831_, 0, v___x_844_);
v_nextIt_847_ = v___x_831_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_844_);
v_nextIt_847_ = v_reuseFailAlloc_850_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v_startInclusive_848_; lean_object* v_endExclusive_849_; 
v_startInclusive_848_ = lean_ctor_get(v_slice_845_, 0);
lean_inc(v_startInclusive_848_);
v_endExclusive_849_ = lean_ctor_get(v_slice_845_, 1);
lean_inc(v_endExclusive_849_);
lean_dec_ref(v_slice_845_);
v_it_822_ = v_nextIt_847_;
v_startInclusive_823_ = v_startInclusive_848_;
v_endExclusive_824_ = v_endExclusive_849_;
goto v___jp_821_;
}
}
}
else
{
lean_object* v___x_851_; 
lean_del_object(v___x_831_);
lean_dec(v_searcher_829_);
v___x_851_ = lean_box(1);
lean_inc(v___x_818_);
v_it_822_ = v___x_851_;
v_startInclusive_823_ = v_currPos_828_;
v_endExclusive_824_ = v___x_818_;
goto v___jp_821_;
}
}
}
else
{
lean_dec(v___x_818_);
return v_b_820_;
}
v___jp_821_:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_string_utf8_extract_fast(v_str_816_, v_startInclusive_823_, v_endExclusive_824_);
lean_dec(v_endExclusive_824_);
lean_dec(v_startInclusive_823_);
v___x_826_ = lean_array_push(v_b_820_, v___x_825_);
v_a_819_ = v_it_822_;
v_b_820_ = v___x_826_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg___boxed(lean_object* v_str_853_, lean_object* v___x_854_, lean_object* v___x_855_, lean_object* v_a_856_, lean_object* v_b_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_853_, v___x_854_, v___x_855_, v_a_856_, v_b_857_);
lean_dec_ref(v___x_854_);
lean_dec_ref(v_str_853_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(lean_object* v_str_859_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_string_utf8_byte_size(v_str_859_);
lean_inc_ref(v_str_859_);
v___x_862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_862_, 0, v_str_859_);
lean_ctor_set(v___x_862_, 1, v___x_860_);
lean_ctor_set(v___x_862_, 2, v___x_861_);
v___x_863_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0);
v___x_864_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_865_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_859_, v___x_862_, v___x_861_, v___x_863_, v___x_864_);
lean_dec_ref_known(v___x_862_, 3);
lean_dec_ref(v_str_859_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(lean_object* v_str_866_, lean_object* v___x_867_, lean_object* v___x_868_, lean_object* v_inst_869_, lean_object* v_R_870_, lean_object* v_a_871_, lean_object* v_b_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_866_, v___x_867_, v___x_868_, v_a_871_, v_b_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___boxed(lean_object* v_str_874_, lean_object* v___x_875_, lean_object* v___x_876_, lean_object* v_inst_877_, lean_object* v_R_878_, lean_object* v_a_879_, lean_object* v_b_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(v_str_874_, v___x_875_, v___x_876_, v_inst_877_, v_R_878_, v_a_879_, v_b_880_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v_str_874_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(lean_object* v_str_882_){
_start:
{
lean_object* v___x_883_; lean_object* v_fence_884_; lean_object* v___y_886_; lean_object* v_body_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_883_ = lean_unsigned_to_nat(2u);
v_fence_884_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_883_, v_str_882_);
v_body_892_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(v_str_882_);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_array_get_size(v_body_892_);
v___x_895_ = lean_nat_dec_lt(v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
v___y_886_ = v_body_892_;
goto v___jp_885_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_896_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_897_ = lean_unsigned_to_nat(1u);
v___x_898_ = lean_nat_sub(v___x_894_, v___x_897_);
v___x_899_ = lean_array_get(v___x_896_, v_body_892_, v___x_898_);
lean_dec(v___x_898_);
v___x_900_ = lean_string_utf8_byte_size(v___x_899_);
lean_dec(v___x_899_);
v___x_901_ = lean_nat_dec_eq(v___x_900_, v___x_893_);
if (v___x_901_ == 0)
{
v___y_886_ = v_body_892_;
goto v___jp_885_;
}
else
{
lean_object* v___x_902_; 
v___x_902_ = lean_array_pop(v_body_892_);
v___y_886_ = v___x_902_;
goto v___jp_885_;
}
}
v___jp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_887_ = lean_unsigned_to_nat(1u);
v___x_888_ = lean_mk_empty_array_with_capacity(v___x_887_);
v___x_889_ = lean_array_push(v___x_888_, v_fence_884_);
lean_inc_ref(v___x_889_);
v___x_890_ = l_Array_append___redArg(v___x_889_, v___y_886_);
lean_dec_ref(v___y_886_);
v___x_891_ = l_Array_append___redArg(v___x_890_, v___x_889_);
lean_dec_ref(v___x_889_);
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_903_, lean_object* v_pos_904_){
_start:
{
lean_object* v_str_905_; lean_object* v_startInclusive_906_; lean_object* v_endExclusive_907_; lean_object* v___x_908_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v_decide_919_; 
v_str_905_ = lean_ctor_get(v_s_903_, 0);
v_startInclusive_906_ = lean_ctor_get(v_s_903_, 1);
v_endExclusive_907_ = lean_ctor_get(v_s_903_, 2);
v___x_908_ = lean_nat_add(v_startInclusive_906_, v_pos_904_);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = lean_nat_sub(v_endExclusive_907_, v___x_908_);
v_decide_919_ = lean_nat_dec_eq(v___x_917_, v___x_918_);
lean_dec(v___x_918_);
if (v_decide_919_ == 0)
{
uint32_t v___x_920_; uint32_t v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_string_utf8_get_fast(v_str_905_, v___x_908_);
v___x_921_ = 32;
v___x_922_ = lean_uint32_dec_eq(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
uint32_t v___x_923_; uint8_t v___x_924_; 
v___x_923_ = 9;
v___x_924_ = lean_uint32_dec_eq(v___x_920_, v___x_923_);
if (v___x_924_ == 0)
{
uint32_t v___x_925_; uint8_t v___x_926_; 
v___x_925_ = 13;
v___x_926_ = lean_uint32_dec_eq(v___x_920_, v___x_925_);
if (v___x_926_ == 0)
{
uint32_t v___x_927_; uint8_t v___x_928_; 
v___x_927_ = 10;
v___x_928_ = lean_uint32_dec_eq(v___x_920_, v___x_927_);
if (v___x_928_ == 0)
{
lean_dec(v___x_908_);
return v_pos_904_;
}
else
{
goto v___jp_909_;
}
}
else
{
goto v___jp_909_;
}
}
else
{
goto v___jp_909_;
}
}
else
{
goto v___jp_909_;
}
}
else
{
lean_dec(v___x_908_);
return v_pos_904_;
}
v___jp_909_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_910_ = lean_string_utf8_next_fast(v_str_905_, v___x_908_);
v___x_911_ = lean_nat_sub(v___x_910_, v___x_908_);
lean_dec(v___x_908_);
v___x_912_ = lean_nat_add(v_pos_904_, v___x_911_);
lean_dec(v___x_911_);
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_nat_add(v_pos_904_, v___x_913_);
v___x_915_ = lean_nat_dec_le(v___x_914_, v___x_912_);
lean_dec(v___x_914_);
if (v___x_915_ == 0)
{
lean_dec(v___x_912_);
return v_pos_904_;
}
else
{
lean_dec(v_pos_904_);
v_pos_904_ = v___x_912_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object* v_s_929_, lean_object* v_pos_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_929_, v_pos_930_);
lean_dec_ref(v_s_929_);
return v_res_931_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Doc_Inline_empty___redArg();
return v___x_932_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object* v_a_936_){
_start:
{
if (lean_obj_tag(v_a_936_) == 0)
{
lean_object* v___x_937_; 
v___x_937_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
return v___x_937_;
}
else
{
lean_object* v_head_938_; 
v_head_938_ = lean_ctor_get(v_a_936_, 0);
lean_inc(v_head_938_);
switch(lean_obj_tag(v_head_938_))
{
case 0:
{
lean_object* v_tail_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_983_; 
v_tail_939_ = lean_ctor_get(v_a_936_, 1);
v_isSharedCheck_983_ = !lean_is_exclusive(v_a_936_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v_a_936_, 0);
lean_dec(v_unused_984_);
v___x_941_ = v_a_936_;
v_isShared_942_ = v_isSharedCheck_983_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_tail_939_);
lean_dec(v_a_936_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_983_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_string_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_982_; 
v_string_943_ = lean_ctor_get(v_head_938_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v_head_938_);
if (v_isSharedCheck_982_ == 0)
{
v___x_945_ = v_head_938_;
v_isShared_946_ = v_isSharedCheck_982_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_string_943_);
lean_dec(v_head_938_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_982_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v_decide_951_; 
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_string_utf8_byte_size(v_string_943_);
lean_inc_ref(v_string_943_);
v___x_949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_949_, 0, v_string_943_);
lean_ctor_set(v___x_949_, 1, v___x_947_);
lean_ctor_set(v___x_949_, 2, v___x_948_);
v___x_950_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_949_, v___x_947_);
lean_dec_ref_known(v___x_949_, 3);
v_decide_951_ = lean_nat_dec_eq(v___x_950_, v___x_948_);
if (v_decide_951_ == 0)
{
lean_object* v_s1_952_; lean_object* v_s2_953_; lean_object* v___x_955_; 
v_s1_952_ = lean_string_utf8_extract_fast(v_string_943_, v___x_947_, v___x_950_);
v_s2_953_ = lean_string_utf8_extract_fast(v_string_943_, v___x_950_, v___x_948_);
lean_dec(v___x_950_);
lean_dec_ref(v_string_943_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v_s2_953_);
v___x_955_ = v___x_945_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_s2_953_);
v___x_955_ = v_reuseFailAlloc_970_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_956_ = lean_array_mk(v_tail_939_);
v___x_957_ = lean_array_get_size(v___x_956_);
v___x_958_ = lean_nat_dec_eq(v___x_957_, v___x_947_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = lean_mk_empty_array_with_capacity(v___x_959_);
v___x_961_ = lean_array_push(v___x_960_, v___x_955_);
v___x_962_ = l_Array_append___redArg(v___x_961_, v___x_956_);
lean_dec_ref(v___x_956_);
v___x_963_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
if (v_isShared_942_ == 0)
{
lean_ctor_set_tag(v___x_941_, 0);
lean_ctor_set(v___x_941_, 1, v___x_963_);
lean_ctor_set(v___x_941_, 0, v_s1_952_);
v___x_965_ = v___x_941_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_s1_952_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
lean_object* v___x_968_; 
lean_dec_ref(v___x_956_);
if (v_isShared_942_ == 0)
{
lean_ctor_set_tag(v___x_941_, 0);
lean_ctor_set(v___x_941_, 1, v___x_955_);
lean_ctor_set(v___x_941_, 0, v_s1_952_);
v___x_968_ = v___x_941_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_s1_952_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_955_);
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
else
{
lean_object* v___x_971_; lean_object* v_fst_972_; lean_object* v_snd_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
lean_dec(v___x_950_);
lean_del_object(v___x_945_);
lean_del_object(v___x_941_);
v___x_971_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_939_);
v_fst_972_ = lean_ctor_get(v___x_971_, 0);
v_snd_973_ = lean_ctor_get(v___x_971_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_981_ == 0)
{
v___x_975_ = v___x_971_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_snd_973_);
lean_inc(v_fst_972_);
lean_dec(v___x_971_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = lean_string_append(v_string_943_, v_fst_972_);
lean_dec(v_fst_972_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_snd_973_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_985_; lean_object* v_content_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_tail_985_ = lean_ctor_get(v_a_936_, 1);
lean_inc(v_tail_985_);
lean_dec_ref_known(v_a_936_, 2);
v_content_986_ = lean_ctor_get(v_head_938_, 0);
lean_inc_ref(v_content_986_);
lean_dec_ref_known(v_head_938_, 1);
v___x_987_ = lean_array_to_list(v_content_986_);
v___x_988_ = l_List_appendTR___redArg(v___x_987_, v_tail_985_);
v_a_936_ = v___x_988_;
goto _start;
}
default: 
{
lean_object* v_tail_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1028_; 
v_tail_990_ = lean_ctor_get(v_a_936_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_a_936_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v_a_936_, 0);
lean_dec(v_unused_1029_);
v___x_992_ = v_a_936_;
v_isShared_993_ = v_isSharedCheck_1028_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_tail_990_);
lean_dec(v_a_936_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1028_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_995_ = lean_array_mk(v_tail_990_);
if (lean_obj_tag(v_head_938_) == 9)
{
lean_object* v_content_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v_content_996_ = lean_ctor_get(v_head_938_, 0);
v___x_997_ = lean_array_get_size(v_content_996_);
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = lean_nat_dec_eq(v___x_997_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = lean_array_get_size(v___x_995_);
v___x_1001_ = lean_nat_dec_eq(v___x_1000_, v___x_998_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_inc_ref(v_content_996_);
lean_dec_ref_known(v_head_938_, 1);
v___x_1002_ = l_Array_append___redArg(v_content_996_, v___x_995_);
lean_dec_ref(v___x_995_);
v___x_1003_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
lean_ctor_set(v___x_992_, 1, v___x_1003_);
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_1005_ = v___x_992_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
else
{
lean_object* v___x_1008_; 
lean_dec_ref(v___x_995_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
lean_ctor_set(v___x_992_, 1, v_head_938_);
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_1008_ = v___x_992_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_head_938_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
lean_dec_ref_known(v_head_938_, 1);
v___x_1010_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_995_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
lean_ctor_set(v___x_992_, 1, v___x_1010_);
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_1012_ = v___x_992_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1014_ = lean_array_get_size(v___x_995_);
v___x_1015_ = lean_unsigned_to_nat(0u);
v___x_1016_ = lean_nat_dec_eq(v___x_1014_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = lean_mk_empty_array_with_capacity(v___x_1017_);
v___x_1019_ = lean_array_push(v___x_1018_, v_head_938_);
v___x_1020_ = l_Array_append___redArg(v___x_1019_, v___x_995_);
lean_dec_ref(v___x_995_);
v___x_1021_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
lean_ctor_set(v___x_992_, 1, v___x_1021_);
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_1023_ = v___x_992_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
else
{
lean_object* v___x_1026_; 
lean_dec_ref(v___x_995_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
lean_ctor_set(v___x_992_, 1, v_head_938_);
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_1026_ = v___x_992_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_head_938_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_1033_){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_inline_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_1037_, lean_object* v_inline_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_1040_, lean_object* v_pos_1041_){
_start:
{
lean_object* v_str_1042_; lean_object* v_startInclusive_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v_decide_1047_; 
v_str_1042_ = lean_ctor_get(v_s_1040_, 0);
v_startInclusive_1043_ = lean_ctor_get(v_s_1040_, 1);
v___x_1044_ = lean_nat_add(v_startInclusive_1043_, v_pos_1041_);
v___x_1045_ = lean_nat_sub(v___x_1044_, v_startInclusive_1043_);
v___x_1046_ = lean_unsigned_to_nat(0u);
v_decide_1047_ = lean_nat_dec_eq(v___x_1045_, v___x_1046_);
if (v_decide_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1056_; uint32_t v___x_1057_; uint32_t v___x_1058_; uint8_t v___x_1059_; 
lean_inc(v_startInclusive_1043_);
lean_inc_ref(v_str_1042_);
v___x_1048_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1048_, 0, v_str_1042_);
lean_ctor_set(v___x_1048_, 1, v_startInclusive_1043_);
lean_ctor_set(v___x_1048_, 2, v___x_1044_);
v___x_1049_ = lean_unsigned_to_nat(1u);
v___x_1050_ = lean_nat_sub(v___x_1045_, v___x_1049_);
lean_dec(v___x_1045_);
v___x_1051_ = l_String_Slice_posLE(v___x_1048_, v___x_1050_);
lean_dec_ref_known(v___x_1048_, 3);
v___x_1056_ = lean_nat_add(v_startInclusive_1043_, v___x_1051_);
v___x_1057_ = lean_string_utf8_get_fast(v_str_1042_, v___x_1056_);
lean_dec(v___x_1056_);
v___x_1058_ = 32;
v___x_1059_ = lean_uint32_dec_eq(v___x_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
uint32_t v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = 9;
v___x_1061_ = lean_uint32_dec_eq(v___x_1057_, v___x_1060_);
if (v___x_1061_ == 0)
{
uint32_t v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = 13;
v___x_1063_ = lean_uint32_dec_eq(v___x_1057_, v___x_1062_);
if (v___x_1063_ == 0)
{
uint32_t v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = 10;
v___x_1065_ = lean_uint32_dec_eq(v___x_1057_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_dec(v___x_1051_);
return v_pos_1041_;
}
else
{
goto v___jp_1052_;
}
}
else
{
goto v___jp_1052_;
}
}
else
{
goto v___jp_1052_;
}
}
else
{
goto v___jp_1052_;
}
v___jp_1052_:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = lean_nat_add(v___x_1051_, v___x_1049_);
v___x_1054_ = lean_nat_dec_le(v___x_1053_, v_pos_1041_);
lean_dec(v___x_1053_);
if (v___x_1054_ == 0)
{
lean_dec(v___x_1051_);
return v_pos_1041_;
}
else
{
lean_dec(v_pos_1041_);
v_pos_1041_ = v___x_1051_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1045_);
lean_dec(v___x_1044_);
return v_pos_1041_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_1066_, lean_object* v_pos_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_1066_, v_pos_1067_);
lean_dec_ref(v_s_1066_);
return v_res_1068_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1070_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_xs_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1073_ = lean_array_get_size(v_xs_1072_);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_nat_dec_eq(v___x_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = lean_unsigned_to_nat(1u);
v___x_1077_ = lean_nat_sub(v___x_1073_, v___x_1076_);
v___x_1078_ = lean_array_fget(v_xs_1072_, v___x_1077_);
lean_dec(v___x_1077_);
switch(lean_obj_tag(v___x_1078_))
{
case 0:
{
lean_object* v_string_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1109_; 
v_string_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1109_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_string_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1109_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v_decide_1086_; 
v___x_1083_ = lean_string_utf8_byte_size(v_string_1079_);
lean_inc_ref(v_string_1079_);
v___x_1084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1084_, 0, v_string_1079_);
lean_ctor_set(v___x_1084_, 1, v___x_1074_);
lean_ctor_set(v___x_1084_, 2, v___x_1083_);
v___x_1085_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_1084_, v___x_1074_);
v_decide_1086_ = lean_nat_dec_eq(v___x_1085_, v___x_1083_);
lean_dec(v___x_1085_);
if (v_decide_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1087_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_1084_, v___x_1083_);
lean_dec_ref_known(v___x_1084_, 3);
v___x_1088_ = lean_array_pop(v_xs_1072_);
v___x_1089_ = lean_string_utf8_extract_fast(v_string_1079_, v___x_1074_, v___x_1087_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1089_);
v___x_1091_ = v___x_1081_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1092_ = lean_array_push(v___x_1088_, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
v___x_1094_ = lean_string_utf8_extract_fast(v_string_1079_, v___x_1087_, v___x_1083_);
lean_dec(v___x_1087_);
lean_dec_ref(v_string_1079_);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
return v___x_1095_;
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_fst_1099_; lean_object* v_snd_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1108_; 
lean_dec_ref_known(v___x_1084_, 3);
lean_del_object(v___x_1081_);
v___x_1097_ = lean_array_pop(v_xs_1072_);
v___x_1098_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1097_);
v_fst_1099_ = lean_ctor_get(v___x_1098_, 0);
v_snd_1100_ = lean_ctor_get(v___x_1098_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1102_ = v___x_1098_;
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_snd_1100_);
lean_inc(v_fst_1099_);
lean_dec(v___x_1098_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1104_ = lean_string_append(v_snd_1100_, v_string_1079_);
lean_dec_ref(v_string_1079_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v___x_1104_);
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_fst_1099_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
case 9:
{
lean_object* v_content_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_content_1110_ = lean_ctor_get(v___x_1078_, 0);
lean_inc_ref(v_content_1110_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1111_ = lean_array_pop(v_xs_1072_);
v___x_1112_ = l_Array_append___redArg(v___x_1111_, v_content_1110_);
lean_dec_ref(v_content_1110_);
v_xs_1072_ = v___x_1112_;
goto _start;
}
default: 
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v___x_1078_);
v___x_1114_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_xs_1072_);
v___x_1115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
return v___x_1116_;
}
}
}
else
{
lean_object* v___x_1117_; 
lean_dec_ref(v_xs_1072_);
v___x_1117_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_1118_, lean_object* v_xs_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_xs_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_1121_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_mk_empty_array_with_capacity(v___x_1122_);
v___x_1124_ = lean_array_push(v___x_1123_, v_inline_1121_);
v___x_1125_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_1126_, lean_object* v_inline_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_1129_){
_start:
{
lean_object* v___x_1130_; lean_object* v_fst_1131_; lean_object* v_snd_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1140_; 
v___x_1130_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1129_);
v_fst_1131_ = lean_ctor_get(v___x_1130_, 0);
v_snd_1132_ = lean_ctor_get(v___x_1130_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1134_ = v___x_1130_;
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_snd_1132_);
lean_inc(v_fst_1131_);
lean_dec(v___x_1130_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1136_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v___x_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_fst_1131_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_1141_, lean_object* v_inline_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_1142_);
return v___x_1143_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_instMonadEIO___redArg();
return v___x_1144_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0);
v___x_1146_ = l_StateRefT_x27_instMonad___redArg(v___x_1145_);
return v___x_1146_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1175_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13));
v___x_1176_ = lean_unsigned_to_nat(3u);
v___x_1177_ = lean_mk_empty_array_with_capacity(v___x_1176_);
v___x_1178_ = lean_array_push(v___x_1177_, v___x_1175_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object* v_inst_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1181_, v_x_1182_, v_x_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_1189_, lean_object* v_x_1190_, lean_object* v_x_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_pieces_1197_; lean_object* v_pieces_1201_; lean_object* v___x_1204_; lean_object* v_toApplicative_1205_; lean_object* v_toFunctor_1206_; lean_object* v_toSeq_1207_; lean_object* v_toSeqLeft_1208_; lean_object* v_toSeqRight_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___f_1212_; lean_object* v___f_1213_; lean_object* v___x_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1204_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1205_ = lean_ctor_get(v___x_1204_, 0);
v_toFunctor_1206_ = lean_ctor_get(v_toApplicative_1205_, 0);
v_toSeq_1207_ = lean_ctor_get(v_toApplicative_1205_, 2);
v_toSeqLeft_1208_ = lean_ctor_get(v_toApplicative_1205_, 3);
v_toSeqRight_1209_ = lean_ctor_get(v_toApplicative_1205_, 4);
v___f_1210_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1211_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1206_, 2);
v___f_1212_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1212_, 0, v_toFunctor_1206_);
v___f_1213_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1213_, 0, v_toFunctor_1206_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___f_1212_);
lean_ctor_set(v___x_1214_, 1, v___f_1213_);
lean_inc(v_toSeqRight_1209_);
v___f_1215_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1215_, 0, v_toSeqRight_1209_);
lean_inc(v_toSeqLeft_1208_);
v___f_1216_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1216_, 0, v_toSeqLeft_1208_);
lean_inc(v_toSeq_1207_);
v___f_1217_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1217_, 0, v_toSeq_1207_);
v___x_1218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1214_);
lean_ctor_set(v___x_1218_, 1, v___f_1210_);
lean_ctor_set(v___x_1218_, 2, v___f_1217_);
lean_ctor_set(v___x_1218_, 3, v___f_1216_);
lean_ctor_set(v___x_1218_, 4, v___f_1215_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___f_1211_);
v___x_1220_ = l_StateRefT_x27_instMonad___redArg(v___x_1219_);
switch(lean_obj_tag(v_x_1191_))
{
case 0:
{
lean_object* v_string_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec_ref(v___x_1220_);
lean_dec_ref(v_x_1190_);
lean_dec_ref(v_inst_1189_);
v_string_1221_ = lean_ctor_get(v_x_1191_, 0);
lean_inc_ref(v_string_1221_);
lean_dec_ref_known(v_x_1191_, 1);
v___x_1222_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1221_);
lean_dec_ref(v_string_1221_);
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = lean_mk_empty_array_with_capacity(v___x_1223_);
v___x_1225_ = lean_array_push(v___x_1224_, v___x_1222_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
case 1:
{
lean_object* v_content_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v___x_1220_);
v_content_1227_ = lean_ctor_get(v_x_1191_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_x_1191_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1229_ = v_x_1191_;
v_isShared_1230_ = v_isSharedCheck_1278_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_content_1227_);
lean_dec(v_x_1191_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1278_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set_tag(v___x_1229_, 9);
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_content_1227_);
v___x_1232_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v_snd_1234_; lean_object* v_fst_1235_; lean_object* v_fst_1236_; lean_object* v_snd_1237_; lean_object* v_pieces_1239_; uint8_t v_inEmph_1247_; uint8_t v_inBold_1248_; uint8_t v_inLink_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1276_; 
v___x_1233_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1232_);
v_snd_1234_ = lean_ctor_get(v___x_1233_, 1);
lean_inc(v_snd_1234_);
v_fst_1235_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_fst_1235_);
lean_dec_ref(v___x_1233_);
v_fst_1236_ = lean_ctor_get(v_snd_1234_, 0);
lean_inc(v_fst_1236_);
v_snd_1237_ = lean_ctor_get(v_snd_1234_, 1);
lean_inc(v_snd_1237_);
lean_dec(v_snd_1234_);
v_inEmph_1247_ = lean_ctor_get_uint8(v_x_1190_, 0);
v_inBold_1248_ = lean_ctor_get_uint8(v_x_1190_, 1);
v_inLink_1249_ = lean_ctor_get_uint8(v_x_1190_, 2);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_x_1190_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1251_ = v_x_1190_;
v_isShared_1252_ = v_isSharedCheck_1276_;
goto v_resetjp_1250_;
}
else
{
lean_dec(v_x_1190_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1276_;
goto v_resetjp_1250_;
}
v___jp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1240_ = lean_string_utf8_byte_size(v_snd_1237_);
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = lean_nat_dec_eq(v___x_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_mk_empty_array_with_capacity(v___x_1243_);
v___x_1245_ = lean_array_push(v___x_1244_, v_snd_1237_);
v___x_1246_ = lean_array_push(v_pieces_1239_, v___x_1245_);
v_pieces_1201_ = v___x_1246_;
goto v___jp_1200_;
}
else
{
lean_dec(v_snd_1237_);
v_pieces_1201_ = v_pieces_1239_;
goto v___jp_1200_;
}
}
v_resetjp_1250_:
{
uint8_t v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = 1;
if (v_isShared_1252_ == 0)
{
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1275_, 1, v_inBold_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1275_, 2, v_inLink_1249_);
v___x_1255_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; 
lean_ctor_set_uint8(v___x_1255_, 0, v___x_1253_);
v___x_1256_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1189_, v___x_1255_, v_fst_1236_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v_pieces_1259_; lean_object* v_pieces_1264_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1269_ = lean_string_utf8_byte_size(v_fst_1235_);
v___x_1270_ = lean_nat_dec_eq(v___x_1269_, v___x_1267_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_mk_empty_array_with_capacity(v___x_1271_);
v___x_1273_ = lean_array_push(v___x_1272_, v_fst_1235_);
v___x_1274_ = lean_array_push(v___x_1268_, v___x_1273_);
v_pieces_1264_ = v___x_1274_;
goto v___jp_1263_;
}
else
{
lean_dec(v_fst_1235_);
v_pieces_1264_ = v___x_1268_;
goto v___jp_1263_;
}
v___jp_1258_:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_array_push(v_pieces_1259_, v_a_1257_);
if (v_inEmph_1247_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1262_ = lean_array_push(v___x_1260_, v___x_1261_);
v_pieces_1239_ = v___x_1262_;
goto v___jp_1238_;
}
else
{
v_pieces_1239_ = v___x_1260_;
goto v___jp_1238_;
}
}
v___jp_1263_:
{
if (v_inEmph_1247_ == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1266_ = lean_array_push(v_pieces_1264_, v___x_1265_);
v_pieces_1259_ = v___x_1266_;
goto v___jp_1258_;
}
else
{
v_pieces_1259_ = v_pieces_1264_;
goto v___jp_1258_;
}
}
}
else
{
lean_dec(v_snd_1237_);
lean_dec(v_fst_1235_);
return v___x_1256_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1330_; 
lean_dec_ref(v___x_1220_);
v_content_1279_ = lean_ctor_get(v_x_1191_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_x_1191_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1281_ = v_x_1191_;
v_isShared_1282_ = v_isSharedCheck_1330_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_content_1279_);
lean_dec(v_x_1191_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1330_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set_tag(v___x_1281_, 9);
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_content_1279_);
v___x_1284_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; lean_object* v_snd_1286_; lean_object* v_fst_1287_; lean_object* v_fst_1288_; lean_object* v_snd_1289_; lean_object* v_pieces_1291_; uint8_t v_inEmph_1299_; uint8_t v_inBold_1300_; uint8_t v_inLink_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1328_; 
v___x_1285_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1284_);
v_snd_1286_ = lean_ctor_get(v___x_1285_, 1);
lean_inc(v_snd_1286_);
v_fst_1287_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_fst_1287_);
lean_dec_ref(v___x_1285_);
v_fst_1288_ = lean_ctor_get(v_snd_1286_, 0);
lean_inc(v_fst_1288_);
v_snd_1289_ = lean_ctor_get(v_snd_1286_, 1);
lean_inc(v_snd_1289_);
lean_dec(v_snd_1286_);
v_inEmph_1299_ = lean_ctor_get_uint8(v_x_1190_, 0);
v_inBold_1300_ = lean_ctor_get_uint8(v_x_1190_, 1);
v_inLink_1301_ = lean_ctor_get_uint8(v_x_1190_, 2);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_x_1190_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1303_ = v_x_1190_;
v_isShared_1304_ = v_isSharedCheck_1328_;
goto v_resetjp_1302_;
}
else
{
lean_dec(v_x_1190_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1328_;
goto v_resetjp_1302_;
}
v___jp_1290_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1292_ = lean_string_utf8_byte_size(v_snd_1289_);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_nat_dec_eq(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_mk_empty_array_with_capacity(v___x_1295_);
v___x_1297_ = lean_array_push(v___x_1296_, v_snd_1289_);
v___x_1298_ = lean_array_push(v_pieces_1291_, v___x_1297_);
v_pieces_1197_ = v___x_1298_;
goto v___jp_1196_;
}
else
{
lean_dec(v_snd_1289_);
v_pieces_1197_ = v_pieces_1291_;
goto v___jp_1196_;
}
}
v_resetjp_1302_:
{
uint8_t v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = 1;
if (v_isShared_1304_ == 0)
{
v___x_1307_ = v___x_1303_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, 0, v_inEmph_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, 2, v_inLink_1301_);
v___x_1307_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; 
lean_ctor_set_uint8(v___x_1307_, 1, v___x_1305_);
v___x_1308_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1189_, v___x_1307_, v_fst_1288_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v_pieces_1311_; lean_object* v_pieces_1316_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v___x_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1321_ = lean_string_utf8_byte_size(v_fst_1287_);
v___x_1322_ = lean_nat_dec_eq(v___x_1321_, v___x_1319_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = lean_mk_empty_array_with_capacity(v___x_1323_);
v___x_1325_ = lean_array_push(v___x_1324_, v_fst_1287_);
v___x_1326_ = lean_array_push(v___x_1320_, v___x_1325_);
v_pieces_1316_ = v___x_1326_;
goto v___jp_1315_;
}
else
{
lean_dec(v_fst_1287_);
v_pieces_1316_ = v___x_1320_;
goto v___jp_1315_;
}
v___jp_1310_:
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_array_push(v_pieces_1311_, v_a_1309_);
if (v_inBold_1300_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1314_ = lean_array_push(v___x_1312_, v___x_1313_);
v_pieces_1291_ = v___x_1314_;
goto v___jp_1290_;
}
else
{
v_pieces_1291_ = v___x_1312_;
goto v___jp_1290_;
}
}
v___jp_1315_:
{
if (v_inBold_1300_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1318_ = lean_array_push(v_pieces_1316_, v___x_1317_);
v_pieces_1311_ = v___x_1318_;
goto v___jp_1310_;
}
else
{
v_pieces_1311_ = v_pieces_1316_;
goto v___jp_1310_;
}
}
}
else
{
lean_dec(v_snd_1289_);
lean_dec(v_fst_1287_);
return v___x_1308_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec_ref(v___x_1220_);
lean_dec_ref(v_x_1190_);
lean_dec_ref(v_inst_1189_);
v_string_1331_ = lean_ctor_get(v_x_1191_, 0);
lean_inc_ref(v_string_1331_);
lean_dec_ref_known(v_x_1191_, 1);
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
lean_dec_ref(v___x_1220_);
lean_dec_ref(v_x_1190_);
lean_dec_ref(v_inst_1189_);
v_mode_1337_ = lean_ctor_get_uint8(v_x_1191_, sizeof(void*)*1);
if (v_mode_1337_ == 0)
{
lean_object* v_string_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_string_1338_ = lean_ctor_get(v_x_1191_, 0);
lean_inc_ref(v_string_1338_);
lean_dec_ref_known(v_x_1191_, 1);
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
v_string_1346_ = lean_ctor_get(v_x_1191_, 0);
lean_inc_ref(v_string_1346_);
lean_dec_ref_known(v_x_1191_, 1);
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
lean_dec_ref_known(v_x_1191_, 1);
lean_dec_ref(v___x_1220_);
lean_dec_ref(v_x_1190_);
lean_dec_ref(v_inst_1189_);
v___x_1354_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
case 6:
{
uint8_t v_inLink_1356_; 
v_inLink_1356_ = lean_ctor_get_uint8(v_x_1190_, 2);
if (v_inLink_1356_ == 0)
{
lean_object* v_content_1357_; lean_object* v_url_1358_; uint8_t v_inEmph_1359_; uint8_t v_inBold_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref(v___x_1220_);
v_content_1357_ = lean_ctor_get(v_x_1191_, 0);
lean_inc_ref(v_content_1357_);
v_url_1358_ = lean_ctor_get(v_x_1191_, 1);
lean_inc_ref(v_url_1358_);
lean_dec_ref_known(v_x_1191_, 2);
v_inEmph_1359_ = lean_ctor_get_uint8(v_x_1190_, 0);
v_inBold_1360_ = lean_ctor_get_uint8(v_x_1190_, 1);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_x_1190_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1362_ = v_x_1190_;
v_isShared_1363_ = v_isSharedCheck_1389_;
goto v_resetjp_1361_;
}
else
{
lean_dec(v_x_1190_);
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
v___x_1368_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1189_, v___x_1366_, v___x_1367_, v_a_1192_, v_a_1193_, v_a_1194_);
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
lean_object* v_content_1390_; lean_object* v___x_1391_; size_t v_sz_1392_; size_t v___x_1393_; lean_object* v___x_4335__overap_1394_; lean_object* v___x_1395_; 
v_content_1390_ = lean_ctor_get(v_x_1191_, 0);
lean_inc_ref(v_content_1390_);
lean_dec_ref_known(v_x_1191_, 2);
v___x_1391_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1391_, 0, v_inst_1189_);
lean_closure_set(v___x_1391_, 1, v_x_1190_);
v_sz_1392_ = lean_array_size(v_content_1390_);
v___x_1393_ = ((size_t)0ULL);
v___x_4335__overap_1394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1220_, v___x_1391_, v_sz_1392_, v___x_1393_, v_content_1390_);
lean_inc(v_a_1194_);
lean_inc_ref(v_a_1193_);
lean_inc(v_a_1192_);
v___x_1395_ = lean_apply_4(v___x_4335__overap_1394_, v_a_1192_, v_a_1193_, v_a_1194_, lean_box(0));
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
lean_object* v_name_1413_; lean_object* v_content_1414_; lean_object* v___x_1415_; size_t v_sz_1416_; size_t v___x_1417_; lean_object* v___x_4338__overap_1418_; lean_object* v___x_1419_; 
v_name_1413_ = lean_ctor_get(v_x_1191_, 0);
lean_inc_ref(v_name_1413_);
v_content_1414_ = lean_ctor_get(v_x_1191_, 1);
lean_inc_ref(v_content_1414_);
lean_dec_ref_known(v_x_1191_, 2);
v___x_1415_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1415_, 0, v_inst_1189_);
lean_closure_set(v___x_1415_, 1, v_x_1190_);
v_sz_1416_ = lean_array_size(v_content_1414_);
v___x_1417_ = ((size_t)0ULL);
v___x_4338__overap_1418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1220_, v___x_1415_, v_sz_1416_, v___x_1417_, v_content_1414_);
lean_inc(v_a_1194_);
lean_inc_ref(v_a_1193_);
lean_inc(v_a_1192_);
v___x_1419_ = lean_apply_4(v___x_4338__overap_1418_, v_a_1192_, v_a_1193_, v_a_1194_, lean_box(0));
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
v___x_1425_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_1413_, v___x_1424_, v_a_1192_);
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
lean_dec_ref(v___x_1220_);
lean_dec_ref(v_x_1190_);
lean_dec_ref(v_inst_1189_);
v_alt_1457_ = lean_ctor_get(v_x_1191_, 0);
lean_inc_ref(v_alt_1457_);
v_url_1458_ = lean_ctor_get(v_x_1191_, 1);
lean_inc_ref(v_url_1458_);
lean_dec_ref_known(v_x_1191_, 2);
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
lean_object* v_content_1471_; lean_object* v___x_1472_; size_t v_sz_1473_; size_t v___x_1474_; lean_object* v___x_4341__overap_1475_; lean_object* v___x_1476_; 
v_content_1471_ = lean_ctor_get(v_x_1191_, 0);
lean_inc_ref(v_content_1471_);
lean_dec_ref_known(v_x_1191_, 1);
v___x_1472_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1472_, 0, v_inst_1189_);
lean_closure_set(v___x_1472_, 1, v_x_1190_);
v_sz_1473_ = lean_array_size(v_content_1471_);
v___x_1474_ = ((size_t)0ULL);
v___x_4341__overap_1475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1220_, v___x_1472_, v_sz_1473_, v___x_1474_, v_content_1471_);
lean_inc(v_a_1194_);
lean_inc_ref(v_a_1193_);
lean_inc(v_a_1192_);
v___x_1476_ = lean_apply_4(v___x_4341__overap_1475_, v_a_1192_, v_a_1193_, v_a_1194_, lean_box(0));
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
lean_dec_ref(v___x_1220_);
v_container_1494_ = lean_ctor_get(v_x_1191_, 0);
lean_inc(v_container_1494_);
v_content_1495_ = lean_ctor_get(v_x_1191_, 1);
lean_inc_ref(v_content_1495_);
lean_dec_ref_known(v_x_1191_, 2);
lean_inc_ref(v_inst_1189_);
v___x_1496_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1496_, 0, v_inst_1189_);
lean_closure_set(v___x_1496_, 1, v_x_1190_);
lean_inc(v_a_1194_);
lean_inc_ref(v_a_1193_);
lean_inc(v_a_1192_);
v___x_1497_ = lean_apply_7(v_inst_1189_, v___x_1496_, v_container_1494_, v_content_1495_, v_a_1192_, v_a_1193_, v_a_1194_, lean_box(0));
return v___x_1497_;
}
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
v___jp_1200_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = l_Lean_Doc_joinInlines(v_pieces_1201_);
lean_dec_ref(v_pieces_1201_);
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
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
uint32_t v___x_2715__boxed_1558_; lean_object* v_res_1559_; 
v___x_2715__boxed_1558_ = lean_unbox_uint32(v___x_1556_);
lean_dec(v___x_1556_);
v_res_1559_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v___x_2715__boxed_1558_, v_s_1557_);
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
lean_object* v_fst_1585_; lean_object* v_snd_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1626_; 
v_fst_1585_ = lean_ctor_get(v___y_1580_, 0);
v_snd_1586_ = lean_ctor_get(v___y_1580_, 1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___y_1580_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1588_ = v___y_1580_;
v_isShared_1589_ = v_isSharedCheck_1626_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_snd_1586_);
lean_inc(v_fst_1585_);
lean_dec(v___y_1580_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1626_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___f_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; size_t v_sz_1598_; size_t v___x_1599_; lean_object* v___x_2656__overap_1600_; lean_object* v___x_1601_; 
lean_inc(v_snd_1586_);
v___x_1590_ = l_Nat_reprFast(v_snd_1586_);
v___x_1591_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_1592_ = lean_string_append(v___x_1590_, v___x_1591_);
v___x_1593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_1594_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1);
v___x_1595_ = lean_string_utf8_byte_size(v___x_1592_);
v___x_1596_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1594_, v___x_1595_, v___x_1593_);
v___x_1597_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1597_, 0, v_inst_1574_);
lean_closure_set(v___x_1597_, 1, v_inst_1575_);
v_sz_1598_ = lean_array_size(v_a_1578_);
v___x_1599_ = ((size_t)0ULL);
v___x_2656__overap_1600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1576_, v___x_1597_, v_sz_1598_, v___x_1599_, v_a_1578_);
lean_inc(v___y_1583_);
lean_inc_ref(v___y_1582_);
lean_inc(v___y_1581_);
v___x_1601_ = lean_apply_4(v___x_2656__overap_1600_, v___y_1581_, v___y_1582_, v___y_1583_, lean_box(0));
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1617_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1617_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1617_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1606_ = l_Lean_Doc_joinBlocks(v_a_1602_);
lean_dec(v_a_1602_);
v___x_1607_ = l_Lean_Doc_prefixListLines(v___x_1592_, v___x_1596_, v___x_1606_);
v___x_1608_ = lean_array_push(v_fst_1585_, v___x_1607_);
v___x_1609_ = lean_nat_add(v_snd_1586_, v___x_1577_);
lean_dec(v_snd_1586_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v___x_1609_);
lean_ctor_set(v___x_1588_, 0, v___x_1608_);
v___x_1611_ = v___x_1588_;
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
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1612_);
v___x_1614_ = v___x_1604_;
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
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec(v___x_1596_);
lean_dec_ref(v___x_1592_);
lean_del_object(v___x_1588_);
lean_dec(v_snd_1586_);
lean_dec(v_fst_1585_);
v_a_1618_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1601_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1601_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
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
lean_object* v_a_1657_; lean_object* v___x_1658_; size_t v_sz_1659_; size_t v___x_1660_; lean_object* v___x_2684__overap_1661_; lean_object* v___x_1662_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1658_, 0, v_inst_1644_);
lean_closure_set(v___x_1658_, 1, v_inst_1645_);
v_sz_1659_ = lean_array_size(v_desc_1654_);
v___x_1660_ = ((size_t)0ULL);
lean_inc_ref(v_desc_1654_);
v___x_2684__overap_1661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1646_, v___x_1658_, v_sz_1659_, v___x_1660_, v_desc_1654_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
lean_inc(v___y_1648_);
v___x_1662_ = lean_apply_4(v___x_2684__overap_1661_, v___y_1648_, v___y_1649_, v___y_1650_, lean_box(0));
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
lean_object* v_items_1752_; lean_object* v___f_1753_; size_t v_sz_1754_; size_t v___x_1755_; lean_object* v___x_2579__overap_1756_; lean_object* v___x_1757_; 
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
v___x_2579__overap_1756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1732_, v___f_1753_, v_sz_1754_, v___x_1755_, v_items_1752_);
lean_inc(v_a_1714_);
lean_inc_ref(v_a_1713_);
lean_inc(v_a_1712_);
v___x_1757_ = lean_apply_4(v___x_2579__overap_1756_, v_a_1712_, v_a_1713_, v_a_1714_, lean_box(0));
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
size_t v_sz_1787_; size_t v___x_1788_; lean_object* v___x_2395__overap_1789_; lean_object* v___x_1790_; 
v_sz_1787_ = lean_array_size(v_items_1776_);
v___x_1788_ = ((size_t)0ULL);
v___x_2395__overap_1789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1732_, v_items_1776_, v___f_1782_, v_sz_1787_, v___x_1788_, v___x_1786_);
lean_inc(v_a_1714_);
lean_inc_ref(v_a_1713_);
lean_inc(v_a_1712_);
v___x_1790_ = lean_apply_4(v___x_2395__overap_1789_, v_a_1712_, v_a_1713_, v_a_1714_, lean_box(0));
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
lean_object* v_items_1813_; lean_object* v___f_1814_; size_t v_sz_1815_; size_t v___x_1816_; lean_object* v___x_2585__overap_1817_; lean_object* v___x_1818_; 
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
v___x_2585__overap_1817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1732_, v___f_1814_, v_sz_1815_, v___x_1816_, v_items_1813_);
lean_inc(v_a_1714_);
lean_inc_ref(v_a_1713_);
lean_inc(v_a_1712_);
v___x_1818_ = lean_apply_4(v___x_2585__overap_1817_, v_a_1712_, v_a_1713_, v_a_1714_, lean_box(0));
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
lean_object* v_items_1836_; lean_object* v___x_1837_; size_t v_sz_1838_; size_t v___x_1839_; lean_object* v___x_2588__overap_1840_; lean_object* v___x_1841_; 
v_items_1836_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_items_1836_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_1837_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1837_, 0, v_inst_1709_);
lean_closure_set(v___x_1837_, 1, v_inst_1710_);
v_sz_1838_ = lean_array_size(v_items_1836_);
v___x_1839_ = ((size_t)0ULL);
v___x_2588__overap_1840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1732_, v___x_1837_, v_sz_1838_, v___x_1839_, v_items_1836_);
lean_inc(v_a_1714_);
lean_inc_ref(v_a_1713_);
lean_inc(v_a_1712_);
v___x_1841_ = lean_apply_4(v___x_2588__overap_1840_, v_a_1712_, v_a_1713_, v_a_1714_, lean_box(0));
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
lean_object* v_content_1861_; lean_object* v___x_1862_; size_t v_sz_1863_; size_t v___x_1864_; lean_object* v___x_2591__overap_1865_; lean_object* v___x_1866_; 
v_content_1861_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_content_1861_);
lean_dec_ref_known(v_x_1711_, 1);
v___x_1862_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1862_, 0, v_inst_1709_);
lean_closure_set(v___x_1862_, 1, v_inst_1710_);
v_sz_1863_ = lean_array_size(v_content_1861_);
v___x_1864_ = ((size_t)0ULL);
v___x_2591__overap_1865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1732_, v___x_1862_, v_sz_1863_, v___x_1864_, v_content_1861_);
lean_inc(v_a_1714_);
lean_inc_ref(v_a_1713_);
lean_inc(v_a_1712_);
v___x_1866_ = lean_apply_4(v___x_2591__overap_1865_, v_a_1712_, v_a_1713_, v_a_1714_, lean_box(0));
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
lean_object* v___x_1906_; size_t v_sz_1907_; size_t v___x_1908_; lean_object* v___x_2623__overap_1909_; lean_object* v___x_1910_; 
v___x_1906_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1906_, 0, v_inst_1898_);
lean_closure_set(v___x_1906_, 1, v_inst_1899_);
v_sz_1907_ = lean_array_size(v_item_1901_);
v___x_1908_ = ((size_t)0ULL);
v___x_2623__overap_1909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1900_, v___x_1906_, v_sz_1907_, v___x_1908_, v_item_1901_);
lean_inc(v___y_1904_);
lean_inc_ref(v___y_1903_);
lean_inc(v___y_1902_);
v___x_1910_ = lean_apply_4(v___x_2623__overap_1909_, v___y_1902_, v___y_1903_, v___y_1904_, lean_box(0));
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
lean_object* v_a_2041_; lean_object* v___x_2042_; lean_object* v___f_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; size_t v_sz_2055_; lean_object* v___x_683__overap_2056_; lean_object* v___x_2057_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v___x_2042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_2043_ = lean_obj_once(&l_Lean_Doc_partMarkdown___redArg___closed__0, &l_Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_partMarkdown___redArg___closed__0);
v___x_2044_ = lean_unsigned_to_nat(1u);
v___x_2045_ = lean_nat_add(v_level_2010_, v___x_2044_);
lean_inc(v___x_2045_);
v___x_2046_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_2043_, v___x_2045_, v___x_2042_);
v___x_2047_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_2048_ = lean_string_append(v___x_2046_, v___x_2047_);
v___x_2049_ = lean_mk_empty_array_with_capacity(v___x_2044_);
lean_inc_ref_n(v___x_2049_, 2);
v___x_2050_ = lean_array_push(v___x_2049_, v___x_2048_);
v___x_2051_ = lean_array_push(v___x_2049_, v___x_2050_);
v___x_2052_ = l_Array_append___redArg(v___x_2051_, v_a_2041_);
lean_dec(v_a_2041_);
v___x_2053_ = l_Lean_Doc_joinInlines(v___x_2052_);
lean_dec_ref(v___x_2052_);
lean_inc_ref(v_inst_2009_);
lean_inc_ref(v_inst_2008_);
v___x_2054_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_2054_, 0, lean_box(0));
lean_closure_set(v___x_2054_, 1, lean_box(0));
lean_closure_set(v___x_2054_, 2, v_inst_2008_);
lean_closure_set(v___x_2054_, 3, v_inst_2009_);
v_sz_2055_ = lean_array_size(v_content_2034_);
lean_inc_ref(v___x_2032_);
v___x_683__overap_2056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2032_, v___x_2054_, v_sz_2055_, v___x_2038_, v_content_2034_);
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
lean_inc(v_a_2012_);
v___x_2057_ = lean_apply_4(v___x_683__overap_2056_, v_a_2012_, v_a_2013_, v_a_2014_, lean_box(0));
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2059_; size_t v_sz_2060_; lean_object* v___x_686__overap_2061_; lean_object* v___x_2062_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2059_ = lean_alloc_closure((void*)(l_Lean_Doc_partMarkdown___redArg___boxed), 8, 3);
lean_closure_set(v___x_2059_, 0, v_inst_2008_);
lean_closure_set(v___x_2059_, 1, v_inst_2009_);
lean_closure_set(v___x_2059_, 2, v___x_2045_);
v_sz_2060_ = lean_array_size(v_subParts_2035_);
v___x_686__overap_2061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2032_, v___x_2059_, v_sz_2060_, v___x_2038_, v_subParts_2035_);
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
lean_inc(v_a_2012_);
v___x_2062_ = lean_apply_4(v___x_686__overap_2061_, v_a_2012_, v_a_2013_, v_a_2014_, lean_box(0));
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2074_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2067_ = lean_array_push(v___x_2049_, v___x_2053_);
v___x_2068_ = l_Array_append___redArg(v___x_2067_, v_a_2058_);
lean_dec(v_a_2058_);
v___x_2069_ = l_Array_append___redArg(v___x_2068_, v_a_2063_);
lean_dec(v_a_2063_);
v___x_2070_ = l_Lean_Doc_joinBlocks(v___x_2069_);
lean_dec_ref(v___x_2069_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2070_);
v___x_2072_ = v___x_2065_;
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
lean_dec(v_a_2058_);
lean_dec_ref(v___x_2053_);
lean_dec_ref(v___x_2049_);
v_a_2075_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2062_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2062_);
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
lean_dec_ref(v___x_2053_);
lean_dec_ref(v___x_2049_);
lean_dec(v___x_2045_);
lean_dec_ref(v_subParts_2035_);
lean_dec_ref(v___x_2032_);
lean_dec_ref(v_inst_2009_);
lean_dec_ref(v_inst_2008_);
v_a_2083_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2057_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2057_);
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
v___x_2527_ = lean_st_ref_put(v___x_2524_, v___x_2526_);
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
v___x_2539_ = lean_st_ref_put(v___x_2536_, v___x_2538_);
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
v___x_2545_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_2550_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_2550_, 10, v___x_2548_);
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
lean_object* v___x_2568_; lean_object* v_toCold_2569_; lean_object* v_env_2570_; lean_object* v_options_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2568_ = lean_st_ref_get(v___y_2566_);
v_toCold_2569_ = lean_ctor_get(v___y_2565_, 0);
v_env_2570_ = lean_ctor_get(v___x_2568_, 0);
lean_inc_ref(v_env_2570_);
lean_dec(v___x_2568_);
v_options_2571_ = lean_ctor_get(v_toCold_2569_, 2);
v___x_2572_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_2573_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_2571_);
v___x_2574_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2574_, 0, v_env_2570_);
lean_ctor_set(v___x_2574_, 1, v___x_2572_);
lean_ctor_set(v___x_2574_, 2, v___x_2573_);
lean_ctor_set(v___x_2574_, 3, v_options_2571_);
v___x_2575_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v_msgData_2564_);
v___x_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_ref_2586_; lean_object* v___x_2587_; lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2596_; 
v_ref_2586_ = lean_ctor_get(v___y_2583_, 2);
v___x_2587_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_2582_, v___y_2583_, v___y_2584_);
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2596_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2596_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
lean_inc(v_ref_2586_);
v___x_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2592_, 0, v_ref_2586_);
lean_ctor_set(v___x_2592_, 1, v_a_2588_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set_tag(v___x_2590_, 1);
lean_ctor_set(v___x_2590_, 0, v___x_2592_);
v___x_2594_ = v___x_2590_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(lean_object* v_x_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
if (lean_obj_tag(v_x_2602_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v_a_2606_ = lean_ctor_get(v_x_2602_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v_x_2602_, 1);
v___x_2607_ = l_Lean_stringToMessageData(v_a_2606_);
v___x_2608_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v___x_2607_, v___y_2603_, v___y_2604_);
return v___x_2608_;
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_a_2609_ = lean_ctor_get(v_x_2602_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_x_2602_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v_x_2602_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v_x_2602_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 0);
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
return v_res_2621_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2622_ = lean_box(0);
v___x_2623_ = l_Lean_Elab_abortCommandExceptionId;
v___x_2624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___x_2622_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(lean_object* v_constName_2630_, uint8_t v_checkMeta_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; lean_object* v_env_2636_; uint8_t v___x_2637_; 
v___x_2635_ = lean_st_ref_get(v___y_2633_);
v_env_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc_ref(v_env_2636_);
lean_dec(v___x_2635_);
lean_inc(v_constName_2630_);
v___x_2637_ = lean_has_compile_error(v_env_2636_, v_constName_2630_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v_env_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2638_ = lean_st_ref_get(v___y_2633_);
v_env_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc_ref(v_env_2639_);
lean_dec(v___x_2638_);
v___x_2640_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2632_);
v___x_2641_ = l_Lean_Environment_evalConst___redArg(v_env_2639_, v___x_2640_, v_constName_2630_, v_checkMeta_2631_);
lean_dec(v_constName_2630_);
lean_dec_ref(v___x_2640_);
lean_dec_ref(v_env_2639_);
v___x_2642_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2641_, v___y_2632_, v___y_2633_);
return v___x_2642_;
}
else
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v___x_2644_; lean_object* v_env_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_dec_ref_known(v___x_2643_, 1);
v___x_2644_ = lean_st_ref_get(v___y_2633_);
v_env_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc_ref(v_env_2645_);
lean_dec(v___x_2644_);
v___x_2646_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2632_);
v___x_2647_ = l_Lean_Environment_evalConst___redArg(v_env_2645_, v___x_2646_, v_constName_2630_, v_checkMeta_2631_);
lean_dec(v_constName_2630_);
lean_dec_ref(v___x_2646_);
lean_dec_ref(v_env_2645_);
v___x_2648_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2647_, v___y_2632_, v___y_2633_);
return v___x_2648_;
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v_constName_2630_);
v_a_2649_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2643_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2643_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg___boxed(lean_object* v_constName_2657_, lean_object* v_checkMeta_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
uint8_t v_checkMeta_boxed_2662_; lean_object* v_res_2663_; 
v_checkMeta_boxed_2662_ = lean_unbox(v_checkMeta_2658_);
v_res_2663_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2657_, v_checkMeta_boxed_2662_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(lean_object* v_type_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___y_2671_; lean_object* v_env_2702_; lean_object* v___x_2703_; lean_object* v_toEnvExtension_2704_; lean_object* v_asyncMode_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v_imported_2708_; lean_object* v_current_2709_; lean_object* v___x_2710_; 
v___x_2668_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2669_ = lean_st_ref_get(v_a_2666_);
v_env_2702_ = lean_ctor_get(v___x_2669_, 0);
lean_inc_ref(v_env_2702_);
lean_dec(v___x_2669_);
v___x_2703_ = l_Lean_Doc_docInlineMdExt;
v_toEnvExtension_2704_ = lean_ctor_get(v___x_2703_, 0);
v_asyncMode_2705_ = lean_ctor_get(v_toEnvExtension_2704_, 2);
v___x_2706_ = lean_box(0);
v___x_2707_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2668_, v___x_2703_, v_env_2702_, v_asyncMode_2705_, v___x_2706_);
v_imported_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_imported_2708_);
v_current_2709_ = lean_ctor_get(v___x_2707_, 1);
lean_inc(v_current_2709_);
lean_dec(v___x_2707_);
v___x_2710_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2709_, v_type_2664_);
lean_dec(v_current_2709_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2708_, v_type_2664_);
lean_dec(v_imported_2708_);
v___y_2671_ = v___x_2711_;
goto v___jp_2670_;
}
else
{
lean_dec(v_imported_2708_);
v___y_2671_ = v___x_2710_;
goto v___jp_2670_;
}
v___jp_2670_:
{
if (lean_obj_tag(v___y_2671_) == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2672_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2673_ = lean_st_ref_get(v___x_2672_);
v___x_2674_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2673_, v_type_2664_);
lean_dec(v___x_2673_);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
else
{
lean_object* v_val_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2701_; 
v_val_2676_ = lean_ctor_get(v___y_2671_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___y_2671_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2678_ = v___y_2671_;
v_isShared_2679_ = v_isSharedCheck_2701_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_val_2676_);
lean_dec(v___y_2671_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2701_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
uint8_t v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = 1;
v___x_2681_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2676_, v___x_2680_, v_a_2665_, v_a_2666_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2692_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2684_ = v___x_2681_;
v_isShared_2685_ = v_isSharedCheck_2692_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2681_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2692_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v_a_2682_);
v___x_2687_ = v___x_2678_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2689_; 
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 0, v___x_2687_);
v___x_2689_ = v___x_2684_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_del_object(v___x_2678_);
v_a_2693_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2681_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2681_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe___boxed(lean_object* v_type_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v_type_2712_, v_a_2713_, v_a_2714_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_type_2712_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(v_00_u03b1_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(lean_object* v_00_u03b1_2727_, lean_object* v_constName_2728_, uint8_t v_checkMeta_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2728_, v_checkMeta_2729_, v___y_2730_, v___y_2731_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___boxed(lean_object* v_00_u03b1_2734_, lean_object* v_constName_2735_, lean_object* v_checkMeta_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
uint8_t v_checkMeta_boxed_2740_; lean_object* v_res_2741_; 
v_checkMeta_boxed_2740_ = lean_unbox(v_checkMeta_2736_);
v_res_2741_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(v_00_u03b1_2734_, v_constName_2735_, v_checkMeta_boxed_2740_, v___y_2737_, v___y_2738_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_2742_, lean_object* v_x_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2743_, v___y_2744_, v___y_2745_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2748_, lean_object* v_x_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(v_00_u03b1_2748_, v_x_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2754_, lean_object* v_msg_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2755_, v___y_2756_, v___y_2757_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2760_, lean_object* v_msg_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_2760_, v_msg_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(lean_object* v_typeName_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___y_2773_; lean_object* v_env_2804_; lean_object* v___x_2805_; lean_object* v_toEnvExtension_2806_; lean_object* v_asyncMode_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v_imported_2810_; lean_object* v_current_2811_; lean_object* v___x_2812_; 
v___x_2770_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2771_ = lean_st_ref_get(v_a_2768_);
v_env_2804_ = lean_ctor_get(v___x_2771_, 0);
lean_inc_ref(v_env_2804_);
lean_dec(v___x_2771_);
v___x_2805_ = l_Lean_Doc_docBlockMdExt;
v_toEnvExtension_2806_ = lean_ctor_get(v___x_2805_, 0);
v_asyncMode_2807_ = lean_ctor_get(v_toEnvExtension_2806_, 2);
v___x_2808_ = lean_box(0);
v___x_2809_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2770_, v___x_2805_, v_env_2804_, v_asyncMode_2807_, v___x_2808_);
v_imported_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_imported_2810_);
v_current_2811_ = lean_ctor_get(v___x_2809_, 1);
lean_inc(v_current_2811_);
lean_dec(v___x_2809_);
v___x_2812_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2811_, v_typeName_2766_);
lean_dec(v_current_2811_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2810_, v_typeName_2766_);
lean_dec(v_imported_2810_);
v___y_2773_ = v___x_2813_;
goto v___jp_2772_;
}
else
{
lean_dec(v_imported_2810_);
v___y_2773_ = v___x_2812_;
goto v___jp_2772_;
}
v___jp_2772_:
{
if (lean_obj_tag(v___y_2773_) == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2774_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2775_ = lean_st_ref_get(v___x_2774_);
v___x_2776_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2775_, v_typeName_2766_);
lean_dec(v___x_2775_);
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
return v___x_2777_;
}
else
{
lean_object* v_val_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2803_; 
v_val_2778_ = lean_ctor_get(v___y_2773_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___y_2773_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2780_ = v___y_2773_;
v_isShared_2781_ = v_isSharedCheck_2803_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_val_2778_);
lean_dec(v___y_2773_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2803_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
uint8_t v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = 1;
v___x_2783_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2778_, v___x_2782_, v_a_2767_, v_a_2768_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2794_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2794_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2794_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v_a_2784_);
v___x_2789_ = v___x_2780_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2791_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v___x_2789_);
v___x_2791_ = v___x_2786_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_del_object(v___x_2780_);
v_a_2795_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2783_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2783_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe___boxed(lean_object* v_typeName_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v_typeName_2814_, v_a_2815_, v_a_2816_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_typeName_2814_);
return v_res_2818_;
}
}
static lean_object* _init_l_Lean_Doc_mdRendererHeartbeats(void){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = lean_unsigned_to_nat(200000u);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg(lean_object* v_x_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v___x_2825_; lean_object* v_toCold_2826_; lean_object* v_currRecDepth_2827_; lean_object* v_ref_2828_; uint16_t v_optionFlags_2829_; uint8_t v_suppressElabErrors_2830_; uint8_t v_isRecordingDeps_2831_; lean_object* v_fileName_2832_; lean_object* v_fileMap_2833_; lean_object* v_options_2834_; lean_object* v_maxRecDepth_2835_; lean_object* v_currNamespace_2836_; lean_object* v_openDecls_2837_; lean_object* v_quotContext_2838_; lean_object* v_currMacroScope_2839_; lean_object* v_cancelTk_x3f_2840_; lean_object* v_inheritedTraceOptions_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2825_ = lean_io_get_num_heartbeats();
v_toCold_2826_ = lean_ctor_get(v_a_2822_, 0);
v_currRecDepth_2827_ = lean_ctor_get(v_a_2822_, 1);
v_ref_2828_ = lean_ctor_get(v_a_2822_, 2);
v_optionFlags_2829_ = lean_ctor_get_uint16(v_a_2822_, sizeof(void*)*3);
v_suppressElabErrors_2830_ = lean_ctor_get_uint8(v_a_2822_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2831_ = lean_ctor_get_uint8(v_a_2822_, sizeof(void*)*3 + 3);
v_fileName_2832_ = lean_ctor_get(v_toCold_2826_, 0);
v_fileMap_2833_ = lean_ctor_get(v_toCold_2826_, 1);
v_options_2834_ = lean_ctor_get(v_toCold_2826_, 2);
v_maxRecDepth_2835_ = lean_ctor_get(v_toCold_2826_, 3);
v_currNamespace_2836_ = lean_ctor_get(v_toCold_2826_, 4);
v_openDecls_2837_ = lean_ctor_get(v_toCold_2826_, 5);
v_quotContext_2838_ = lean_ctor_get(v_toCold_2826_, 8);
v_currMacroScope_2839_ = lean_ctor_get(v_toCold_2826_, 9);
v_cancelTk_x3f_2840_ = lean_ctor_get(v_toCold_2826_, 10);
v_inheritedTraceOptions_2841_ = lean_ctor_get(v_toCold_2826_, 11);
v___x_2842_ = lean_unsigned_to_nat(200000u);
lean_inc_ref(v_inheritedTraceOptions_2841_);
lean_inc(v_cancelTk_x3f_2840_);
lean_inc(v_currMacroScope_2839_);
lean_inc(v_quotContext_2838_);
lean_inc(v_openDecls_2837_);
lean_inc(v_currNamespace_2836_);
lean_inc(v_maxRecDepth_2835_);
lean_inc_ref(v_options_2834_);
lean_inc_ref(v_fileMap_2833_);
lean_inc_ref(v_fileName_2832_);
v___x_2843_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2843_, 0, v_fileName_2832_);
lean_ctor_set(v___x_2843_, 1, v_fileMap_2833_);
lean_ctor_set(v___x_2843_, 2, v_options_2834_);
lean_ctor_set(v___x_2843_, 3, v_maxRecDepth_2835_);
lean_ctor_set(v___x_2843_, 4, v_currNamespace_2836_);
lean_ctor_set(v___x_2843_, 5, v_openDecls_2837_);
lean_ctor_set(v___x_2843_, 6, v___x_2825_);
lean_ctor_set(v___x_2843_, 7, v___x_2842_);
lean_ctor_set(v___x_2843_, 8, v_quotContext_2838_);
lean_ctor_set(v___x_2843_, 9, v_currMacroScope_2839_);
lean_ctor_set(v___x_2843_, 10, v_cancelTk_x3f_2840_);
lean_ctor_set(v___x_2843_, 11, v_inheritedTraceOptions_2841_);
lean_inc(v_ref_2828_);
lean_inc(v_currRecDepth_2827_);
v___x_2844_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v_currRecDepth_2827_);
lean_ctor_set(v___x_2844_, 2, v_ref_2828_);
lean_ctor_set_uint16(v___x_2844_, sizeof(void*)*3, v_optionFlags_2829_);
lean_ctor_set_uint8(v___x_2844_, sizeof(void*)*3 + 2, v_suppressElabErrors_2830_);
lean_ctor_set_uint8(v___x_2844_, sizeof(void*)*3 + 3, v_isRecordingDeps_2831_);
lean_inc(v_a_2823_);
lean_inc(v_a_2821_);
v___x_2845_ = lean_apply_4(v_x_2820_, v_a_2821_, v___x_2844_, v_a_2823_, lean_box(0));
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg___boxed(lean_object* v_x_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2846_, v_a_2847_, v_a_2848_, v_a_2849_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget(lean_object* v_00_u03b1_2852_, lean_object* v_x_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2853_, v_a_2854_, v_a_2855_, v_a_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___boxed(lean_object* v_00_u03b1_2859_, lean_object* v_x_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_Doc_withMdRendererBudget(v_00_u03b1_2859_, v_x_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
lean_dec(v_a_2861_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback(lean_object* v_fallback_2866_, lean_object* v_act_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_st_ref_get(v_a_2868_);
v___x_2873_ = l_Lean_Doc_withMdRendererBudget___redArg(v_act_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_dec(v___x_2872_);
lean_dec_ref(v_fallback_2866_);
return v___x_2873_;
}
else
{
lean_object* v_a_2874_; uint8_t v___x_2875_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
v___x_2875_ = l_Lean_Exception_isInterrupt(v_a_2874_);
lean_dec(v_a_2874_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec_ref_known(v___x_2873_, 1);
v___x_2876_ = lean_st_ref_swap(v_a_2868_, v___x_2872_);
lean_dec(v___x_2876_);
lean_inc(v_a_2870_);
lean_inc_ref(v_a_2869_);
lean_inc(v_a_2868_);
v___x_2877_ = lean_apply_4(v_fallback_2866_, v_a_2868_, v_a_2869_, v_a_2870_, lean_box(0));
return v___x_2877_;
}
else
{
lean_dec(v___x_2872_);
lean_dec_ref(v_fallback_2866_);
return v___x_2873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback___boxed(lean_object* v_fallback_2878_, lean_object* v_act_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_Doc_withRendererFallback(v_fallback_2878_, v_act_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
lean_dec(v_a_2880_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0(lean_object* v_____do__lift_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = l_Lean_Doc_joinInlines(v_____do__lift_2885_);
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0___boxed(lean_object* v_____do__lift_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__0(v_____do__lift_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v_____do__lift_2892_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1(lean_object* v___x_2898_, lean_object* v___x_2899_, lean_object* v___f_2900_, lean_object* v_go_2901_, lean_object* v_container_2902_, lean_object* v_content_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
if (lean_obj_tag(v_container_2902_) == 0)
{
lean_object* v_val_2908_; size_t v_sz_2909_; size_t v___x_2910_; lean_object* v___x_2911_; lean_object* v_fallback_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v_val_2908_ = lean_ctor_get(v_container_2902_, 0);
lean_inc(v_val_2908_);
lean_dec_ref_known(v_container_2902_, 1);
v_sz_2909_ = lean_array_size(v_content_2903_);
v___x_2910_ = ((size_t)0ULL);
lean_inc_ref(v_content_2903_);
lean_inc_ref(v_go_2901_);
lean_inc_ref(v___x_2898_);
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2898_, v_go_2901_, v_sz_2909_, v___x_2910_, v_content_2903_);
lean_inc_ref(v___f_2900_);
v_fallback_2912_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_2912_, 0, lean_box(0));
lean_closure_set(v_fallback_2912_, 1, lean_box(0));
lean_closure_set(v_fallback_2912_, 2, v___x_2899_);
lean_closure_set(v_fallback_2912_, 3, lean_box(0));
lean_closure_set(v_fallback_2912_, 4, lean_box(0));
lean_closure_set(v_fallback_2912_, 5, v___x_2911_);
lean_closure_set(v_fallback_2912_, 6, v___f_2900_);
v___x_2913_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2908_);
v___x_2914_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_2913_, v___y_2905_, v___y_2906_);
lean_dec(v___x_2913_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
if (lean_obj_tag(v_a_2915_) == 0)
{
lean_object* v___x_543__overap_2916_; lean_object* v___x_2917_; 
lean_dec_ref(v_fallback_2912_);
lean_dec(v_val_2908_);
v___x_543__overap_2916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2898_, v_go_2901_, v_sz_2909_, v___x_2910_, v_content_2903_);
lean_inc(v___y_2906_);
lean_inc_ref(v___y_2905_);
lean_inc(v___y_2904_);
v___x_2917_ = lean_apply_4(v___x_543__overap_2916_, v___y_2904_, v___y_2905_, v___y_2906_, lean_box(0));
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2919_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
lean_inc(v___y_2906_);
lean_inc_ref(v___y_2905_);
lean_inc(v___y_2904_);
v___x_2919_ = lean_apply_5(v___f_2900_, v_a_2918_, v___y_2904_, v___y_2905_, v___y_2906_, lean_box(0));
return v___x_2919_;
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec_ref(v___f_2900_);
v_a_2920_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2917_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2917_);
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
lean_object* v_val_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec_ref(v___f_2900_);
lean_dec_ref(v___x_2898_);
v_val_2928_ = lean_ctor_get(v_a_2915_, 0);
lean_inc(v_val_2928_);
lean_dec_ref_known(v_a_2915_, 1);
v___x_2929_ = lean_apply_3(v_val_2928_, v_go_2901_, v_val_2908_, v_content_2903_);
v___x_2930_ = l_Lean_Doc_withRendererFallback(v_fallback_2912_, v___x_2929_, v___y_2904_, v___y_2905_, v___y_2906_);
return v___x_2930_;
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec_ref(v_fallback_2912_);
lean_dec(v_val_2908_);
lean_dec_ref(v_content_2903_);
lean_dec_ref(v_go_2901_);
lean_dec_ref(v___f_2900_);
lean_dec_ref(v___x_2898_);
v_a_2931_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2914_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2914_);
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
else
{
size_t v_sz_2939_; size_t v___x_2940_; lean_object* v___x_558__overap_2941_; lean_object* v___x_2942_; 
lean_dec_ref_known(v_container_2902_, 1);
lean_dec_ref(v___f_2900_);
lean_dec_ref(v___x_2899_);
v_sz_2939_ = lean_array_size(v_content_2903_);
v___x_2940_ = ((size_t)0ULL);
v___x_558__overap_2941_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2898_, v_go_2901_, v_sz_2939_, v___x_2940_, v_content_2903_);
lean_inc(v___y_2906_);
lean_inc_ref(v___y_2905_);
lean_inc(v___y_2904_);
v___x_2942_ = lean_apply_4(v___x_558__overap_2941_, v___y_2904_, v___y_2905_, v___y_2906_, lean_box(0));
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2951_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_2951_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2951_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2947_ = l_Lean_Doc_joinInlines(v_a_2943_);
lean_dec(v_a_2943_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2947_);
v___x_2949_ = v___x_2945_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
v_a_2952_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2942_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2942_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed(lean_object* v___x_2960_, lean_object* v___x_2961_, lean_object* v___f_2962_, lean_object* v_go_2963_, lean_object* v_container_2964_, lean_object* v_content_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__1(v___x_2960_, v___x_2961_, v___f_2962_, v_go_2963_, v_container_2964_, v_content_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
return v_res_2970_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownInlineElabInline(void){
_start:
{
lean_object* v___x_2972_; lean_object* v_toApplicative_2973_; lean_object* v_toFunctor_2974_; lean_object* v_toSeq_2975_; lean_object* v_toSeqLeft_2976_; lean_object* v_toSeqRight_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; lean_object* v___f_2980_; lean_object* v___f_2981_; lean_object* v___f_2982_; lean_object* v___x_2983_; lean_object* v___f_2984_; lean_object* v___f_2985_; lean_object* v___f_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___f_2990_; 
v___x_2972_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2973_ = lean_ctor_get(v___x_2972_, 0);
v_toFunctor_2974_ = lean_ctor_get(v_toApplicative_2973_, 0);
v_toSeq_2975_ = lean_ctor_get(v_toApplicative_2973_, 2);
v_toSeqLeft_2976_ = lean_ctor_get(v_toApplicative_2973_, 3);
v_toSeqRight_2977_ = lean_ctor_get(v_toApplicative_2973_, 4);
v___f_2978_ = ((lean_object*)(l_Lean_Doc_instMarkdownInlineElabInline___closed__0));
v___f_2979_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2980_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2974_, 2);
v___f_2981_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2981_, 0, v_toFunctor_2974_);
v___f_2982_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2982_, 0, v_toFunctor_2974_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___f_2981_);
lean_ctor_set(v___x_2983_, 1, v___f_2982_);
lean_inc(v_toSeqRight_2977_);
v___f_2984_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2984_, 0, v_toSeqRight_2977_);
lean_inc(v_toSeqLeft_2976_);
v___f_2985_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2985_, 0, v_toSeqLeft_2976_);
lean_inc(v_toSeq_2975_);
v___f_2986_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2986_, 0, v_toSeq_2975_);
v___x_2987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2983_);
lean_ctor_set(v___x_2987_, 1, v___f_2979_);
lean_ctor_set(v___x_2987_, 2, v___f_2986_);
lean_ctor_set(v___x_2987_, 3, v___f_2985_);
lean_ctor_set(v___x_2987_, 4, v___f_2984_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v___f_2980_);
lean_inc_ref(v___x_2988_);
v___x_2989_ = l_StateRefT_x27_instMonad___redArg(v___x_2988_);
v___f_2990_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2990_, 0, v___x_2989_);
lean_closure_set(v___f_2990_, 1, v___x_2988_);
lean_closure_set(v___f_2990_, 2, v___f_2978_);
return v___f_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v_____do__lift_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = l_Lean_Doc_joinBlocks(v_____do__lift_2991_);
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object* v_____do__lift_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(v_____do__lift_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v_____do__lift_2998_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object* v___x_3004_, lean_object* v___x_3005_, lean_object* v___f_3006_, lean_object* v_goI_3007_, lean_object* v_goB_3008_, lean_object* v_container_3009_, lean_object* v_content_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
if (lean_obj_tag(v_container_3009_) == 0)
{
lean_object* v_val_3015_; size_t v_sz_3016_; size_t v___x_3017_; lean_object* v___x_3018_; lean_object* v_fallback_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_val_3015_ = lean_ctor_get(v_container_3009_, 0);
lean_inc(v_val_3015_);
lean_dec_ref_known(v_container_3009_, 1);
v_sz_3016_ = lean_array_size(v_content_3010_);
v___x_3017_ = ((size_t)0ULL);
lean_inc_ref(v_content_3010_);
lean_inc_ref(v_goB_3008_);
lean_inc_ref(v___x_3004_);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3004_, v_goB_3008_, v_sz_3016_, v___x_3017_, v_content_3010_);
lean_inc_ref(v___f_3006_);
v_fallback_3019_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_3019_, 0, lean_box(0));
lean_closure_set(v_fallback_3019_, 1, lean_box(0));
lean_closure_set(v_fallback_3019_, 2, v___x_3005_);
lean_closure_set(v_fallback_3019_, 3, lean_box(0));
lean_closure_set(v_fallback_3019_, 4, lean_box(0));
lean_closure_set(v_fallback_3019_, 5, v___x_3018_);
lean_closure_set(v_fallback_3019_, 6, v___f_3006_);
v___x_3020_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3015_);
v___x_3021_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_3020_, v___y_3012_, v___y_3013_);
lean_dec(v___x_3020_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
if (lean_obj_tag(v_a_3022_) == 0)
{
lean_object* v___x_543__overap_3023_; lean_object* v___x_3024_; 
lean_dec_ref(v_fallback_3019_);
lean_dec(v_val_3015_);
lean_dec_ref(v_goI_3007_);
v___x_543__overap_3023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3004_, v_goB_3008_, v_sz_3016_, v___x_3017_, v_content_3010_);
lean_inc(v___y_3013_);
lean_inc_ref(v___y_3012_);
lean_inc(v___y_3011_);
v___x_3024_ = lean_apply_4(v___x_543__overap_3023_, v___y_3011_, v___y_3012_, v___y_3013_, lean_box(0));
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
lean_inc(v___y_3013_);
lean_inc_ref(v___y_3012_);
lean_inc(v___y_3011_);
v___x_3026_ = lean_apply_5(v___f_3006_, v_a_3025_, v___y_3011_, v___y_3012_, v___y_3013_, lean_box(0));
return v___x_3026_;
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref(v___f_3006_);
v_a_3027_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3024_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3024_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
else
{
lean_object* v_val_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
lean_dec_ref(v___f_3006_);
lean_dec_ref(v___x_3004_);
v_val_3035_ = lean_ctor_get(v_a_3022_, 0);
lean_inc(v_val_3035_);
lean_dec_ref_known(v_a_3022_, 1);
v___x_3036_ = lean_apply_4(v_val_3035_, v_goI_3007_, v_goB_3008_, v_val_3015_, v_content_3010_);
v___x_3037_ = l_Lean_Doc_withRendererFallback(v_fallback_3019_, v___x_3036_, v___y_3011_, v___y_3012_, v___y_3013_);
return v___x_3037_;
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v_fallback_3019_);
lean_dec(v_val_3015_);
lean_dec_ref(v_content_3010_);
lean_dec_ref(v_goB_3008_);
lean_dec_ref(v_goI_3007_);
lean_dec_ref(v___f_3006_);
lean_dec_ref(v___x_3004_);
v_a_3038_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3021_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3021_);
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
lean_dec_ref_known(v_container_3009_, 1);
lean_dec_ref(v_goI_3007_);
lean_dec_ref(v___f_3006_);
lean_dec_ref(v___x_3005_);
v_sz_3046_ = lean_array_size(v_content_3010_);
v___x_3047_ = ((size_t)0ULL);
v___x_558__overap_3048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3004_, v_goB_3008_, v_sz_3046_, v___x_3047_, v_content_3010_);
lean_inc(v___y_3013_);
lean_inc_ref(v___y_3012_);
lean_inc(v___y_3011_);
v___x_3049_ = lean_apply_4(v___x_558__overap_3048_, v___y_3011_, v___y_3012_, v___y_3013_, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object* v___x_3067_, lean_object* v___x_3068_, lean_object* v___f_3069_, lean_object* v_goI_3070_, lean_object* v_goB_3071_, lean_object* v_container_3072_, lean_object* v_content_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_3067_, v___x_3068_, v___f_3069_, v_goI_3070_, v_goB_3071_, v_container_3072_, v_content_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
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
lean_closure_set(v___f_3098_, 1, v___x_3096_);
lean_closure_set(v___f_3098_, 2, v___f_3086_);
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
lean_object* v_text_3125_; lean_object* v_subsections_3126_; lean_object* v___x_3127_; size_t v_sz_3128_; size_t v___x_3129_; lean_object* v___x_443__overap_3130_; lean_object* v___x_3131_; 
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
v___x_443__overap_3130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3118_, v___x_3127_, v_sz_3128_, v___x_3129_, v_text_3125_);
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
lean_inc(v___y_3121_);
v___x_3131_ = lean_apply_4(v___x_443__overap_3130_, v___y_3121_, v___y_3122_, v___y_3123_, lean_box(0));
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; size_t v_sz_3133_; lean_object* v___x_446__overap_3134_; lean_object* v___x_3135_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3131_, 1);
v_sz_3133_ = lean_array_size(v_subsections_3126_);
v___x_446__overap_3134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3118_, v___f_3119_, v_sz_3133_, v___x_3129_, v_subsections_3126_);
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
lean_inc(v___y_3121_);
v___x_3135_ = lean_apply_4(v___x_446__overap_3134_, v___y_3121_, v___y_3122_, v___y_3123_, lean_box(0));
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
lean_object* v_text_3224_; lean_object* v_sections_3225_; lean_object* v___x_3226_; size_t v_sz_3227_; size_t v___x_3228_; lean_object* v___x_490__overap_3229_; lean_object* v___x_3230_; 
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
v___x_490__overap_3229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3217_, v___x_3226_, v_sz_3227_, v___x_3228_, v_text_3224_);
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
lean_inc(v___y_3220_);
v___x_3230_ = lean_apply_4(v___x_490__overap_3229_, v___y_3220_, v___y_3221_, v___y_3222_, lean_box(0));
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; size_t v_sz_3232_; lean_object* v___x_493__overap_3233_; lean_object* v___x_3234_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v_sz_3232_ = lean_array_size(v_sections_3225_);
v___x_493__overap_3233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3217_, v___f_3218_, v_sz_3232_, v___x_3228_, v_sections_3225_);
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
lean_inc(v___y_3220_);
v___x_3234_ = lean_apply_4(v___x_493__overap_3233_, v___y_3220_, v___y_3221_, v___y_3222_, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(lean_object* v_opts_3295_, lean_object* v_opt_3296_){
_start:
{
lean_object* v_name_3297_; lean_object* v_defValue_3298_; lean_object* v_map_3299_; lean_object* v___x_3300_; 
v_name_3297_ = lean_ctor_get(v_opt_3296_, 0);
v_defValue_3298_ = lean_ctor_get(v_opt_3296_, 1);
v_map_3299_ = lean_ctor_get(v_opts_3295_, 0);
v___x_3300_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3299_, v_name_3297_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_inc(v_defValue_3298_);
return v_defValue_3298_;
}
else
{
lean_object* v_val_3301_; 
v_val_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_val_3301_);
lean_dec_ref_known(v___x_3300_, 1);
if (lean_obj_tag(v_val_3301_) == 3)
{
lean_object* v_v_3302_; 
v_v_3302_ = lean_ctor_get(v_val_3301_, 0);
lean_inc(v_v_3302_);
lean_dec_ref_known(v_val_3301_, 1);
return v_v_3302_;
}
else
{
lean_dec(v_val_3301_);
lean_inc(v_defValue_3298_);
return v_defValue_3298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0___boxed(lean_object* v_opts_3303_, lean_object* v_opt_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_opts_3303_, v_opt_3304_);
lean_dec_ref(v_opt_3304_);
lean_dec_ref(v_opts_3303_);
return v_res_3305_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = lean_unsigned_to_nat(1u);
v___x_3308_ = l_Lean_firstFrontendMacroScope;
v___x_3309_ = lean_nat_add(v___x_3308_, v___x_3307_);
return v___x_3309_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__6(void){
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
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__7(void){
_start:
{
size_t v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3323_ = ((size_t)5ULL);
v___x_3324_ = lean_unsigned_to_nat(0u);
v___x_3325_ = lean_unsigned_to_nat(32u);
v___x_3326_ = lean_mk_empty_array_with_capacity(v___x_3325_);
v___x_3327_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__6, &l_Lean_Doc_runMarkdown___redArg___closed__6_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__6);
v___x_3328_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
lean_ctor_set(v___x_3328_, 1, v___x_3326_);
lean_ctor_set(v___x_3328_, 2, v___x_3324_);
lean_ctor_set(v___x_3328_, 3, v___x_3324_);
lean_ctor_set_usize(v___x_3328_, 4, v___x_3323_);
return v___x_3328_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__8(void){
_start:
{
lean_object* v___x_3329_; uint64_t v___x_3330_; lean_object* v___x_3331_; 
v___x_3329_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3330_ = 0ULL;
v___x_3331_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3331_, 0, v___x_3329_);
lean_ctor_set_uint64(v___x_3331_, sizeof(void*)*1, v___x_3330_);
return v___x_3331_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__9(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
return v___x_3333_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__10(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__9, &l_Lean_Doc_runMarkdown___redArg___closed__9_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__9);
v___x_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
return v___x_3335_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__12(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3338_ = l_Lean_NameSet_empty;
v___x_3339_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
lean_ctor_set(v___x_3340_, 2, v___x_3338_);
return v___x_3340_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__13(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; lean_object* v___x_3344_; 
v___x_3341_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3342_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__9, &l_Lean_Doc_runMarkdown___redArg___closed__9_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__9);
v___x_3343_ = 1;
v___x_3344_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v___x_3342_);
lean_ctor_set(v___x_3344_, 2, v___x_3341_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*3, v___x_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg(lean_object* v_env_3348_, lean_object* v_act_3349_, lean_object* v_options_3350_, lean_object* v_currNamespace_3351_, lean_object* v_openDecls_3352_, lean_object* v_cancelTk_x3f_3353_){
_start:
{
lean_object* v_a_3356_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; uint16_t v___x_3366_; uint8_t v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v_fileName_3381_; lean_object* v_fileMap_3382_; lean_object* v_currNamespace_3383_; lean_object* v_openDecls_3384_; lean_object* v_initHeartbeats_3385_; lean_object* v_maxHeartbeats_3386_; lean_object* v_quotContext_3387_; lean_object* v_currMacroScope_3388_; lean_object* v_cancelTk_x3f_3389_; lean_object* v_inheritedTraceOptions_3390_; lean_object* v_currRecDepth_3391_; lean_object* v_ref_3392_; uint8_t v_suppressElabErrors_3393_; uint8_t v_isRecordingDeps_3394_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; uint8_t v___y_3435_; lean_object* v_env_3456_; uint8_t v___x_3457_; uint16_t v___x_3458_; uint16_t v___x_3459_; uint16_t v___x_3460_; uint8_t v___x_3461_; 
v___x_3359_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__0));
v___x_3360_ = l_Lean_instInhabitedFileMap_default;
v___x_3361_ = lean_unsigned_to_nat(0u);
v___x_3362_ = l_Lean_Core_getMaxHeartbeats(v_options_3350_);
v___x_3363_ = lean_box(0);
v___x_3364_ = l_Lean_firstFrontendMacroScope;
v___x_3365_ = lean_box(0);
v___x_3366_ = l_Lean_OptionFlags_ofOptions(v_options_3350_);
v___x_3367_ = 0;
v___x_3368_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3369_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__4));
v___x_3370_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__5));
v___x_3371_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__8, &l_Lean_Doc_runMarkdown___redArg___closed__8_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__8);
v___x_3372_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__10, &l_Lean_Doc_runMarkdown___redArg___closed__10_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__10);
v___x_3373_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__11));
v___x_3374_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__12, &l_Lean_Doc_runMarkdown___redArg___closed__12_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__12);
v___x_3375_ = 1;
v___x_3376_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__13, &l_Lean_Doc_runMarkdown___redArg___closed__13_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__13);
v___x_3377_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3377_, 0, v_env_3348_);
lean_ctor_set(v___x_3377_, 1, v___x_3368_);
lean_ctor_set(v___x_3377_, 2, v___x_3369_);
lean_ctor_set(v___x_3377_, 3, v___x_3370_);
lean_ctor_set(v___x_3377_, 4, v___x_3371_);
lean_ctor_set(v___x_3377_, 5, v___x_3372_);
lean_ctor_set(v___x_3377_, 6, v___x_3373_);
lean_ctor_set(v___x_3377_, 7, v___x_3374_);
lean_ctor_set(v___x_3377_, 8, v___x_3376_);
lean_ctor_set(v___x_3377_, 9, v___x_3373_);
v___x_3378_ = lean_io_get_num_heartbeats();
v___x_3379_ = lean_st_mk_ref(v___x_3377_);
v___x_3431_ = l_Lean_inheritedTraceOptions;
v___x_3432_ = lean_st_ref_get(v___x_3431_);
v___x_3433_ = lean_st_ref_get(v___x_3379_);
v_env_3456_ = lean_ctor_get(v___x_3433_, 0);
lean_inc_ref(v_env_3456_);
lean_dec(v___x_3433_);
v___x_3457_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3456_);
lean_dec_ref(v_env_3456_);
v___x_3458_ = 512;
v___x_3459_ = lean_uint16_land(v___x_3366_, v___x_3458_);
v___x_3460_ = 0;
v___x_3461_ = lean_uint16_dec_eq(v___x_3459_, v___x_3460_);
if (v___x_3461_ == 0)
{
if (v___x_3457_ == 0)
{
v___y_3435_ = v___x_3375_;
goto v___jp_3434_;
}
else
{
v_fileName_3381_ = v___x_3359_;
v_fileMap_3382_ = v___x_3360_;
v_currNamespace_3383_ = v_currNamespace_3351_;
v_openDecls_3384_ = v_openDecls_3352_;
v_initHeartbeats_3385_ = v___x_3378_;
v_maxHeartbeats_3386_ = v___x_3362_;
v_quotContext_3387_ = v___x_3363_;
v_currMacroScope_3388_ = v___x_3364_;
v_cancelTk_x3f_3389_ = v_cancelTk_x3f_3353_;
v_inheritedTraceOptions_3390_ = v___x_3432_;
v_currRecDepth_3391_ = v___x_3361_;
v_ref_3392_ = v___x_3365_;
v_suppressElabErrors_3393_ = v___x_3367_;
v_isRecordingDeps_3394_ = v___x_3367_;
goto v___jp_3380_;
}
}
else
{
if (v___x_3457_ == 0)
{
v_fileName_3381_ = v___x_3359_;
v_fileMap_3382_ = v___x_3360_;
v_currNamespace_3383_ = v_currNamespace_3351_;
v_openDecls_3384_ = v_openDecls_3352_;
v_initHeartbeats_3385_ = v___x_3378_;
v_maxHeartbeats_3386_ = v___x_3362_;
v_quotContext_3387_ = v___x_3363_;
v_currMacroScope_3388_ = v___x_3364_;
v_cancelTk_x3f_3389_ = v_cancelTk_x3f_3353_;
v_inheritedTraceOptions_3390_ = v___x_3432_;
v_currRecDepth_3391_ = v___x_3361_;
v_ref_3392_ = v___x_3365_;
v_suppressElabErrors_3393_ = v___x_3367_;
v_isRecordingDeps_3394_ = v___x_3367_;
goto v___jp_3380_;
}
else
{
v___y_3435_ = v___x_3367_;
goto v___jp_3434_;
}
}
v___jp_3355_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = lean_mk_io_user_error(v_a_3356_);
v___x_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
return v___x_3358_;
}
v___jp_3380_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3395_ = l_Lean_maxRecDepth;
v___x_3396_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_options_3350_, v___x_3395_);
lean_inc(v_currMacroScope_3388_);
lean_inc(v_quotContext_3387_);
lean_inc_ref(v_fileMap_3382_);
lean_inc_ref(v_fileName_3381_);
v___x_3397_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3397_, 0, v_fileName_3381_);
lean_ctor_set(v___x_3397_, 1, v_fileMap_3382_);
lean_ctor_set(v___x_3397_, 2, v_options_3350_);
lean_ctor_set(v___x_3397_, 3, v___x_3396_);
lean_ctor_set(v___x_3397_, 4, v_currNamespace_3383_);
lean_ctor_set(v___x_3397_, 5, v_openDecls_3384_);
lean_ctor_set(v___x_3397_, 6, v_initHeartbeats_3385_);
lean_ctor_set(v___x_3397_, 7, v_maxHeartbeats_3386_);
lean_ctor_set(v___x_3397_, 8, v_quotContext_3387_);
lean_ctor_set(v___x_3397_, 9, v_currMacroScope_3388_);
lean_ctor_set(v___x_3397_, 10, v_cancelTk_x3f_3389_);
lean_ctor_set(v___x_3397_, 11, v_inheritedTraceOptions_3390_);
lean_inc(v_ref_3392_);
v___x_3398_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
lean_ctor_set(v___x_3398_, 1, v_currRecDepth_3391_);
lean_ctor_set(v___x_3398_, 2, v_ref_3392_);
lean_ctor_set_uint16(v___x_3398_, sizeof(void*)*3, v___x_3366_);
lean_ctor_set_uint8(v___x_3398_, sizeof(void*)*3 + 2, v_suppressElabErrors_3393_);
lean_ctor_set_uint8(v___x_3398_, sizeof(void*)*3 + 3, v_isRecordingDeps_3394_);
lean_inc(v___x_3379_);
v___x_3399_ = lean_apply_3(v_act_3349_, v___x_3398_, v___x_3379_, lean_box(0));
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3408_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3402_ = v___x_3399_;
v_isShared_3403_ = v_isSharedCheck_3408_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3399_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3408_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3406_; 
v___x_3404_ = lean_st_ref_get(v___x_3379_);
lean_dec(v___x_3379_);
lean_dec(v___x_3404_);
if (v_isShared_3403_ == 0)
{
v___x_3406_ = v___x_3402_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3400_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3430_; 
lean_dec(v___x_3379_);
v_a_3409_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3411_ = v___x_3399_;
v_isShared_3412_ = v_isSharedCheck_3430_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3399_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3430_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
if (lean_obj_tag(v_a_3409_) == 0)
{
lean_object* v_msg_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
v_msg_3413_ = lean_ctor_get(v_a_3409_, 1);
lean_inc_ref(v_msg_3413_);
lean_dec_ref_known(v_a_3409_, 2);
v___x_3414_ = l_Lean_MessageData_toString(v_msg_3413_);
v___x_3415_ = lean_mk_io_user_error(v___x_3414_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3415_);
v___x_3417_ = v___x_3411_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
else
{
lean_object* v_id_3419_; lean_object* v___x_3420_; 
lean_del_object(v___x_3411_);
v_id_3419_ = lean_ctor_get(v_a_3409_, 0);
lean_inc(v_id_3419_);
lean_dec_ref_known(v_a_3409_, 2);
v___x_3420_ = l_Lean_InternalExceptionId_getName(v_id_3419_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_dec(v_id_3419_);
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref_known(v___x_3420_, 1);
v___x_3422_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__14));
v___x_3423_ = l_Lean_Name_toString(v_a_3421_, v___x_3375_);
v___x_3424_ = lean_string_append(v___x_3422_, v___x_3423_);
lean_dec_ref(v___x_3423_);
v_a_3356_ = v___x_3424_;
goto v___jp_3355_;
}
else
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_dec_ref_known(v___x_3420_, 1);
v___x_3425_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__15));
v___x_3426_ = l_Nat_reprFast(v_id_3419_);
v___x_3427_ = lean_string_append(v___x_3425_, v___x_3426_);
lean_dec_ref(v___x_3426_);
v___x_3428_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__16));
v___x_3429_ = lean_string_append(v___x_3427_, v___x_3428_);
v_a_3356_ = v___x_3429_;
goto v___jp_3355_;
}
}
}
}
}
v___jp_3434_:
{
lean_object* v___x_3436_; lean_object* v_env_3437_; lean_object* v_nextMacroScope_3438_; lean_object* v_ngen_3439_; lean_object* v_auxDeclNGen_3440_; lean_object* v_traceState_3441_; lean_object* v_recordedDeps_3442_; lean_object* v_messages_3443_; lean_object* v_infoState_3444_; lean_object* v_snapshotTasks_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3454_; 
v___x_3436_ = lean_st_ref_take(v___x_3379_);
v_env_3437_ = lean_ctor_get(v___x_3436_, 0);
v_nextMacroScope_3438_ = lean_ctor_get(v___x_3436_, 1);
v_ngen_3439_ = lean_ctor_get(v___x_3436_, 2);
v_auxDeclNGen_3440_ = lean_ctor_get(v___x_3436_, 3);
v_traceState_3441_ = lean_ctor_get(v___x_3436_, 4);
v_recordedDeps_3442_ = lean_ctor_get(v___x_3436_, 6);
v_messages_3443_ = lean_ctor_get(v___x_3436_, 7);
v_infoState_3444_ = lean_ctor_get(v___x_3436_, 8);
v_snapshotTasks_3445_ = lean_ctor_get(v___x_3436_, 9);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; 
v_unused_3455_ = lean_ctor_get(v___x_3436_, 5);
lean_dec(v_unused_3455_);
v___x_3447_ = v___x_3436_;
v_isShared_3448_ = v_isSharedCheck_3454_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_snapshotTasks_3445_);
lean_inc(v_infoState_3444_);
lean_inc(v_messages_3443_);
lean_inc(v_recordedDeps_3442_);
lean_inc(v_traceState_3441_);
lean_inc(v_auxDeclNGen_3440_);
lean_inc(v_ngen_3439_);
lean_inc(v_nextMacroScope_3438_);
lean_inc(v_env_3437_);
lean_dec(v___x_3436_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3454_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3449_ = l_Lean_Kernel_enableDiag(v_env_3437_, v___y_3435_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 5, v___x_3372_);
lean_ctor_set(v___x_3447_, 0, v___x_3449_);
v___x_3451_ = v___x_3447_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_nextMacroScope_3438_);
lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_ngen_3439_);
lean_ctor_set(v_reuseFailAlloc_3453_, 3, v_auxDeclNGen_3440_);
lean_ctor_set(v_reuseFailAlloc_3453_, 4, v_traceState_3441_);
lean_ctor_set(v_reuseFailAlloc_3453_, 5, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3453_, 6, v_recordedDeps_3442_);
lean_ctor_set(v_reuseFailAlloc_3453_, 7, v_messages_3443_);
lean_ctor_set(v_reuseFailAlloc_3453_, 8, v_infoState_3444_);
lean_ctor_set(v_reuseFailAlloc_3453_, 9, v_snapshotTasks_3445_);
v___x_3451_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_st_ref_put(v___x_3379_, v___x_3451_);
v_fileName_3381_ = v___x_3359_;
v_fileMap_3382_ = v___x_3360_;
v_currNamespace_3383_ = v_currNamespace_3351_;
v_openDecls_3384_ = v_openDecls_3352_;
v_initHeartbeats_3385_ = v___x_3378_;
v_maxHeartbeats_3386_ = v___x_3362_;
v_quotContext_3387_ = v___x_3363_;
v_currMacroScope_3388_ = v___x_3364_;
v_cancelTk_x3f_3389_ = v_cancelTk_x3f_3353_;
v_inheritedTraceOptions_3390_ = v___x_3432_;
v_currRecDepth_3391_ = v___x_3361_;
v_ref_3392_ = v___x_3365_;
v_suppressElabErrors_3393_ = v___x_3367_;
v_isRecordingDeps_3394_ = v___x_3367_;
goto v___jp_3380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg___boxed(lean_object* v_env_3462_, lean_object* v_act_3463_, lean_object* v_options_3464_, lean_object* v_currNamespace_3465_, lean_object* v_openDecls_3466_, lean_object* v_cancelTk_x3f_3467_, lean_object* v_a_3468_){
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l_Lean_Doc_runMarkdown___redArg(v_env_3462_, v_act_3463_, v_options_3464_, v_currNamespace_3465_, v_openDecls_3466_, v_cancelTk_x3f_3467_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown(lean_object* v_00_u03b1_3470_, lean_object* v_env_3471_, lean_object* v_act_3472_, lean_object* v_options_3473_, lean_object* v_currNamespace_3474_, lean_object* v_openDecls_3475_, lean_object* v_cancelTk_x3f_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_Doc_runMarkdown___redArg(v_env_3471_, v_act_3472_, v_options_3473_, v_currNamespace_3474_, v_openDecls_3475_, v_cancelTk_x3f_3476_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___boxed(lean_object* v_00_u03b1_3479_, lean_object* v_env_3480_, lean_object* v_act_3481_, lean_object* v_options_3482_, lean_object* v_currNamespace_3483_, lean_object* v_openDecls_3484_, lean_object* v_cancelTk_x3f_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_Doc_runMarkdown(v_00_u03b1_3479_, v_env_3480_, v_act_3481_, v_options_3482_, v_currNamespace_3483_, v_openDecls_3484_, v_cancelTk_x3f_3485_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(lean_object* v_x_3488_, size_t v_sz_3489_, size_t v_i_3490_, lean_object* v_bs_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
uint8_t v___x_3496_; 
v___x_3496_ = lean_usize_dec_lt(v_i_3490_, v_sz_3489_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
lean_dec_ref(v_x_3488_);
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v_bs_3491_);
return v___x_3497_;
}
else
{
lean_object* v_v_3498_; lean_object* v___x_3499_; lean_object* v_bs_x27_3500_; lean_object* v___x_3501_; 
v_v_3498_ = lean_array_uget(v_bs_3491_, v_i_3490_);
v___x_3499_ = lean_unsigned_to_nat(0u);
v_bs_x27_3500_ = lean_array_uset(v_bs_3491_, v_i_3490_, v___x_3499_);
lean_inc_ref(v_x_3488_);
v___x_3501_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3488_, v_v_3498_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; size_t v___x_3503_; size_t v___x_3504_; lean_object* v___x_3505_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___x_3503_ = ((size_t)1ULL);
v___x_3504_ = lean_usize_add(v_i_3490_, v___x_3503_);
v___x_3505_ = lean_array_uset(v_bs_x27_3500_, v_i_3490_, v_a_3502_);
v_i_3490_ = v___x_3504_;
v_bs_3491_ = v___x_3505_;
goto _start;
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec_ref(v_bs_x27_3500_);
lean_dec_ref(v_x_3488_);
v_a_3507_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3501_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3501_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed(lean_object* v_x_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(v_x_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(lean_object* v_x_3524_, size_t v_sz_3525_, size_t v___x_3526_, lean_object* v_content_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3524_, v_sz_3525_, v___x_3526_, v_content_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3541_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3541_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3541_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3537_ = l_Lean_Doc_joinInlines(v_a_3533_);
lean_dec(v_a_3533_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3537_);
v___x_3539_ = v___x_3535_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
v_a_3542_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3532_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3532_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed(lean_object* v_x_3550_, lean_object* v_sz_3551_, lean_object* v___x_3552_, lean_object* v_content_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
size_t v_sz_boxed_3558_; size_t v___x_3977__boxed_3559_; lean_object* v_res_3560_; 
v_sz_boxed_3558_ = lean_unbox_usize(v_sz_3551_);
lean_dec(v_sz_3551_);
v___x_3977__boxed_3559_ = lean_unbox_usize(v___x_3552_);
lean_dec(v___x_3552_);
v_res_3560_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(v_x_3550_, v_sz_boxed_3558_, v___x_3977__boxed_3559_, v_content_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(lean_object* v_x_3561_, lean_object* v_x_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v_pieces_3568_; lean_object* v_pieces_3572_; 
switch(lean_obj_tag(v_x_3562_))
{
case 0:
{
lean_object* v_string_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
lean_dec_ref(v_x_3561_);
v_string_3575_ = lean_ctor_get(v_x_3562_, 0);
lean_inc_ref(v_string_3575_);
lean_dec_ref_known(v_x_3562_, 1);
v___x_3576_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_3575_);
lean_dec_ref(v_string_3575_);
v___x_3577_ = lean_unsigned_to_nat(1u);
v___x_3578_ = lean_mk_empty_array_with_capacity(v___x_3577_);
v___x_3579_ = lean_array_push(v___x_3578_, v___x_3576_);
v___x_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
return v___x_3580_;
}
case 1:
{
lean_object* v_content_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3636_; 
v_content_3581_ = lean_ctor_get(v_x_3562_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_x_3562_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3583_ = v_x_3562_;
v_isShared_3584_ = v_isSharedCheck_3636_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_content_3581_);
lean_dec(v_x_3562_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3636_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
lean_ctor_set_tag(v___x_3583_, 9);
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_content_3581_);
v___x_3586_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3587_; lean_object* v_snd_3588_; lean_object* v_fst_3589_; lean_object* v_fst_3590_; lean_object* v_snd_3591_; lean_object* v_pieces_3593_; uint8_t v_inEmph_3601_; uint8_t v_inBold_3602_; uint8_t v_inLink_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3634_; 
v___x_3587_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3586_);
v_snd_3588_ = lean_ctor_get(v___x_3587_, 1);
lean_inc(v_snd_3588_);
v_fst_3589_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_fst_3589_);
lean_dec_ref(v___x_3587_);
v_fst_3590_ = lean_ctor_get(v_snd_3588_, 0);
lean_inc(v_fst_3590_);
v_snd_3591_ = lean_ctor_get(v_snd_3588_, 1);
lean_inc(v_snd_3591_);
lean_dec(v_snd_3588_);
v_inEmph_3601_ = lean_ctor_get_uint8(v_x_3561_, 0);
v_inBold_3602_ = lean_ctor_get_uint8(v_x_3561_, 1);
v_inLink_3603_ = lean_ctor_get_uint8(v_x_3561_, 2);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_x_3561_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3605_ = v_x_3561_;
v_isShared_3606_ = v_isSharedCheck_3634_;
goto v_resetjp_3604_;
}
else
{
lean_dec(v_x_3561_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3634_;
goto v_resetjp_3604_;
}
v___jp_3592_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v___x_3594_ = lean_string_utf8_byte_size(v_snd_3591_);
v___x_3595_ = lean_unsigned_to_nat(0u);
v___x_3596_ = lean_nat_dec_eq(v___x_3594_, v___x_3595_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3597_ = lean_unsigned_to_nat(1u);
v___x_3598_ = lean_mk_empty_array_with_capacity(v___x_3597_);
v___x_3599_ = lean_array_push(v___x_3598_, v_snd_3591_);
v___x_3600_ = lean_array_push(v_pieces_3593_, v___x_3599_);
v_pieces_3572_ = v___x_3600_;
goto v___jp_3571_;
}
else
{
lean_dec(v_snd_3591_);
v_pieces_3572_ = v_pieces_3593_;
goto v___jp_3571_;
}
}
v_resetjp_3604_:
{
uint8_t v___x_3607_; lean_object* v___x_3609_; 
v___x_3607_ = 1;
if (v_isShared_3606_ == 0)
{
v___x_3609_ = v___x_3605_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3633_, 1, v_inBold_3602_);
lean_ctor_set_uint8(v_reuseFailAlloc_3633_, 2, v_inLink_3603_);
v___x_3609_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___x_3610_; 
lean_ctor_set_uint8(v___x_3609_, 0, v___x_3607_);
v___x_3610_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3609_, v_fst_3590_, v_a_3563_, v_a_3564_, v_a_3565_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v_pieces_3613_; lean_object* v_pieces_3620_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3610_, 1);
v___x_3625_ = lean_unsigned_to_nat(0u);
v___x_3626_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3627_ = lean_string_utf8_byte_size(v_fst_3589_);
v___x_3628_ = lean_nat_dec_eq(v___x_3627_, v___x_3625_);
if (v___x_3628_ == 0)
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3629_ = lean_unsigned_to_nat(1u);
v___x_3630_ = lean_mk_empty_array_with_capacity(v___x_3629_);
v___x_3631_ = lean_array_push(v___x_3630_, v_fst_3589_);
v___x_3632_ = lean_array_push(v___x_3626_, v___x_3631_);
v_pieces_3620_ = v___x_3632_;
goto v___jp_3619_;
}
else
{
lean_dec(v_fst_3589_);
v_pieces_3620_ = v___x_3626_;
goto v___jp_3619_;
}
v___jp_3612_:
{
lean_object* v___x_3614_; 
v___x_3614_ = lean_array_push(v_pieces_3613_, v_a_3611_);
if (v_inEmph_3601_ == 0)
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3615_ = lean_unsigned_to_nat(1u);
v___x_3616_ = lean_mk_empty_array_with_capacity(v___x_3615_);
lean_dec_ref(v___x_3616_);
v___x_3617_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3618_ = lean_array_push(v___x_3614_, v___x_3617_);
v_pieces_3593_ = v___x_3618_;
goto v___jp_3592_;
}
else
{
v_pieces_3593_ = v___x_3614_;
goto v___jp_3592_;
}
}
v___jp_3619_:
{
if (v_inEmph_3601_ == 0)
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3621_ = lean_unsigned_to_nat(1u);
v___x_3622_ = lean_mk_empty_array_with_capacity(v___x_3621_);
lean_dec_ref(v___x_3622_);
v___x_3623_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3624_ = lean_array_push(v_pieces_3620_, v___x_3623_);
v_pieces_3613_ = v___x_3624_;
goto v___jp_3612_;
}
else
{
v_pieces_3613_ = v_pieces_3620_;
goto v___jp_3612_;
}
}
}
else
{
lean_dec(v_snd_3591_);
lean_dec(v_fst_3589_);
return v___x_3610_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3692_; 
v_content_3637_ = lean_ctor_get(v_x_3562_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_x_3562_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3639_ = v_x_3562_;
v_isShared_3640_ = v_isSharedCheck_3692_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_content_3637_);
lean_dec(v_x_3562_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3692_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
lean_ctor_set_tag(v___x_3639_, 9);
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_content_3637_);
v___x_3642_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
lean_object* v___x_3643_; lean_object* v_snd_3644_; lean_object* v_fst_3645_; lean_object* v_fst_3646_; lean_object* v_snd_3647_; lean_object* v_pieces_3649_; uint8_t v_inEmph_3657_; uint8_t v_inBold_3658_; uint8_t v_inLink_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3690_; 
v___x_3643_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3642_);
v_snd_3644_ = lean_ctor_get(v___x_3643_, 1);
lean_inc(v_snd_3644_);
v_fst_3645_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_fst_3645_);
lean_dec_ref(v___x_3643_);
v_fst_3646_ = lean_ctor_get(v_snd_3644_, 0);
lean_inc(v_fst_3646_);
v_snd_3647_ = lean_ctor_get(v_snd_3644_, 1);
lean_inc(v_snd_3647_);
lean_dec(v_snd_3644_);
v_inEmph_3657_ = lean_ctor_get_uint8(v_x_3561_, 0);
v_inBold_3658_ = lean_ctor_get_uint8(v_x_3561_, 1);
v_inLink_3659_ = lean_ctor_get_uint8(v_x_3561_, 2);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_x_3561_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3661_ = v_x_3561_;
v_isShared_3662_ = v_isSharedCheck_3690_;
goto v_resetjp_3660_;
}
else
{
lean_dec(v_x_3561_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3690_;
goto v_resetjp_3660_;
}
v___jp_3648_:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; 
v___x_3650_ = lean_string_utf8_byte_size(v_snd_3647_);
v___x_3651_ = lean_unsigned_to_nat(0u);
v___x_3652_ = lean_nat_dec_eq(v___x_3650_, v___x_3651_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3653_ = lean_unsigned_to_nat(1u);
v___x_3654_ = lean_mk_empty_array_with_capacity(v___x_3653_);
v___x_3655_ = lean_array_push(v___x_3654_, v_snd_3647_);
v___x_3656_ = lean_array_push(v_pieces_3649_, v___x_3655_);
v_pieces_3568_ = v___x_3656_;
goto v___jp_3567_;
}
else
{
lean_dec(v_snd_3647_);
v_pieces_3568_ = v_pieces_3649_;
goto v___jp_3567_;
}
}
v_resetjp_3660_:
{
uint8_t v___x_3663_; lean_object* v___x_3665_; 
v___x_3663_ = 1;
if (v_isShared_3662_ == 0)
{
v___x_3665_ = v___x_3661_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3689_, 0, v_inEmph_3657_);
lean_ctor_set_uint8(v_reuseFailAlloc_3689_, 2, v_inLink_3659_);
v___x_3665_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; 
lean_ctor_set_uint8(v___x_3665_, 1, v___x_3663_);
v___x_3666_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3665_, v_fst_3646_, v_a_3563_, v_a_3564_, v_a_3565_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v_pieces_3669_; lean_object* v_pieces_3676_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
v___x_3681_ = lean_unsigned_to_nat(0u);
v___x_3682_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3683_ = lean_string_utf8_byte_size(v_fst_3645_);
v___x_3684_ = lean_nat_dec_eq(v___x_3683_, v___x_3681_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3685_ = lean_unsigned_to_nat(1u);
v___x_3686_ = lean_mk_empty_array_with_capacity(v___x_3685_);
v___x_3687_ = lean_array_push(v___x_3686_, v_fst_3645_);
v___x_3688_ = lean_array_push(v___x_3682_, v___x_3687_);
v_pieces_3676_ = v___x_3688_;
goto v___jp_3675_;
}
else
{
lean_dec(v_fst_3645_);
v_pieces_3676_ = v___x_3682_;
goto v___jp_3675_;
}
v___jp_3668_:
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_array_push(v_pieces_3669_, v_a_3667_);
if (v_inBold_3658_ == 0)
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3671_ = lean_unsigned_to_nat(1u);
v___x_3672_ = lean_mk_empty_array_with_capacity(v___x_3671_);
lean_dec_ref(v___x_3672_);
v___x_3673_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3674_ = lean_array_push(v___x_3670_, v___x_3673_);
v_pieces_3649_ = v___x_3674_;
goto v___jp_3648_;
}
else
{
v_pieces_3649_ = v___x_3670_;
goto v___jp_3648_;
}
}
v___jp_3675_:
{
if (v_inBold_3658_ == 0)
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3677_ = lean_unsigned_to_nat(1u);
v___x_3678_ = lean_mk_empty_array_with_capacity(v___x_3677_);
lean_dec_ref(v___x_3678_);
v___x_3679_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3680_ = lean_array_push(v_pieces_3676_, v___x_3679_);
v_pieces_3669_ = v___x_3680_;
goto v___jp_3668_;
}
else
{
v_pieces_3669_ = v_pieces_3676_;
goto v___jp_3668_;
}
}
}
else
{
lean_dec(v_snd_3647_);
lean_dec(v_fst_3645_);
return v___x_3666_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
lean_dec_ref(v_x_3561_);
v_string_3693_ = lean_ctor_get(v_x_3562_, 0);
lean_inc_ref(v_string_3693_);
lean_dec_ref_known(v_x_3562_, 1);
v___x_3694_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_3693_);
v___x_3695_ = lean_unsigned_to_nat(1u);
v___x_3696_ = lean_mk_empty_array_with_capacity(v___x_3695_);
v___x_3697_ = lean_array_push(v___x_3696_, v___x_3694_);
v___x_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
return v___x_3698_;
}
case 4:
{
uint8_t v_mode_3699_; 
lean_dec_ref(v_x_3561_);
v_mode_3699_ = lean_ctor_get_uint8(v_x_3562_, sizeof(void*)*1);
if (v_mode_3699_ == 0)
{
lean_object* v_string_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_string_3700_ = lean_ctor_get(v_x_3562_, 0);
lean_inc_ref(v_string_3700_);
lean_dec_ref_known(v_x_3562_, 1);
v___x_3701_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_3702_ = lean_string_append(v___x_3701_, v_string_3700_);
lean_dec_ref(v_string_3700_);
v___x_3703_ = lean_string_append(v___x_3702_, v___x_3701_);
v___x_3704_ = lean_unsigned_to_nat(1u);
v___x_3705_ = lean_mk_empty_array_with_capacity(v___x_3704_);
v___x_3706_ = lean_array_push(v___x_3705_, v___x_3703_);
v___x_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
return v___x_3707_;
}
else
{
lean_object* v_string_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v_string_3708_ = lean_ctor_get(v_x_3562_, 0);
lean_inc_ref(v_string_3708_);
lean_dec_ref_known(v_x_3562_, 1);
v___x_3709_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_3710_ = lean_string_append(v___x_3709_, v_string_3708_);
lean_dec_ref(v_string_3708_);
v___x_3711_ = lean_string_append(v___x_3710_, v___x_3709_);
v___x_3712_ = lean_unsigned_to_nat(1u);
v___x_3713_ = lean_mk_empty_array_with_capacity(v___x_3712_);
v___x_3714_ = lean_array_push(v___x_3713_, v___x_3711_);
v___x_3715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
return v___x_3715_;
}
}
case 5:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
lean_dec_ref_known(v_x_3562_, 1);
lean_dec_ref(v_x_3561_);
v___x_3716_ = lean_unsigned_to_nat(2u);
v___x_3717_ = lean_mk_empty_array_with_capacity(v___x_3716_);
lean_dec_ref(v___x_3717_);
v___x_3718_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
return v___x_3719_;
}
case 6:
{
uint8_t v_inLink_3720_; 
v_inLink_3720_ = lean_ctor_get_uint8(v_x_3561_, 2);
if (v_inLink_3720_ == 0)
{
lean_object* v_content_3721_; lean_object* v_url_3722_; uint8_t v_inEmph_3723_; uint8_t v_inBold_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3755_; 
v_content_3721_ = lean_ctor_get(v_x_3562_, 0);
lean_inc_ref(v_content_3721_);
v_url_3722_ = lean_ctor_get(v_x_3562_, 1);
lean_inc_ref(v_url_3722_);
lean_dec_ref_known(v_x_3562_, 2);
v_inEmph_3723_ = lean_ctor_get_uint8(v_x_3561_, 0);
v_inBold_3724_ = lean_ctor_get_uint8(v_x_3561_, 1);
v_isSharedCheck_3755_ = !lean_is_exclusive(v_x_3561_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3726_ = v_x_3561_;
v_isShared_3727_ = v_isSharedCheck_3755_;
goto v_resetjp_3725_;
}
else
{
lean_dec(v_x_3561_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3755_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
uint8_t v___x_3728_; lean_object* v___x_3730_; 
v___x_3728_ = 1;
if (v_isShared_3727_ == 0)
{
v___x_3730_ = v___x_3726_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 0, v_inEmph_3723_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 1, v_inBold_3724_);
v___x_3730_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
lean_ctor_set_uint8(v___x_3730_, 2, v___x_3728_);
v___x_3731_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3731_, 0, v_content_3721_);
v___x_3732_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3730_, v___x_3731_, v_a_3563_, v_a_3564_, v_a_3565_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3753_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3735_ = v___x_3732_;
v_isShared_3736_ = v_isSharedCheck_3753_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3732_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3753_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3751_; 
v___x_3737_ = lean_unsigned_to_nat(1u);
v___x_3738_ = lean_mk_empty_array_with_capacity(v___x_3737_);
v___x_3739_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3740_ = lean_string_append(v___x_3739_, v_url_3722_);
lean_dec_ref(v_url_3722_);
v___x_3741_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3742_ = lean_string_append(v___x_3740_, v___x_3741_);
v___x_3743_ = lean_array_push(v___x_3738_, v___x_3742_);
v___x_3744_ = lean_unsigned_to_nat(3u);
v___x_3745_ = lean_mk_empty_array_with_capacity(v___x_3744_);
lean_dec_ref(v___x_3745_);
v___x_3746_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_3747_ = lean_array_push(v___x_3746_, v_a_3733_);
v___x_3748_ = lean_array_push(v___x_3747_, v___x_3743_);
v___x_3749_ = l_Lean_Doc_joinInlines(v___x_3748_);
lean_dec_ref(v___x_3748_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v___x_3749_);
v___x_3751_ = v___x_3735_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
else
{
lean_dec_ref(v_url_3722_);
return v___x_3732_;
}
}
}
}
else
{
lean_object* v_content_3756_; size_t v_sz_3757_; size_t v___x_3758_; lean_object* v___x_3759_; 
v_content_3756_ = lean_ctor_get(v_x_3562_, 0);
lean_inc_ref(v_content_3756_);
lean_dec_ref_known(v_x_3562_, 2);
v_sz_3757_ = lean_array_size(v_content_3756_);
v___x_3758_ = ((size_t)0ULL);
v___x_3759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3561_, v_sz_3757_, v___x_3758_, v_content_3756_, v_a_3563_, v_a_3564_, v_a_3565_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3768_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3762_ = v___x_3759_;
v_isShared_3763_ = v_isSharedCheck_3768_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3759_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3768_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3764_; lean_object* v___x_3766_; 
v___x_3764_ = l_Lean_Doc_joinInlines(v_a_3760_);
lean_dec(v_a_3760_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 0, v___x_3764_);
v___x_3766_ = v___x_3762_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
v_a_3769_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3759_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3759_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
}
case 7:
{
lean_object* v_name_3777_; lean_object* v_content_3778_; size_t v_sz_3779_; size_t v___x_3780_; lean_object* v___x_3781_; 
v_name_3777_ = lean_ctor_get(v_x_3562_, 0);
lean_inc_ref(v_name_3777_);
v_content_3778_ = lean_ctor_get(v_x_3562_, 1);
lean_inc_ref(v_content_3778_);
lean_dec_ref_known(v_x_3562_, 2);
v_sz_3779_ = lean_array_size(v_content_3778_);
v___x_3780_ = ((size_t)0ULL);
v___x_3781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3561_, v_sz_3779_, v___x_3780_, v_content_3778_, v_a_3563_, v_a_3564_, v_a_3565_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
v___x_3783_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_3784_ = l_Lean_Doc_joinInlines(v_a_3782_);
lean_dec(v_a_3782_);
v___x_3785_ = lean_array_to_list(v___x_3784_);
v___x_3786_ = l_String_intercalate(v___x_3783_, v___x_3785_);
lean_inc_ref(v_name_3777_);
v___x_3787_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_3777_, v___x_3786_, v_a_3563_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3801_; 
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; 
v_unused_3802_ = lean_ctor_get(v___x_3787_, 0);
lean_dec(v_unused_3802_);
v___x_3789_ = v___x_3787_;
v_isShared_3790_ = v_isSharedCheck_3801_;
goto v_resetjp_3788_;
}
else
{
lean_dec(v___x_3787_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3801_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3799_; 
v___x_3791_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_3792_ = lean_string_append(v___x_3791_, v_name_3777_);
lean_dec_ref(v_name_3777_);
v___x_3793_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_3794_ = lean_string_append(v___x_3792_, v___x_3793_);
v___x_3795_ = lean_unsigned_to_nat(1u);
v___x_3796_ = lean_mk_empty_array_with_capacity(v___x_3795_);
v___x_3797_ = lean_array_push(v___x_3796_, v___x_3794_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3797_);
v___x_3799_ = v___x_3789_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3797_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec_ref(v_name_3777_);
v_a_3803_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3787_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3787_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref(v_name_3777_);
v_a_3811_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3781_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3781_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
case 8:
{
lean_object* v_alt_3819_; lean_object* v_url_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
lean_dec_ref(v_x_3561_);
v_alt_3819_ = lean_ctor_get(v_x_3562_, 0);
lean_inc_ref(v_alt_3819_);
v_url_3820_ = lean_ctor_get(v_x_3562_, 1);
lean_inc_ref(v_url_3820_);
lean_dec_ref_known(v_x_3562_, 2);
v___x_3821_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_3822_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_3819_);
lean_dec_ref(v_alt_3819_);
v___x_3823_ = lean_string_append(v___x_3821_, v___x_3822_);
lean_dec_ref(v___x_3822_);
v___x_3824_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3825_ = lean_string_append(v___x_3823_, v___x_3824_);
v___x_3826_ = lean_string_append(v___x_3825_, v_url_3820_);
lean_dec_ref(v_url_3820_);
v___x_3827_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3828_ = lean_string_append(v___x_3826_, v___x_3827_);
v___x_3829_ = lean_unsigned_to_nat(1u);
v___x_3830_ = lean_mk_empty_array_with_capacity(v___x_3829_);
v___x_3831_ = lean_array_push(v___x_3830_, v___x_3828_);
v___x_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
return v___x_3832_;
}
case 9:
{
lean_object* v_content_3833_; size_t v_sz_3834_; size_t v___x_3835_; lean_object* v___x_3836_; 
v_content_3833_ = lean_ctor_get(v_x_3562_, 0);
lean_inc_ref(v_content_3833_);
lean_dec_ref_known(v_x_3562_, 1);
v_sz_3834_ = lean_array_size(v_content_3833_);
v___x_3835_ = ((size_t)0ULL);
v___x_3836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3561_, v_sz_3834_, v___x_3835_, v_content_3833_, v_a_3563_, v_a_3564_, v_a_3565_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3845_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3845_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3845_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3841_; lean_object* v___x_3843_; 
v___x_3841_ = l_Lean_Doc_joinInlines(v_a_3837_);
lean_dec(v_a_3837_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3841_);
v___x_3843_ = v___x_3839_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3841_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
v_a_3846_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3836_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3836_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
default: 
{
lean_object* v_container_3854_; 
v_container_3854_ = lean_ctor_get(v_x_3562_, 0);
if (lean_obj_tag(v_container_3854_) == 0)
{
lean_object* v_content_3855_; lean_object* v_val_3856_; lean_object* v___f_3857_; size_t v_sz_3858_; size_t v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v_fallback_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
lean_inc_ref(v_container_3854_);
v_content_3855_ = lean_ctor_get(v_x_3562_, 1);
lean_inc_ref_n(v_content_3855_, 2);
lean_dec_ref_known(v_x_3562_, 2);
v_val_3856_ = lean_ctor_get(v_container_3854_, 0);
lean_inc(v_val_3856_);
lean_dec_ref_known(v_container_3854_, 1);
lean_inc_ref_n(v_x_3561_, 2);
v___f_3857_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3857_, 0, v_x_3561_);
v_sz_3858_ = lean_array_size(v_content_3855_);
v___x_3859_ = ((size_t)0ULL);
v___x_3860_ = lean_box_usize(v_sz_3858_);
v___x_3861_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
v_fallback_3862_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v_fallback_3862_, 0, v_x_3561_);
lean_closure_set(v_fallback_3862_, 1, v___x_3860_);
lean_closure_set(v_fallback_3862_, 2, v___x_3861_);
lean_closure_set(v_fallback_3862_, 3, v_content_3855_);
v___x_3863_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3856_);
v___x_3864_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_3863_, v_a_3564_, v_a_3565_);
lean_dec(v___x_3863_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
if (lean_obj_tag(v_a_3865_) == 0)
{
lean_object* v___x_3866_; 
lean_dec_ref(v_fallback_3862_);
lean_dec_ref(v___f_3857_);
lean_dec(v_val_3856_);
v___x_3866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3561_, v_sz_3858_, v___x_3859_, v_content_3855_, v_a_3563_, v_a_3564_, v_a_3565_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3875_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3869_ = v___x_3866_;
v_isShared_3870_ = v_isSharedCheck_3875_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3866_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3875_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3871_; lean_object* v___x_3873_; 
v___x_3871_ = l_Lean_Doc_joinInlines(v_a_3867_);
lean_dec(v_a_3867_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3871_);
v___x_3873_ = v___x_3869_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
v_a_3876_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3866_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3866_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
else
{
lean_object* v_val_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
lean_dec_ref(v_x_3561_);
v_val_3884_ = lean_ctor_get(v_a_3865_, 0);
lean_inc(v_val_3884_);
lean_dec_ref_known(v_a_3865_, 1);
v___x_3885_ = lean_apply_3(v_val_3884_, v___f_3857_, v_val_3856_, v_content_3855_);
v___x_3886_ = l_Lean_Doc_withRendererFallback(v_fallback_3862_, v___x_3885_, v_a_3563_, v_a_3564_, v_a_3565_);
return v___x_3886_;
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec_ref(v_fallback_3862_);
lean_dec_ref(v___f_3857_);
lean_dec(v_val_3856_);
lean_dec_ref(v_content_3855_);
lean_dec_ref(v_x_3561_);
v_a_3887_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3864_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3864_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
else
{
lean_object* v_content_3895_; size_t v_sz_3896_; size_t v___x_3897_; lean_object* v___x_3898_; 
v_content_3895_ = lean_ctor_get(v_x_3562_, 1);
lean_inc_ref(v_content_3895_);
lean_dec_ref_known(v_x_3562_, 2);
v_sz_3896_ = lean_array_size(v_content_3895_);
v___x_3897_ = ((size_t)0ULL);
v___x_3898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3561_, v_sz_3896_, v___x_3897_, v_content_3895_, v_a_3563_, v_a_3564_, v_a_3565_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3907_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3901_ = v___x_3898_;
v_isShared_3902_ = v_isSharedCheck_3907_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3907_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3903_ = l_Lean_Doc_joinInlines(v_a_3899_);
lean_dec(v_a_3899_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3903_);
v___x_3905_ = v___x_3901_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
v_a_3908_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3898_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3898_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
}
}
v___jp_3567_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = l_Lean_Doc_joinInlines(v_pieces_3568_);
lean_dec_ref(v_pieces_3568_);
v___x_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
return v___x_3570_;
}
v___jp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = l_Lean_Doc_joinInlines(v_pieces_3572_);
lean_dec_ref(v_pieces_3572_);
v___x_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
return v___x_3574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(lean_object* v_x_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3923_, lean_object* v_sz_3924_, lean_object* v_i_3925_, lean_object* v_bs_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
size_t v_sz_boxed_3931_; size_t v_i_boxed_3932_; lean_object* v_res_3933_; 
v_sz_boxed_3931_ = lean_unbox_usize(v_sz_3924_);
lean_dec(v_sz_3924_);
v_i_boxed_3932_ = lean_unbox_usize(v_i_3925_);
lean_dec(v_i_3925_);
v_res_3933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3923_, v_sz_boxed_3931_, v_i_boxed_3932_, v_bs_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed(lean_object* v_x_3934_, lean_object* v_x_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3934_, v_x_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
lean_dec(v_a_3936_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(lean_object* v___x_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0___boxed(lean_object* v___x_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(v___x_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(lean_object* v_x_3955_, lean_object* v_x_3956_){
_start:
{
lean_object* v_zero_3957_; uint8_t v_isZero_3958_; 
v_zero_3957_ = lean_unsigned_to_nat(0u);
v_isZero_3958_ = lean_nat_dec_eq(v_x_3955_, v_zero_3957_);
if (v_isZero_3958_ == 1)
{
lean_dec(v_x_3955_);
return v_x_3956_;
}
else
{
uint32_t v___x_3959_; lean_object* v_one_3960_; lean_object* v_n_3961_; lean_object* v___x_3962_; 
v___x_3959_ = 32;
v_one_3960_ = lean_unsigned_to_nat(1u);
v_n_3961_ = lean_nat_sub(v_x_3955_, v_one_3960_);
lean_dec(v_x_3955_);
v___x_3962_ = lean_string_push(v_x_3956_, v___x_3959_);
v_x_3955_ = v_n_3961_;
v_x_3956_ = v___x_3962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(size_t v_sz_3964_, size_t v_i_3965_, lean_object* v_bs_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
uint8_t v___x_3971_; 
v___x_3971_ = lean_usize_dec_lt(v_i_3965_, v_sz_3964_);
if (v___x_3971_ == 0)
{
lean_object* v___x_3972_; 
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v_bs_3966_);
return v___x_3972_;
}
else
{
lean_object* v_v_3973_; lean_object* v___x_3974_; lean_object* v_bs_x27_3975_; size_t v_sz_3976_; size_t v___x_3977_; lean_object* v___x_3978_; 
v_v_3973_ = lean_array_uget(v_bs_3966_, v_i_3965_);
v___x_3974_ = lean_unsigned_to_nat(0u);
v_bs_x27_3975_ = lean_array_uset(v_bs_3966_, v_i_3965_, v___x_3974_);
v_sz_3976_ = lean_array_size(v_v_3973_);
v___x_3977_ = ((size_t)0ULL);
v___x_3978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_3976_, v___x_3977_, v_v_3973_, v___y_3967_, v___y_3968_, v___y_3969_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; size_t v___x_3984_; size_t v___x_3985_; lean_object* v___x_3986_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3979_);
lean_dec_ref_known(v___x_3978_, 1);
v___x_3980_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_3981_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_3982_ = l_Lean_Doc_joinBlocks(v_a_3979_);
lean_dec(v_a_3979_);
v___x_3983_ = l_Lean_Doc_prefixListLines(v___x_3980_, v___x_3981_, v___x_3982_);
v___x_3984_ = ((size_t)1ULL);
v___x_3985_ = lean_usize_add(v_i_3965_, v___x_3984_);
v___x_3986_ = lean_array_uset(v_bs_x27_3975_, v_i_3965_, v___x_3983_);
v_i_3965_ = v___x_3985_;
v_bs_3966_ = v___x_3986_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_3975_);
return v___x_3978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(lean_object* v_as_3988_, size_t v_sz_3989_, size_t v_i_3990_, lean_object* v_b_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
uint8_t v___x_3996_; 
v___x_3996_ = lean_usize_dec_lt(v_i_3990_, v_sz_3989_);
if (v___x_3996_ == 0)
{
lean_object* v___x_3997_; 
v___x_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3997_, 0, v_b_3991_);
return v___x_3997_;
}
else
{
lean_object* v_fst_3998_; lean_object* v_snd_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4033_; 
v_fst_3998_ = lean_ctor_get(v_b_3991_, 0);
v_snd_3999_ = lean_ctor_get(v_b_3991_, 1);
v_isSharedCheck_4033_ = !lean_is_exclusive(v_b_3991_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4001_ = v_b_3991_;
v_isShared_4002_ = v_isSharedCheck_4033_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_snd_3999_);
lean_inc(v_fst_3998_);
lean_dec(v_b_3991_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4033_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4003_; lean_object* v_a_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; size_t v_sz_4011_; size_t v___x_4012_; lean_object* v___x_4013_; 
v___x_4003_ = lean_unsigned_to_nat(1u);
v_a_4004_ = lean_array_uget_borrowed(v_as_3988_, v_i_3990_);
lean_inc(v_snd_3999_);
v___x_4005_ = l_Nat_reprFast(v_snd_3999_);
v___x_4006_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_4007_ = lean_string_append(v___x_4005_, v___x_4006_);
v___x_4008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4009_ = lean_string_utf8_byte_size(v___x_4007_);
v___x_4010_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(v___x_4009_, v___x_4008_);
v_sz_4011_ = lean_array_size(v_a_4004_);
v___x_4012_ = ((size_t)0ULL);
lean_inc(v_a_4004_);
v___x_4013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4011_, v___x_4012_, v_a_4004_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4020_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4014_);
lean_dec_ref_known(v___x_4013_, 1);
v___x_4015_ = l_Lean_Doc_joinBlocks(v_a_4014_);
lean_dec(v_a_4014_);
v___x_4016_ = l_Lean_Doc_prefixListLines(v___x_4007_, v___x_4010_, v___x_4015_);
v___x_4017_ = lean_array_push(v_fst_3998_, v___x_4016_);
v___x_4018_ = lean_nat_add(v_snd_3999_, v___x_4003_);
lean_dec(v_snd_3999_);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 1, v___x_4018_);
lean_ctor_set(v___x_4001_, 0, v___x_4017_);
v___x_4020_ = v___x_4001_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v___x_4017_);
lean_ctor_set(v_reuseFailAlloc_4024_, 1, v___x_4018_);
v___x_4020_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
size_t v___x_4021_; size_t v___x_4022_; 
v___x_4021_ = ((size_t)1ULL);
v___x_4022_ = lean_usize_add(v_i_3990_, v___x_4021_);
v_i_3990_ = v___x_4022_;
v_b_3991_ = v___x_4020_;
goto _start;
}
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec_ref(v___x_4010_);
lean_dec_ref(v___x_4007_);
lean_del_object(v___x_4001_);
lean_dec(v_snd_3999_);
lean_dec(v_fst_3998_);
v_a_4025_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_4013_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4013_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(size_t v_sz_4034_, size_t v_i_4035_, lean_object* v_bs_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
uint8_t v___x_4041_; 
v___x_4041_ = lean_usize_dec_lt(v_i_4035_, v_sz_4034_);
if (v___x_4041_ == 0)
{
lean_object* v___x_4042_; 
v___x_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4042_, 0, v_bs_4036_);
return v___x_4042_;
}
else
{
lean_object* v_v_4043_; lean_object* v___x_4044_; lean_object* v_term_4045_; lean_object* v_desc_4046_; lean_object* v___x_4047_; lean_object* v_bs_x27_4048_; lean_object* v_a_4050_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v_v_4043_ = lean_array_uget_borrowed(v_bs_4036_, v_i_4035_);
v___x_4044_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_4045_ = lean_ctor_get(v_v_4043_, 0);
lean_inc_ref(v_term_4045_);
v_desc_4046_ = lean_ctor_get(v_v_4043_, 1);
lean_inc_ref(v_desc_4046_);
v___x_4047_ = lean_unsigned_to_nat(0u);
v_bs_x27_4048_ = lean_array_uset(v_bs_4036_, v_i_4035_, v___x_4047_);
v___x_4055_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4055_, 0, v_term_4045_);
v___x_4056_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4044_, v___x_4055_, v___y_4037_, v___y_4038_, v___y_4039_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; size_t v_sz_4058_; size_t v___x_4059_; lean_object* v___x_4060_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref_known(v___x_4056_, 1);
v_sz_4058_ = lean_array_size(v_desc_4046_);
v___x_4059_ = ((size_t)0ULL);
lean_inc_ref(v_desc_4046_);
v___x_4060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4058_, v___x_4059_, v_desc_4046_, v___y_4037_, v___y_4038_, v___y_4039_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___y_4063_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; uint8_t v___x_4076_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
v___x_4067_ = lean_unsigned_to_nat(1u);
v___x_4068_ = lean_mk_empty_array_with_capacity(v___x_4067_);
v___x_4069_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_4070_ = lean_unsigned_to_nat(2u);
v___x_4071_ = lean_mk_empty_array_with_capacity(v___x_4070_);
v___x_4072_ = lean_array_push(v___x_4071_, v_a_4057_);
v___x_4073_ = lean_array_push(v___x_4072_, v___x_4069_);
v___x_4074_ = l_Lean_Doc_joinInlines(v___x_4073_);
lean_dec_ref(v___x_4073_);
v___x_4075_ = lean_array_get_size(v_desc_4046_);
lean_dec_ref(v_desc_4046_);
v___x_4076_ = lean_nat_dec_le(v___x_4075_, v___x_4067_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4077_ = lean_array_push(v___x_4068_, v___x_4074_);
v___x_4078_ = l_Array_append___redArg(v___x_4077_, v_a_4061_);
lean_dec(v_a_4061_);
v___x_4079_ = l_Lean_Doc_joinBlocks(v___x_4078_);
lean_dec_ref(v___x_4078_);
v___y_4063_ = v___x_4079_;
goto v___jp_4062_;
}
else
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
lean_dec_ref(v___x_4068_);
v___x_4080_ = l_Lean_Doc_joinBlocks(v_a_4061_);
lean_dec(v_a_4061_);
v___x_4081_ = l_Array_append___redArg(v___x_4074_, v___x_4080_);
lean_dec_ref(v___x_4080_);
v___y_4063_ = v___x_4081_;
goto v___jp_4062_;
}
v___jp_4062_:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4064_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_4065_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_4066_ = l_Lean_Doc_prefixListLines(v___x_4064_, v___x_4065_, v___y_4063_);
v_a_4050_ = v___x_4066_;
goto v___jp_4049_;
}
}
else
{
lean_dec(v_a_4057_);
lean_dec_ref(v_bs_x27_4048_);
lean_dec_ref(v_desc_4046_);
return v___x_4060_;
}
}
else
{
lean_dec_ref(v_desc_4046_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4082_; 
v_a_4082_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v___x_4056_, 1);
v_a_4050_ = v_a_4082_;
goto v___jp_4049_;
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec_ref(v_bs_x27_4048_);
v_a_4083_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4056_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4056_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
v___jp_4049_:
{
size_t v___x_4051_; size_t v___x_4052_; lean_object* v___x_4053_; 
v___x_4051_ = ((size_t)1ULL);
v___x_4052_ = lean_usize_add(v_i_4035_, v___x_4051_);
v___x_4053_ = lean_array_uset(v_bs_x27_4048_, v_i_4035_, v_a_4050_);
v_i_4035_ = v___x_4052_;
v_bs_4036_ = v___x_4053_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed(lean_object* v_x_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_x_4091_, v_a_4092_, v_a_4093_, v_a_4094_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
lean_dec(v_a_4092_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed(lean_object* v_sz_4099_, lean_object* v___x_4100_, lean_object* v_content_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
size_t v_sz_boxed_4106_; size_t v___x_4832__boxed_4107_; lean_object* v_res_4108_; 
v_sz_boxed_4106_ = lean_unbox_usize(v_sz_4099_);
lean_dec(v_sz_4099_);
v___x_4832__boxed_4107_ = lean_unbox_usize(v___x_4100_);
lean_dec(v___x_4100_);
v_res_4108_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(v_sz_boxed_4106_, v___x_4832__boxed_4107_, v_content_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(lean_object* v_x_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_){
_start:
{
switch(lean_obj_tag(v_x_4109_))
{
case 0:
{
lean_object* v_contents_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4123_; 
v_contents_4114_ = lean_ctor_get(v_x_4109_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v_x_4109_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4116_ = v_x_4109_;
v_isShared_4117_ = v_isSharedCheck_4123_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_contents_4114_);
lean_dec(v_x_4109_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4123_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4118_; lean_object* v___x_4120_; 
v___x_4118_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_4117_ == 0)
{
lean_ctor_set_tag(v___x_4116_, 9);
v___x_4120_ = v___x_4116_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_contents_4114_);
v___x_4120_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4121_; 
v___x_4121_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4118_, v___x_4120_, v_a_4110_, v_a_4111_, v_a_4112_);
return v___x_4121_;
}
}
}
case 1:
{
lean_object* v_content_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4132_; 
v_content_4124_ = lean_ctor_get(v_x_4109_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_x_4109_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4126_ = v_x_4109_;
v_isShared_4127_ = v_isSharedCheck_4132_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_content_4124_);
lean_dec(v_x_4109_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4132_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4128_; lean_object* v___x_4130_; 
v___x_4128_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_4124_);
if (v_isShared_4127_ == 0)
{
lean_ctor_set_tag(v___x_4126_, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4128_);
v___x_4130_ = v___x_4126_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v___x_4128_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
case 2:
{
lean_object* v_items_4133_; size_t v_sz_4134_; size_t v___x_4135_; lean_object* v___x_4136_; 
v_items_4133_ = lean_ctor_get(v_x_4109_, 0);
lean_inc_ref(v_items_4133_);
lean_dec_ref_known(v_x_4109_, 1);
v_sz_4134_ = lean_array_size(v_items_4133_);
v___x_4135_ = ((size_t)0ULL);
v___x_4136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_4134_, v___x_4135_, v_items_4133_, v_a_4110_, v_a_4111_, v_a_4112_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4145_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4139_ = v___x_4136_;
v_isShared_4140_ = v_isSharedCheck_4145_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4136_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4145_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4141_; lean_object* v___x_4143_; 
v___x_4141_ = l_Lean_Doc_joinBlocks(v_a_4137_);
lean_dec(v_a_4137_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v___x_4141_);
v___x_4143_ = v___x_4139_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
v_a_4146_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4136_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4136_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
case 3:
{
lean_object* v_start_4154_; lean_object* v_items_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4189_; 
v_start_4154_ = lean_ctor_get(v_x_4109_, 0);
v_items_4155_ = lean_ctor_get(v_x_4109_, 1);
v_isSharedCheck_4189_ = !lean_is_exclusive(v_x_4109_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4157_ = v_x_4109_;
v_isShared_4158_ = v_isSharedCheck_4189_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_items_4155_);
lean_inc(v_start_4154_);
lean_dec(v_x_4109_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4189_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v_out_4159_; lean_object* v___y_4161_; lean_object* v___x_4186_; lean_object* v___x_4187_; uint8_t v___x_4188_; 
v_out_4159_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_4186_ = lean_unsigned_to_nat(1u);
v___x_4187_ = l_Int_toNat(v_start_4154_);
lean_dec(v_start_4154_);
v___x_4188_ = lean_nat_dec_le(v___x_4186_, v___x_4187_);
if (v___x_4188_ == 0)
{
lean_dec(v___x_4187_);
v___y_4161_ = v___x_4186_;
goto v___jp_4160_;
}
else
{
v___y_4161_ = v___x_4187_;
goto v___jp_4160_;
}
v___jp_4160_:
{
lean_object* v___x_4163_; 
if (v_isShared_4158_ == 0)
{
lean_ctor_set_tag(v___x_4157_, 0);
lean_ctor_set(v___x_4157_, 1, v___y_4161_);
lean_ctor_set(v___x_4157_, 0, v_out_4159_);
v___x_4163_ = v___x_4157_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_out_4159_);
lean_ctor_set(v_reuseFailAlloc_4185_, 1, v___y_4161_);
v___x_4163_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
size_t v_sz_4164_; size_t v___x_4165_; lean_object* v___x_4166_; 
v_sz_4164_ = lean_array_size(v_items_4155_);
v___x_4165_ = ((size_t)0ULL);
v___x_4166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_items_4155_, v_sz_4164_, v___x_4165_, v___x_4163_, v_a_4110_, v_a_4111_, v_a_4112_);
lean_dec_ref(v_items_4155_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4176_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4169_ = v___x_4166_;
v_isShared_4170_ = v_isSharedCheck_4176_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4166_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4176_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v_fst_4171_; lean_object* v___x_4172_; lean_object* v___x_4174_; 
v_fst_4171_ = lean_ctor_get(v_a_4167_, 0);
lean_inc(v_fst_4171_);
lean_dec(v_a_4167_);
v___x_4172_ = l_Lean_Doc_joinBlocks(v_fst_4171_);
lean_dec(v_fst_4171_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 0, v___x_4172_);
v___x_4174_ = v___x_4169_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4172_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
v_a_4177_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4166_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4166_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_4190_; size_t v_sz_4191_; size_t v___x_4192_; lean_object* v___x_4193_; 
v_items_4190_ = lean_ctor_get(v_x_4109_, 0);
lean_inc_ref(v_items_4190_);
lean_dec_ref_known(v_x_4109_, 1);
v_sz_4191_ = lean_array_size(v_items_4190_);
v___x_4192_ = ((size_t)0ULL);
v___x_4193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_4191_, v___x_4192_, v_items_4190_, v_a_4110_, v_a_4111_, v_a_4112_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4202_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4196_ = v___x_4193_;
v_isShared_4197_ = v_isSharedCheck_4202_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4193_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4202_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4198_; lean_object* v___x_4200_; 
v___x_4198_ = l_Lean_Doc_joinBlocks(v_a_4194_);
lean_dec(v_a_4194_);
if (v_isShared_4197_ == 0)
{
lean_ctor_set(v___x_4196_, 0, v___x_4198_);
v___x_4200_ = v___x_4196_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4198_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
v_a_4203_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4193_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4193_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
case 5:
{
lean_object* v_items_4211_; size_t v_sz_4212_; size_t v___x_4213_; lean_object* v___x_4214_; 
v_items_4211_ = lean_ctor_get(v_x_4109_, 0);
lean_inc_ref(v_items_4211_);
lean_dec_ref_known(v_x_4109_, 1);
v_sz_4212_ = lean_array_size(v_items_4211_);
v___x_4213_ = ((size_t)0ULL);
v___x_4214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4212_, v___x_4213_, v_items_4211_, v_a_4110_, v_a_4111_, v_a_4112_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4225_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4217_ = v___x_4214_;
v_isShared_4218_ = v_isSharedCheck_4225_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4214_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4225_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4223_; 
v___x_4219_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_4220_ = l_Lean_Doc_joinBlocks(v_a_4215_);
lean_dec(v_a_4215_);
v___x_4221_ = l_Lean_Doc_prefixLines(v___x_4219_, v___x_4220_);
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 0, v___x_4221_);
v___x_4223_ = v___x_4217_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4221_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
v_a_4226_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4214_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4214_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
case 6:
{
lean_object* v_content_4234_; size_t v_sz_4235_; size_t v___x_4236_; lean_object* v___x_4237_; 
v_content_4234_ = lean_ctor_get(v_x_4109_, 0);
lean_inc_ref(v_content_4234_);
lean_dec_ref_known(v_x_4109_, 1);
v_sz_4235_ = lean_array_size(v_content_4234_);
v___x_4236_ = ((size_t)0ULL);
v___x_4237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4235_, v___x_4236_, v_content_4234_, v_a_4110_, v_a_4111_, v_a_4112_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4246_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4240_ = v___x_4237_;
v_isShared_4241_ = v_isSharedCheck_4246_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4246_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4242_; lean_object* v___x_4244_; 
v___x_4242_ = l_Lean_Doc_joinBlocks(v_a_4238_);
lean_dec(v_a_4238_);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v___x_4242_);
v___x_4244_ = v___x_4240_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v___x_4242_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
v_a_4247_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4237_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4237_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
default: 
{
lean_object* v_container_4255_; 
v_container_4255_ = lean_ctor_get(v_x_4109_, 0);
if (lean_obj_tag(v_container_4255_) == 0)
{
lean_object* v_content_4256_; lean_object* v_val_4257_; lean_object* v___f_4258_; lean_object* v___f_4259_; size_t v_sz_4260_; size_t v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v_fallback_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
lean_inc_ref(v_container_4255_);
v_content_4256_ = lean_ctor_get(v_x_4109_, 1);
lean_inc_ref_n(v_content_4256_, 2);
lean_dec_ref_known(v_x_4109_, 2);
v_val_4257_ = lean_ctor_get(v_container_4255_, 0);
lean_inc(v_val_4257_);
lean_dec_ref_known(v_container_4255_, 1);
v___f_4258_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed), 5, 0);
v___f_4259_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___closed__0));
v_sz_4260_ = lean_array_size(v_content_4256_);
v___x_4261_ = ((size_t)0ULL);
v___x_4262_ = lean_box_usize(v_sz_4260_);
v___x_4263_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
v_fallback_4264_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_fallback_4264_, 0, v___x_4262_);
lean_closure_set(v_fallback_4264_, 1, v___x_4263_);
lean_closure_set(v_fallback_4264_, 2, v_content_4256_);
v___x_4265_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_4257_);
v___x_4266_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_4265_, v_a_4111_, v_a_4112_);
lean_dec(v___x_4265_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref_known(v___x_4266_, 1);
if (lean_obj_tag(v_a_4267_) == 0)
{
lean_object* v___x_4268_; 
lean_dec_ref(v_fallback_4264_);
lean_dec_ref(v___f_4258_);
lean_dec(v_val_4257_);
v___x_4268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4260_, v___x_4261_, v_content_4256_, v_a_4110_, v_a_4111_, v_a_4112_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4277_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4271_ = v___x_4268_;
v_isShared_4272_ = v_isSharedCheck_4277_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4268_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4277_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4273_; lean_object* v___x_4275_; 
v___x_4273_ = l_Lean_Doc_joinBlocks(v_a_4269_);
lean_dec(v_a_4269_);
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 0, v___x_4273_);
v___x_4275_ = v___x_4271_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v___x_4273_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
v_a_4278_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4268_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4268_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
else
{
lean_object* v_val_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v_val_4286_ = lean_ctor_get(v_a_4267_, 0);
lean_inc(v_val_4286_);
lean_dec_ref_known(v_a_4267_, 1);
v___x_4287_ = lean_apply_4(v_val_4286_, v___f_4259_, v___f_4258_, v_val_4257_, v_content_4256_);
v___x_4288_ = l_Lean_Doc_withRendererFallback(v_fallback_4264_, v___x_4287_, v_a_4110_, v_a_4111_, v_a_4112_);
return v___x_4288_;
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec_ref(v_fallback_4264_);
lean_dec_ref(v___f_4258_);
lean_dec(v_val_4257_);
lean_dec_ref(v_content_4256_);
v_a_4289_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4266_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4266_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
else
{
lean_object* v_content_4297_; size_t v_sz_4298_; size_t v___x_4299_; lean_object* v___x_4300_; 
v_content_4297_ = lean_ctor_get(v_x_4109_, 1);
lean_inc_ref(v_content_4297_);
lean_dec_ref_known(v_x_4109_, 2);
v_sz_4298_ = lean_array_size(v_content_4297_);
v___x_4299_ = ((size_t)0ULL);
v___x_4300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4298_, v___x_4299_, v_content_4297_, v_a_4110_, v_a_4111_, v_a_4112_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4309_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4303_ = v___x_4300_;
v_isShared_4304_ = v_isSharedCheck_4309_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4300_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4309_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4305_; lean_object* v___x_4307_; 
v___x_4305_ = l_Lean_Doc_joinBlocks(v_a_4301_);
lean_dec(v_a_4301_);
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 0, v___x_4305_);
v___x_4307_ = v___x_4303_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4305_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
v_a_4310_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4300_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4300_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(size_t v_sz_4318_, size_t v_i_4319_, lean_object* v_bs_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
uint8_t v___x_4325_; 
v___x_4325_ = lean_usize_dec_lt(v_i_4319_, v_sz_4318_);
if (v___x_4325_ == 0)
{
lean_object* v___x_4326_; 
v___x_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4326_, 0, v_bs_4320_);
return v___x_4326_;
}
else
{
lean_object* v_v_4327_; lean_object* v___x_4328_; lean_object* v_bs_x27_4329_; lean_object* v___x_4330_; 
v_v_4327_ = lean_array_uget(v_bs_4320_, v_i_4319_);
v___x_4328_ = lean_unsigned_to_nat(0u);
v_bs_x27_4329_ = lean_array_uset(v_bs_4320_, v_i_4319_, v___x_4328_);
v___x_4330_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_v_4327_, v___y_4321_, v___y_4322_, v___y_4323_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; size_t v___x_4332_; size_t v___x_4333_; lean_object* v___x_4334_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref_known(v___x_4330_, 1);
v___x_4332_ = ((size_t)1ULL);
v___x_4333_ = lean_usize_add(v_i_4319_, v___x_4332_);
v___x_4334_ = lean_array_uset(v_bs_x27_4329_, v_i_4319_, v_a_4331_);
v_i_4319_ = v___x_4333_;
v_bs_4320_ = v___x_4334_;
goto _start;
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_dec_ref(v_bs_x27_4329_);
v_a_4336_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4330_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4330_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(size_t v_sz_4344_, size_t v___x_4345_, lean_object* v_content_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v___x_4351_; 
v___x_4351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4344_, v___x_4345_, v_content_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4360_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4354_ = v___x_4351_;
v_isShared_4355_ = v_isSharedCheck_4360_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4351_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4360_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4356_; lean_object* v___x_4358_; 
v___x_4356_ = l_Lean_Doc_joinBlocks(v_a_4352_);
lean_dec(v_a_4352_);
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 0, v___x_4356_);
v___x_4358_ = v___x_4354_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v___x_4356_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
else
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4368_; 
v_a_4361_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4363_ = v___x_4351_;
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4351_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4366_; 
if (v_isShared_4364_ == 0)
{
v___x_4366_ = v___x_4363_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_a_4361_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2___boxed(lean_object* v_sz_4369_, lean_object* v_i_4370_, lean_object* v_bs_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
size_t v_sz_boxed_4376_; size_t v_i_boxed_4377_; lean_object* v_res_4378_; 
v_sz_boxed_4376_ = lean_unbox_usize(v_sz_4369_);
lean_dec(v_sz_4369_);
v_i_boxed_4377_ = lean_unbox_usize(v_i_4370_);
lean_dec(v_i_4370_);
v_res_4378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_boxed_4376_, v_i_boxed_4377_, v_bs_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5___boxed(lean_object* v_sz_4379_, lean_object* v_i_4380_, lean_object* v_bs_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
size_t v_sz_boxed_4386_; size_t v_i_boxed_4387_; lean_object* v_res_4388_; 
v_sz_boxed_4386_ = lean_unbox_usize(v_sz_4379_);
lean_dec(v_sz_4379_);
v_i_boxed_4387_ = lean_unbox_usize(v_i_4380_);
lean_dec(v_i_4380_);
v_res_4388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_boxed_4386_, v_i_boxed_4387_, v_bs_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7___boxed(lean_object* v_as_4389_, lean_object* v_sz_4390_, lean_object* v_i_4391_, lean_object* v_b_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
size_t v_sz_boxed_4397_; size_t v_i_boxed_4398_; lean_object* v_res_4399_; 
v_sz_boxed_4397_ = lean_unbox_usize(v_sz_4390_);
lean_dec(v_sz_4390_);
v_i_boxed_4398_ = lean_unbox_usize(v_i_4391_);
lean_dec(v_i_4391_);
v_res_4399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_as_4389_, v_sz_boxed_4397_, v_i_boxed_4398_, v_b_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec(v___y_4393_);
lean_dec_ref(v_as_4389_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8___boxed(lean_object* v_sz_4400_, lean_object* v_i_4401_, lean_object* v_bs_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
size_t v_sz_boxed_4407_; size_t v_i_boxed_4408_; lean_object* v_res_4409_; 
v_sz_boxed_4407_ = lean_unbox_usize(v_sz_4400_);
lean_dec(v_sz_4400_);
v_i_boxed_4408_ = lean_unbox_usize(v_i_4401_);
lean_dec(v_i_4401_);
v_res_4409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_boxed_4407_, v_i_boxed_4408_, v_bs_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(size_t v_sz_4410_, size_t v_i_4411_, lean_object* v_bs_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
uint8_t v___x_4417_; 
v___x_4417_ = lean_usize_dec_lt(v_i_4411_, v_sz_4410_);
if (v___x_4417_ == 0)
{
lean_object* v___x_4418_; 
v___x_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4418_, 0, v_bs_4412_);
return v___x_4418_;
}
else
{
lean_object* v_v_4419_; lean_object* v___x_4420_; lean_object* v_bs_x27_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v_v_4419_ = lean_array_uget(v_bs_4412_, v_i_4411_);
v___x_4420_ = lean_unsigned_to_nat(0u);
v_bs_x27_4421_ = lean_array_uset(v_bs_4412_, v_i_4411_, v___x_4420_);
v___x_4422_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_4423_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4422_, v_v_4419_, v___y_4413_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; size_t v___x_4425_; size_t v___x_4426_; lean_object* v___x_4427_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_a_4424_);
lean_dec_ref_known(v___x_4423_, 1);
v___x_4425_ = ((size_t)1ULL);
v___x_4426_ = lean_usize_add(v_i_4411_, v___x_4425_);
v___x_4427_ = lean_array_uset(v_bs_x27_4421_, v_i_4411_, v_a_4424_);
v_i_4411_ = v___x_4426_;
v_bs_4412_ = v___x_4427_;
goto _start;
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec_ref(v_bs_x27_4421_);
v_a_4429_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4423_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4423_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1___boxed(lean_object* v_sz_4437_, lean_object* v_i_4438_, lean_object* v_bs_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
size_t v_sz_boxed_4444_; size_t v_i_boxed_4445_; lean_object* v_res_4446_; 
v_sz_boxed_4444_ = lean_unbox_usize(v_sz_4437_);
lean_dec(v_sz_4437_);
v_i_boxed_4445_ = lean_unbox_usize(v_i_4438_);
lean_dec(v_i_4438_);
v_res_4446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_boxed_4444_, v_i_boxed_4445_, v_bs_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec(v___y_4440_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(lean_object* v_x_4447_, lean_object* v_x_4448_){
_start:
{
lean_object* v_zero_4449_; uint8_t v_isZero_4450_; 
v_zero_4449_ = lean_unsigned_to_nat(0u);
v_isZero_4450_ = lean_nat_dec_eq(v_x_4447_, v_zero_4449_);
if (v_isZero_4450_ == 1)
{
lean_dec(v_x_4447_);
return v_x_4448_;
}
else
{
uint32_t v___x_4451_; lean_object* v_one_4452_; lean_object* v_n_4453_; lean_object* v___x_4454_; 
v___x_4451_ = 35;
v_one_4452_ = lean_unsigned_to_nat(1u);
v_n_4453_ = lean_nat_sub(v_x_4447_, v_one_4452_);
lean_dec(v_x_4447_);
v___x_4454_ = lean_string_push(v_x_4448_, v___x_4451_);
v_x_4447_ = v_n_4453_;
v_x_4448_ = v___x_4454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(lean_object* v_level_4456_, lean_object* v_part_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_){
_start:
{
lean_object* v_title_4462_; lean_object* v_content_4463_; lean_object* v_subParts_4464_; size_t v_sz_4465_; size_t v___x_4466_; lean_object* v___x_4467_; 
v_title_4462_ = lean_ctor_get(v_part_4457_, 0);
lean_inc_ref(v_title_4462_);
v_content_4463_ = lean_ctor_get(v_part_4457_, 3);
lean_inc_ref(v_content_4463_);
v_subParts_4464_ = lean_ctor_get(v_part_4457_, 4);
lean_inc_ref(v_subParts_4464_);
lean_dec_ref(v_part_4457_);
v_sz_4465_ = lean_array_size(v_title_4462_);
v___x_4466_ = ((size_t)0ULL);
v___x_4467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_4465_, v___x_4466_, v_title_4462_, v_a_4458_, v_a_4459_, v_a_4460_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; size_t v_sz_4480_; lean_object* v___x_4481_; 
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
lean_inc(v_a_4468_);
lean_dec_ref_known(v___x_4467_, 1);
v___x_4469_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4470_ = lean_unsigned_to_nat(1u);
v___x_4471_ = lean_nat_add(v_level_4456_, v___x_4470_);
lean_inc(v___x_4471_);
v___x_4472_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(v___x_4471_, v___x_4469_);
v___x_4473_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_4474_ = lean_string_append(v___x_4472_, v___x_4473_);
v___x_4475_ = lean_mk_empty_array_with_capacity(v___x_4470_);
lean_inc_ref_n(v___x_4475_, 2);
v___x_4476_ = lean_array_push(v___x_4475_, v___x_4474_);
v___x_4477_ = lean_array_push(v___x_4475_, v___x_4476_);
v___x_4478_ = l_Array_append___redArg(v___x_4477_, v_a_4468_);
lean_dec(v_a_4468_);
v___x_4479_ = l_Lean_Doc_joinInlines(v___x_4478_);
lean_dec_ref(v___x_4478_);
v_sz_4480_ = lean_array_size(v_content_4463_);
v___x_4481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4480_, v___x_4466_, v_content_4463_, v_a_4458_, v_a_4459_, v_a_4460_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; size_t v_sz_4483_; lean_object* v___x_4484_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref_known(v___x_4481_, 1);
v_sz_4483_ = lean_array_size(v_subParts_4464_);
v___x_4484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4471_, v_sz_4483_, v___x_4466_, v_subParts_4464_, v_a_4458_, v_a_4459_, v_a_4460_);
lean_dec(v___x_4471_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4496_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4487_ = v___x_4484_;
v_isShared_4488_ = v_isSharedCheck_4496_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4484_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4496_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4494_; 
v___x_4489_ = lean_array_push(v___x_4475_, v___x_4479_);
v___x_4490_ = l_Array_append___redArg(v___x_4489_, v_a_4482_);
lean_dec(v_a_4482_);
v___x_4491_ = l_Array_append___redArg(v___x_4490_, v_a_4485_);
lean_dec(v_a_4485_);
v___x_4492_ = l_Lean_Doc_joinBlocks(v___x_4491_);
lean_dec_ref(v___x_4491_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 0, v___x_4492_);
v___x_4494_ = v___x_4487_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4492_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
else
{
lean_object* v_a_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4504_; 
lean_dec(v_a_4482_);
lean_dec_ref(v___x_4479_);
lean_dec_ref(v___x_4475_);
v_a_4497_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4499_ = v___x_4484_;
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_a_4497_);
lean_dec(v___x_4484_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4500_ == 0)
{
v___x_4502_ = v___x_4499_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4497_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
else
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
lean_dec_ref(v___x_4479_);
lean_dec_ref(v___x_4475_);
lean_dec(v___x_4471_);
lean_dec_ref(v_subParts_4464_);
v_a_4505_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4507_ = v___x_4481_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v___x_4481_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4505_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
lean_dec_ref(v_subParts_4464_);
lean_dec_ref(v_content_4463_);
v_a_4513_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4467_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4467_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(lean_object* v___x_4521_, size_t v_sz_4522_, size_t v_i_4523_, lean_object* v_bs_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
uint8_t v___x_4529_; 
v___x_4529_ = lean_usize_dec_lt(v_i_4523_, v_sz_4522_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; 
v___x_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4530_, 0, v_bs_4524_);
return v___x_4530_;
}
else
{
lean_object* v_v_4531_; lean_object* v___x_4532_; lean_object* v_bs_x27_4533_; lean_object* v___x_4534_; 
v_v_4531_ = lean_array_uget(v_bs_4524_, v_i_4523_);
v___x_4532_ = lean_unsigned_to_nat(0u);
v_bs_x27_4533_ = lean_array_uset(v_bs_4524_, v_i_4523_, v___x_4532_);
v___x_4534_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4521_, v_v_4531_, v___y_4525_, v___y_4526_, v___y_4527_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v_a_4535_; size_t v___x_4536_; size_t v___x_4537_; lean_object* v___x_4538_; 
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc(v_a_4535_);
lean_dec_ref_known(v___x_4534_, 1);
v___x_4536_ = ((size_t)1ULL);
v___x_4537_ = lean_usize_add(v_i_4523_, v___x_4536_);
v___x_4538_ = lean_array_uset(v_bs_x27_4533_, v_i_4523_, v_a_4535_);
v_i_4523_ = v___x_4537_;
v_bs_4524_ = v___x_4538_;
goto _start;
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
lean_dec_ref(v_bs_x27_4533_);
v_a_4540_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4534_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4534_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg___boxed(lean_object* v___x_4548_, lean_object* v_sz_4549_, lean_object* v_i_4550_, lean_object* v_bs_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
size_t v_sz_boxed_4556_; size_t v_i_boxed_4557_; lean_object* v_res_4558_; 
v_sz_boxed_4556_ = lean_unbox_usize(v_sz_4549_);
lean_dec(v_sz_4549_);
v_i_boxed_4557_ = lean_unbox_usize(v_i_4550_);
lean_dec(v_i_4550_);
v_res_4558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4548_, v_sz_boxed_4556_, v_i_boxed_4557_, v_bs_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec(v___x_4548_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg___boxed(lean_object* v_level_4559_, lean_object* v_part_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_){
_start:
{
lean_object* v_res_4565_; 
v_res_4565_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4559_, v_part_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec(v_level_4559_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(size_t v_sz_4566_, size_t v_i_4567_, lean_object* v_bs_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
uint8_t v___x_4573_; 
v___x_4573_ = lean_usize_dec_lt(v_i_4567_, v_sz_4566_);
if (v___x_4573_ == 0)
{
lean_object* v___x_4574_; 
v___x_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4574_, 0, v_bs_4568_);
return v___x_4574_;
}
else
{
lean_object* v_v_4575_; lean_object* v___x_4576_; lean_object* v_bs_x27_4577_; lean_object* v___x_4578_; 
v_v_4575_ = lean_array_uget(v_bs_4568_, v_i_4567_);
v___x_4576_ = lean_unsigned_to_nat(0u);
v_bs_x27_4577_ = lean_array_uset(v_bs_4568_, v_i_4567_, v___x_4576_);
v___x_4578_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4576_, v_v_4575_, v___y_4569_, v___y_4570_, v___y_4571_);
if (lean_obj_tag(v___x_4578_) == 0)
{
lean_object* v_a_4579_; size_t v___x_4580_; size_t v___x_4581_; lean_object* v___x_4582_; 
v_a_4579_ = lean_ctor_get(v___x_4578_, 0);
lean_inc(v_a_4579_);
lean_dec_ref_known(v___x_4578_, 1);
v___x_4580_ = ((size_t)1ULL);
v___x_4581_ = lean_usize_add(v_i_4567_, v___x_4580_);
v___x_4582_ = lean_array_uset(v_bs_x27_4577_, v_i_4567_, v_a_4579_);
v_i_4567_ = v___x_4581_;
v_bs_4568_ = v___x_4582_;
goto _start;
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_dec_ref(v_bs_x27_4577_);
v_a_4584_ = lean_ctor_get(v___x_4578_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4578_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4578_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4578_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3___boxed(lean_object* v_sz_4592_, lean_object* v_i_4593_, lean_object* v_bs_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
size_t v_sz_boxed_4599_; size_t v_i_boxed_4600_; lean_object* v_res_4601_; 
v_sz_boxed_4599_ = lean_unbox_usize(v_sz_4592_);
lean_dec(v_sz_4592_);
v_i_boxed_4600_ = lean_unbox_usize(v_i_4593_);
lean_dec(v_i_4593_);
v_res_4601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_boxed_4599_, v_i_boxed_4600_, v_bs_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec(v___y_4595_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0(lean_object* v_val_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_){
_start:
{
lean_object* v_text_4607_; lean_object* v_subsections_4608_; size_t v_sz_4609_; size_t v___x_4610_; lean_object* v___x_4611_; 
v_text_4607_ = lean_ctor_get(v_val_4602_, 0);
lean_inc_ref(v_text_4607_);
v_subsections_4608_ = lean_ctor_get(v_val_4602_, 1);
lean_inc_ref(v_subsections_4608_);
lean_dec_ref(v_val_4602_);
v_sz_4609_ = lean_array_size(v_text_4607_);
v___x_4610_ = ((size_t)0ULL);
v___x_4611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4609_, v___x_4610_, v_text_4607_, v___y_4603_, v___y_4604_, v___y_4605_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; size_t v_sz_4613_; lean_object* v___x_4614_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
lean_inc(v_a_4612_);
lean_dec_ref_known(v___x_4611_, 1);
v_sz_4613_ = lean_array_size(v_subsections_4608_);
v___x_4614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_4613_, v___x_4610_, v_subsections_4608_, v___y_4603_, v___y_4604_, v___y_4605_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4624_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4617_ = v___x_4614_;
v_isShared_4618_ = v_isSharedCheck_4624_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4614_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4624_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4622_; 
v___x_4619_ = l_Array_append___redArg(v_a_4612_, v_a_4615_);
lean_dec(v_a_4615_);
v___x_4620_ = l_Lean_Doc_joinBlocks(v___x_4619_);
lean_dec_ref(v___x_4619_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4620_);
v___x_4622_ = v___x_4617_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4620_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_dec(v_a_4612_);
v_a_4625_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4614_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4614_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4640_; 
lean_dec_ref(v_subsections_4608_);
v_a_4633_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4635_ = v___x_4611_;
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v___x_4611_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4638_; 
if (v_isShared_4636_ == 0)
{
v___x_4638_ = v___x_4635_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0___boxed(lean_object* v_val_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l_Lean_findSimpleDocString_x3f___lam__0(v_val_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
lean_dec(v___y_4644_);
lean_dec_ref(v___y_4643_);
lean_dec(v___y_4642_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_4647_, lean_object* v_declName_4648_, uint8_t v_includeBuiltin_4649_, lean_object* v_options_4650_, lean_object* v_currNamespace_4651_, lean_object* v_openDecls_4652_, lean_object* v_cancelTk_x3f_4653_){
_start:
{
lean_object* v___x_4655_; 
lean_inc_ref(v_env_4647_);
v___x_4655_ = l_Lean_findInternalDocString_x3f(v_env_4647_, v_declName_4648_, v_includeBuiltin_4649_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4699_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4658_ = v___x_4655_;
v_isShared_4659_ = v_isSharedCheck_4699_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4655_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4699_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
if (lean_obj_tag(v_a_4656_) == 0)
{
lean_object* v___x_4660_; lean_object* v___x_4662_; 
lean_dec(v_cancelTk_x3f_4653_);
lean_dec(v_openDecls_4652_);
lean_dec(v_currNamespace_4651_);
lean_dec_ref(v_options_4650_);
lean_dec_ref(v_env_4647_);
v___x_4660_ = lean_box(0);
if (v_isShared_4659_ == 0)
{
lean_ctor_set(v___x_4658_, 0, v___x_4660_);
v___x_4662_ = v___x_4658_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4660_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
else
{
lean_object* v_val_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4698_; 
v_val_4664_ = lean_ctor_get(v_a_4656_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v_a_4656_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4666_ = v_a_4656_;
v_isShared_4667_ = v_isSharedCheck_4698_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_val_4664_);
lean_dec(v_a_4656_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4698_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
if (lean_obj_tag(v_val_4664_) == 0)
{
lean_object* v_val_4668_; lean_object* v___x_4670_; 
lean_dec(v_cancelTk_x3f_4653_);
lean_dec(v_openDecls_4652_);
lean_dec(v_currNamespace_4651_);
lean_dec_ref(v_options_4650_);
lean_dec_ref(v_env_4647_);
v_val_4668_ = lean_ctor_get(v_val_4664_, 0);
lean_inc(v_val_4668_);
lean_dec_ref_known(v_val_4664_, 1);
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 0, v_val_4668_);
v___x_4670_ = v___x_4666_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_val_4668_);
v___x_4670_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
lean_object* v___x_4672_; 
if (v_isShared_4659_ == 0)
{
lean_ctor_set(v___x_4658_, 0, v___x_4670_);
v___x_4672_ = v___x_4658_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v___x_4670_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
}
else
{
lean_object* v_val_4675_; lean_object* v___f_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
lean_del_object(v___x_4658_);
v_val_4675_ = lean_ctor_get(v_val_4664_, 0);
lean_inc(v_val_4675_);
lean_dec_ref_known(v_val_4664_, 1);
v___f_4676_ = lean_alloc_closure((void*)(l_Lean_findSimpleDocString_x3f___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4676_, 0, v_val_4675_);
v___x_4677_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_4677_, 0, v___f_4676_);
v___x_4678_ = l_Lean_Doc_runMarkdown___redArg(v_env_4647_, v___x_4677_, v_options_4650_, v_currNamespace_4651_, v_openDecls_4652_, v_cancelTk_x3f_4653_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4689_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4681_ = v___x_4678_;
v_isShared_4682_ = v_isSharedCheck_4689_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4678_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4689_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 0, v_a_4679_);
v___x_4684_ = v___x_4666_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4679_);
v___x_4684_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
lean_object* v___x_4686_; 
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 0, v___x_4684_);
v___x_4686_ = v___x_4681_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4684_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
}
else
{
lean_object* v_a_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4697_; 
lean_del_object(v___x_4666_);
v_a_4690_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4692_ = v___x_4678_;
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_a_4690_);
lean_dec(v___x_4678_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4695_; 
if (v_isShared_4693_ == 0)
{
v___x_4695_ = v___x_4692_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
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
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4707_; 
lean_dec(v_cancelTk_x3f_4653_);
lean_dec(v_openDecls_4652_);
lean_dec(v_currNamespace_4651_);
lean_dec_ref(v_options_4650_);
lean_dec_ref(v_env_4647_);
v_a_4700_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4702_ = v___x_4655_;
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4655_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4703_ == 0)
{
v___x_4705_ = v___x_4702_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_a_4700_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_4708_, lean_object* v_declName_4709_, lean_object* v_includeBuiltin_4710_, lean_object* v_options_4711_, lean_object* v_currNamespace_4712_, lean_object* v_openDecls_4713_, lean_object* v_cancelTk_x3f_4714_, lean_object* v_a_4715_){
_start:
{
uint8_t v_includeBuiltin_boxed_4716_; lean_object* v_res_4717_; 
v_includeBuiltin_boxed_4716_ = lean_unbox(v_includeBuiltin_4710_);
v_res_4717_ = l_Lean_findSimpleDocString_x3f(v_env_4708_, v_declName_4709_, v_includeBuiltin_boxed_4716_, v_options_4711_, v_currNamespace_4712_, v_openDecls_4713_, v_cancelTk_x3f_4714_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(lean_object* v_p_4718_, lean_object* v_level_4719_, lean_object* v_part_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_){
_start:
{
lean_object* v___x_4725_; 
v___x_4725_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4719_, v_part_4720_, v_a_4721_, v_a_4722_, v_a_4723_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___boxed(lean_object* v_p_4726_, lean_object* v_level_4727_, lean_object* v_part_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(v_p_4726_, v_level_4727_, v_part_4728_, v_a_4729_, v_a_4730_, v_a_4731_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
lean_dec(v_a_4729_);
lean_dec(v_level_4727_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(lean_object* v_p_4734_, lean_object* v___x_4735_, size_t v_sz_4736_, size_t v_i_4737_, lean_object* v_bs_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4735_, v_sz_4736_, v_i_4737_, v_bs_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___boxed(lean_object* v_p_4744_, lean_object* v___x_4745_, lean_object* v_sz_4746_, lean_object* v_i_4747_, lean_object* v_bs_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_){
_start:
{
size_t v_sz_boxed_4753_; size_t v_i_boxed_4754_; lean_object* v_res_4755_; 
v_sz_boxed_4753_ = lean_unbox_usize(v_sz_4746_);
lean_dec(v_sz_4746_);
v_i_boxed_4754_ = lean_unbox_usize(v_i_4747_);
lean_dec(v_i_4747_);
v_res_4755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(v_p_4744_, v___x_4745_, v_sz_boxed_4753_, v_i_boxed_4754_, v_bs_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
lean_dec(v___y_4751_);
lean_dec_ref(v___y_4750_);
lean_dec(v___y_4749_);
lean_dec(v___x_4745_);
return v_res_4755_;
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
