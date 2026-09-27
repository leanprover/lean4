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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
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
extern lean_object* l_Lean_Options_empty;
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
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(11) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2;
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
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1_value;
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
static lean_once_cell_t l_Lean_Doc_runMarkdown___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_runMarkdown___redArg___closed__14;
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(lean_object* v_l_273_, lean_object* v_r_274_){
_start:
{
uint8_t v___y_276_; uint8_t v___y_277_; lean_object* v___x_283_; uint8_t v___y_285_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_283_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1));
v___x_291_ = lean_string_utf8_byte_size(v_l_273_);
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_dec_le(v___x_292_, v___x_291_);
if (v___x_293_ == 0)
{
v___y_285_ = v___x_293_;
goto v___jp_284_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_nat_sub(v___x_291_, v___x_292_);
v___x_296_ = lean_string_memcmp(v_l_273_, v___x_283_, v___x_295_, v___x_294_, v___x_292_);
lean_dec(v___x_295_);
v___y_285_ = v___x_296_;
goto v___jp_284_;
}
v___jp_275_:
{
if (v___y_276_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = lean_string_append(v_l_273_, v_r_274_);
return v___x_278_;
}
else
{
if (v___y_277_ == 0)
{
lean_object* v___x_279_; 
v___x_279_ = lean_string_append(v_l_273_, v_r_274_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_281_ = lean_string_append(v_l_273_, v___x_280_);
v___x_282_ = lean_string_append(v___x_281_, v_r_274_);
return v___x_282_;
}
}
}
v___jp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_string_utf8_byte_size(v_r_274_);
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_dec_le(v___x_287_, v___x_286_);
if (v___x_288_ == 0)
{
v___y_276_ = v___y_285_;
v___y_277_ = v___x_288_;
goto v___jp_275_;
}
else
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_string_memcmp(v_r_274_, v___x_283_, v___x_289_, v___x_289_, v___x_287_);
v___y_276_ = v___y_285_;
v___y_277_ = v___x_290_;
goto v___jp_275_;
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
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0(lean_object* v_a_363_, lean_object* v_a_364_, uint8_t v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0___boxed(lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
uint8_t v_a_41__boxed_379_; lean_object* v_res_380_; 
v_a_41__boxed_379_ = lean_unbox(v_a_373_);
v_res_380_ = l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0(v_a_371_, v_a_372_, v_a_41__boxed_379_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec_ref(v_a_372_);
lean_dec_ref(v_a_371_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg(){
_start:
{
lean_object* v___f_383_; 
v___f_383_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0));
return v___f_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___boxed(lean_object* v___dummy_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Doc_instMarkdownBlockEmpty___redArg();
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object* v_i_386_){
_start:
{
lean_object* v___f_387_; 
v___f_387_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0));
return v___f_387_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(lean_object* v_x_388_, lean_object* v_x_389_){
_start:
{
if (lean_obj_tag(v_x_388_) == 0)
{
if (lean_obj_tag(v_x_389_) == 0)
{
uint8_t v___x_390_; 
v___x_390_ = 1;
return v___x_390_;
}
else
{
uint8_t v___x_391_; 
v___x_391_ = 0;
return v___x_391_;
}
}
else
{
if (lean_obj_tag(v_x_389_) == 0)
{
uint8_t v___x_392_; 
v___x_392_ = 0;
return v___x_392_;
}
else
{
lean_object* v_val_393_; lean_object* v_val_394_; uint32_t v___x_395_; uint32_t v___x_396_; uint8_t v___x_397_; 
v_val_393_ = lean_ctor_get(v_x_388_, 0);
v_val_394_ = lean_ctor_get(v_x_389_, 0);
v___x_395_ = lean_unbox_uint32(v_val_393_);
v___x_396_ = lean_unbox_uint32(v_val_394_);
v___x_397_ = lean_uint32_dec_eq(v___x_395_, v___x_396_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1___boxed(lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_x_398_, v_x_399_);
lean_dec(v_x_399_);
lean_dec(v_x_398_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(lean_object* v_s_402_, uint32_t v_c_403_, lean_object* v_a_404_, uint8_t v_b_405_){
_start:
{
lean_object* v_str_406_; lean_object* v_startInclusive_407_; lean_object* v_endExclusive_408_; lean_object* v___x_409_; uint8_t v_decide_410_; 
v_str_406_ = lean_ctor_get(v_s_402_, 0);
v_startInclusive_407_ = lean_ctor_get(v_s_402_, 1);
v_endExclusive_408_ = lean_ctor_get(v_s_402_, 2);
v___x_409_ = lean_nat_sub(v_endExclusive_408_, v_startInclusive_407_);
v_decide_410_ = lean_nat_dec_eq(v_a_404_, v___x_409_);
lean_dec(v___x_409_);
if (v_decide_410_ == 0)
{
lean_object* v___x_411_; uint32_t v___x_412_; uint8_t v___x_413_; 
v___x_411_ = lean_nat_add(v_startInclusive_407_, v_a_404_);
lean_dec(v_a_404_);
v___x_412_ = lean_string_utf8_get_fast(v_str_406_, v___x_411_);
v___x_413_ = lean_uint32_dec_eq(v___x_412_, v_c_403_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_string_utf8_next_fast(v_str_406_, v___x_411_);
lean_dec(v___x_411_);
v___x_415_ = lean_nat_sub(v___x_414_, v_startInclusive_407_);
v_a_404_ = v___x_415_;
v_b_405_ = v___x_413_;
goto _start;
}
else
{
lean_dec(v___x_411_);
return v___x_413_;
}
}
else
{
lean_dec(v_a_404_);
return v_b_405_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg___boxed(lean_object* v_s_417_, lean_object* v_c_418_, lean_object* v_a_419_, lean_object* v_b_420_){
_start:
{
uint32_t v_c_boxed_421_; uint8_t v_b_boxed_422_; uint8_t v_res_423_; lean_object* v_r_424_; 
v_c_boxed_421_ = lean_unbox_uint32(v_c_418_);
lean_dec(v_c_418_);
v_b_boxed_422_ = lean_unbox(v_b_420_);
v_res_423_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_417_, v_c_boxed_421_, v_a_419_, v_b_boxed_422_);
lean_dec_ref(v_s_417_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(uint32_t v_c_425_, lean_object* v_s_426_){
_start:
{
lean_object* v_searcher_427_; uint8_t v___x_428_; uint8_t v___x_429_; 
v_searcher_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = 0;
v___x_429_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_426_, v_c_425_, v_searcher_427_, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0___boxed(lean_object* v_c_430_, lean_object* v_s_431_){
_start:
{
uint32_t v_c_boxed_432_; uint8_t v_res_433_; lean_object* v_r_434_; 
v_c_boxed_432_ = lean_unbox_uint32(v_c_430_);
lean_dec(v_c_430_);
v_res_433_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_boxed_432_, v_s_431_);
lean_dec_ref(v_s_431_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_440_; lean_object* v___x_441_; 
v___x_440_ = 91;
v___x_441_ = lean_box_uint32(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2___boxed__const__1;
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
v___x_448_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1));
v___x_449_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_444_, v___x_448_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(uint32_t v___x_515_, lean_object* v___x_516_, lean_object* v_____r_517_, lean_object* v_s_x27_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint32_t v___x_532_; uint8_t v___x_533_; 
v___x_519_ = lean_string_push(v_s_x27_518_, v___x_515_);
v___x_520_ = lean_box_uint32(v___x_515_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
v___x_532_ = 48;
v___x_533_ = lean_uint32_dec_le(v___x_532_, v___x_515_);
if (v___x_533_ == 0)
{
goto v___jp_526_;
}
else
{
uint32_t v___x_534_; uint8_t v___x_535_; 
v___x_534_ = 57;
v___x_535_ = lean_uint32_dec_le(v___x_515_, v___x_534_);
if (v___x_535_ == 0)
{
goto v___jp_526_;
}
else
{
goto v___jp_522_;
}
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
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1));
v___x_528_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v___x_515_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_516_);
lean_ctor_set(v___x_529_, 1, v___x_521_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_519_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
else
{
goto v___jp_522_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed(lean_object* v___x_536_, lean_object* v___x_537_, lean_object* v_____r_538_, lean_object* v_s_x27_539_){
_start:
{
uint32_t v___x_2069__boxed_540_; lean_object* v_res_541_; 
v___x_2069__boxed_540_ = lean_unbox_uint32(v___x_536_);
lean_dec(v___x_536_);
v_res_541_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_2069__boxed_540_, v___x_537_, v_____r_538_, v_s_x27_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(lean_object* v_s_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___y_545_; lean_object* v_snd_549_; lean_object* v_fst_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_588_; 
v_snd_549_ = lean_ctor_get(v_a_543_, 1);
v_fst_550_ = lean_ctor_get(v_a_543_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_588_ == 0)
{
v___x_552_ = v_a_543_;
v_isShared_553_ = v_isSharedCheck_588_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snd_549_);
lean_inc(v_fst_550_);
lean_dec(v_a_543_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_588_;
goto v_resetjp_551_;
}
v___jp_544_:
{
if (lean_obj_tag(v___y_545_) == 0)
{
lean_object* v_a_546_; 
v_a_546_ = lean_ctor_get(v___y_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___y_545_, 1);
return v_a_546_;
}
else
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v___y_545_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___y_545_, 1);
v_a_543_ = v_a_547_;
goto _start;
}
}
v_resetjp_551_:
{
lean_object* v_fst_554_; lean_object* v_snd_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_587_; 
v_fst_554_ = lean_ctor_get(v_snd_549_, 0);
v_snd_555_ = lean_ctor_get(v_snd_549_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_snd_549_);
if (v_isSharedCheck_587_ == 0)
{
v___x_557_ = v_snd_549_;
v_isShared_558_ = v_isSharedCheck_587_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_snd_555_);
lean_inc(v_fst_554_);
lean_dec(v_snd_549_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_587_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; uint8_t v_decide_560_; 
v___x_559_ = lean_string_utf8_byte_size(v_s_542_);
v_decide_560_ = lean_nat_dec_eq(v_fst_554_, v___x_559_);
if (v_decide_560_ == 0)
{
uint32_t v___x_561_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___f_574_; uint8_t v_decide_579_; 
lean_del_object(v___x_557_);
lean_del_object(v___x_552_);
v___x_561_ = lean_string_utf8_get_fast(v_s_542_, v_fst_554_);
v___x_572_ = lean_string_utf8_next_fast(v_s_542_, v_fst_554_);
lean_dec(v_fst_554_);
v___x_573_ = lean_box_uint32(v___x_561_);
v___f_574_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_574_, 0, v___x_573_);
lean_closure_set(v___f_574_, 1, v___x_572_);
v_decide_579_ = lean_nat_dec_eq(v___x_572_, v___x_559_);
if (v_decide_579_ == 0)
{
goto v___jp_575_;
}
else
{
if (v_decide_560_ == 0)
{
lean_object* v_prev_x3f_580_; 
v_prev_x3f_580_ = lean_box(0);
v___y_563_ = v___f_574_;
v___y_564_ = v_prev_x3f_580_;
goto v___jp_562_;
}
else
{
goto v___jp_575_;
}
}
v___jp_562_:
{
uint8_t v___x_565_; 
v___x_565_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_snd_555_, v___x_561_, v___y_564_);
lean_dec(v___y_564_);
lean_dec(v_snd_555_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_box(0);
v___x_567_ = lean_apply_2(v___y_563_, v___x_566_, v_fst_550_);
v___y_545_ = v___x_567_;
goto v___jp_544_;
}
else
{
uint32_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_568_ = 92;
v___x_569_ = lean_string_push(v_fst_550_, v___x_568_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_apply_2(v___y_563_, v___x_570_, v___x_569_);
v___y_545_ = v___x_571_;
goto v___jp_544_;
}
}
v___jp_575_:
{
uint32_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = lean_string_utf8_get_fast(v_s_542_, v___x_572_);
v___x_577_ = lean_box_uint32(v___x_576_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
v___y_563_ = v___f_574_;
v___y_564_ = v___x_578_;
goto v___jp_562_;
}
}
else
{
lean_object* v___x_582_; 
if (v_isShared_558_ == 0)
{
v___x_582_ = v___x_557_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_fst_554_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_snd_555_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_582_);
v___x_584_ = v___x_552_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_fst_550_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___boxed(lean_object* v_s_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_589_, v_a_590_);
lean_dec_ref(v_s_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(uint32_t v___x_592_, lean_object* v___x_593_, lean_object* v_____r_594_, lean_object* v_s_x27_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_string_push(v_s_x27_595_, v___x_592_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_593_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0___boxed(lean_object* v___x_599_, lean_object* v___x_600_, lean_object* v_____r_601_, lean_object* v_s_x27_602_){
_start:
{
uint32_t v___x_2197__boxed_603_; lean_object* v_res_604_; 
v___x_2197__boxed_603_ = lean_unbox_uint32(v___x_599_);
lean_dec(v___x_599_);
v_res_604_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_2197__boxed_603_, v___x_600_, v_____r_601_, v_s_x27_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(lean_object* v_s_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___y_608_; lean_object* v_fst_612_; lean_object* v_snd_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_638_; 
v_fst_612_ = lean_ctor_get(v_a_606_, 0);
v_snd_613_ = lean_ctor_get(v_a_606_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_a_606_);
if (v_isSharedCheck_638_ == 0)
{
v___x_615_ = v_a_606_;
v_isShared_616_ = v_isSharedCheck_638_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_snd_613_);
lean_inc(v_fst_612_);
lean_dec(v_a_606_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_638_;
goto v_resetjp_614_;
}
v___jp_607_:
{
if (lean_obj_tag(v___y_608_) == 0)
{
lean_object* v_a_609_; 
v_a_609_ = lean_ctor_get(v___y_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___y_608_, 1);
return v_a_609_;
}
else
{
lean_object* v_a_610_; 
v_a_610_ = lean_ctor_get(v___y_608_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___y_608_, 1);
v_a_606_ = v_a_610_;
goto _start;
}
}
v_resetjp_614_:
{
lean_object* v___x_617_; uint8_t v_decide_618_; 
v___x_617_ = lean_string_utf8_byte_size(v_s_605_);
v_decide_618_ = lean_nat_dec_eq(v_snd_613_, v___x_617_);
if (v_decide_618_ == 0)
{
uint32_t v___x_619_; lean_object* v___x_620_; lean_object* v___y_622_; uint8_t v_decide_630_; 
lean_del_object(v___x_615_);
v___x_619_ = lean_string_utf8_get_fast(v_s_605_, v_snd_613_);
v___x_620_ = lean_string_utf8_next_fast(v_s_605_, v_snd_613_);
lean_dec(v_snd_613_);
v_decide_630_ = lean_nat_dec_eq(v___x_620_, v___x_617_);
if (v_decide_630_ == 0)
{
uint32_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_string_utf8_get_fast(v_s_605_, v___x_620_);
v___x_632_ = lean_box_uint32(v___x_631_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___y_622_ = v___x_633_;
goto v___jp_621_;
}
else
{
lean_object* v_prev_x3f_634_; 
v_prev_x3f_634_ = lean_box(0);
v___y_622_ = v_prev_x3f_634_;
goto v___jp_621_;
}
v___jp_621_:
{
uint8_t v___x_623_; 
v___x_623_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v___x_619_, v___y_622_);
lean_dec(v___y_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_box(0);
v___x_625_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_619_, v___x_620_, v___x_624_, v_fst_612_);
v___y_608_ = v___x_625_;
goto v___jp_607_;
}
else
{
uint32_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_626_ = 92;
v___x_627_ = lean_string_push(v_fst_612_, v___x_626_);
v___x_628_ = lean_box(0);
v___x_629_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_619_, v___x_620_, v___x_628_, v___x_627_);
v___y_608_ = v___x_629_;
goto v___jp_607_;
}
}
}
else
{
lean_object* v___x_636_; 
if (v_isShared_616_ == 0)
{
v___x_636_ = v___x_615_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_fst_612_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_snd_613_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___boxed(lean_object* v_s_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_639_, v_a_640_);
lean_dec_ref(v_s_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object* v_s_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v_snd_651_; lean_object* v_fst_652_; lean_object* v_fst_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_662_; 
v___x_649_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1));
v___x_650_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_648_, v___x_649_);
v_snd_651_ = lean_ctor_get(v___x_650_, 1);
lean_inc(v_snd_651_);
v_fst_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_fst_652_);
lean_dec_ref(v___x_650_);
v_fst_653_ = lean_ctor_get(v_snd_651_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v_snd_651_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v_snd_651_, 1);
lean_dec(v_unused_663_);
v___x_655_ = v_snd_651_;
v_isShared_656_ = v_isSharedCheck_662_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_fst_653_);
lean_dec(v_snd_651_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_662_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v_fst_653_);
lean_ctor_set(v___x_655_, 0, v_fst_652_);
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_fst_652_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_fst_653_);
v___x_658_ = v_reuseFailAlloc_661_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; lean_object* v_fst_660_; 
v___x_659_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_648_, v___x_658_);
v_fst_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_fst_660_);
lean_dec_ref(v___x_659_);
return v_fst_660_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object* v_s_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_664_);
lean_dec_ref(v_s_664_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object* v_s_666_, lean_object* v_inst_667_, lean_object* v_a_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_666_, v_a_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object* v_s_670_, lean_object* v_inst_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_670_, v_inst_671_, v_a_672_);
lean_dec_ref(v_s_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(lean_object* v_s_674_, lean_object* v_inst_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_674_, v_a_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___boxed(lean_object* v_s_678_, lean_object* v_inst_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(v_s_678_, v_inst_679_, v_a_680_);
lean_dec_ref(v_s_678_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v_str_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_snd_684_; lean_object* v_fst_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_727_; 
v_snd_684_ = lean_ctor_get(v_a_683_, 1);
v_fst_685_ = lean_ctor_get(v_a_683_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v_a_683_);
if (v_isSharedCheck_727_ == 0)
{
v___x_687_ = v_a_683_;
v_isShared_688_ = v_isSharedCheck_727_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_snd_684_);
lean_inc(v_fst_685_);
lean_dec(v_a_683_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_727_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_fst_689_; lean_object* v_snd_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_726_; 
v_fst_689_ = lean_ctor_get(v_snd_684_, 0);
v_snd_690_ = lean_ctor_get(v_snd_684_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_snd_684_);
if (v_isSharedCheck_726_ == 0)
{
v___x_692_ = v_snd_684_;
v_isShared_693_ = v_isSharedCheck_726_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_snd_690_);
lean_inc(v_fst_689_);
lean_dec(v_snd_684_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_726_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; uint8_t v_decide_695_; 
v___x_694_ = lean_string_utf8_byte_size(v_str_682_);
v_decide_695_ = lean_nat_dec_eq(v_snd_690_, v___x_694_);
if (v_decide_695_ == 0)
{
uint32_t v___x_696_; lean_object* v___x_697_; uint32_t v___x_698_; uint8_t v___x_699_; 
v___x_696_ = lean_string_utf8_get_fast(v_str_682_, v_snd_690_);
v___x_697_ = lean_string_utf8_next_fast(v_str_682_, v_snd_690_);
lean_dec(v_snd_690_);
v___x_698_ = 96;
v___x_699_ = lean_uint32_dec_eq(v___x_696_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v_longest_700_; lean_object* v___y_702_; uint8_t v___x_710_; 
v_longest_700_ = lean_unsigned_to_nat(0u);
v___x_710_ = lean_nat_dec_le(v_fst_685_, v_fst_689_);
if (v___x_710_ == 0)
{
lean_dec(v_fst_689_);
v___y_702_ = v_fst_685_;
goto v___jp_701_;
}
else
{
lean_dec(v_fst_685_);
v___y_702_ = v_fst_689_;
goto v___jp_701_;
}
v___jp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_697_);
lean_ctor_set(v___x_692_, 0, v_longest_700_);
v___x_704_ = v___x_692_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_longest_700_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_697_);
v___x_704_ = v_reuseFailAlloc_709_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_706_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_704_);
lean_ctor_set(v___x_687_, 0, v___y_702_);
v___x_706_ = v___x_687_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___y_702_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_708_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
v_a_683_ = v___x_706_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = lean_nat_add(v_fst_689_, v___x_711_);
lean_dec(v_fst_689_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_697_);
lean_ctor_set(v___x_692_, 0, v___x_712_);
v___x_714_ = v___x_692_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_697_);
v___x_714_ = v_reuseFailAlloc_719_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_714_);
v___x_716_ = v___x_687_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_fst_685_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_714_);
v___x_716_ = v_reuseFailAlloc_718_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
v_a_683_ = v___x_716_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_721_; 
if (v_isShared_693_ == 0)
{
v___x_721_ = v___x_692_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_fst_689_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_snd_690_);
v___x_721_ = v_reuseFailAlloc_725_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_721_);
v___x_723_ = v___x_687_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_fst_685_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v_str_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_728_, v_a_729_);
lean_dec_ref(v_str_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(lean_object* v_str_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v_snd_739_; lean_object* v_fst_740_; lean_object* v_fst_741_; uint8_t v___x_742_; 
v___x_737_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1));
v___x_738_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_736_, v___x_737_);
v_snd_739_ = lean_ctor_get(v___x_738_, 1);
lean_inc(v_snd_739_);
v_fst_740_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_fst_740_);
lean_dec_ref(v___x_738_);
v_fst_741_ = lean_ctor_get(v_snd_739_, 0);
lean_inc(v_fst_741_);
lean_dec(v_snd_739_);
v___x_742_ = lean_nat_dec_le(v_fst_740_, v_fst_741_);
if (v___x_742_ == 0)
{
lean_dec(v_fst_741_);
return v_fst_740_;
}
else
{
lean_dec(v_fst_740_);
return v_fst_741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___boxed(lean_object* v_str_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_743_);
lean_dec_ref(v_str_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(lean_object* v_str_745_, lean_object* v_inst_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_745_, v_a_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v_str_749_, lean_object* v_inst_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(v_str_749_, v_inst_750_, v_a_751_);
lean_dec_ref(v_str_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
lean_object* v_zero_755_; uint8_t v_isZero_756_; 
v_zero_755_ = lean_unsigned_to_nat(0u);
v_isZero_756_ = lean_nat_dec_eq(v_x_753_, v_zero_755_);
if (v_isZero_756_ == 1)
{
lean_dec(v_x_753_);
return v_x_754_;
}
else
{
uint32_t v___x_757_; lean_object* v_one_758_; lean_object* v_n_759_; lean_object* v___x_760_; 
v___x_757_ = 96;
v_one_758_ = lean_unsigned_to_nat(1u);
v_n_759_ = lean_nat_sub(v_x_753_, v_one_758_);
lean_dec(v_x_753_);
v___x_760_ = lean_string_push(v_x_754_, v___x_757_);
v_x_753_ = v_n_759_;
v_x_754_ = v___x_760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(lean_object* v_atLeast_762_, lean_object* v_str_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___y_766_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_770_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_763_);
v___x_771_ = lean_nat_dec_le(v_atLeast_762_, v___x_770_);
if (v___x_771_ == 0)
{
lean_dec(v___x_770_);
v___y_766_ = v_atLeast_762_;
goto v___jp_765_;
}
else
{
lean_dec(v_atLeast_762_);
v___y_766_ = v___x_770_;
goto v___jp_765_;
}
v___jp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = lean_nat_add(v___y_766_, v___x_767_);
lean_dec(v___y_766_);
v___x_769_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(v___x_768_, v___x_764_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor___boxed(lean_object* v_atLeast_772_, lean_object* v_str_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v_atLeast_772_, v_str_773_);
lean_dec_ref(v_str_773_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object* v_str_776_){
_start:
{
lean_object* v___x_777_; lean_object* v_backticks_778_; lean_object* v___y_780_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_777_ = lean_unsigned_to_nat(0u);
v_backticks_778_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_777_, v_str_776_);
v___x_794_ = lean_string_utf8_byte_size(v_str_776_);
v___x_795_ = lean_unsigned_to_nat(1u);
v___x_796_ = lean_nat_dec_le(v___x_795_, v___x_794_);
if (v___x_796_ == 0)
{
goto v___jp_787_;
}
else
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1));
v___x_798_ = lean_string_memcmp(v_str_776_, v___x_797_, v___x_777_, v___x_777_, v___x_795_);
if (v___x_798_ == 0)
{
goto v___jp_787_;
}
else
{
goto v___jp_783_;
}
}
v___jp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_inc_ref(v_backticks_778_);
v___x_781_ = lean_string_append(v_backticks_778_, v___y_780_);
lean_dec_ref(v___y_780_);
v___x_782_ = lean_string_append(v___x_781_, v_backticks_778_);
lean_dec_ref(v_backticks_778_);
return v___x_782_;
}
v___jp_783_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_785_ = lean_string_append(v___x_784_, v_str_776_);
lean_dec_ref(v_str_776_);
v___x_786_ = lean_string_append(v___x_785_, v___x_784_);
v___y_780_ = v___x_786_;
goto v___jp_779_;
}
v___jp_787_:
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = lean_string_utf8_byte_size(v_str_776_);
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_dec_le(v___x_789_, v___x_788_);
if (v___x_790_ == 0)
{
v___y_780_ = v_str_776_;
goto v___jp_779_;
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_791_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1));
v___x_792_ = lean_nat_sub(v___x_788_, v___x_789_);
v___x_793_ = lean_string_memcmp(v_str_776_, v___x_791_, v___x_792_, v___x_777_, v___x_789_);
lean_dec(v___x_792_);
if (v___x_793_ == 0)
{
v___y_780_ = v_str_776_;
goto v___jp_779_;
}
else
{
goto v___jp_783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg(){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___closed__0));
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___boxed(lean_object* v___dummy_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg();
return v_res_804_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg();
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(lean_object* v_s_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___boxed(lean_object* v_s_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v_s_808_);
lean_dec_ref(v_s_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(lean_object* v_str_810_, lean_object* v___x_811_, lean_object* v___x_812_, lean_object* v_a_813_, lean_object* v_b_814_){
_start:
{
lean_object* v_it_816_; lean_object* v_startInclusive_817_; lean_object* v_endExclusive_818_; 
if (lean_obj_tag(v_a_813_) == 0)
{
lean_object* v_currPos_822_; lean_object* v_searcher_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_846_; 
v_currPos_822_ = lean_ctor_get(v_a_813_, 0);
v_searcher_823_ = lean_ctor_get(v_a_813_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v_a_813_);
if (v_isSharedCheck_846_ == 0)
{
v___x_825_ = v_a_813_;
v_isShared_826_ = v_isSharedCheck_846_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_searcher_823_);
lean_inc(v_currPos_822_);
lean_dec(v_a_813_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_846_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
uint8_t v_decide_827_; 
v_decide_827_ = lean_nat_dec_eq(v_searcher_823_, v___x_812_);
if (v_decide_827_ == 0)
{
uint32_t v___x_828_; uint32_t v___x_829_; uint8_t v___x_830_; 
v___x_828_ = 10;
v___x_829_ = lean_string_utf8_get_fast(v_str_810_, v_searcher_823_);
v___x_830_ = lean_uint32_dec_eq(v___x_829_, v___x_828_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_831_ = lean_string_utf8_next_fast(v_str_810_, v_searcher_823_);
lean_dec(v_searcher_823_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v___x_831_);
v___x_833_ = v___x_825_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_currPos_822_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_831_);
v___x_833_ = v_reuseFailAlloc_835_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
v_a_813_ = v___x_833_;
goto _start;
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v_slice_839_; lean_object* v_nextIt_841_; 
v___x_836_ = lean_string_utf8_next_fast(v_str_810_, v_searcher_823_);
v___x_837_ = lean_nat_sub(v___x_836_, v_searcher_823_);
v___x_838_ = lean_nat_add(v_searcher_823_, v___x_837_);
lean_dec(v___x_837_);
v_slice_839_ = l_String_Slice_subslice_x21(v___x_811_, v_currPos_822_, v_searcher_823_);
lean_inc(v___x_838_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v___x_838_);
lean_ctor_set(v___x_825_, 0, v___x_838_);
v_nextIt_841_ = v___x_825_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_838_);
v_nextIt_841_ = v_reuseFailAlloc_844_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v_startInclusive_842_; lean_object* v_endExclusive_843_; 
v_startInclusive_842_ = lean_ctor_get(v_slice_839_, 0);
lean_inc(v_startInclusive_842_);
v_endExclusive_843_ = lean_ctor_get(v_slice_839_, 1);
lean_inc(v_endExclusive_843_);
lean_dec_ref(v_slice_839_);
v_it_816_ = v_nextIt_841_;
v_startInclusive_817_ = v_startInclusive_842_;
v_endExclusive_818_ = v_endExclusive_843_;
goto v___jp_815_;
}
}
}
else
{
lean_object* v___x_845_; 
lean_del_object(v___x_825_);
lean_dec(v_searcher_823_);
v___x_845_ = lean_box(1);
lean_inc(v___x_812_);
v_it_816_ = v___x_845_;
v_startInclusive_817_ = v_currPos_822_;
v_endExclusive_818_ = v___x_812_;
goto v___jp_815_;
}
}
}
else
{
lean_dec(v___x_812_);
return v_b_814_;
}
v___jp_815_:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_string_utf8_extract_fast(v_str_810_, v_startInclusive_817_, v_endExclusive_818_);
lean_dec(v_endExclusive_818_);
lean_dec(v_startInclusive_817_);
v___x_820_ = lean_array_push(v_b_814_, v___x_819_);
v_a_813_ = v_it_816_;
v_b_814_ = v___x_820_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg___boxed(lean_object* v_str_847_, lean_object* v___x_848_, lean_object* v___x_849_, lean_object* v_a_850_, lean_object* v_b_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_847_, v___x_848_, v___x_849_, v_a_850_, v_b_851_);
lean_dec_ref(v___x_848_);
lean_dec_ref(v_str_847_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(lean_object* v_str_853_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_string_utf8_byte_size(v_str_853_);
lean_inc_ref(v_str_853_);
v___x_856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_856_, 0, v_str_853_);
lean_ctor_set(v___x_856_, 1, v___x_854_);
lean_ctor_set(v___x_856_, 2, v___x_855_);
v___x_857_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0);
v___x_858_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_859_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_853_, v___x_856_, v___x_855_, v___x_857_, v___x_858_);
lean_dec_ref_known(v___x_856_, 3);
lean_dec_ref(v_str_853_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(lean_object* v_str_860_, lean_object* v___x_861_, lean_object* v___x_862_, lean_object* v_inst_863_, lean_object* v_R_864_, lean_object* v_a_865_, lean_object* v_b_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_860_, v___x_861_, v___x_862_, v_a_865_, v_b_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___boxed(lean_object* v_str_868_, lean_object* v___x_869_, lean_object* v___x_870_, lean_object* v_inst_871_, lean_object* v_R_872_, lean_object* v_a_873_, lean_object* v_b_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(v_str_868_, v___x_869_, v___x_870_, v_inst_871_, v_R_872_, v_a_873_, v_b_874_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v_str_868_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(lean_object* v_str_876_){
_start:
{
lean_object* v___x_877_; lean_object* v_fence_878_; lean_object* v___y_880_; lean_object* v_body_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_877_ = lean_unsigned_to_nat(2u);
v_fence_878_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_877_, v_str_876_);
v_body_886_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(v_str_876_);
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = lean_array_get_size(v_body_886_);
v___x_889_ = lean_nat_dec_lt(v___x_887_, v___x_888_);
if (v___x_889_ == 0)
{
v___y_880_ = v_body_886_;
goto v___jp_879_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_891_ = lean_unsigned_to_nat(1u);
v___x_892_ = lean_nat_sub(v___x_888_, v___x_891_);
v___x_893_ = lean_array_get_borrowed(v___x_890_, v_body_886_, v___x_892_);
lean_dec(v___x_892_);
v___x_894_ = lean_string_utf8_byte_size(v___x_893_);
v___x_895_ = lean_nat_dec_eq(v___x_894_, v___x_887_);
if (v___x_895_ == 0)
{
v___y_880_ = v_body_886_;
goto v___jp_879_;
}
else
{
lean_object* v___x_896_; 
v___x_896_ = lean_array_pop(v_body_886_);
v___y_880_ = v___x_896_;
goto v___jp_879_;
}
}
v___jp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_881_ = lean_unsigned_to_nat(1u);
v___x_882_ = lean_mk_empty_array_with_capacity(v___x_881_);
v___x_883_ = lean_array_push(v___x_882_, v_fence_878_);
lean_inc_ref(v___x_883_);
v___x_884_ = l_Array_append___redArg(v___x_883_, v___y_880_);
lean_dec_ref(v___y_880_);
v___x_885_ = l_Array_append___redArg(v___x_884_, v___x_883_);
lean_dec_ref(v___x_883_);
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_897_, lean_object* v_pos_898_){
_start:
{
lean_object* v_str_899_; lean_object* v_startInclusive_900_; lean_object* v_endExclusive_901_; lean_object* v___x_902_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v_decide_913_; 
v_str_899_ = lean_ctor_get(v_s_897_, 0);
v_startInclusive_900_ = lean_ctor_get(v_s_897_, 1);
v_endExclusive_901_ = lean_ctor_get(v_s_897_, 2);
v___x_902_ = lean_nat_add(v_startInclusive_900_, v_pos_898_);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = lean_nat_sub(v_endExclusive_901_, v___x_902_);
v_decide_913_ = lean_nat_dec_eq(v___x_911_, v___x_912_);
lean_dec(v___x_912_);
if (v_decide_913_ == 0)
{
uint32_t v___x_914_; uint32_t v___x_915_; uint8_t v___x_916_; 
v___x_914_ = lean_string_utf8_get_fast(v_str_899_, v___x_902_);
v___x_915_ = 32;
v___x_916_ = lean_uint32_dec_eq(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
uint32_t v___x_917_; uint8_t v___x_918_; 
v___x_917_ = 9;
v___x_918_ = lean_uint32_dec_eq(v___x_914_, v___x_917_);
if (v___x_918_ == 0)
{
uint32_t v___x_919_; uint8_t v___x_920_; 
v___x_919_ = 13;
v___x_920_ = lean_uint32_dec_eq(v___x_914_, v___x_919_);
if (v___x_920_ == 0)
{
uint32_t v___x_921_; uint8_t v___x_922_; 
v___x_921_ = 10;
v___x_922_ = lean_uint32_dec_eq(v___x_914_, v___x_921_);
if (v___x_922_ == 0)
{
lean_dec(v___x_902_);
return v_pos_898_;
}
else
{
goto v___jp_903_;
}
}
else
{
goto v___jp_903_;
}
}
else
{
goto v___jp_903_;
}
}
else
{
goto v___jp_903_;
}
}
else
{
lean_dec(v___x_902_);
return v_pos_898_;
}
v___jp_903_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_904_ = lean_string_utf8_next_fast(v_str_899_, v___x_902_);
v___x_905_ = lean_nat_sub(v___x_904_, v___x_902_);
lean_dec(v___x_902_);
v___x_906_ = lean_nat_add(v_pos_898_, v___x_905_);
lean_dec(v___x_905_);
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_nat_add(v_pos_898_, v___x_907_);
v___x_909_ = lean_nat_dec_le(v___x_908_, v___x_906_);
lean_dec(v___x_908_);
if (v___x_909_ == 0)
{
lean_dec(v___x_906_);
return v_pos_898_;
}
else
{
lean_dec(v_pos_898_);
v_pos_898_ = v___x_906_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object* v_s_923_, lean_object* v_pos_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_923_, v_pos_924_);
lean_dec_ref(v_s_923_);
return v_res_925_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_Doc_Inline_empty___redArg();
return v___x_926_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_928_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object* v_a_930_){
_start:
{
if (lean_obj_tag(v_a_930_) == 0)
{
lean_object* v___x_931_; 
v___x_931_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
return v___x_931_;
}
else
{
lean_object* v_head_932_; 
v_head_932_ = lean_ctor_get(v_a_930_, 0);
lean_inc(v_head_932_);
switch(lean_obj_tag(v_head_932_))
{
case 0:
{
lean_object* v_tail_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_977_; 
v_tail_933_ = lean_ctor_get(v_a_930_, 1);
v_isSharedCheck_977_ = !lean_is_exclusive(v_a_930_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v_a_930_, 0);
lean_dec(v_unused_978_);
v___x_935_ = v_a_930_;
v_isShared_936_ = v_isSharedCheck_977_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_tail_933_);
lean_dec(v_a_930_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_977_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_string_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_976_; 
v_string_937_ = lean_ctor_get(v_head_932_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v_head_932_);
if (v_isSharedCheck_976_ == 0)
{
v___x_939_ = v_head_932_;
v_isShared_940_ = v_isSharedCheck_976_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_string_937_);
lean_dec(v_head_932_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_976_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v_decide_945_; 
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_string_utf8_byte_size(v_string_937_);
lean_inc_ref(v_string_937_);
v___x_943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_943_, 0, v_string_937_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
lean_ctor_set(v___x_943_, 2, v___x_942_);
v___x_944_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_943_, v___x_941_);
lean_dec_ref_known(v___x_943_, 3);
v_decide_945_ = lean_nat_dec_eq(v___x_944_, v___x_942_);
if (v_decide_945_ == 0)
{
lean_object* v_s1_946_; lean_object* v_s2_947_; lean_object* v___x_949_; 
v_s1_946_ = lean_string_utf8_extract_fast(v_string_937_, v___x_941_, v___x_944_);
v_s2_947_ = lean_string_utf8_extract_fast(v_string_937_, v___x_944_, v___x_942_);
lean_dec(v___x_944_);
lean_dec_ref(v_string_937_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_s2_947_);
v___x_949_ = v___x_939_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_s2_947_);
v___x_949_ = v_reuseFailAlloc_964_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_950_ = lean_array_mk(v_tail_933_);
v___x_951_ = lean_array_get_size(v___x_950_);
v___x_952_ = lean_nat_dec_eq(v___x_951_, v___x_941_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_mk_empty_array_with_capacity(v___x_953_);
v___x_955_ = lean_array_push(v___x_954_, v___x_949_);
v___x_956_ = l_Array_append___redArg(v___x_955_, v___x_950_);
lean_dec_ref(v___x_950_);
v___x_957_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 0);
lean_ctor_set(v___x_935_, 1, v___x_957_);
lean_ctor_set(v___x_935_, 0, v_s1_946_);
v___x_959_ = v___x_935_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_s1_946_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
else
{
lean_object* v___x_962_; 
lean_dec_ref(v___x_950_);
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 0);
lean_ctor_set(v___x_935_, 1, v___x_949_);
lean_ctor_set(v___x_935_, 0, v_s1_946_);
v___x_962_ = v___x_935_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_s1_946_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v___x_949_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
else
{
lean_object* v___x_965_; lean_object* v_fst_966_; lean_object* v_snd_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_975_; 
lean_dec(v___x_944_);
lean_del_object(v___x_939_);
lean_del_object(v___x_935_);
v___x_965_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_933_);
v_fst_966_ = lean_ctor_get(v___x_965_, 0);
v_snd_967_ = lean_ctor_get(v___x_965_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_975_ == 0)
{
v___x_969_ = v___x_965_;
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_snd_967_);
lean_inc(v_fst_966_);
lean_dec(v___x_965_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = lean_string_append(v_string_937_, v_fst_966_);
lean_dec(v_fst_966_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_971_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_snd_967_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_979_; lean_object* v_content_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_tail_979_ = lean_ctor_get(v_a_930_, 1);
lean_inc(v_tail_979_);
lean_dec_ref_known(v_a_930_, 2);
v_content_980_ = lean_ctor_get(v_head_932_, 0);
lean_inc_ref(v_content_980_);
lean_dec_ref_known(v_head_932_, 1);
v___x_981_ = lean_array_to_list(v_content_980_);
v___x_982_ = l_List_appendTR___redArg(v___x_981_, v_tail_979_);
v_a_930_ = v___x_982_;
goto _start;
}
default: 
{
lean_object* v_tail_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1022_; 
v_tail_984_ = lean_ctor_get(v_a_930_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_a_930_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v_a_930_, 0);
lean_dec(v_unused_1023_);
v___x_986_ = v_a_930_;
v_isShared_987_ = v_isSharedCheck_1022_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_tail_984_);
lean_dec(v_a_930_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1022_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_989_ = lean_array_mk(v_tail_984_);
if (lean_obj_tag(v_head_932_) == 9)
{
lean_object* v_content_990_; lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v_content_990_ = lean_ctor_get(v_head_932_, 0);
v___x_991_ = lean_array_get_size(v_content_990_);
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = lean_nat_dec_eq(v___x_991_, v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = lean_array_get_size(v___x_989_);
v___x_995_ = lean_nat_dec_eq(v___x_994_, v___x_992_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
lean_inc_ref(v_content_990_);
lean_dec_ref_known(v_head_932_, 1);
v___x_996_ = l_Array_append___redArg(v_content_990_, v___x_989_);
lean_dec_ref(v___x_989_);
v___x_997_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 0);
lean_ctor_set(v___x_986_, 1, v___x_997_);
lean_ctor_set(v___x_986_, 0, v___x_988_);
v___x_999_ = v___x_986_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
else
{
lean_object* v___x_1002_; 
lean_dec_ref(v___x_989_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 0);
lean_ctor_set(v___x_986_, 1, v_head_932_);
lean_ctor_set(v___x_986_, 0, v___x_988_);
v___x_1002_ = v___x_986_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_head_932_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
lean_dec_ref_known(v_head_932_, 1);
v___x_1004_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_989_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 0);
lean_ctor_set(v___x_986_, 1, v___x_1004_);
lean_ctor_set(v___x_986_, 0, v___x_988_);
v___x_1006_ = v___x_986_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1008_ = lean_array_get_size(v___x_989_);
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = lean_nat_dec_eq(v___x_1008_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_mk_empty_array_with_capacity(v___x_1011_);
v___x_1013_ = lean_array_push(v___x_1012_, v_head_932_);
v___x_1014_ = l_Array_append___redArg(v___x_1013_, v___x_989_);
lean_dec_ref(v___x_989_);
v___x_1015_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 0);
lean_ctor_set(v___x_986_, 1, v___x_1015_);
lean_ctor_set(v___x_986_, 0, v___x_988_);
v___x_1017_ = v___x_986_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
else
{
lean_object* v___x_1020_; 
lean_dec_ref(v___x_989_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 0);
lean_ctor_set(v___x_986_, 1, v_head_932_);
lean_ctor_set(v___x_986_, 0, v___x_988_);
v___x_1020_ = v___x_986_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_head_932_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_1027_){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_inline_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_1031_, lean_object* v_inline_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_1034_, lean_object* v_pos_1035_){
_start:
{
lean_object* v_str_1036_; lean_object* v_startInclusive_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v_decide_1041_; 
v_str_1036_ = lean_ctor_get(v_s_1034_, 0);
v_startInclusive_1037_ = lean_ctor_get(v_s_1034_, 1);
v___x_1038_ = lean_nat_add(v_startInclusive_1037_, v_pos_1035_);
v___x_1039_ = lean_nat_sub(v___x_1038_, v_startInclusive_1037_);
v___x_1040_ = lean_unsigned_to_nat(0u);
v_decide_1041_ = lean_nat_dec_eq(v___x_1039_, v___x_1040_);
if (v_decide_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1050_; uint32_t v___x_1051_; uint32_t v___x_1052_; uint8_t v___x_1053_; 
lean_inc(v_startInclusive_1037_);
lean_inc_ref(v_str_1036_);
v___x_1042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1042_, 0, v_str_1036_);
lean_ctor_set(v___x_1042_, 1, v_startInclusive_1037_);
lean_ctor_set(v___x_1042_, 2, v___x_1038_);
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_nat_sub(v___x_1039_, v___x_1043_);
lean_dec(v___x_1039_);
v___x_1045_ = l_String_Slice_posLE(v___x_1042_, v___x_1044_);
lean_dec_ref_known(v___x_1042_, 3);
v___x_1050_ = lean_nat_add(v_startInclusive_1037_, v___x_1045_);
v___x_1051_ = lean_string_utf8_get_fast(v_str_1036_, v___x_1050_);
lean_dec(v___x_1050_);
v___x_1052_ = 32;
v___x_1053_ = lean_uint32_dec_eq(v___x_1051_, v___x_1052_);
if (v___x_1053_ == 0)
{
uint32_t v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = 9;
v___x_1055_ = lean_uint32_dec_eq(v___x_1051_, v___x_1054_);
if (v___x_1055_ == 0)
{
uint32_t v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = 13;
v___x_1057_ = lean_uint32_dec_eq(v___x_1051_, v___x_1056_);
if (v___x_1057_ == 0)
{
uint32_t v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = 10;
v___x_1059_ = lean_uint32_dec_eq(v___x_1051_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_dec(v___x_1045_);
return v_pos_1035_;
}
else
{
goto v___jp_1046_;
}
}
else
{
goto v___jp_1046_;
}
}
else
{
goto v___jp_1046_;
}
}
else
{
goto v___jp_1046_;
}
v___jp_1046_:
{
lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = lean_nat_add(v___x_1045_, v___x_1043_);
v___x_1048_ = lean_nat_dec_le(v___x_1047_, v_pos_1035_);
lean_dec(v___x_1047_);
if (v___x_1048_ == 0)
{
lean_dec(v___x_1045_);
return v_pos_1035_;
}
else
{
lean_dec(v_pos_1035_);
v_pos_1035_ = v___x_1045_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1039_);
lean_dec(v___x_1038_);
return v_pos_1035_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_1060_, lean_object* v_pos_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_1060_, v_pos_1061_);
lean_dec_ref(v_s_1060_);
return v_res_1062_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1064_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___x_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_xs_1066_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1067_ = lean_array_get_size(v_xs_1066_);
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = lean_nat_dec_eq(v___x_1067_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = lean_nat_sub(v___x_1067_, v___x_1070_);
v___x_1072_ = lean_array_fget(v_xs_1066_, v___x_1071_);
lean_dec(v___x_1071_);
switch(lean_obj_tag(v___x_1072_))
{
case 0:
{
lean_object* v_string_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1103_; 
v_string_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1103_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_string_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1103_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v_decide_1080_; 
v___x_1077_ = lean_string_utf8_byte_size(v_string_1073_);
lean_inc_ref(v_string_1073_);
v___x_1078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1078_, 0, v_string_1073_);
lean_ctor_set(v___x_1078_, 1, v___x_1068_);
lean_ctor_set(v___x_1078_, 2, v___x_1077_);
v___x_1079_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_1078_, v___x_1068_);
v_decide_1080_ = lean_nat_dec_eq(v___x_1079_, v___x_1077_);
lean_dec(v___x_1079_);
if (v_decide_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1081_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_1078_, v___x_1077_);
lean_dec_ref_known(v___x_1078_, 3);
v___x_1082_ = lean_array_pop(v_xs_1066_);
v___x_1083_ = lean_string_utf8_extract_fast(v_string_1073_, v___x_1068_, v___x_1081_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1083_);
v___x_1085_ = v___x_1075_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1086_ = lean_array_push(v___x_1082_, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
v___x_1088_ = lean_string_utf8_extract_fast(v_string_1073_, v___x_1081_, v___x_1077_);
lean_dec(v___x_1081_);
lean_dec_ref(v_string_1073_);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
return v___x_1089_;
}
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_fst_1093_; lean_object* v_snd_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref_known(v___x_1078_, 3);
lean_del_object(v___x_1075_);
v___x_1091_ = lean_array_pop(v_xs_1066_);
v___x_1092_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1091_);
v_fst_1093_ = lean_ctor_get(v___x_1092_, 0);
v_snd_1094_ = lean_ctor_get(v___x_1092_, 1);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1096_ = v___x_1092_;
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_snd_1094_);
lean_inc(v_fst_1093_);
lean_dec(v___x_1092_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_string_append(v_snd_1094_, v_string_1073_);
lean_dec_ref(v_string_1073_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v___x_1098_);
v___x_1100_ = v___x_1096_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_fst_1093_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
case 9:
{
lean_object* v_content_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_content_1104_ = lean_ctor_get(v___x_1072_, 0);
lean_inc_ref(v_content_1104_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1105_ = lean_array_pop(v_xs_1066_);
v___x_1106_ = l_Array_append___redArg(v___x_1105_, v_content_1104_);
lean_dec_ref(v_content_1104_);
v_xs_1066_ = v___x_1106_;
goto _start;
}
default: 
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_dec(v___x_1072_);
v___x_1108_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_xs_1066_);
v___x_1109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
return v___x_1110_;
}
}
}
else
{
lean_object* v___x_1111_; 
lean_dec_ref(v_xs_1066_);
v___x_1111_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_1112_, lean_object* v_xs_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_xs_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_mk_empty_array_with_capacity(v___x_1116_);
v___x_1118_ = lean_array_push(v___x_1117_, v_inline_1115_);
v___x_1119_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_1120_, lean_object* v_inline_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v_fst_1125_; lean_object* v_snd_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1134_; 
v___x_1124_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1123_);
v_fst_1125_ = lean_ctor_get(v___x_1124_, 0);
v_snd_1126_ = lean_ctor_get(v___x_1124_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1128_ = v___x_1124_;
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_snd_1126_);
lean_inc(v_fst_1125_);
lean_dec(v___x_1124_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 1, v___x_1130_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_fst_1125_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_1135_, lean_object* v_inline_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_instMonadEIO___redArg();
return v___x_1138_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0);
v___x_1140_ = l_StateRefT_x27_instMonad___redArg(v___x_1139_);
return v___x_1140_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1169_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13));
v___x_1170_ = lean_unsigned_to_nat(3u);
v___x_1171_ = lean_mk_empty_array_with_capacity(v___x_1170_);
v___x_1172_ = lean_array_push(v___x_1171_, v___x_1169_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object* v_inst_1175_, lean_object* v_x_1176_, lean_object* v_x_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1175_, v_x_1176_, v_x_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_pieces_1191_; lean_object* v_pieces_1195_; lean_object* v___x_1198_; lean_object* v_toApplicative_1199_; lean_object* v_toFunctor_1200_; lean_object* v_toSeq_1201_; lean_object* v_toSeqLeft_1202_; lean_object* v_toSeqRight_1203_; lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1198_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1199_ = lean_ctor_get(v___x_1198_, 0);
v_toFunctor_1200_ = lean_ctor_get(v_toApplicative_1199_, 0);
v_toSeq_1201_ = lean_ctor_get(v_toApplicative_1199_, 2);
v_toSeqLeft_1202_ = lean_ctor_get(v_toApplicative_1199_, 3);
v_toSeqRight_1203_ = lean_ctor_get(v_toApplicative_1199_, 4);
v___f_1204_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1205_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1200_, 2);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toFunctor_1200_);
v___f_1207_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1207_, 0, v_toFunctor_1200_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___f_1206_);
lean_ctor_set(v___x_1208_, 1, v___f_1207_);
lean_inc(v_toSeqRight_1203_);
v___f_1209_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1209_, 0, v_toSeqRight_1203_);
lean_inc(v_toSeqLeft_1202_);
v___f_1210_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1210_, 0, v_toSeqLeft_1202_);
lean_inc(v_toSeq_1201_);
v___f_1211_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1211_, 0, v_toSeq_1201_);
v___x_1212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1208_);
lean_ctor_set(v___x_1212_, 1, v___f_1204_);
lean_ctor_set(v___x_1212_, 2, v___f_1211_);
lean_ctor_set(v___x_1212_, 3, v___f_1210_);
lean_ctor_set(v___x_1212_, 4, v___f_1209_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___f_1205_);
v___x_1214_ = l_StateRefT_x27_instMonad___redArg(v___x_1213_);
switch(lean_obj_tag(v_x_1185_))
{
case 0:
{
lean_object* v_string_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec_ref(v___x_1214_);
lean_dec_ref(v_x_1184_);
lean_dec_ref(v_inst_1183_);
v_string_1215_ = lean_ctor_get(v_x_1185_, 0);
lean_inc_ref(v_string_1215_);
lean_dec_ref_known(v_x_1185_, 1);
v___x_1216_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1215_);
lean_dec_ref(v_string_1215_);
v___x_1217_ = lean_unsigned_to_nat(1u);
v___x_1218_ = lean_mk_empty_array_with_capacity(v___x_1217_);
v___x_1219_ = lean_array_push(v___x_1218_, v___x_1216_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
case 1:
{
lean_object* v_content_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1272_; 
lean_dec_ref(v___x_1214_);
v_content_1221_ = lean_ctor_get(v_x_1185_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_x_1185_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1223_ = v_x_1185_;
v_isShared_1224_ = v_isSharedCheck_1272_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_content_1221_);
lean_dec(v_x_1185_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1272_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 9);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_content_1221_);
v___x_1226_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; lean_object* v_snd_1228_; lean_object* v_fst_1229_; lean_object* v_fst_1230_; lean_object* v_snd_1231_; lean_object* v_pieces_1233_; uint8_t v_inEmph_1241_; uint8_t v_inBold_1242_; uint8_t v_inLink_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1270_; 
v___x_1227_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1226_);
v_snd_1228_ = lean_ctor_get(v___x_1227_, 1);
lean_inc(v_snd_1228_);
v_fst_1229_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_fst_1229_);
lean_dec_ref(v___x_1227_);
v_fst_1230_ = lean_ctor_get(v_snd_1228_, 0);
lean_inc(v_fst_1230_);
v_snd_1231_ = lean_ctor_get(v_snd_1228_, 1);
lean_inc(v_snd_1231_);
lean_dec(v_snd_1228_);
v_inEmph_1241_ = lean_ctor_get_uint8(v_x_1184_, 0);
v_inBold_1242_ = lean_ctor_get_uint8(v_x_1184_, 1);
v_inLink_1243_ = lean_ctor_get_uint8(v_x_1184_, 2);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_x_1184_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1245_ = v_x_1184_;
v_isShared_1246_ = v_isSharedCheck_1270_;
goto v_resetjp_1244_;
}
else
{
lean_dec(v_x_1184_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1270_;
goto v_resetjp_1244_;
}
v___jp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1234_ = lean_string_utf8_byte_size(v_snd_1231_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_nat_dec_eq(v___x_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = lean_mk_empty_array_with_capacity(v___x_1237_);
v___x_1239_ = lean_array_push(v___x_1238_, v_snd_1231_);
v___x_1240_ = lean_array_push(v_pieces_1233_, v___x_1239_);
v_pieces_1195_ = v___x_1240_;
goto v___jp_1194_;
}
else
{
lean_dec(v_snd_1231_);
v_pieces_1195_ = v_pieces_1233_;
goto v___jp_1194_;
}
}
v_resetjp_1244_:
{
uint8_t v___x_1247_; lean_object* v___x_1249_; 
v___x_1247_ = 1;
if (v_isShared_1246_ == 0)
{
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, 1, v_inBold_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, 2, v_inLink_1243_);
v___x_1249_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; 
lean_ctor_set_uint8(v___x_1249_, 0, v___x_1247_);
v___x_1250_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1183_, v___x_1249_, v_fst_1230_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v_pieces_1253_; lean_object* v_pieces_1258_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1263_ = lean_string_utf8_byte_size(v_fst_1229_);
v___x_1264_ = lean_nat_dec_eq(v___x_1263_, v___x_1261_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_mk_empty_array_with_capacity(v___x_1265_);
v___x_1267_ = lean_array_push(v___x_1266_, v_fst_1229_);
v___x_1268_ = lean_array_push(v___x_1262_, v___x_1267_);
v_pieces_1258_ = v___x_1268_;
goto v___jp_1257_;
}
else
{
lean_dec(v_fst_1229_);
v_pieces_1258_ = v___x_1262_;
goto v___jp_1257_;
}
v___jp_1252_:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_array_push(v_pieces_1253_, v_a_1251_);
if (v_inEmph_1241_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1256_ = lean_array_push(v___x_1254_, v___x_1255_);
v_pieces_1233_ = v___x_1256_;
goto v___jp_1232_;
}
else
{
v_pieces_1233_ = v___x_1254_;
goto v___jp_1232_;
}
}
v___jp_1257_:
{
if (v_inEmph_1241_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1260_ = lean_array_push(v_pieces_1258_, v___x_1259_);
v_pieces_1253_ = v___x_1260_;
goto v___jp_1252_;
}
else
{
v_pieces_1253_ = v_pieces_1258_;
goto v___jp_1252_;
}
}
}
else
{
lean_dec(v_snd_1231_);
lean_dec(v_fst_1229_);
return v___x_1250_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v___x_1214_);
v_content_1273_ = lean_ctor_get(v_x_1185_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_x_1185_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1275_ = v_x_1185_;
v_isShared_1276_ = v_isSharedCheck_1324_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_content_1273_);
lean_dec(v_x_1185_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1324_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set_tag(v___x_1275_, 9);
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_content_1273_);
v___x_1278_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; lean_object* v_snd_1280_; lean_object* v_fst_1281_; lean_object* v_fst_1282_; lean_object* v_snd_1283_; lean_object* v_pieces_1285_; uint8_t v_inEmph_1293_; uint8_t v_inBold_1294_; uint8_t v_inLink_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1322_; 
v___x_1279_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1278_);
v_snd_1280_ = lean_ctor_get(v___x_1279_, 1);
lean_inc(v_snd_1280_);
v_fst_1281_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_fst_1281_);
lean_dec_ref(v___x_1279_);
v_fst_1282_ = lean_ctor_get(v_snd_1280_, 0);
lean_inc(v_fst_1282_);
v_snd_1283_ = lean_ctor_get(v_snd_1280_, 1);
lean_inc(v_snd_1283_);
lean_dec(v_snd_1280_);
v_inEmph_1293_ = lean_ctor_get_uint8(v_x_1184_, 0);
v_inBold_1294_ = lean_ctor_get_uint8(v_x_1184_, 1);
v_inLink_1295_ = lean_ctor_get_uint8(v_x_1184_, 2);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_x_1184_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1297_ = v_x_1184_;
v_isShared_1298_ = v_isSharedCheck_1322_;
goto v_resetjp_1296_;
}
else
{
lean_dec(v_x_1184_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1322_;
goto v_resetjp_1296_;
}
v___jp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1286_ = lean_string_utf8_byte_size(v_snd_1283_);
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = lean_nat_dec_eq(v___x_1286_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = lean_mk_empty_array_with_capacity(v___x_1289_);
v___x_1291_ = lean_array_push(v___x_1290_, v_snd_1283_);
v___x_1292_ = lean_array_push(v_pieces_1285_, v___x_1291_);
v_pieces_1191_ = v___x_1292_;
goto v___jp_1190_;
}
else
{
lean_dec(v_snd_1283_);
v_pieces_1191_ = v_pieces_1285_;
goto v___jp_1190_;
}
}
v_resetjp_1296_:
{
uint8_t v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = 1;
if (v_isShared_1298_ == 0)
{
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1321_, 0, v_inEmph_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1321_, 2, v_inLink_1295_);
v___x_1301_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; 
lean_ctor_set_uint8(v___x_1301_, 1, v___x_1299_);
v___x_1302_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1183_, v___x_1301_, v_fst_1282_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v_pieces_1305_; lean_object* v_pieces_1310_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1315_ = lean_string_utf8_byte_size(v_fst_1281_);
v___x_1316_ = lean_nat_dec_eq(v___x_1315_, v___x_1313_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = lean_unsigned_to_nat(1u);
v___x_1318_ = lean_mk_empty_array_with_capacity(v___x_1317_);
v___x_1319_ = lean_array_push(v___x_1318_, v_fst_1281_);
v___x_1320_ = lean_array_push(v___x_1314_, v___x_1319_);
v_pieces_1310_ = v___x_1320_;
goto v___jp_1309_;
}
else
{
lean_dec(v_fst_1281_);
v_pieces_1310_ = v___x_1314_;
goto v___jp_1309_;
}
v___jp_1304_:
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_array_push(v_pieces_1305_, v_a_1303_);
if (v_inBold_1294_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1308_ = lean_array_push(v___x_1306_, v___x_1307_);
v_pieces_1285_ = v___x_1308_;
goto v___jp_1284_;
}
else
{
v_pieces_1285_ = v___x_1306_;
goto v___jp_1284_;
}
}
v___jp_1309_:
{
if (v_inBold_1294_ == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1312_ = lean_array_push(v_pieces_1310_, v___x_1311_);
v_pieces_1305_ = v___x_1312_;
goto v___jp_1304_;
}
else
{
v_pieces_1305_ = v_pieces_1310_;
goto v___jp_1304_;
}
}
}
else
{
lean_dec(v_snd_1283_);
lean_dec(v_fst_1281_);
return v___x_1302_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v___x_1214_);
lean_dec_ref(v_x_1184_);
lean_dec_ref(v_inst_1183_);
v_string_1325_ = lean_ctor_get(v_x_1185_, 0);
lean_inc_ref(v_string_1325_);
lean_dec_ref_known(v_x_1185_, 1);
v___x_1326_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1325_);
v___x_1327_ = lean_unsigned_to_nat(1u);
v___x_1328_ = lean_mk_empty_array_with_capacity(v___x_1327_);
v___x_1329_ = lean_array_push(v___x_1328_, v___x_1326_);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
case 4:
{
uint8_t v_mode_1331_; 
lean_dec_ref(v___x_1214_);
lean_dec_ref(v_x_1184_);
lean_dec_ref(v_inst_1183_);
v_mode_1331_ = lean_ctor_get_uint8(v_x_1185_, sizeof(void*)*1);
if (v_mode_1331_ == 0)
{
lean_object* v_string_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_string_1332_ = lean_ctor_get(v_x_1185_, 0);
lean_inc_ref(v_string_1332_);
lean_dec_ref_known(v_x_1185_, 1);
v___x_1333_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_1334_ = lean_string_append(v___x_1333_, v_string_1332_);
lean_dec_ref(v_string_1332_);
v___x_1335_ = lean_string_append(v___x_1334_, v___x_1333_);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_mk_empty_array_with_capacity(v___x_1336_);
v___x_1338_ = lean_array_push(v___x_1337_, v___x_1335_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
return v___x_1339_;
}
else
{
lean_object* v_string_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_string_1340_ = lean_ctor_get(v_x_1185_, 0);
lean_inc_ref(v_string_1340_);
lean_dec_ref_known(v_x_1185_, 1);
v___x_1341_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_1342_ = lean_string_append(v___x_1341_, v_string_1340_);
lean_dec_ref(v_string_1340_);
v___x_1343_ = lean_string_append(v___x_1342_, v___x_1341_);
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = lean_mk_empty_array_with_capacity(v___x_1344_);
v___x_1346_ = lean_array_push(v___x_1345_, v___x_1343_);
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
}
case 5:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec_ref_known(v_x_1185_, 1);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v_x_1184_);
lean_dec_ref(v_inst_1183_);
v___x_1348_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
case 6:
{
uint8_t v_inLink_1350_; 
v_inLink_1350_ = lean_ctor_get_uint8(v_x_1184_, 2);
if (v_inLink_1350_ == 0)
{
lean_object* v_content_1351_; lean_object* v_url_1352_; uint8_t v_inEmph_1353_; uint8_t v_inBold_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref(v___x_1214_);
v_content_1351_ = lean_ctor_get(v_x_1185_, 0);
lean_inc_ref(v_content_1351_);
v_url_1352_ = lean_ctor_get(v_x_1185_, 1);
lean_inc_ref(v_url_1352_);
lean_dec_ref_known(v_x_1185_, 2);
v_inEmph_1353_ = lean_ctor_get_uint8(v_x_1184_, 0);
v_inBold_1354_ = lean_ctor_get_uint8(v_x_1184_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_x_1184_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1356_ = v_x_1184_;
v_isShared_1357_ = v_isSharedCheck_1383_;
goto v_resetjp_1355_;
}
else
{
lean_dec(v_x_1184_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1383_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
uint8_t v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = 1;
if (v_isShared_1357_ == 0)
{
v___x_1360_ = v___x_1356_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 0, v_inEmph_1353_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, 1, v_inBold_1354_);
v___x_1360_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_ctor_set_uint8(v___x_1360_, 2, v___x_1358_);
v___x_1361_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1361_, 0, v_content_1351_);
v___x_1362_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1183_, v___x_1360_, v___x_1361_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1381_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1381_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1381_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_mk_empty_array_with_capacity(v___x_1367_);
v___x_1369_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1370_ = lean_string_append(v___x_1369_, v_url_1352_);
lean_dec_ref(v_url_1352_);
v___x_1371_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1372_ = lean_string_append(v___x_1370_, v___x_1371_);
v___x_1373_ = lean_array_push(v___x_1368_, v___x_1372_);
v___x_1374_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_1375_ = lean_array_push(v___x_1374_, v_a_1363_);
v___x_1376_ = lean_array_push(v___x_1375_, v___x_1373_);
v___x_1377_ = l_Lean_Doc_joinInlines(v___x_1376_);
lean_dec_ref(v___x_1376_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1377_);
v___x_1379_ = v___x_1365_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
lean_dec_ref(v_url_1352_);
return v___x_1362_;
}
}
}
}
else
{
lean_object* v_content_1384_; lean_object* v___x_1385_; size_t v_sz_1386_; size_t v___x_1387_; lean_object* v___x_4335__overap_1388_; lean_object* v___x_1389_; 
v_content_1384_ = lean_ctor_get(v_x_1185_, 0);
lean_inc_ref(v_content_1384_);
lean_dec_ref_known(v_x_1185_, 2);
v___x_1385_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1385_, 0, v_inst_1183_);
lean_closure_set(v___x_1385_, 1, v_x_1184_);
v_sz_1386_ = lean_array_size(v_content_1384_);
v___x_1387_ = ((size_t)0ULL);
v___x_4335__overap_1388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1214_, v___x_1385_, v_sz_1386_, v___x_1387_, v_content_1384_);
lean_inc(v_a_1188_);
lean_inc_ref(v_a_1187_);
lean_inc(v_a_1186_);
v___x_1389_ = lean_apply_4(v___x_4335__overap_1388_, v_a_1186_, v_a_1187_, v_a_1188_, lean_box(0));
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1398_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1398_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1398_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1394_ = l_Lean_Doc_joinInlines(v_a_1390_);
lean_dec(v_a_1390_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1394_);
v___x_1396_ = v___x_1392_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
v_a_1399_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1389_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1389_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
case 7:
{
lean_object* v_name_1407_; lean_object* v_content_1408_; lean_object* v___x_1409_; size_t v_sz_1410_; size_t v___x_1411_; lean_object* v___x_4338__overap_1412_; lean_object* v___x_1413_; 
v_name_1407_ = lean_ctor_get(v_x_1185_, 0);
lean_inc_ref(v_name_1407_);
v_content_1408_ = lean_ctor_get(v_x_1185_, 1);
lean_inc_ref(v_content_1408_);
lean_dec_ref_known(v_x_1185_, 2);
v___x_1409_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1409_, 0, v_inst_1183_);
lean_closure_set(v___x_1409_, 1, v_x_1184_);
v_sz_1410_ = lean_array_size(v_content_1408_);
v___x_1411_ = ((size_t)0ULL);
v___x_4338__overap_1412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1214_, v___x_1409_, v_sz_1410_, v___x_1411_, v_content_1408_);
lean_inc(v_a_1188_);
lean_inc_ref(v_a_1187_);
lean_inc(v_a_1186_);
v___x_1413_ = lean_apply_4(v___x_4338__overap_1412_, v_a_1186_, v_a_1187_, v_a_1188_, lean_box(0));
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_1416_ = l_Lean_Doc_joinInlines(v_a_1414_);
lean_dec(v_a_1414_);
v___x_1417_ = lean_array_to_list(v___x_1416_);
v___x_1418_ = l_String_intercalate(v___x_1415_, v___x_1417_);
lean_inc_ref(v_name_1407_);
v___x_1419_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_1407_, v___x_1418_, v_a_1186_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1433_; 
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v___x_1419_, 0);
lean_dec(v_unused_1434_);
v___x_1421_ = v___x_1419_;
v_isShared_1422_ = v_isSharedCheck_1433_;
goto v_resetjp_1420_;
}
else
{
lean_dec(v___x_1419_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1433_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1423_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_1424_ = lean_string_append(v___x_1423_, v_name_1407_);
lean_dec_ref(v_name_1407_);
v___x_1425_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_1426_ = lean_string_append(v___x_1424_, v___x_1425_);
v___x_1427_ = lean_unsigned_to_nat(1u);
v___x_1428_ = lean_mk_empty_array_with_capacity(v___x_1427_);
v___x_1429_ = lean_array_push(v___x_1428_, v___x_1426_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1429_);
v___x_1431_ = v___x_1421_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec_ref(v_name_1407_);
v_a_1435_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1419_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1419_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec_ref(v_name_1407_);
v_a_1443_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1413_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1413_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
case 8:
{
lean_object* v_alt_1451_; lean_object* v_url_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec_ref(v___x_1214_);
lean_dec_ref(v_x_1184_);
lean_dec_ref(v_inst_1183_);
v_alt_1451_ = lean_ctor_get(v_x_1185_, 0);
lean_inc_ref(v_alt_1451_);
v_url_1452_ = lean_ctor_get(v_x_1185_, 1);
lean_inc_ref(v_url_1452_);
lean_dec_ref_known(v_x_1185_, 2);
v___x_1453_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_1454_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1451_);
lean_dec_ref(v_alt_1451_);
v___x_1455_ = lean_string_append(v___x_1453_, v___x_1454_);
lean_dec_ref(v___x_1454_);
v___x_1456_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1457_ = lean_string_append(v___x_1455_, v___x_1456_);
v___x_1458_ = lean_string_append(v___x_1457_, v_url_1452_);
lean_dec_ref(v_url_1452_);
v___x_1459_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1460_ = lean_string_append(v___x_1458_, v___x_1459_);
v___x_1461_ = lean_unsigned_to_nat(1u);
v___x_1462_ = lean_mk_empty_array_with_capacity(v___x_1461_);
v___x_1463_ = lean_array_push(v___x_1462_, v___x_1460_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
case 9:
{
lean_object* v_content_1465_; lean_object* v___x_1466_; size_t v_sz_1467_; size_t v___x_1468_; lean_object* v___x_4341__overap_1469_; lean_object* v___x_1470_; 
v_content_1465_ = lean_ctor_get(v_x_1185_, 0);
lean_inc_ref(v_content_1465_);
lean_dec_ref_known(v_x_1185_, 1);
v___x_1466_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1466_, 0, v_inst_1183_);
lean_closure_set(v___x_1466_, 1, v_x_1184_);
v_sz_1467_ = lean_array_size(v_content_1465_);
v___x_1468_ = ((size_t)0ULL);
v___x_4341__overap_1469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1214_, v___x_1466_, v_sz_1467_, v___x_1468_, v_content_1465_);
lean_inc(v_a_1188_);
lean_inc_ref(v_a_1187_);
lean_inc(v_a_1186_);
v___x_1470_ = lean_apply_4(v___x_4341__overap_1469_, v_a_1186_, v_a_1187_, v_a_1188_, lean_box(0));
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1479_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1475_ = l_Lean_Doc_joinInlines(v_a_1471_);
lean_dec(v_a_1471_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1475_);
v___x_1477_ = v___x_1473_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
v_a_1480_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1470_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1470_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
default: 
{
lean_object* v_container_1488_; lean_object* v_content_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec_ref(v___x_1214_);
v_container_1488_ = lean_ctor_get(v_x_1185_, 0);
lean_inc(v_container_1488_);
v_content_1489_ = lean_ctor_get(v_x_1185_, 1);
lean_inc_ref(v_content_1489_);
lean_dec_ref_known(v_x_1185_, 2);
lean_inc_ref(v_inst_1183_);
v___x_1490_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1490_, 0, v_inst_1183_);
lean_closure_set(v___x_1490_, 1, v_x_1184_);
lean_inc(v_a_1188_);
lean_inc_ref(v_a_1187_);
lean_inc(v_a_1186_);
v___x_1491_ = lean_apply_7(v_inst_1183_, v___x_1490_, v_container_1488_, v_content_1489_, v_a_1186_, v_a_1187_, v_a_1188_, lean_box(0));
return v___x_1491_;
}
}
v___jp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = l_Lean_Doc_joinInlines(v_pieces_1191_);
lean_dec_ref(v_pieces_1191_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
v___jp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = l_Lean_Doc_joinInlines(v_pieces_1195_);
lean_dec_ref(v_pieces_1195_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1492_, lean_object* v_inst_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1493_, v_x_1494_, v_x_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object* v_i_1501_, lean_object* v_inst_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(v_i_1501_, v_inst_1502_, v_x_1503_, v_x_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1517_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1510_, v___x_1516_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object* v_inst_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(v_inst_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1525_, lean_object* v_inst_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1533_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1526_, v___x_1532_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object* v_i_1534_, lean_object* v_inst_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(v_i_1534_, v_inst_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1543_, 0, lean_box(0));
lean_closure_set(v___x_1543_, 1, v_inst_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1544_, lean_object* v_inst_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1546_, 0, lean_box(0));
lean_closure_set(v___x_1546_, 1, v_inst_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(uint32_t v___x_1547_, lean_object* v_s_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_string_push(v_s_1548_, v___x_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object* v___x_1550_, lean_object* v_s_1551_){
_start:
{
uint32_t v___x_2718__boxed_1552_; lean_object* v_res_1553_; 
v___x_2718__boxed_1552_ = lean_unbox_uint32(v___x_1550_);
lean_dec(v___x_1550_);
v_res_1553_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v___x_2718__boxed_1552_, v_s_1551_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed(lean_object* v_inst_1556_, lean_object* v_inst_1557_, lean_object* v___x_1558_, lean_object* v_item_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(v_inst_1556_, v_inst_1557_, v___x_1558_, v_item_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
return v_res_1564_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___f_1567_; 
v___x_1566_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___f_1567_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1567_, 0, v___x_1566_);
return v___f_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1568_, lean_object* v_inst_1569_, lean_object* v___x_1570_, lean_object* v___x_1571_, lean_object* v_a_1572_, lean_object* v_x_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_fst_1579_; lean_object* v_snd_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1620_; 
v_fst_1579_ = lean_ctor_get(v___y_1574_, 0);
v_snd_1580_ = lean_ctor_get(v___y_1574_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___y_1574_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1582_ = v___y_1574_;
v_isShared_1583_ = v_isSharedCheck_1620_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_snd_1580_);
lean_inc(v_fst_1579_);
lean_dec(v___y_1574_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1620_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___f_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; size_t v_sz_1592_; size_t v___x_1593_; lean_object* v___x_2659__overap_1594_; lean_object* v___x_1595_; 
lean_inc(v_snd_1580_);
v___x_1584_ = l_Nat_reprFast(v_snd_1580_);
v___x_1585_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_1586_ = lean_string_append(v___x_1584_, v___x_1585_);
v___x_1587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_1588_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1);
v___x_1589_ = lean_string_utf8_byte_size(v___x_1586_);
v___x_1590_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1588_, v___x_1589_, v___x_1587_);
v___x_1591_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1591_, 0, v_inst_1568_);
lean_closure_set(v___x_1591_, 1, v_inst_1569_);
v_sz_1592_ = lean_array_size(v_a_1572_);
v___x_1593_ = ((size_t)0ULL);
v___x_2659__overap_1594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1570_, v___x_1591_, v_sz_1592_, v___x_1593_, v_a_1572_);
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1575_);
v___x_1595_ = lean_apply_4(v___x_2659__overap_1594_, v___y_1575_, v___y_1576_, v___y_1577_, lean_box(0));
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1611_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1611_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1611_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1600_ = l_Lean_Doc_joinBlocks(v_a_1596_);
lean_dec(v_a_1596_);
v___x_1601_ = l_Lean_Doc_prefixListLines(v___x_1586_, v___x_1590_, v___x_1600_);
v___x_1602_ = lean_array_push(v_fst_1579_, v___x_1601_);
v___x_1603_ = lean_nat_add(v_snd_1580_, v___x_1571_);
lean_dec(v_snd_1580_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 1, v___x_1603_);
lean_ctor_set(v___x_1582_, 0, v___x_1602_);
v___x_1605_ = v___x_1582_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1606_);
v___x_1608_ = v___x_1598_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v___x_1590_);
lean_dec_ref(v___x_1586_);
lean_del_object(v___x_1582_);
lean_dec(v_snd_1580_);
lean_dec(v_fst_1579_);
v_a_1612_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1595_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1595_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v___x_1623_, lean_object* v___x_1624_, lean_object* v_a_1625_, lean_object* v_x_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1621_, v_inst_1622_, v___x_1623_, v___x_1624_, v_a_1625_, v_x_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec(v___x_1624_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1638_, lean_object* v_inst_1639_, lean_object* v___x_1640_, lean_object* v_item_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; lean_object* v_term_1647_; lean_object* v_desc_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1646_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_1647_ = lean_ctor_get(v_item_1641_, 0);
lean_inc_ref(v_term_1647_);
v_desc_1648_ = lean_ctor_get(v_item_1641_, 1);
lean_inc_ref(v_desc_1648_);
lean_dec_ref(v_item_1641_);
v___x_1649_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_term_1647_);
lean_inc_ref(v_inst_1638_);
v___x_1650_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1638_, v___x_1646_, v___x_1649_, v___y_1642_, v___y_1643_, v___y_1644_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; size_t v_sz_1653_; size_t v___x_1654_; lean_object* v___x_2687__overap_1655_; lean_object* v___x_1656_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1652_, 0, v_inst_1638_);
lean_closure_set(v___x_1652_, 1, v_inst_1639_);
v_sz_1653_ = lean_array_size(v_desc_1648_);
v___x_1654_ = ((size_t)0ULL);
lean_inc_ref(v_desc_1648_);
v___x_2687__overap_1655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1640_, v___x_1652_, v_sz_1653_, v___x_1654_, v_desc_1648_);
lean_inc(v___y_1644_);
lean_inc_ref(v___y_1643_);
lean_inc(v___y_1642_);
v___x_1656_ = lean_apply_4(v___x_2687__overap_1655_, v___y_1642_, v___y_1643_, v___y_1644_, lean_box(0));
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1684_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1684_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1684_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___y_1662_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_mk_empty_array_with_capacity(v___x_1669_);
v___x_1671_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_1672_ = lean_unsigned_to_nat(2u);
v___x_1673_ = lean_mk_empty_array_with_capacity(v___x_1672_);
v___x_1674_ = lean_array_push(v___x_1673_, v_a_1651_);
v___x_1675_ = lean_array_push(v___x_1674_, v___x_1671_);
v___x_1676_ = l_Lean_Doc_joinInlines(v___x_1675_);
lean_dec_ref(v___x_1675_);
v___x_1677_ = lean_array_get_size(v_desc_1648_);
lean_dec_ref(v_desc_1648_);
v___x_1678_ = lean_nat_dec_le(v___x_1677_, v___x_1669_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_array_push(v___x_1670_, v___x_1676_);
v___x_1680_ = l_Array_append___redArg(v___x_1679_, v_a_1657_);
lean_dec(v_a_1657_);
v___x_1681_ = l_Lean_Doc_joinBlocks(v___x_1680_);
lean_dec_ref(v___x_1680_);
v___y_1662_ = v___x_1681_;
goto v___jp_1661_;
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec_ref(v___x_1670_);
v___x_1682_ = l_Lean_Doc_joinBlocks(v_a_1657_);
lean_dec(v_a_1657_);
v___x_1683_ = l_Array_append___redArg(v___x_1676_, v___x_1682_);
lean_dec_ref(v___x_1682_);
v___y_1662_ = v___x_1683_;
goto v___jp_1661_;
}
v___jp_1661_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1663_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1664_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1665_ = l_Lean_Doc_prefixListLines(v___x_1663_, v___x_1664_, v___y_1662_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1665_);
v___x_1667_ = v___x_1659_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_a_1651_);
lean_dec_ref(v_desc_1648_);
v_a_1685_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1656_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1656_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_dec_ref(v_desc_1648_);
lean_dec_ref(v___x_1640_);
lean_dec_ref(v_inst_1639_);
lean_dec_ref(v_inst_1638_);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v___x_1695_, lean_object* v_item_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1693_, v_inst_1694_, v___x_1695_, v_item_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v_x_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v___x_1710_; lean_object* v_toApplicative_1711_; lean_object* v_toFunctor_1712_; lean_object* v_toSeq_1713_; lean_object* v_toSeqLeft_1714_; lean_object* v_toSeqRight_1715_; lean_object* v___f_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___x_1720_; lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1710_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1711_ = lean_ctor_get(v___x_1710_, 0);
v_toFunctor_1712_ = lean_ctor_get(v_toApplicative_1711_, 0);
v_toSeq_1713_ = lean_ctor_get(v_toApplicative_1711_, 2);
v_toSeqLeft_1714_ = lean_ctor_get(v_toApplicative_1711_, 3);
v_toSeqRight_1715_ = lean_ctor_get(v_toApplicative_1711_, 4);
v___f_1716_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1717_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1712_, 2);
v___f_1718_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1718_, 0, v_toFunctor_1712_);
v___f_1719_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1719_, 0, v_toFunctor_1712_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___f_1718_);
lean_ctor_set(v___x_1720_, 1, v___f_1719_);
lean_inc(v_toSeqRight_1715_);
v___f_1721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1721_, 0, v_toSeqRight_1715_);
lean_inc(v_toSeqLeft_1714_);
v___f_1722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1722_, 0, v_toSeqLeft_1714_);
lean_inc(v_toSeq_1713_);
v___f_1723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1723_, 0, v_toSeq_1713_);
v___x_1724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1720_);
lean_ctor_set(v___x_1724_, 1, v___f_1716_);
lean_ctor_set(v___x_1724_, 2, v___f_1723_);
lean_ctor_set(v___x_1724_, 3, v___f_1722_);
lean_ctor_set(v___x_1724_, 4, v___f_1721_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
lean_ctor_set(v___x_1725_, 1, v___f_1717_);
v___x_1726_ = l_StateRefT_x27_instMonad___redArg(v___x_1725_);
switch(lean_obj_tag(v_x_1705_))
{
case 0:
{
lean_object* v_contents_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref(v___x_1726_);
lean_dec_ref(v_inst_1704_);
v_contents_1727_ = lean_ctor_get(v_x_1705_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_x_1705_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1729_ = v_x_1705_;
v_isShared_1730_ = v_isSharedCheck_1736_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_contents_1727_);
lean_dec(v_x_1705_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1736_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1731_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 9);
v___x_1733_ = v___x_1729_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_contents_1727_);
v___x_1733_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; 
v___x_1734_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1703_, v___x_1731_, v___x_1733_, v_a_1706_, v_a_1707_, v_a_1708_);
return v___x_1734_;
}
}
}
case 1:
{
lean_object* v_content_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1745_; 
lean_dec_ref(v___x_1726_);
lean_dec_ref(v_inst_1704_);
lean_dec_ref(v_inst_1703_);
v_content_1737_ = lean_ctor_get(v_x_1705_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_x_1705_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1739_ = v_x_1705_;
v_isShared_1740_ = v_isSharedCheck_1745_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_content_1737_);
lean_dec(v_x_1705_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1745_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1741_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_1737_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set_tag(v___x_1739_, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1741_);
v___x_1743_ = v___x_1739_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
case 2:
{
lean_object* v_items_1746_; lean_object* v___f_1747_; size_t v_sz_1748_; size_t v___x_1749_; lean_object* v___x_2582__overap_1750_; lean_object* v___x_1751_; 
v_items_1746_ = lean_ctor_get(v_x_1705_, 0);
lean_inc_ref(v_items_1746_);
lean_dec_ref_known(v_x_1705_, 1);
lean_inc_ref(v___x_1726_);
v___f_1747_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1747_, 0, v_inst_1703_);
lean_closure_set(v___f_1747_, 1, v_inst_1704_);
lean_closure_set(v___f_1747_, 2, v___x_1726_);
v_sz_1748_ = lean_array_size(v_items_1746_);
v___x_1749_ = ((size_t)0ULL);
v___x_2582__overap_1750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1726_, v___f_1747_, v_sz_1748_, v___x_1749_, v_items_1746_);
lean_inc(v_a_1708_);
lean_inc_ref(v_a_1707_);
lean_inc(v_a_1706_);
v___x_1751_ = lean_apply_4(v___x_2582__overap_1750_, v_a_1706_, v_a_1707_, v_a_1708_, lean_box(0));
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1760_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1760_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1760_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1756_ = l_Lean_Doc_joinBlocks(v_a_1752_);
lean_dec(v_a_1752_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1756_);
v___x_1758_ = v___x_1754_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1751_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1751_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
case 3:
{
lean_object* v_start_1769_; lean_object* v_items_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1806_; 
v_start_1769_ = lean_ctor_get(v_x_1705_, 0);
v_items_1770_ = lean_ctor_get(v_x_1705_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_x_1705_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1772_ = v_x_1705_;
v_isShared_1773_ = v_isSharedCheck_1806_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_items_1770_);
lean_inc(v_start_1769_);
lean_dec(v_x_1705_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1806_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v_out_1774_; lean_object* v___x_1775_; lean_object* v___f_1776_; lean_object* v___y_1778_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v_out_1774_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1775_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_1726_);
v___f_1776_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1776_, 0, v_inst_1703_);
lean_closure_set(v___f_1776_, 1, v_inst_1704_);
lean_closure_set(v___f_1776_, 2, v___x_1726_);
lean_closure_set(v___f_1776_, 3, v___x_1775_);
v___x_1804_ = l_Int_toNat(v_start_1769_);
lean_dec(v_start_1769_);
v___x_1805_ = lean_nat_dec_le(v___x_1775_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_dec(v___x_1804_);
v___y_1778_ = v___x_1775_;
goto v___jp_1777_;
}
else
{
v___y_1778_ = v___x_1804_;
goto v___jp_1777_;
}
v___jp_1777_:
{
lean_object* v___x_1780_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 0);
lean_ctor_set(v___x_1772_, 1, v___y_1778_);
lean_ctor_set(v___x_1772_, 0, v_out_1774_);
v___x_1780_ = v___x_1772_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_out_1774_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v___y_1778_);
v___x_1780_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
size_t v_sz_1781_; size_t v___x_1782_; lean_object* v___x_2398__overap_1783_; lean_object* v___x_1784_; 
v_sz_1781_ = lean_array_size(v_items_1770_);
v___x_1782_ = ((size_t)0ULL);
v___x_2398__overap_1783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1726_, v_items_1770_, v___f_1776_, v_sz_1781_, v___x_1782_, v___x_1780_);
lean_inc(v_a_1708_);
lean_inc_ref(v_a_1707_);
lean_inc(v_a_1706_);
v___x_1784_ = lean_apply_4(v___x_2398__overap_1783_, v_a_1706_, v_a_1707_, v_a_1708_, lean_box(0));
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1794_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1794_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1794_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v_fst_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v_fst_1789_ = lean_ctor_get(v_a_1785_, 0);
lean_inc(v_fst_1789_);
lean_dec(v_a_1785_);
v___x_1790_ = l_Lean_Doc_joinBlocks(v_fst_1789_);
lean_dec(v_fst_1789_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1790_);
v___x_1792_ = v___x_1787_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v_a_1795_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1784_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1784_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_1807_; lean_object* v___f_1808_; size_t v_sz_1809_; size_t v___x_1810_; lean_object* v___x_2588__overap_1811_; lean_object* v___x_1812_; 
v_items_1807_ = lean_ctor_get(v_x_1705_, 0);
lean_inc_ref(v_items_1807_);
lean_dec_ref_known(v_x_1705_, 1);
lean_inc_ref(v___x_1726_);
v___f_1808_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 8, 3);
lean_closure_set(v___f_1808_, 0, v_inst_1703_);
lean_closure_set(v___f_1808_, 1, v_inst_1704_);
lean_closure_set(v___f_1808_, 2, v___x_1726_);
v_sz_1809_ = lean_array_size(v_items_1807_);
v___x_1810_ = ((size_t)0ULL);
v___x_2588__overap_1811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1726_, v___f_1808_, v_sz_1809_, v___x_1810_, v_items_1807_);
lean_inc(v_a_1708_);
lean_inc_ref(v_a_1707_);
lean_inc(v_a_1706_);
v___x_1812_ = lean_apply_4(v___x_2588__overap_1811_, v_a_1706_, v_a_1707_, v_a_1708_, lean_box(0));
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1821_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1821_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1821_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = l_Lean_Doc_joinBlocks(v_a_1813_);
lean_dec(v_a_1813_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1812_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1812_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
case 5:
{
lean_object* v_items_1830_; lean_object* v___x_1831_; size_t v_sz_1832_; size_t v___x_1833_; lean_object* v___x_2591__overap_1834_; lean_object* v___x_1835_; 
v_items_1830_ = lean_ctor_get(v_x_1705_, 0);
lean_inc_ref(v_items_1830_);
lean_dec_ref_known(v_x_1705_, 1);
v___x_1831_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1831_, 0, v_inst_1703_);
lean_closure_set(v___x_1831_, 1, v_inst_1704_);
v_sz_1832_ = lean_array_size(v_items_1830_);
v___x_1833_ = ((size_t)0ULL);
v___x_2591__overap_1834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1726_, v___x_1831_, v_sz_1832_, v___x_1833_, v_items_1830_);
lean_inc(v_a_1708_);
lean_inc_ref(v_a_1707_);
lean_inc(v_a_1706_);
v___x_1835_ = lean_apply_4(v___x_2591__overap_1834_, v_a_1706_, v_a_1707_, v_a_1708_, lean_box(0));
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1846_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1840_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_1841_ = l_Lean_Doc_joinBlocks(v_a_1836_);
lean_dec(v_a_1836_);
v___x_1842_ = l_Lean_Doc_prefixLines(v___x_1840_, v___x_1841_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1842_);
v___x_1844_ = v___x_1838_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_a_1847_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1835_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1835_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
case 6:
{
lean_object* v_content_1855_; lean_object* v___x_1856_; size_t v_sz_1857_; size_t v___x_1858_; lean_object* v___x_2594__overap_1859_; lean_object* v___x_1860_; 
v_content_1855_ = lean_ctor_get(v_x_1705_, 0);
lean_inc_ref(v_content_1855_);
lean_dec_ref_known(v_x_1705_, 1);
v___x_1856_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1856_, 0, v_inst_1703_);
lean_closure_set(v___x_1856_, 1, v_inst_1704_);
v_sz_1857_ = lean_array_size(v_content_1855_);
v___x_1858_ = ((size_t)0ULL);
v___x_2594__overap_1859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1726_, v___x_1856_, v_sz_1857_, v___x_1858_, v_content_1855_);
lean_inc(v_a_1708_);
lean_inc_ref(v_a_1707_);
lean_inc(v_a_1706_);
v___x_1860_ = lean_apply_4(v___x_2594__overap_1859_, v_a_1706_, v_a_1707_, v_a_1708_, lean_box(0));
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1869_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = l_Lean_Doc_joinBlocks(v_a_1861_);
lean_dec(v_a_1861_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1865_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_a_1870_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1860_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1860_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
default: 
{
lean_object* v_container_1878_; lean_object* v_content_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec_ref(v___x_1726_);
v_container_1878_ = lean_ctor_get(v_x_1705_, 0);
lean_inc(v_container_1878_);
v_content_1879_ = lean_ctor_get(v_x_1705_, 1);
lean_inc_ref(v_content_1879_);
lean_dec_ref_known(v_x_1705_, 2);
v___x_1880_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc_ref(v_inst_1703_);
v___x_1881_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed), 8, 3);
lean_closure_set(v___x_1881_, 0, lean_box(0));
lean_closure_set(v___x_1881_, 1, v_inst_1703_);
lean_closure_set(v___x_1881_, 2, v___x_1880_);
lean_inc_ref(v_inst_1704_);
v___x_1882_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1882_, 0, v_inst_1703_);
lean_closure_set(v___x_1882_, 1, v_inst_1704_);
lean_inc(v_a_1708_);
lean_inc_ref(v_a_1707_);
lean_inc(v_a_1706_);
v___x_1883_ = lean_apply_8(v_inst_1704_, v___x_1881_, v___x_1882_, v_container_1878_, v_content_1879_, v_a_1706_, v_a_1707_, v_a_1708_, lean_box(0));
return v___x_1883_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed(lean_object* v_inst_1884_, lean_object* v_inst_1885_, lean_object* v_x_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1884_, v_inst_1885_, v_x_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v_inst_1892_, lean_object* v_inst_1893_, lean_object* v___x_1894_, lean_object* v_item_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; size_t v_sz_1901_; size_t v___x_1902_; lean_object* v___x_2626__overap_1903_; lean_object* v___x_1904_; 
v___x_1900_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1900_, 0, v_inst_1892_);
lean_closure_set(v___x_1900_, 1, v_inst_1893_);
v_sz_1901_ = lean_array_size(v_item_1895_);
v___x_1902_ = ((size_t)0ULL);
v___x_2626__overap_1903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1894_, v___x_1900_, v_sz_1901_, v___x_1902_, v_item_1895_);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
lean_inc(v___y_1896_);
v___x_1904_ = lean_apply_4(v___x_2626__overap_1903_, v___y_1896_, v___y_1897_, v___y_1898_, lean_box(0));
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1916_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1916_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1916_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1909_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1910_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1911_ = l_Lean_Doc_joinBlocks(v_a_1905_);
lean_dec(v_a_1905_);
v___x_1912_ = l_Lean_Doc_prefixListLines(v___x_1909_, v___x_1910_, v___x_1911_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1912_);
v___x_1914_ = v___x_1907_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
v_a_1917_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1904_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1904_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1925_, lean_object* v_b_1926_, lean_object* v_inst_1927_, lean_object* v_inst_1928_, lean_object* v_x_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1927_, v_inst_1928_, v_x_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object* v_i_1935_, lean_object* v_b_1936_, lean_object* v_inst_1937_, lean_object* v_inst_1938_, lean_object* v_x_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(v_i_1935_, v_b_1936_, v_inst_1937_, v_inst_1938_, v_x_1939_, v_a_1940_, v_a_1941_, v_a_1942_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1945_, lean_object* v_inst_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1945_, v_inst_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1953_, v_inst_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1961_, lean_object* v_b_1962_, lean_object* v_inst_1963_, lean_object* v_inst_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1963_, v_inst_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1971_, lean_object* v_b_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1971_, v_b_1972_, v_inst_1973_, v_inst_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1981_, lean_object* v_inst_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_1983_, 0, lean_box(0));
lean_closure_set(v___x_1983_, 1, lean_box(0));
lean_closure_set(v___x_1983_, 2, v_inst_1981_);
lean_closure_set(v___x_1983_, 3, v_inst_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1984_, lean_object* v_b_1985_, lean_object* v_inst_1986_, lean_object* v_inst_1987_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_1988_, 0, lean_box(0));
lean_closure_set(v___x_1988_, 1, lean_box(0));
lean_closure_set(v___x_1988_, 2, v_inst_1986_);
lean_closure_set(v___x_1988_, 3, v_inst_1987_);
return v___x_1988_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = 35;
v___x_1990_ = lean_box_uint32(v___x_1989_);
return v___x_1990_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___f_1992_; 
v___x_1991_ = l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1992_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1992_, 0, v___x_1991_);
return v___f_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1993_, lean_object* v_inst_1994_, lean_object* v_level_1995_, lean_object* v_part_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_Doc_partMarkdown___redArg(v_inst_1993_, v_inst_1994_, v_level_1995_, v_part_1996_, v_a_1997_, v_a_1998_, v_a_1999_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
lean_dec(v_a_1997_);
lean_dec(v_level_1995_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg(lean_object* v_inst_2002_, lean_object* v_inst_2003_, lean_object* v_level_2004_, lean_object* v_part_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___x_2010_; lean_object* v_toApplicative_2011_; lean_object* v_toFunctor_2012_; lean_object* v_toSeq_2013_; lean_object* v_toSeqLeft_2014_; lean_object* v_toSeqRight_2015_; lean_object* v___f_2016_; lean_object* v___f_2017_; lean_object* v___f_2018_; lean_object* v___f_2019_; lean_object* v___x_2020_; lean_object* v___f_2021_; lean_object* v___f_2022_; lean_object* v___f_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v_title_2027_; lean_object* v_content_2028_; lean_object* v_subParts_2029_; lean_object* v___x_2030_; size_t v_sz_2031_; size_t v___x_2032_; lean_object* v___x_684__overap_2033_; lean_object* v___x_2034_; 
v___x_2010_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2011_ = lean_ctor_get(v___x_2010_, 0);
v_toFunctor_2012_ = lean_ctor_get(v_toApplicative_2011_, 0);
v_toSeq_2013_ = lean_ctor_get(v_toApplicative_2011_, 2);
v_toSeqLeft_2014_ = lean_ctor_get(v_toApplicative_2011_, 3);
v_toSeqRight_2015_ = lean_ctor_get(v_toApplicative_2011_, 4);
v___f_2016_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2017_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2012_, 2);
v___f_2018_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2018_, 0, v_toFunctor_2012_);
v___f_2019_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2019_, 0, v_toFunctor_2012_);
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___f_2018_);
lean_ctor_set(v___x_2020_, 1, v___f_2019_);
lean_inc(v_toSeqRight_2015_);
v___f_2021_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2021_, 0, v_toSeqRight_2015_);
lean_inc(v_toSeqLeft_2014_);
v___f_2022_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2022_, 0, v_toSeqLeft_2014_);
lean_inc(v_toSeq_2013_);
v___f_2023_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2023_, 0, v_toSeq_2013_);
v___x_2024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2020_);
lean_ctor_set(v___x_2024_, 1, v___f_2016_);
lean_ctor_set(v___x_2024_, 2, v___f_2023_);
lean_ctor_set(v___x_2024_, 3, v___f_2022_);
lean_ctor_set(v___x_2024_, 4, v___f_2021_);
v___x_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
lean_ctor_set(v___x_2025_, 1, v___f_2017_);
v___x_2026_ = l_StateRefT_x27_instMonad___redArg(v___x_2025_);
v_title_2027_ = lean_ctor_get(v_part_2005_, 0);
lean_inc_ref(v_title_2027_);
v_content_2028_ = lean_ctor_get(v_part_2005_, 3);
lean_inc_ref(v_content_2028_);
v_subParts_2029_ = lean_ctor_get(v_part_2005_, 4);
lean_inc_ref(v_subParts_2029_);
lean_dec_ref(v_part_2005_);
lean_inc_ref(v_inst_2002_);
v___x_2030_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_2030_, 0, lean_box(0));
lean_closure_set(v___x_2030_, 1, v_inst_2002_);
v_sz_2031_ = lean_array_size(v_title_2027_);
v___x_2032_ = ((size_t)0ULL);
lean_inc_ref(v___x_2026_);
v___x_684__overap_2033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2026_, v___x_2030_, v_sz_2031_, v___x_2032_, v_title_2027_);
lean_inc(v_a_2008_);
lean_inc_ref(v_a_2007_);
lean_inc(v_a_2006_);
v___x_2034_ = lean_apply_4(v___x_684__overap_2033_, v_a_2006_, v_a_2007_, v_a_2008_, lean_box(0));
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; lean_object* v___f_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; size_t v_sz_2049_; lean_object* v___x_687__overap_2050_; lean_object* v___x_2051_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_2037_ = lean_obj_once(&l_Lean_Doc_partMarkdown___redArg___closed__0, &l_Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_partMarkdown___redArg___closed__0);
v___x_2038_ = lean_unsigned_to_nat(1u);
v___x_2039_ = lean_nat_add(v_level_2004_, v___x_2038_);
lean_inc(v___x_2039_);
v___x_2040_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_2037_, v___x_2039_, v___x_2036_);
v___x_2041_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_2042_ = lean_string_append(v___x_2040_, v___x_2041_);
v___x_2043_ = lean_mk_empty_array_with_capacity(v___x_2038_);
lean_inc_ref_n(v___x_2043_, 2);
v___x_2044_ = lean_array_push(v___x_2043_, v___x_2042_);
v___x_2045_ = lean_array_push(v___x_2043_, v___x_2044_);
v___x_2046_ = l_Array_append___redArg(v___x_2045_, v_a_2035_);
lean_dec(v_a_2035_);
v___x_2047_ = l_Lean_Doc_joinInlines(v___x_2046_);
lean_dec_ref(v___x_2046_);
lean_inc_ref(v_inst_2003_);
lean_inc_ref(v_inst_2002_);
v___x_2048_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_2048_, 0, lean_box(0));
lean_closure_set(v___x_2048_, 1, lean_box(0));
lean_closure_set(v___x_2048_, 2, v_inst_2002_);
lean_closure_set(v___x_2048_, 3, v_inst_2003_);
v_sz_2049_ = lean_array_size(v_content_2028_);
lean_inc_ref(v___x_2026_);
v___x_687__overap_2050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2026_, v___x_2048_, v_sz_2049_, v___x_2032_, v_content_2028_);
lean_inc(v_a_2008_);
lean_inc_ref(v_a_2007_);
lean_inc(v_a_2006_);
v___x_2051_ = lean_apply_4(v___x_687__overap_2050_, v_a_2006_, v_a_2007_, v_a_2008_, lean_box(0));
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; size_t v_sz_2054_; lean_object* v___x_690__overap_2055_; lean_object* v___x_2056_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2053_ = lean_alloc_closure((void*)(l_Lean_Doc_partMarkdown___redArg___boxed), 8, 3);
lean_closure_set(v___x_2053_, 0, v_inst_2002_);
lean_closure_set(v___x_2053_, 1, v_inst_2003_);
lean_closure_set(v___x_2053_, 2, v___x_2039_);
v_sz_2054_ = lean_array_size(v_subParts_2029_);
v___x_690__overap_2055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2026_, v___x_2053_, v_sz_2054_, v___x_2032_, v_subParts_2029_);
lean_inc(v_a_2008_);
lean_inc_ref(v_a_2007_);
lean_inc(v_a_2006_);
v___x_2056_ = lean_apply_4(v___x_690__overap_2055_, v_a_2006_, v_a_2007_, v_a_2008_, lean_box(0));
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2068_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2068_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2068_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2061_ = lean_array_push(v___x_2043_, v___x_2047_);
v___x_2062_ = l_Array_append___redArg(v___x_2061_, v_a_2052_);
lean_dec(v_a_2052_);
v___x_2063_ = l_Array_append___redArg(v___x_2062_, v_a_2057_);
lean_dec(v_a_2057_);
v___x_2064_ = l_Lean_Doc_joinBlocks(v___x_2063_);
lean_dec_ref(v___x_2063_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2064_);
v___x_2066_ = v___x_2059_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v_a_2052_);
lean_dec_ref(v___x_2047_);
lean_dec_ref(v___x_2043_);
v_a_2069_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2056_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2056_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref(v___x_2047_);
lean_dec_ref(v___x_2043_);
lean_dec(v___x_2039_);
lean_dec_ref(v_subParts_2029_);
lean_dec_ref(v___x_2026_);
lean_dec_ref(v_inst_2003_);
lean_dec_ref(v_inst_2002_);
v_a_2077_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2051_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2051_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v_subParts_2029_);
lean_dec_ref(v_content_2028_);
lean_dec_ref(v___x_2026_);
lean_dec_ref(v_inst_2003_);
lean_dec_ref(v_inst_2002_);
v_a_2085_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2034_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2034_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown(lean_object* v_i_2093_, lean_object* v_b_2094_, lean_object* v_p_2095_, lean_object* v_inst_2096_, lean_object* v_inst_2097_, lean_object* v_level_2098_, lean_object* v_part_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2096_, v_inst_2097_, v_level_2098_, v_part_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___boxed(lean_object* v_i_2105_, lean_object* v_b_2106_, lean_object* v_p_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_level_2110_, lean_object* v_part_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_Doc_partMarkdown(v_i_2105_, v_b_2106_, v_p_2107_, v_inst_2108_, v_inst_2109_, v_level_2110_, v_part_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
lean_dec(v_level_2110_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_part_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_unsigned_to_nat(0u);
v___x_2125_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2117_, v_inst_2118_, v___x_2124_, v_part_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_2126_, lean_object* v_inst_2127_, lean_object* v_part_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_2126_, v_inst_2127_, v_part_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_2134_, lean_object* v_inst_2135_){
_start:
{
lean_object* v___f_2136_; 
v___f_2136_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2136_, 0, v_inst_2134_);
lean_closure_set(v___f_2136_, 1, v_inst_2135_);
return v___f_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_2137_, lean_object* v_b_2138_, lean_object* v_p_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_){
_start:
{
lean_object* v___f_2142_; 
v___f_2142_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2142_, 0, v_inst_2140_);
lean_closure_set(v___f_2142_, 1, v_inst_2141_);
return v___f_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg(lean_object* v_inst_2143_, lean_object* v_f_2144_, lean_object* v_go_2145_, lean_object* v_val_2146_, lean_object* v_content_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v___x_2152_; lean_object* v_toApplicative_2153_; lean_object* v_toFunctor_2154_; lean_object* v_toSeq_2155_; lean_object* v_toSeqLeft_2156_; lean_object* v_toSeqRight_2157_; lean_object* v___f_2158_; lean_object* v___f_2159_; lean_object* v___f_2160_; lean_object* v___f_2161_; lean_object* v___x_2162_; lean_object* v___f_2163_; lean_object* v___f_2164_; lean_object* v___f_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2152_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2153_ = lean_ctor_get(v___x_2152_, 0);
v_toFunctor_2154_ = lean_ctor_get(v_toApplicative_2153_, 0);
v_toSeq_2155_ = lean_ctor_get(v_toApplicative_2153_, 2);
v_toSeqLeft_2156_ = lean_ctor_get(v_toApplicative_2153_, 3);
v_toSeqRight_2157_ = lean_ctor_get(v_toApplicative_2153_, 4);
v___f_2158_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2159_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2154_, 2);
v___f_2160_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2160_, 0, v_toFunctor_2154_);
v___f_2161_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2161_, 0, v_toFunctor_2154_);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___f_2160_);
lean_ctor_set(v___x_2162_, 1, v___f_2161_);
lean_inc(v_toSeqRight_2157_);
v___f_2163_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2163_, 0, v_toSeqRight_2157_);
lean_inc(v_toSeqLeft_2156_);
v___f_2164_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2164_, 0, v_toSeqLeft_2156_);
lean_inc(v_toSeq_2155_);
v___f_2165_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2165_, 0, v_toSeq_2155_);
v___x_2166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2162_);
lean_ctor_set(v___x_2166_, 1, v___f_2158_);
lean_ctor_set(v___x_2166_, 2, v___f_2165_);
lean_ctor_set(v___x_2166_, 3, v___f_2164_);
lean_ctor_set(v___x_2166_, 4, v___f_2163_);
v___x_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v___f_2159_);
v___x_2168_ = l_StateRefT_x27_instMonad___redArg(v___x_2167_);
v___x_2169_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2146_, v_inst_2143_);
if (lean_obj_tag(v___x_2169_) == 0)
{
size_t v_sz_2170_; size_t v___x_2171_; lean_object* v___x_288__overap_2172_; lean_object* v___x_2173_; 
lean_dec_ref(v_f_2144_);
v_sz_2170_ = lean_array_size(v_content_2147_);
v___x_2171_ = ((size_t)0ULL);
v___x_288__overap_2172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2168_, v_go_2145_, v_sz_2170_, v___x_2171_, v_content_2147_);
lean_inc(v_a_2150_);
lean_inc_ref(v_a_2149_);
lean_inc(v_a_2148_);
v___x_2173_ = lean_apply_4(v___x_288__overap_2172_, v_a_2148_, v_a_2149_, v_a_2150_, lean_box(0));
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2182_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2182_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2182_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
v___x_2178_ = l_Lean_Doc_joinInlines(v_a_2174_);
lean_dec(v_a_2174_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2178_);
v___x_2180_ = v___x_2176_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
v_a_2183_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2173_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2173_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
else
{
lean_object* v_val_2191_; lean_object* v___x_2192_; 
lean_dec_ref(v___x_2168_);
v_val_2191_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_val_2191_);
lean_dec_ref_known(v___x_2169_, 1);
lean_inc(v_a_2150_);
lean_inc_ref(v_a_2149_);
lean_inc(v_a_2148_);
v___x_2192_ = lean_apply_7(v_f_2144_, v_go_2145_, v_val_2191_, v_content_2147_, v_a_2148_, v_a_2149_, v_a_2150_, lean_box(0));
return v___x_2192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg___boxed(lean_object* v_inst_2193_, lean_object* v_f_2194_, lean_object* v_go_2195_, lean_object* v_val_2196_, lean_object* v_content_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2193_, v_f_2194_, v_go_2195_, v_val_2196_, v_content_2197_, v_a_2198_, v_a_2199_, v_a_2200_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec(v_val_2196_);
lean_dec(v_inst_2193_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer(lean_object* v_00_u03b1_2203_, lean_object* v_inst_2204_, lean_object* v_f_2205_, lean_object* v_go_2206_, lean_object* v_val_2207_, lean_object* v_content_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2204_, v_f_2205_, v_go_2206_, v_val_2207_, v_content_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___boxed(lean_object* v_00_u03b1_2214_, lean_object* v_inst_2215_, lean_object* v_f_2216_, lean_object* v_go_2217_, lean_object* v_val_2218_, lean_object* v_content_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_Doc_mkInlineMdRenderer(v_00_u03b1_2214_, v_inst_2215_, v_f_2216_, v_go_2217_, v_val_2218_, v_content_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec(v_val_2218_);
lean_dec(v_inst_2215_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg(lean_object* v_inst_2225_, lean_object* v_f_2226_, lean_object* v_goI_2227_, lean_object* v_goB_2228_, lean_object* v_val_2229_, lean_object* v_content_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v___x_2235_; lean_object* v_toApplicative_2236_; lean_object* v_toFunctor_2237_; lean_object* v_toSeq_2238_; lean_object* v_toSeqLeft_2239_; lean_object* v_toSeqRight_2240_; lean_object* v___f_2241_; lean_object* v___f_2242_; lean_object* v___f_2243_; lean_object* v___f_2244_; lean_object* v___x_2245_; lean_object* v___f_2246_; lean_object* v___f_2247_; lean_object* v___f_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2235_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2236_ = lean_ctor_get(v___x_2235_, 0);
v_toFunctor_2237_ = lean_ctor_get(v_toApplicative_2236_, 0);
v_toSeq_2238_ = lean_ctor_get(v_toApplicative_2236_, 2);
v_toSeqLeft_2239_ = lean_ctor_get(v_toApplicative_2236_, 3);
v_toSeqRight_2240_ = lean_ctor_get(v_toApplicative_2236_, 4);
v___f_2241_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2242_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2237_, 2);
v___f_2243_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2243_, 0, v_toFunctor_2237_);
v___f_2244_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2244_, 0, v_toFunctor_2237_);
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___f_2243_);
lean_ctor_set(v___x_2245_, 1, v___f_2244_);
lean_inc(v_toSeqRight_2240_);
v___f_2246_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2246_, 0, v_toSeqRight_2240_);
lean_inc(v_toSeqLeft_2239_);
v___f_2247_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2247_, 0, v_toSeqLeft_2239_);
lean_inc(v_toSeq_2238_);
v___f_2248_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2248_, 0, v_toSeq_2238_);
v___x_2249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2245_);
lean_ctor_set(v___x_2249_, 1, v___f_2241_);
lean_ctor_set(v___x_2249_, 2, v___f_2248_);
lean_ctor_set(v___x_2249_, 3, v___f_2247_);
lean_ctor_set(v___x_2249_, 4, v___f_2246_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v___f_2242_);
v___x_2251_ = l_StateRefT_x27_instMonad___redArg(v___x_2250_);
v___x_2252_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2229_, v_inst_2225_);
if (lean_obj_tag(v___x_2252_) == 0)
{
size_t v_sz_2253_; size_t v___x_2254_; lean_object* v___x_288__overap_2255_; lean_object* v___x_2256_; 
lean_dec_ref(v_goI_2227_);
lean_dec_ref(v_f_2226_);
v_sz_2253_ = lean_array_size(v_content_2230_);
v___x_2254_ = ((size_t)0ULL);
v___x_288__overap_2255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2251_, v_goB_2228_, v_sz_2253_, v___x_2254_, v_content_2230_);
lean_inc(v_a_2233_);
lean_inc_ref(v_a_2232_);
lean_inc(v_a_2231_);
v___x_2256_ = lean_apply_4(v___x_288__overap_2255_, v_a_2231_, v_a_2232_, v_a_2233_, lean_box(0));
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2265_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2265_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2265_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2261_ = l_Lean_Doc_joinBlocks(v_a_2257_);
lean_dec(v_a_2257_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2261_);
v___x_2263_ = v___x_2259_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
v_a_2266_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2256_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2256_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
lean_object* v_val_2274_; lean_object* v___x_2275_; 
lean_dec_ref(v___x_2251_);
v_val_2274_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_val_2274_);
lean_dec_ref_known(v___x_2252_, 1);
lean_inc(v_a_2233_);
lean_inc_ref(v_a_2232_);
lean_inc(v_a_2231_);
v___x_2275_ = lean_apply_8(v_f_2226_, v_goI_2227_, v_goB_2228_, v_val_2274_, v_content_2230_, v_a_2231_, v_a_2232_, v_a_2233_, lean_box(0));
return v___x_2275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg___boxed(lean_object* v_inst_2276_, lean_object* v_f_2277_, lean_object* v_goI_2278_, lean_object* v_goB_2279_, lean_object* v_val_2280_, lean_object* v_content_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2276_, v_f_2277_, v_goI_2278_, v_goB_2279_, v_val_2280_, v_content_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec(v_val_2280_);
lean_dec(v_inst_2276_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer(lean_object* v_00_u03b1_2287_, lean_object* v_inst_2288_, lean_object* v_f_2289_, lean_object* v_goI_2290_, lean_object* v_goB_2291_, lean_object* v_val_2292_, lean_object* v_content_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2288_, v_f_2289_, v_goI_2290_, v_goB_2291_, v_val_2292_, v_content_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___boxed(lean_object* v_00_u03b1_2299_, lean_object* v_inst_2300_, lean_object* v_f_2301_, lean_object* v_goI_2302_, lean_object* v_goB_2303_, lean_object* v_val_2304_, lean_object* v_content_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Doc_mkBlockMdRenderer(v_00_u03b1_2299_, v_inst_2300_, v_f_2301_, v_goI_2302_, v_goB_2303_, v_val_2304_, v_content_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec(v_a_2306_);
lean_dec(v_val_2304_);
lean_dec(v_inst_2300_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(lean_object* v_as_2315_, size_t v_i_2316_, size_t v_stop_2317_, lean_object* v_b_2318_){
_start:
{
uint8_t v___x_2319_; 
v___x_2319_ = lean_usize_dec_eq(v_i_2316_, v_stop_2317_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; lean_object* v_fst_2321_; lean_object* v_snd_2322_; lean_object* v___x_2323_; size_t v___x_2324_; size_t v___x_2325_; 
v___x_2320_ = lean_array_uget_borrowed(v_as_2315_, v_i_2316_);
v_fst_2321_ = lean_ctor_get(v___x_2320_, 0);
v_snd_2322_ = lean_ctor_get(v___x_2320_, 1);
lean_inc(v_snd_2322_);
lean_inc(v_fst_2321_);
v___x_2323_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2321_, v_snd_2322_, v_b_2318_);
v___x_2324_ = ((size_t)1ULL);
v___x_2325_ = lean_usize_add(v_i_2316_, v___x_2324_);
v_i_2316_ = v___x_2325_;
v_b_2318_ = v___x_2323_;
goto _start;
}
else
{
return v_b_2318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0___boxed(lean_object* v_as_2327_, lean_object* v_i_2328_, lean_object* v_stop_2329_, lean_object* v_b_2330_){
_start:
{
size_t v_i_boxed_2331_; size_t v_stop_boxed_2332_; lean_object* v_res_2333_; 
v_i_boxed_2331_ = lean_unbox_usize(v_i_2328_);
lean_dec(v_i_2328_);
v_stop_boxed_2332_ = lean_unbox_usize(v_stop_2329_);
lean_dec(v_stop_2329_);
v_res_2333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v_as_2327_, v_i_boxed_2331_, v_stop_boxed_2332_, v_b_2330_);
lean_dec_ref(v_as_2327_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(lean_object* v_as_2334_, size_t v_i_2335_, size_t v_stop_2336_, lean_object* v_b_2337_){
_start:
{
lean_object* v___y_2339_; uint8_t v___x_2343_; 
v___x_2343_ = lean_usize_dec_eq(v_i_2335_, v_stop_2336_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2344_ = lean_array_uget_borrowed(v_as_2334_, v_i_2335_);
v___x_2345_ = lean_unsigned_to_nat(0u);
v___x_2346_ = lean_array_get_size(v___x_2344_);
v___x_2347_ = lean_nat_dec_lt(v___x_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
v___y_2339_ = v_b_2337_;
goto v___jp_2338_;
}
else
{
uint8_t v___x_2348_; 
v___x_2348_ = lean_nat_dec_le(v___x_2346_, v___x_2346_);
if (v___x_2348_ == 0)
{
if (v___x_2347_ == 0)
{
v___y_2339_ = v_b_2337_;
goto v___jp_2338_;
}
else
{
size_t v___x_2349_; size_t v___x_2350_; lean_object* v___x_2351_; 
v___x_2349_ = ((size_t)0ULL);
v___x_2350_ = lean_usize_of_nat(v___x_2346_);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2344_, v___x_2349_, v___x_2350_, v_b_2337_);
v___y_2339_ = v___x_2351_;
goto v___jp_2338_;
}
}
else
{
size_t v___x_2352_; size_t v___x_2353_; lean_object* v___x_2354_; 
v___x_2352_ = ((size_t)0ULL);
v___x_2353_ = lean_usize_of_nat(v___x_2346_);
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2344_, v___x_2352_, v___x_2353_, v_b_2337_);
v___y_2339_ = v___x_2354_;
goto v___jp_2338_;
}
}
}
else
{
return v_b_2337_;
}
v___jp_2338_:
{
size_t v___x_2340_; size_t v___x_2341_; 
v___x_2340_ = ((size_t)1ULL);
v___x_2341_ = lean_usize_add(v_i_2335_, v___x_2340_);
v_i_2335_ = v___x_2341_;
v_b_2337_ = v___y_2339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1___boxed(lean_object* v_as_2355_, lean_object* v_i_2356_, lean_object* v_stop_2357_, lean_object* v_b_2358_){
_start:
{
size_t v_i_boxed_2359_; size_t v_stop_boxed_2360_; lean_object* v_res_2361_; 
v_i_boxed_2359_ = lean_unbox_usize(v_i_2356_);
lean_dec(v_i_2356_);
v_stop_boxed_2360_ = lean_unbox_usize(v_stop_2357_);
lean_dec(v_stop_2357_);
v_res_2361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_as_2355_, v_i_boxed_2359_, v_stop_boxed_2360_, v_b_2358_);
lean_dec_ref(v_as_2355_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(lean_object* v_init_2362_, lean_object* v_es_2363_){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2364_ = lean_unsigned_to_nat(0u);
v___x_2365_ = lean_array_get_size(v_es_2363_);
v___x_2366_ = lean_nat_dec_lt(v___x_2364_, v___x_2365_);
if (v___x_2366_ == 0)
{
return v_init_2362_;
}
else
{
uint8_t v___x_2367_; 
v___x_2367_ = lean_nat_dec_le(v___x_2365_, v___x_2365_);
if (v___x_2367_ == 0)
{
if (v___x_2366_ == 0)
{
return v_init_2362_;
}
else
{
size_t v___x_2368_; size_t v___x_2369_; lean_object* v___x_2370_; 
v___x_2368_ = ((size_t)0ULL);
v___x_2369_ = lean_usize_of_nat(v___x_2365_);
v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2363_, v___x_2368_, v___x_2369_, v_init_2362_);
return v___x_2370_;
}
}
else
{
size_t v___x_2371_; size_t v___x_2372_; lean_object* v___x_2373_; 
v___x_2371_ = ((size_t)0ULL);
v___x_2372_ = lean_usize_of_nat(v___x_2365_);
v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2363_, v___x_2371_, v___x_2372_, v_init_2362_);
return v___x_2373_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries___boxed(lean_object* v_init_2374_, lean_object* v_es_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v_init_2374_, v_es_2375_);
lean_dec_ref(v_es_2375_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_2377_, lean_object* v_x_2378_){
_start:
{
if (lean_obj_tag(v_x_2378_) == 0)
{
lean_object* v_k_2379_; lean_object* v_v_2380_; lean_object* v_l_2381_; lean_object* v_r_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_k_2379_ = lean_ctor_get(v_x_2378_, 1);
v_v_2380_ = lean_ctor_get(v_x_2378_, 2);
v_l_2381_ = lean_ctor_get(v_x_2378_, 3);
v_r_2382_ = lean_ctor_get(v_x_2378_, 4);
v___x_2383_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2377_, v_l_2381_);
lean_inc(v_v_2380_);
lean_inc(v_k_2379_);
v___x_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2384_, 0, v_k_2379_);
lean_ctor_set(v___x_2384_, 1, v_v_2380_);
v___x_2385_ = lean_array_push(v___x_2383_, v___x_2384_);
v_init_2377_ = v___x_2385_;
v_x_2378_ = v_r_2382_;
goto _start;
}
else
{
return v_init_2377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_2387_, lean_object* v_x_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2387_, v_x_2388_);
lean_dec(v_x_2388_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2392_){
_start:
{
lean_object* v_current_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_current_2393_ = lean_ctor_get(v_s_2392_, 1);
v___x_2394_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2395_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2394_, v_current_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_s_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_s_2396_);
lean_dec_ref(v_s_2396_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_box(0);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2400_);
lean_dec_ref(v_x_2400_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2402_, lean_object* v_s_2403_){
_start:
{
lean_object* v_current_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_current_2404_ = lean_ctor_get(v_s_2403_, 1);
v___x_2405_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2406_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2405_, v_current_2404_);
lean_inc_ref_n(v___x_2406_, 2);
v___x_2407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
lean_ctor_set(v___x_2407_, 2, v___x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2408_, lean_object* v_s_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2408_, v_s_2409_);
lean_dec_ref(v_s_2409_);
lean_dec_ref(v_x_2408_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2411_, lean_object* v_x_2412_){
_start:
{
lean_object* v_fst_2413_; lean_object* v_snd_2414_; lean_object* v_imported_2415_; lean_object* v_current_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
v_fst_2413_ = lean_ctor_get(v_x_2412_, 0);
lean_inc(v_fst_2413_);
v_snd_2414_ = lean_ctor_get(v_x_2412_, 1);
lean_inc(v_snd_2414_);
lean_dec_ref(v_x_2412_);
v_imported_2415_ = lean_ctor_get(v_s_2411_, 0);
v_current_2416_ = lean_ctor_get(v_s_2411_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_s_2411_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2418_ = v_s_2411_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_current_2416_);
lean_inc(v_imported_2415_);
lean_dec(v_s_2411_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2413_, v_snd_2414_, v_current_2416_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 1, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_imported_2415_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2425_, lean_object* v_es_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_inc(v___x_2425_);
v___x_2429_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v___x_2425_, v_es_2426_);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
lean_ctor_set(v___x_2430_, 1, v___x_2425_);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2432_, lean_object* v_es_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2432_, v_es_2433_, v___y_2434_);
lean_dec_ref(v___y_2434_);
lean_dec_ref(v_es_2433_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2437_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2440_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2472_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_a_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_();
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(lean_object* v_init_2475_, lean_object* v_t_2476_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2475_, v_t_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_2478_, lean_object* v_t_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(v_init_2478_, v_t_2479_);
lean_dec(v_t_2479_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_));
v___x_2500_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2____boxed(lean_object* v_a_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_();
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2504_ = lean_box(1);
v___x_2505_ = lean_st_mk_ref(v___x_2504_);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2____boxed(lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_();
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2____boxed(lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_();
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer(lean_object* v_type_2515_, lean_object* v_r_2516_){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2518_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2519_ = lean_st_ref_take(v___x_2518_);
v___x_2520_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2515_, v_r_2516_, v___x_2519_);
v___x_2521_ = lean_st_ref_put(v___x_2518_, v___x_2520_);
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer___boxed(lean_object* v_type_2523_, lean_object* v_r_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_Doc_addBuiltinInlineMdRenderer(v_type_2523_, v_r_2524_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer(lean_object* v_type_2527_, lean_object* v_r_2528_){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2530_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2531_ = lean_st_ref_take(v___x_2530_);
v___x_2532_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2527_, v_r_2528_, v___x_2531_);
v___x_2533_ = lean_st_ref_put(v___x_2530_, v___x_2532_);
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer___boxed(lean_object* v_type_2535_, lean_object* v_r_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Doc_addBuiltinBlockMdRenderer(v_type_2535_, v_r_2536_);
return v_res_2538_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2539_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
return v___x_2541_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
lean_ctor_set(v___x_2544_, 2, v___x_2543_);
lean_ctor_set(v___x_2544_, 3, v___x_2543_);
lean_ctor_set(v___x_2544_, 4, v___x_2542_);
lean_ctor_set(v___x_2544_, 5, v___x_2542_);
lean_ctor_set(v___x_2544_, 6, v___x_2542_);
lean_ctor_set(v___x_2544_, 7, v___x_2542_);
lean_ctor_set(v___x_2544_, 8, v___x_2542_);
lean_ctor_set(v___x_2544_, 9, v___x_2542_);
lean_ctor_set(v___x_2544_, 10, v___x_2542_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_unsigned_to_nat(32u);
v___x_2546_ = lean_mk_empty_array_with_capacity(v___x_2545_);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2548_ = ((size_t)5ULL);
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = lean_unsigned_to_nat(32u);
v___x_2551_ = lean_mk_empty_array_with_capacity(v___x_2550_);
v___x_2552_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_2553_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
lean_ctor_set(v___x_2553_, 1, v___x_2551_);
lean_ctor_set(v___x_2553_, 2, v___x_2549_);
lean_ctor_set(v___x_2553_, 3, v___x_2549_);
lean_ctor_set_usize(v___x_2553_, 4, v___x_2548_);
return v___x_2553_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2554_ = lean_box(1);
v___x_2555_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_2556_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v___x_2555_);
lean_ctor_set(v___x_2557_, 2, v___x_2554_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___x_2562_; lean_object* v_toCold_2563_; lean_object* v_env_2564_; lean_object* v_options_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2562_ = lean_st_ref_get(v___y_2560_);
v_toCold_2563_ = lean_ctor_get(v___y_2559_, 0);
v_env_2564_ = lean_ctor_get(v___x_2562_, 0);
lean_inc_ref(v_env_2564_);
lean_dec(v___x_2562_);
v_options_2565_ = lean_ctor_get(v_toCold_2563_, 2);
v___x_2566_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_2567_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_2565_);
v___x_2568_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2568_, 0, v_env_2564_);
lean_ctor_set(v___x_2568_, 1, v___x_2566_);
lean_ctor_set(v___x_2568_, 2, v___x_2567_);
lean_ctor_set(v___x_2568_, 3, v_options_2565_);
v___x_2569_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
lean_ctor_set(v___x_2569_, 1, v_msgData_2558_);
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_2571_, v___y_2572_, v___y_2573_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_ref_2580_; lean_object* v___x_2581_; lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2590_; 
v_ref_2580_ = lean_ctor_get(v___y_2577_, 2);
v___x_2581_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_2576_, v___y_2577_, v___y_2578_);
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
lean_inc(v_ref_2580_);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v_ref_2580_);
lean_ctor_set(v___x_2586_, 1, v_a_2582_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 1);
lean_ctor_set(v___x_2584_, 0, v___x_2586_);
v___x_2588_ = v___x_2584_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(lean_object* v_x_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
if (lean_obj_tag(v_x_2596_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_a_2600_ = lean_ctor_get(v_x_2596_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v_x_2596_, 1);
v___x_2601_ = l_Lean_stringToMessageData(v_a_2600_);
v___x_2602_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v___x_2601_, v___y_2597_, v___y_2598_);
return v___x_2602_;
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
v_a_2603_ = lean_ctor_get(v_x_2596_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_x_2596_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v_x_2596_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v_x_2596_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set_tag(v___x_2605_, 0);
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
return v_res_2615_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = lean_box(0);
v___x_2617_ = l_Lean_Elab_abortCommandExceptionId;
v___x_2618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
lean_ctor_set(v___x_2618_, 1, v___x_2616_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(lean_object* v_constName_2624_, uint8_t v_checkMeta_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; lean_object* v_env_2630_; uint8_t v___x_2631_; 
v___x_2629_ = lean_st_ref_get(v___y_2627_);
v_env_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc_ref(v_env_2630_);
lean_dec(v___x_2629_);
lean_inc(v_constName_2624_);
v___x_2631_ = lean_has_compile_error(v_env_2630_, v_constName_2624_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; lean_object* v_env_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2632_ = lean_st_ref_get(v___y_2627_);
v_env_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc_ref(v_env_2633_);
lean_dec(v___x_2632_);
v___x_2634_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2626_);
v___x_2635_ = l_Lean_Environment_evalConst___redArg(v_env_2633_, v___x_2634_, v_constName_2624_, v_checkMeta_2625_);
lean_dec(v_constName_2624_);
lean_dec_ref(v___x_2634_);
lean_dec_ref(v_env_2633_);
v___x_2636_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2635_, v___y_2626_, v___y_2627_);
return v___x_2636_;
}
else
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v___x_2638_; lean_object* v_env_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_dec_ref_known(v___x_2637_, 1);
v___x_2638_ = lean_st_ref_get(v___y_2627_);
v_env_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc_ref(v_env_2639_);
lean_dec(v___x_2638_);
v___x_2640_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2626_);
v___x_2641_ = l_Lean_Environment_evalConst___redArg(v_env_2639_, v___x_2640_, v_constName_2624_, v_checkMeta_2625_);
lean_dec(v_constName_2624_);
lean_dec_ref(v___x_2640_);
lean_dec_ref(v_env_2639_);
v___x_2642_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2641_, v___y_2626_, v___y_2627_);
return v___x_2642_;
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_constName_2624_);
v_a_2643_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2637_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2637_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg___boxed(lean_object* v_constName_2651_, lean_object* v_checkMeta_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
uint8_t v_checkMeta_boxed_2656_; lean_object* v_res_2657_; 
v_checkMeta_boxed_2656_ = lean_unbox(v_checkMeta_2652_);
v_res_2657_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2651_, v_checkMeta_boxed_2656_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(lean_object* v_type_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___y_2665_; lean_object* v_env_2696_; lean_object* v___x_2697_; lean_object* v_toEnvExtension_2698_; lean_object* v_asyncMode_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v_imported_2702_; lean_object* v_current_2703_; lean_object* v___x_2704_; 
v___x_2662_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2663_ = lean_st_ref_get(v_a_2660_);
v_env_2696_ = lean_ctor_get(v___x_2663_, 0);
lean_inc_ref(v_env_2696_);
lean_dec(v___x_2663_);
v___x_2697_ = l_Lean_Doc_docInlineMdExt;
v_toEnvExtension_2698_ = lean_ctor_get(v___x_2697_, 0);
v_asyncMode_2699_ = lean_ctor_get(v_toEnvExtension_2698_, 2);
v___x_2700_ = lean_box(0);
v___x_2701_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2662_, v___x_2697_, v_env_2696_, v_asyncMode_2699_, v___x_2700_);
v_imported_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_imported_2702_);
v_current_2703_ = lean_ctor_get(v___x_2701_, 1);
lean_inc(v_current_2703_);
lean_dec(v___x_2701_);
v___x_2704_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2703_, v_type_2658_);
lean_dec(v_current_2703_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2702_, v_type_2658_);
lean_dec(v_imported_2702_);
v___y_2665_ = v___x_2705_;
goto v___jp_2664_;
}
else
{
lean_dec(v_imported_2702_);
v___y_2665_ = v___x_2704_;
goto v___jp_2664_;
}
v___jp_2664_:
{
if (lean_obj_tag(v___y_2665_) == 0)
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2666_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2667_ = lean_st_ref_get(v___x_2666_);
v___x_2668_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2667_, v_type_2658_);
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
v___x_2675_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2670_, v___x_2674_, v_a_2659_, v_a_2660_);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe___boxed(lean_object* v_type_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v_type_2706_, v_a_2707_, v_a_2708_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_type_2706_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(v_00_u03b1_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(lean_object* v_00_u03b1_2721_, lean_object* v_constName_2722_, uint8_t v_checkMeta_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2722_, v_checkMeta_2723_, v___y_2724_, v___y_2725_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___boxed(lean_object* v_00_u03b1_2728_, lean_object* v_constName_2729_, lean_object* v_checkMeta_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
uint8_t v_checkMeta_boxed_2734_; lean_object* v_res_2735_; 
v_checkMeta_boxed_2734_ = lean_unbox(v_checkMeta_2730_);
v_res_2735_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(v_00_u03b1_2728_, v_constName_2729_, v_checkMeta_boxed_2734_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_2736_, lean_object* v_x_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2737_, v___y_2738_, v___y_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_x_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(v_00_u03b1_2742_, v_x_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2748_, lean_object* v_msg_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2749_, v___y_2750_, v___y_2751_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2754_, lean_object* v_msg_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_2754_, v_msg_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(lean_object* v_typeName_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___y_2767_; lean_object* v_env_2798_; lean_object* v___x_2799_; lean_object* v_toEnvExtension_2800_; lean_object* v_asyncMode_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v_imported_2804_; lean_object* v_current_2805_; lean_object* v___x_2806_; 
v___x_2764_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2765_ = lean_st_ref_get(v_a_2762_);
v_env_2798_ = lean_ctor_get(v___x_2765_, 0);
lean_inc_ref(v_env_2798_);
lean_dec(v___x_2765_);
v___x_2799_ = l_Lean_Doc_docBlockMdExt;
v_toEnvExtension_2800_ = lean_ctor_get(v___x_2799_, 0);
v_asyncMode_2801_ = lean_ctor_get(v_toEnvExtension_2800_, 2);
v___x_2802_ = lean_box(0);
v___x_2803_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2764_, v___x_2799_, v_env_2798_, v_asyncMode_2801_, v___x_2802_);
v_imported_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_imported_2804_);
v_current_2805_ = lean_ctor_get(v___x_2803_, 1);
lean_inc(v_current_2805_);
lean_dec(v___x_2803_);
v___x_2806_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2805_, v_typeName_2760_);
lean_dec(v_current_2805_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2804_, v_typeName_2760_);
lean_dec(v_imported_2804_);
v___y_2767_ = v___x_2807_;
goto v___jp_2766_;
}
else
{
lean_dec(v_imported_2804_);
v___y_2767_ = v___x_2806_;
goto v___jp_2766_;
}
v___jp_2766_:
{
if (lean_obj_tag(v___y_2767_) == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2768_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2769_ = lean_st_ref_get(v___x_2768_);
v___x_2770_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2769_, v_typeName_2760_);
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
v___x_2777_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2772_, v___x_2776_, v_a_2761_, v_a_2762_);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe___boxed(lean_object* v_typeName_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v_typeName_2808_, v_a_2809_, v_a_2810_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_typeName_2808_);
return v_res_2812_;
}
}
static lean_object* _init_l_Lean_Doc_mdRendererHeartbeats(void){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_unsigned_to_nat(200000u);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg(lean_object* v_x_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v___x_2819_; lean_object* v_toCold_2820_; lean_object* v_currRecDepth_2821_; lean_object* v_ref_2822_; uint16_t v_optionFlags_2823_; uint8_t v_suppressElabErrors_2824_; uint8_t v_isRecordingDeps_2825_; lean_object* v_fileName_2826_; lean_object* v_fileMap_2827_; lean_object* v_options_2828_; lean_object* v_maxRecDepth_2829_; lean_object* v_currNamespace_2830_; lean_object* v_openDecls_2831_; lean_object* v_quotContext_2832_; lean_object* v_currMacroScope_2833_; lean_object* v_cancelTk_x3f_2834_; lean_object* v_inheritedTraceOptions_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2819_ = lean_io_get_num_heartbeats();
v_toCold_2820_ = lean_ctor_get(v_a_2816_, 0);
v_currRecDepth_2821_ = lean_ctor_get(v_a_2816_, 1);
v_ref_2822_ = lean_ctor_get(v_a_2816_, 2);
v_optionFlags_2823_ = lean_ctor_get_uint16(v_a_2816_, sizeof(void*)*3);
v_suppressElabErrors_2824_ = lean_ctor_get_uint8(v_a_2816_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2825_ = lean_ctor_get_uint8(v_a_2816_, sizeof(void*)*3 + 3);
v_fileName_2826_ = lean_ctor_get(v_toCold_2820_, 0);
v_fileMap_2827_ = lean_ctor_get(v_toCold_2820_, 1);
v_options_2828_ = lean_ctor_get(v_toCold_2820_, 2);
v_maxRecDepth_2829_ = lean_ctor_get(v_toCold_2820_, 3);
v_currNamespace_2830_ = lean_ctor_get(v_toCold_2820_, 4);
v_openDecls_2831_ = lean_ctor_get(v_toCold_2820_, 5);
v_quotContext_2832_ = lean_ctor_get(v_toCold_2820_, 8);
v_currMacroScope_2833_ = lean_ctor_get(v_toCold_2820_, 9);
v_cancelTk_x3f_2834_ = lean_ctor_get(v_toCold_2820_, 10);
v_inheritedTraceOptions_2835_ = lean_ctor_get(v_toCold_2820_, 11);
v___x_2836_ = lean_unsigned_to_nat(200000u);
lean_inc_ref(v_inheritedTraceOptions_2835_);
lean_inc(v_cancelTk_x3f_2834_);
lean_inc(v_currMacroScope_2833_);
lean_inc(v_quotContext_2832_);
lean_inc(v_openDecls_2831_);
lean_inc(v_currNamespace_2830_);
lean_inc(v_maxRecDepth_2829_);
lean_inc_ref(v_options_2828_);
lean_inc_ref(v_fileMap_2827_);
lean_inc_ref(v_fileName_2826_);
v___x_2837_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2837_, 0, v_fileName_2826_);
lean_ctor_set(v___x_2837_, 1, v_fileMap_2827_);
lean_ctor_set(v___x_2837_, 2, v_options_2828_);
lean_ctor_set(v___x_2837_, 3, v_maxRecDepth_2829_);
lean_ctor_set(v___x_2837_, 4, v_currNamespace_2830_);
lean_ctor_set(v___x_2837_, 5, v_openDecls_2831_);
lean_ctor_set(v___x_2837_, 6, v___x_2819_);
lean_ctor_set(v___x_2837_, 7, v___x_2836_);
lean_ctor_set(v___x_2837_, 8, v_quotContext_2832_);
lean_ctor_set(v___x_2837_, 9, v_currMacroScope_2833_);
lean_ctor_set(v___x_2837_, 10, v_cancelTk_x3f_2834_);
lean_ctor_set(v___x_2837_, 11, v_inheritedTraceOptions_2835_);
lean_inc(v_ref_2822_);
lean_inc(v_currRecDepth_2821_);
v___x_2838_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
lean_ctor_set(v___x_2838_, 1, v_currRecDepth_2821_);
lean_ctor_set(v___x_2838_, 2, v_ref_2822_);
lean_ctor_set_uint16(v___x_2838_, sizeof(void*)*3, v_optionFlags_2823_);
lean_ctor_set_uint8(v___x_2838_, sizeof(void*)*3 + 2, v_suppressElabErrors_2824_);
lean_ctor_set_uint8(v___x_2838_, sizeof(void*)*3 + 3, v_isRecordingDeps_2825_);
lean_inc(v_a_2817_);
lean_inc(v_a_2815_);
v___x_2839_ = lean_apply_4(v_x_2814_, v_a_2815_, v___x_2838_, v_a_2817_, lean_box(0));
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg___boxed(lean_object* v_x_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2842_);
lean_dec(v_a_2841_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget(lean_object* v_00_u03b1_2846_, lean_object* v_x_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___boxed(lean_object* v_00_u03b1_2853_, lean_object* v_x_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_Doc_withMdRendererBudget(v_00_u03b1_2853_, v_x_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback(lean_object* v_fallback_2860_, lean_object* v_act_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_st_ref_get(v_a_2862_);
v___x_2867_ = l_Lean_Doc_withMdRendererBudget___redArg(v_act_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_dec(v___x_2866_);
lean_dec_ref(v_fallback_2860_);
return v___x_2867_;
}
else
{
lean_object* v_a_2868_; uint8_t v___x_2869_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v___x_2869_ = l_Lean_Exception_isInterrupt(v_a_2868_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_dec_ref_known(v___x_2867_, 1);
v___x_2870_ = lean_st_ref_swap(v_a_2862_, v___x_2866_);
lean_dec(v___x_2870_);
lean_inc(v_a_2864_);
lean_inc_ref(v_a_2863_);
lean_inc(v_a_2862_);
v___x_2871_ = lean_apply_4(v_fallback_2860_, v_a_2862_, v_a_2863_, v_a_2864_, lean_box(0));
return v___x_2871_;
}
else
{
lean_dec(v___x_2866_);
lean_dec_ref(v_fallback_2860_);
return v___x_2867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback___boxed(lean_object* v_fallback_2872_, lean_object* v_act_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_Doc_withRendererFallback(v_fallback_2872_, v_act_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
lean_dec(v_a_2874_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0(lean_object* v_____do__lift_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = l_Lean_Doc_joinInlines(v_____do__lift_2879_);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0___boxed(lean_object* v_____do__lift_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__0(v_____do__lift_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v_____do__lift_2886_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1(lean_object* v___x_2892_, lean_object* v___x_2893_, lean_object* v___f_2894_, lean_object* v_go_2895_, lean_object* v_container_2896_, lean_object* v_content_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
if (lean_obj_tag(v_container_2896_) == 0)
{
lean_object* v_val_2902_; size_t v_sz_2903_; size_t v___x_2904_; lean_object* v___x_2905_; lean_object* v_fallback_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_val_2902_ = lean_ctor_get(v_container_2896_, 0);
lean_inc(v_val_2902_);
lean_dec_ref_known(v_container_2896_, 1);
v_sz_2903_ = lean_array_size(v_content_2897_);
v___x_2904_ = ((size_t)0ULL);
lean_inc_ref(v_content_2897_);
lean_inc_ref(v_go_2895_);
lean_inc_ref(v___x_2892_);
v___x_2905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2892_, v_go_2895_, v_sz_2903_, v___x_2904_, v_content_2897_);
lean_inc_ref(v___f_2894_);
v_fallback_2906_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_2906_, 0, lean_box(0));
lean_closure_set(v_fallback_2906_, 1, lean_box(0));
lean_closure_set(v_fallback_2906_, 2, v___x_2893_);
lean_closure_set(v_fallback_2906_, 3, lean_box(0));
lean_closure_set(v_fallback_2906_, 4, lean_box(0));
lean_closure_set(v_fallback_2906_, 5, v___x_2905_);
lean_closure_set(v_fallback_2906_, 6, v___f_2894_);
v___x_2907_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2902_);
v___x_2908_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_2907_, v___y_2899_, v___y_2900_);
lean_dec(v___x_2907_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2908_, 1);
if (lean_obj_tag(v_a_2909_) == 0)
{
lean_object* v___x_543__overap_2910_; lean_object* v___x_2911_; 
lean_dec_ref(v_fallback_2906_);
lean_dec(v_val_2902_);
v___x_543__overap_2910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2892_, v_go_2895_, v_sz_2903_, v___x_2904_, v_content_2897_);
lean_inc(v___y_2900_);
lean_inc_ref(v___y_2899_);
lean_inc(v___y_2898_);
v___x_2911_ = lean_apply_4(v___x_543__overap_2910_, v___y_2898_, v___y_2899_, v___y_2900_, lean_box(0));
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2913_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
lean_inc(v___y_2900_);
lean_inc_ref(v___y_2899_);
lean_inc(v___y_2898_);
v___x_2913_ = lean_apply_5(v___f_2894_, v_a_2912_, v___y_2898_, v___y_2899_, v___y_2900_, lean_box(0));
return v___x_2913_;
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v___f_2894_);
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
lean_object* v_val_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_dec_ref(v___f_2894_);
lean_dec_ref(v___x_2892_);
v_val_2922_ = lean_ctor_get(v_a_2909_, 0);
lean_inc(v_val_2922_);
lean_dec_ref_known(v_a_2909_, 1);
v___x_2923_ = lean_apply_3(v_val_2922_, v_go_2895_, v_val_2902_, v_content_2897_);
v___x_2924_ = l_Lean_Doc_withRendererFallback(v_fallback_2906_, v___x_2923_, v___y_2898_, v___y_2899_, v___y_2900_);
return v___x_2924_;
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec_ref(v_fallback_2906_);
lean_dec(v_val_2902_);
lean_dec_ref(v_content_2897_);
lean_dec_ref(v_go_2895_);
lean_dec_ref(v___f_2894_);
lean_dec_ref(v___x_2892_);
v_a_2925_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2908_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2908_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
size_t v_sz_2933_; size_t v___x_2934_; lean_object* v___x_558__overap_2935_; lean_object* v___x_2936_; 
lean_dec_ref_known(v_container_2896_, 1);
lean_dec_ref(v___f_2894_);
lean_dec_ref(v___x_2893_);
v_sz_2933_ = lean_array_size(v_content_2897_);
v___x_2934_ = ((size_t)0ULL);
v___x_558__overap_2935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2892_, v_go_2895_, v_sz_2933_, v___x_2934_, v_content_2897_);
lean_inc(v___y_2900_);
lean_inc_ref(v___y_2899_);
lean_inc(v___y_2898_);
v___x_2936_ = lean_apply_4(v___x_558__overap_2935_, v___y_2898_, v___y_2899_, v___y_2900_, lean_box(0));
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2945_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2945_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2945_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; lean_object* v___x_2943_; 
v___x_2941_ = l_Lean_Doc_joinInlines(v_a_2937_);
lean_dec(v_a_2937_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2941_);
v___x_2943_ = v___x_2939_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
v_a_2946_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2936_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2936_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed(lean_object* v___x_2954_, lean_object* v___x_2955_, lean_object* v___f_2956_, lean_object* v_go_2957_, lean_object* v_container_2958_, lean_object* v_content_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__1(v___x_2954_, v___x_2955_, v___f_2956_, v_go_2957_, v_container_2958_, v_content_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
return v_res_2964_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownInlineElabInline(void){
_start:
{
lean_object* v___x_2966_; lean_object* v_toApplicative_2967_; lean_object* v_toFunctor_2968_; lean_object* v_toSeq_2969_; lean_object* v_toSeqLeft_2970_; lean_object* v_toSeqRight_2971_; lean_object* v___f_2972_; lean_object* v___f_2973_; lean_object* v___f_2974_; lean_object* v___f_2975_; lean_object* v___f_2976_; lean_object* v___x_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; lean_object* v___f_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___f_2984_; 
v___x_2966_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2967_ = lean_ctor_get(v___x_2966_, 0);
v_toFunctor_2968_ = lean_ctor_get(v_toApplicative_2967_, 0);
v_toSeq_2969_ = lean_ctor_get(v_toApplicative_2967_, 2);
v_toSeqLeft_2970_ = lean_ctor_get(v_toApplicative_2967_, 3);
v_toSeqRight_2971_ = lean_ctor_get(v_toApplicative_2967_, 4);
v___f_2972_ = ((lean_object*)(l_Lean_Doc_instMarkdownInlineElabInline___closed__0));
v___f_2973_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2974_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2968_, 2);
v___f_2975_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2975_, 0, v_toFunctor_2968_);
v___f_2976_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2976_, 0, v_toFunctor_2968_);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___f_2975_);
lean_ctor_set(v___x_2977_, 1, v___f_2976_);
lean_inc(v_toSeqRight_2971_);
v___f_2978_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2978_, 0, v_toSeqRight_2971_);
lean_inc(v_toSeqLeft_2970_);
v___f_2979_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2979_, 0, v_toSeqLeft_2970_);
lean_inc(v_toSeq_2969_);
v___f_2980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2980_, 0, v_toSeq_2969_);
v___x_2981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2977_);
lean_ctor_set(v___x_2981_, 1, v___f_2973_);
lean_ctor_set(v___x_2981_, 2, v___f_2980_);
lean_ctor_set(v___x_2981_, 3, v___f_2979_);
lean_ctor_set(v___x_2981_, 4, v___f_2978_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
lean_ctor_set(v___x_2982_, 1, v___f_2974_);
lean_inc_ref(v___x_2982_);
v___x_2983_ = l_StateRefT_x27_instMonad___redArg(v___x_2982_);
v___f_2984_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2984_, 0, v___x_2983_);
lean_closure_set(v___f_2984_, 1, v___x_2982_);
lean_closure_set(v___f_2984_, 2, v___f_2972_);
return v___f_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v_____do__lift_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = l_Lean_Doc_joinBlocks(v_____do__lift_2985_);
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object* v_____do__lift_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(v_____do__lift_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v_____do__lift_2992_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object* v___x_2998_, lean_object* v___x_2999_, lean_object* v___f_3000_, lean_object* v_goI_3001_, lean_object* v_goB_3002_, lean_object* v_container_3003_, lean_object* v_content_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
if (lean_obj_tag(v_container_3003_) == 0)
{
lean_object* v_val_3009_; size_t v_sz_3010_; size_t v___x_3011_; lean_object* v___x_3012_; lean_object* v_fallback_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_val_3009_ = lean_ctor_get(v_container_3003_, 0);
lean_inc(v_val_3009_);
lean_dec_ref_known(v_container_3003_, 1);
v_sz_3010_ = lean_array_size(v_content_3004_);
v___x_3011_ = ((size_t)0ULL);
lean_inc_ref(v_content_3004_);
lean_inc_ref(v_goB_3002_);
lean_inc_ref(v___x_2998_);
v___x_3012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2998_, v_goB_3002_, v_sz_3010_, v___x_3011_, v_content_3004_);
lean_inc_ref(v___f_3000_);
v_fallback_3013_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_3013_, 0, lean_box(0));
lean_closure_set(v_fallback_3013_, 1, lean_box(0));
lean_closure_set(v_fallback_3013_, 2, v___x_2999_);
lean_closure_set(v_fallback_3013_, 3, lean_box(0));
lean_closure_set(v_fallback_3013_, 4, lean_box(0));
lean_closure_set(v_fallback_3013_, 5, v___x_3012_);
lean_closure_set(v_fallback_3013_, 6, v___f_3000_);
v___x_3014_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3009_);
v___x_3015_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_3014_, v___y_3006_, v___y_3007_);
lean_dec(v___x_3014_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
if (lean_obj_tag(v_a_3016_) == 0)
{
lean_object* v___x_543__overap_3017_; lean_object* v___x_3018_; 
lean_dec_ref(v_fallback_3013_);
lean_dec(v_val_3009_);
lean_dec_ref(v_goI_3001_);
v___x_543__overap_3017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2998_, v_goB_3002_, v_sz_3010_, v___x_3011_, v_content_3004_);
lean_inc(v___y_3007_);
lean_inc_ref(v___y_3006_);
lean_inc(v___y_3005_);
v___x_3018_ = lean_apply_4(v___x_543__overap_3017_, v___y_3005_, v___y_3006_, v___y_3007_, lean_box(0));
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3020_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
lean_inc(v___y_3007_);
lean_inc_ref(v___y_3006_);
lean_inc(v___y_3005_);
v___x_3020_ = lean_apply_5(v___f_3000_, v_a_3019_, v___y_3005_, v___y_3006_, v___y_3007_, lean_box(0));
return v___x_3020_;
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref(v___f_3000_);
v_a_3021_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3018_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3018_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_object* v_val_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
lean_dec_ref(v___f_3000_);
lean_dec_ref(v___x_2998_);
v_val_3029_ = lean_ctor_get(v_a_3016_, 0);
lean_inc(v_val_3029_);
lean_dec_ref_known(v_a_3016_, 1);
v___x_3030_ = lean_apply_4(v_val_3029_, v_goI_3001_, v_goB_3002_, v_val_3009_, v_content_3004_);
v___x_3031_ = l_Lean_Doc_withRendererFallback(v_fallback_3013_, v___x_3030_, v___y_3005_, v___y_3006_, v___y_3007_);
return v___x_3031_;
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_fallback_3013_);
lean_dec(v_val_3009_);
lean_dec_ref(v_content_3004_);
lean_dec_ref(v_goB_3002_);
lean_dec_ref(v_goI_3001_);
lean_dec_ref(v___f_3000_);
lean_dec_ref(v___x_2998_);
v_a_3032_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3015_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3015_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
size_t v_sz_3040_; size_t v___x_3041_; lean_object* v___x_558__overap_3042_; lean_object* v___x_3043_; 
lean_dec_ref_known(v_container_3003_, 1);
lean_dec_ref(v_goI_3001_);
lean_dec_ref(v___f_3000_);
lean_dec_ref(v___x_2999_);
v_sz_3040_ = lean_array_size(v_content_3004_);
v___x_3041_ = ((size_t)0ULL);
v___x_558__overap_3042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2998_, v_goB_3002_, v_sz_3040_, v___x_3041_, v_content_3004_);
lean_inc(v___y_3007_);
lean_inc_ref(v___y_3006_);
lean_inc(v___y_3005_);
v___x_3043_ = lean_apply_4(v___x_558__overap_3042_, v___y_3005_, v___y_3006_, v___y_3007_, lean_box(0));
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3052_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3052_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3052_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3048_ = l_Lean_Doc_joinBlocks(v_a_3044_);
lean_dec(v_a_3044_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v___x_3048_);
v___x_3050_ = v___x_3046_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
v_a_3053_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3043_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3043_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object* v___x_3061_, lean_object* v___x_3062_, lean_object* v___f_3063_, lean_object* v_goI_3064_, lean_object* v_goB_3065_, lean_object* v_container_3066_, lean_object* v_content_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_3061_, v___x_3062_, v___f_3063_, v_goI_3064_, v_goB_3065_, v_container_3066_, v_content_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
return v_res_3072_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownBlockElabInlineElabBlock(void){
_start:
{
lean_object* v___x_3074_; lean_object* v_toApplicative_3075_; lean_object* v_toFunctor_3076_; lean_object* v_toSeq_3077_; lean_object* v_toSeqLeft_3078_; lean_object* v_toSeqRight_3079_; lean_object* v___f_3080_; lean_object* v___f_3081_; lean_object* v___f_3082_; lean_object* v___f_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; lean_object* v___f_3086_; lean_object* v___f_3087_; lean_object* v___f_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___f_3092_; 
v___x_3074_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3075_ = lean_ctor_get(v___x_3074_, 0);
v_toFunctor_3076_ = lean_ctor_get(v_toApplicative_3075_, 0);
v_toSeq_3077_ = lean_ctor_get(v_toApplicative_3075_, 2);
v_toSeqLeft_3078_ = lean_ctor_get(v_toApplicative_3075_, 3);
v_toSeqRight_3079_ = lean_ctor_get(v_toApplicative_3075_, 4);
v___f_3080_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___closed__0));
v___f_3081_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3082_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3076_, 2);
v___f_3083_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3083_, 0, v_toFunctor_3076_);
v___f_3084_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3084_, 0, v_toFunctor_3076_);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___f_3083_);
lean_ctor_set(v___x_3085_, 1, v___f_3084_);
lean_inc(v_toSeqRight_3079_);
v___f_3086_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3086_, 0, v_toSeqRight_3079_);
lean_inc(v_toSeqLeft_3078_);
v___f_3087_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3087_, 0, v_toSeqLeft_3078_);
lean_inc(v_toSeq_3077_);
v___f_3088_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3088_, 0, v_toSeq_3077_);
v___x_3089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3085_);
lean_ctor_set(v___x_3089_, 1, v___f_3081_);
lean_ctor_set(v___x_3089_, 2, v___f_3088_);
lean_ctor_set(v___x_3089_, 3, v___f_3087_);
lean_ctor_set(v___x_3089_, 4, v___f_3086_);
v___x_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
lean_ctor_set(v___x_3090_, 1, v___f_3082_);
lean_inc_ref(v___x_3090_);
v___x_3091_ = l_StateRefT_x27_instMonad___redArg(v___x_3090_);
v___f_3092_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3092_, 0, v___x_3091_);
lean_closure_set(v___f_3092_, 1, v___x_3090_);
lean_closure_set(v___f_3092_, 2, v___f_3080_);
return v___f_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0(lean_object* v___x_3093_, lean_object* v___x_3094_, lean_object* v_part_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = lean_unsigned_to_nat(0u);
v___x_3101_ = l_Lean_Doc_partMarkdown___redArg(v___x_3093_, v___x_3094_, v___x_3100_, v_part_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed(lean_object* v___x_3102_, lean_object* v___x_3103_, lean_object* v_part_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__0(v___x_3102_, v___x_3103_, v_part_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1(lean_object* v___x_3110_, lean_object* v___x_3111_, lean_object* v___x_3112_, lean_object* v___f_3113_, lean_object* v_x_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_text_3119_; lean_object* v_subsections_3120_; lean_object* v___x_3121_; size_t v_sz_3122_; size_t v___x_3123_; lean_object* v___x_443__overap_3124_; lean_object* v___x_3125_; 
v_text_3119_ = lean_ctor_get(v_x_3114_, 0);
lean_inc_ref(v_text_3119_);
v_subsections_3120_ = lean_ctor_get(v_x_3114_, 1);
lean_inc_ref(v_subsections_3120_);
lean_dec_ref(v_x_3114_);
v___x_3121_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3121_, 0, lean_box(0));
lean_closure_set(v___x_3121_, 1, lean_box(0));
lean_closure_set(v___x_3121_, 2, v___x_3110_);
lean_closure_set(v___x_3121_, 3, v___x_3111_);
v_sz_3122_ = lean_array_size(v_text_3119_);
v___x_3123_ = ((size_t)0ULL);
lean_inc_ref(v___x_3112_);
v___x_443__overap_3124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3112_, v___x_3121_, v_sz_3122_, v___x_3123_, v_text_3119_);
lean_inc(v___y_3117_);
lean_inc_ref(v___y_3116_);
lean_inc(v___y_3115_);
v___x_3125_ = lean_apply_4(v___x_443__overap_3124_, v___y_3115_, v___y_3116_, v___y_3117_, lean_box(0));
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; size_t v_sz_3127_; lean_object* v___x_446__overap_3128_; lean_object* v___x_3129_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3126_);
lean_dec_ref_known(v___x_3125_, 1);
v_sz_3127_ = lean_array_size(v_subsections_3120_);
v___x_446__overap_3128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3112_, v___f_3113_, v_sz_3127_, v___x_3123_, v_subsections_3120_);
lean_inc(v___y_3117_);
lean_inc_ref(v___y_3116_);
lean_inc(v___y_3115_);
v___x_3129_ = lean_apply_4(v___x_446__overap_3128_, v___y_3115_, v___y_3116_, v___y_3117_, lean_box(0));
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3139_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3139_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3139_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3134_ = l_Array_append___redArg(v_a_3126_, v_a_3130_);
lean_dec(v_a_3130_);
v___x_3135_ = l_Lean_Doc_joinBlocks(v___x_3134_);
lean_dec_ref(v___x_3134_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3135_);
v___x_3137_ = v___x_3132_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v_a_3126_);
v_a_3140_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3129_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3129_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec_ref(v_subsections_3120_);
lean_dec_ref(v___f_3113_);
lean_dec_ref(v___x_3112_);
v_a_3148_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3125_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3125_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed(lean_object* v___x_3156_, lean_object* v___x_3157_, lean_object* v___x_3158_, lean_object* v___f_3159_, lean_object* v_x_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__1(v___x_3156_, v___x_3157_, v___x_3158_, v___f_3159_, v_x_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
return v_res_3165_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0(void){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___f_3168_; 
v___x_3166_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3167_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3168_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3168_, 0, v___x_3167_);
lean_closure_set(v___f_3168_, 1, v___x_3166_);
return v___f_3168_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString(void){
_start:
{
lean_object* v___x_3169_; lean_object* v_toApplicative_3170_; lean_object* v_toFunctor_3171_; lean_object* v_toSeq_3172_; lean_object* v_toSeqLeft_3173_; lean_object* v_toSeqRight_3174_; lean_object* v___f_3175_; lean_object* v___f_3176_; lean_object* v___f_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; lean_object* v___f_3180_; lean_object* v___f_3181_; lean_object* v___f_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___f_3188_; lean_object* v___f_3189_; 
v___x_3169_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3170_ = lean_ctor_get(v___x_3169_, 0);
v_toFunctor_3171_ = lean_ctor_get(v_toApplicative_3170_, 0);
v_toSeq_3172_ = lean_ctor_get(v_toApplicative_3170_, 2);
v_toSeqLeft_3173_ = lean_ctor_get(v_toApplicative_3170_, 3);
v_toSeqRight_3174_ = lean_ctor_get(v_toApplicative_3170_, 4);
v___f_3175_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3176_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3171_, 2);
v___f_3177_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3177_, 0, v_toFunctor_3171_);
v___f_3178_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3178_, 0, v_toFunctor_3171_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___f_3177_);
lean_ctor_set(v___x_3179_, 1, v___f_3178_);
lean_inc(v_toSeqRight_3174_);
v___f_3180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3180_, 0, v_toSeqRight_3174_);
lean_inc(v_toSeqLeft_3173_);
v___f_3181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3181_, 0, v_toSeqLeft_3173_);
lean_inc(v_toSeq_3172_);
v___f_3182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3182_, 0, v_toSeq_3172_);
v___x_3183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3179_);
lean_ctor_set(v___x_3183_, 1, v___f_3175_);
lean_ctor_set(v___x_3183_, 2, v___f_3182_);
lean_ctor_set(v___x_3183_, 3, v___f_3181_);
lean_ctor_set(v___x_3183_, 4, v___f_3180_);
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v___f_3176_);
v___x_3185_ = l_StateRefT_x27_instMonad___redArg(v___x_3184_);
v___x_3186_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3187_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3188_ = lean_obj_once(&l_Lean_Doc_instToMarkdownVersoDocString___closed__0, &l_Lean_Doc_instToMarkdownVersoDocString___closed__0_once, _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0);
v___f_3189_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3189_, 0, v___x_3186_);
lean_closure_set(v___f_3189_, 1, v___x_3187_);
lean_closure_set(v___f_3189_, 2, v___x_3185_);
lean_closure_set(v___f_3189_, 3, v___f_3188_);
return v___f_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0(lean_object* v___x_3190_, lean_object* v___x_3191_, lean_object* v_x_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_snd_3197_; lean_object* v_fst_3198_; lean_object* v_snd_3199_; lean_object* v___x_3200_; 
v_snd_3197_ = lean_ctor_get(v_x_3192_, 1);
lean_inc(v_snd_3197_);
v_fst_3198_ = lean_ctor_get(v_x_3192_, 0);
lean_inc(v_fst_3198_);
lean_dec_ref(v_x_3192_);
v_snd_3199_ = lean_ctor_get(v_snd_3197_, 1);
lean_inc(v_snd_3199_);
lean_dec(v_snd_3197_);
v___x_3200_ = l_Lean_Doc_partMarkdown___redArg(v___x_3190_, v___x_3191_, v_fst_3198_, v_snd_3199_, v___y_3193_, v___y_3194_, v___y_3195_);
lean_dec(v_fst_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_3201_, lean_object* v___x_3202_, lean_object* v_x_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_Doc_instToMarkdownSnippet___lam__0(v___x_3201_, v___x_3202_, v_x_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1(lean_object* v___x_3209_, lean_object* v___x_3210_, lean_object* v___x_3211_, lean_object* v___f_3212_, lean_object* v_x_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_text_3218_; lean_object* v_sections_3219_; lean_object* v___x_3220_; size_t v_sz_3221_; size_t v___x_3222_; lean_object* v___x_490__overap_3223_; lean_object* v___x_3224_; 
v_text_3218_ = lean_ctor_get(v_x_3213_, 0);
lean_inc_ref(v_text_3218_);
v_sections_3219_ = lean_ctor_get(v_x_3213_, 1);
lean_inc_ref(v_sections_3219_);
lean_dec_ref(v_x_3213_);
v___x_3220_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3220_, 0, lean_box(0));
lean_closure_set(v___x_3220_, 1, lean_box(0));
lean_closure_set(v___x_3220_, 2, v___x_3209_);
lean_closure_set(v___x_3220_, 3, v___x_3210_);
v_sz_3221_ = lean_array_size(v_text_3218_);
v___x_3222_ = ((size_t)0ULL);
lean_inc_ref(v___x_3211_);
v___x_490__overap_3223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3211_, v___x_3220_, v_sz_3221_, v___x_3222_, v_text_3218_);
lean_inc(v___y_3216_);
lean_inc_ref(v___y_3215_);
lean_inc(v___y_3214_);
v___x_3224_ = lean_apply_4(v___x_490__overap_3223_, v___y_3214_, v___y_3215_, v___y_3216_, lean_box(0));
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; size_t v_sz_3226_; lean_object* v___x_493__overap_3227_; lean_object* v___x_3228_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v_sz_3226_ = lean_array_size(v_sections_3219_);
v___x_493__overap_3227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3211_, v___f_3212_, v_sz_3226_, v___x_3222_, v_sections_3219_);
lean_inc(v___y_3216_);
lean_inc_ref(v___y_3215_);
lean_inc(v___y_3214_);
v___x_3228_ = lean_apply_4(v___x_493__overap_3227_, v___y_3214_, v___y_3215_, v___y_3216_, lean_box(0));
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3238_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3231_ = v___x_3228_;
v_isShared_3232_ = v_isSharedCheck_3238_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3228_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3238_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3233_ = l_Array_append___redArg(v_a_3225_, v_a_3229_);
lean_dec(v_a_3229_);
v___x_3234_ = l_Lean_Doc_joinBlocks(v___x_3233_);
lean_dec_ref(v___x_3233_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v___x_3234_);
v___x_3236_ = v___x_3231_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_dec(v_a_3225_);
v_a_3239_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3228_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3228_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec_ref(v_sections_3219_);
lean_dec_ref(v___f_3212_);
lean_dec_ref(v___x_3211_);
v_a_3247_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3224_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3224_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_3255_, lean_object* v___x_3256_, lean_object* v___x_3257_, lean_object* v___f_3258_, lean_object* v_x_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_Lean_Doc_instToMarkdownSnippet___lam__1(v___x_3255_, v___x_3256_, v___x_3257_, v___f_3258_, v_x_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
return v_res_3264_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___f_3267_; 
v___x_3265_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3266_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3267_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3267_, 0, v___x_3266_);
lean_closure_set(v___f_3267_, 1, v___x_3265_);
return v___f_3267_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet(void){
_start:
{
lean_object* v___x_3268_; lean_object* v_toApplicative_3269_; lean_object* v_toFunctor_3270_; lean_object* v_toSeq_3271_; lean_object* v_toSeqLeft_3272_; lean_object* v_toSeqRight_3273_; lean_object* v___f_3274_; lean_object* v___f_3275_; lean_object* v___f_3276_; lean_object* v___f_3277_; lean_object* v___x_3278_; lean_object* v___f_3279_; lean_object* v___f_3280_; lean_object* v___f_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___f_3287_; lean_object* v___f_3288_; 
v___x_3268_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3269_ = lean_ctor_get(v___x_3268_, 0);
v_toFunctor_3270_ = lean_ctor_get(v_toApplicative_3269_, 0);
v_toSeq_3271_ = lean_ctor_get(v_toApplicative_3269_, 2);
v_toSeqLeft_3272_ = lean_ctor_get(v_toApplicative_3269_, 3);
v_toSeqRight_3273_ = lean_ctor_get(v_toApplicative_3269_, 4);
v___f_3274_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3275_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3270_, 2);
v___f_3276_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3276_, 0, v_toFunctor_3270_);
v___f_3277_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3277_, 0, v_toFunctor_3270_);
v___x_3278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___f_3276_);
lean_ctor_set(v___x_3278_, 1, v___f_3277_);
lean_inc(v_toSeqRight_3273_);
v___f_3279_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3279_, 0, v_toSeqRight_3273_);
lean_inc(v_toSeqLeft_3272_);
v___f_3280_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3280_, 0, v_toSeqLeft_3272_);
lean_inc(v_toSeq_3271_);
v___f_3281_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3281_, 0, v_toSeq_3271_);
v___x_3282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3278_);
lean_ctor_set(v___x_3282_, 1, v___f_3274_);
lean_ctor_set(v___x_3282_, 2, v___f_3281_);
lean_ctor_set(v___x_3282_, 3, v___f_3280_);
lean_ctor_set(v___x_3282_, 4, v___f_3279_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
lean_ctor_set(v___x_3283_, 1, v___f_3275_);
v___x_3284_ = l_StateRefT_x27_instMonad___redArg(v___x_3283_);
v___x_3285_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3286_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3287_ = lean_obj_once(&l_Lean_Doc_instToMarkdownSnippet___closed__0, &l_Lean_Doc_instToMarkdownSnippet___closed__0_once, _init_l_Lean_Doc_instToMarkdownSnippet___closed__0);
v___f_3288_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3288_, 0, v___x_3285_);
lean_closure_set(v___f_3288_, 1, v___x_3286_);
lean_closure_set(v___f_3288_, 2, v___x_3284_);
lean_closure_set(v___f_3288_, 3, v___f_3287_);
return v___f_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(lean_object* v_opts_3289_, lean_object* v_opt_3290_){
_start:
{
lean_object* v_name_3291_; lean_object* v_defValue_3292_; lean_object* v_map_3293_; lean_object* v___x_3294_; 
v_name_3291_ = lean_ctor_get(v_opt_3290_, 0);
v_defValue_3292_ = lean_ctor_get(v_opt_3290_, 1);
v_map_3293_ = lean_ctor_get(v_opts_3289_, 0);
v___x_3294_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3293_, v_name_3291_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_inc(v_defValue_3292_);
return v_defValue_3292_;
}
else
{
lean_object* v_val_3295_; 
v_val_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_val_3295_);
lean_dec_ref_known(v___x_3294_, 1);
if (lean_obj_tag(v_val_3295_) == 3)
{
lean_object* v_v_3296_; 
v_v_3296_ = lean_ctor_get(v_val_3295_, 0);
lean_inc(v_v_3296_);
lean_dec_ref_known(v_val_3295_, 1);
return v_v_3296_;
}
else
{
lean_dec(v_val_3295_);
lean_inc(v_defValue_3292_);
return v_defValue_3292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0___boxed(lean_object* v_opts_3297_, lean_object* v_opt_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_opts_3297_, v_opt_3298_);
lean_dec_ref(v_opt_3298_);
lean_dec_ref(v_opts_3297_);
return v_res_3299_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3301_ = lean_unsigned_to_nat(1u);
v___x_3302_ = l_Lean_firstFrontendMacroScope;
v___x_3303_ = lean_nat_add(v___x_3302_, v___x_3301_);
return v___x_3303_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__6(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3314_ = lean_unsigned_to_nat(32u);
v___x_3315_ = lean_mk_empty_array_with_capacity(v___x_3314_);
v___x_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
return v___x_3316_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__7(void){
_start:
{
size_t v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3317_ = ((size_t)5ULL);
v___x_3318_ = lean_unsigned_to_nat(0u);
v___x_3319_ = lean_unsigned_to_nat(32u);
v___x_3320_ = lean_mk_empty_array_with_capacity(v___x_3319_);
v___x_3321_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__6, &l_Lean_Doc_runMarkdown___redArg___closed__6_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__6);
v___x_3322_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
lean_ctor_set(v___x_3322_, 1, v___x_3320_);
lean_ctor_set(v___x_3322_, 2, v___x_3318_);
lean_ctor_set(v___x_3322_, 3, v___x_3318_);
lean_ctor_set_usize(v___x_3322_, 4, v___x_3317_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__8(void){
_start:
{
lean_object* v___x_3323_; uint64_t v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3324_ = 0ULL;
v___x_3325_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set_uint64(v___x_3325_, sizeof(void*)*1, v___x_3324_);
return v___x_3325_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__9(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
return v___x_3327_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__10(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__9, &l_Lean_Doc_runMarkdown___redArg___closed__9_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__9);
v___x_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
return v___x_3329_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__12(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3332_ = l_Lean_Options_empty;
v___x_3333_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__11));
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
lean_ctor_set(v___x_3334_, 1, v___x_3332_);
return v___x_3334_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__13(void){
_start:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = l_Lean_NameSet_empty;
v___x_3336_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
lean_ctor_set(v___x_3337_, 2, v___x_3335_);
return v___x_3337_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__14(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; 
v___x_3338_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3339_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__9, &l_Lean_Doc_runMarkdown___redArg___closed__9_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__9);
v___x_3340_ = 1;
v___x_3341_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3341_, 0, v___x_3339_);
lean_ctor_set(v___x_3341_, 1, v___x_3339_);
lean_ctor_set(v___x_3341_, 2, v___x_3338_);
lean_ctor_set_uint8(v___x_3341_, sizeof(void*)*3, v___x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg(lean_object* v_env_3345_, lean_object* v_act_3346_, lean_object* v_options_3347_, lean_object* v_currNamespace_3348_, lean_object* v_openDecls_3349_, lean_object* v_cancelTk_x3f_3350_){
_start:
{
lean_object* v_a_3353_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; uint16_t v___x_3363_; uint8_t v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v_fileName_3379_; lean_object* v_fileMap_3380_; lean_object* v_currNamespace_3381_; lean_object* v_openDecls_3382_; lean_object* v_initHeartbeats_3383_; lean_object* v_maxHeartbeats_3384_; lean_object* v_quotContext_3385_; lean_object* v_currMacroScope_3386_; lean_object* v_cancelTk_x3f_3387_; lean_object* v_inheritedTraceOptions_3388_; lean_object* v_currRecDepth_3389_; lean_object* v_ref_3390_; uint8_t v_suppressElabErrors_3391_; uint8_t v_isRecordingDeps_3392_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; uint8_t v___y_3433_; lean_object* v_env_3454_; uint8_t v___x_3455_; uint16_t v___x_3456_; uint16_t v___x_3457_; uint16_t v___x_3458_; uint8_t v___x_3459_; 
v___x_3356_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__0));
v___x_3357_ = l_Lean_instInhabitedFileMap_default;
v___x_3358_ = lean_unsigned_to_nat(0u);
v___x_3359_ = l_Lean_Core_getMaxHeartbeats(v_options_3347_);
v___x_3360_ = lean_box(0);
v___x_3361_ = l_Lean_firstFrontendMacroScope;
v___x_3362_ = lean_box(0);
v___x_3363_ = l_Lean_OptionFlags_ofOptions(v_options_3347_);
v___x_3364_ = 0;
v___x_3365_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3366_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__4));
v___x_3367_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__5));
v___x_3368_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__8, &l_Lean_Doc_runMarkdown___redArg___closed__8_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__8);
v___x_3369_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__10, &l_Lean_Doc_runMarkdown___redArg___closed__10_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__10);
v___x_3370_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__11));
v___x_3371_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__12, &l_Lean_Doc_runMarkdown___redArg___closed__12_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__12);
v___x_3372_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__13, &l_Lean_Doc_runMarkdown___redArg___closed__13_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__13);
v___x_3373_ = 1;
v___x_3374_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__14, &l_Lean_Doc_runMarkdown___redArg___closed__14_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__14);
v___x_3375_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3375_, 0, v_env_3345_);
lean_ctor_set(v___x_3375_, 1, v___x_3365_);
lean_ctor_set(v___x_3375_, 2, v___x_3366_);
lean_ctor_set(v___x_3375_, 3, v___x_3367_);
lean_ctor_set(v___x_3375_, 4, v___x_3368_);
lean_ctor_set(v___x_3375_, 5, v___x_3369_);
lean_ctor_set(v___x_3375_, 6, v___x_3371_);
lean_ctor_set(v___x_3375_, 7, v___x_3372_);
lean_ctor_set(v___x_3375_, 8, v___x_3374_);
lean_ctor_set(v___x_3375_, 9, v___x_3370_);
v___x_3376_ = lean_io_get_num_heartbeats();
v___x_3377_ = lean_st_mk_ref(v___x_3375_);
v___x_3429_ = l_Lean_inheritedTraceOptions;
v___x_3430_ = lean_st_ref_get(v___x_3429_);
v___x_3431_ = lean_st_ref_get(v___x_3377_);
v_env_3454_ = lean_ctor_get(v___x_3431_, 0);
lean_inc_ref(v_env_3454_);
lean_dec(v___x_3431_);
v___x_3455_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3454_);
lean_dec_ref(v_env_3454_);
v___x_3456_ = 512;
v___x_3457_ = lean_uint16_land(v___x_3363_, v___x_3456_);
v___x_3458_ = 0;
v___x_3459_ = lean_uint16_dec_eq(v___x_3457_, v___x_3458_);
if (v___x_3459_ == 0)
{
if (v___x_3455_ == 0)
{
v___y_3433_ = v___x_3373_;
goto v___jp_3432_;
}
else
{
v_fileName_3379_ = v___x_3356_;
v_fileMap_3380_ = v___x_3357_;
v_currNamespace_3381_ = v_currNamespace_3348_;
v_openDecls_3382_ = v_openDecls_3349_;
v_initHeartbeats_3383_ = v___x_3376_;
v_maxHeartbeats_3384_ = v___x_3359_;
v_quotContext_3385_ = v___x_3360_;
v_currMacroScope_3386_ = v___x_3361_;
v_cancelTk_x3f_3387_ = v_cancelTk_x3f_3350_;
v_inheritedTraceOptions_3388_ = v___x_3430_;
v_currRecDepth_3389_ = v___x_3358_;
v_ref_3390_ = v___x_3362_;
v_suppressElabErrors_3391_ = v___x_3364_;
v_isRecordingDeps_3392_ = v___x_3364_;
goto v___jp_3378_;
}
}
else
{
if (v___x_3455_ == 0)
{
v_fileName_3379_ = v___x_3356_;
v_fileMap_3380_ = v___x_3357_;
v_currNamespace_3381_ = v_currNamespace_3348_;
v_openDecls_3382_ = v_openDecls_3349_;
v_initHeartbeats_3383_ = v___x_3376_;
v_maxHeartbeats_3384_ = v___x_3359_;
v_quotContext_3385_ = v___x_3360_;
v_currMacroScope_3386_ = v___x_3361_;
v_cancelTk_x3f_3387_ = v_cancelTk_x3f_3350_;
v_inheritedTraceOptions_3388_ = v___x_3430_;
v_currRecDepth_3389_ = v___x_3358_;
v_ref_3390_ = v___x_3362_;
v_suppressElabErrors_3391_ = v___x_3364_;
v_isRecordingDeps_3392_ = v___x_3364_;
goto v___jp_3378_;
}
else
{
v___y_3433_ = v___x_3364_;
goto v___jp_3432_;
}
}
v___jp_3352_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3354_ = lean_mk_io_user_error(v_a_3353_);
v___x_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
return v___x_3355_;
}
v___jp_3378_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3393_ = l_Lean_maxRecDepth;
v___x_3394_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_options_3347_, v___x_3393_);
lean_inc(v_currMacroScope_3386_);
lean_inc(v_quotContext_3385_);
lean_inc_ref(v_fileMap_3380_);
lean_inc_ref(v_fileName_3379_);
v___x_3395_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3395_, 0, v_fileName_3379_);
lean_ctor_set(v___x_3395_, 1, v_fileMap_3380_);
lean_ctor_set(v___x_3395_, 2, v_options_3347_);
lean_ctor_set(v___x_3395_, 3, v___x_3394_);
lean_ctor_set(v___x_3395_, 4, v_currNamespace_3381_);
lean_ctor_set(v___x_3395_, 5, v_openDecls_3382_);
lean_ctor_set(v___x_3395_, 6, v_initHeartbeats_3383_);
lean_ctor_set(v___x_3395_, 7, v_maxHeartbeats_3384_);
lean_ctor_set(v___x_3395_, 8, v_quotContext_3385_);
lean_ctor_set(v___x_3395_, 9, v_currMacroScope_3386_);
lean_ctor_set(v___x_3395_, 10, v_cancelTk_x3f_3387_);
lean_ctor_set(v___x_3395_, 11, v_inheritedTraceOptions_3388_);
lean_inc(v_ref_3390_);
v___x_3396_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
lean_ctor_set(v___x_3396_, 1, v_currRecDepth_3389_);
lean_ctor_set(v___x_3396_, 2, v_ref_3390_);
lean_ctor_set_uint16(v___x_3396_, sizeof(void*)*3, v___x_3363_);
lean_ctor_set_uint8(v___x_3396_, sizeof(void*)*3 + 2, v_suppressElabErrors_3391_);
lean_ctor_set_uint8(v___x_3396_, sizeof(void*)*3 + 3, v_isRecordingDeps_3392_);
lean_inc(v___x_3377_);
v___x_3397_ = lean_apply_3(v_act_3346_, v___x_3396_, v___x_3377_, lean_box(0));
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3406_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3400_ = v___x_3397_;
v_isShared_3401_ = v_isSharedCheck_3406_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3406_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3402_; lean_object* v___x_3404_; 
v___x_3402_ = lean_st_ref_get(v___x_3377_);
lean_dec(v___x_3377_);
lean_dec(v___x_3402_);
if (v_isShared_3401_ == 0)
{
v___x_3404_ = v___x_3400_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3398_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3428_; 
lean_dec(v___x_3377_);
v_a_3407_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3409_ = v___x_3397_;
v_isShared_3410_ = v_isSharedCheck_3428_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3397_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3428_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
if (lean_obj_tag(v_a_3407_) == 0)
{
lean_object* v_msg_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3415_; 
v_msg_3411_ = lean_ctor_get(v_a_3407_, 1);
lean_inc_ref(v_msg_3411_);
lean_dec_ref_known(v_a_3407_, 2);
v___x_3412_ = l_Lean_MessageData_toString(v_msg_3411_);
v___x_3413_ = lean_mk_io_user_error(v___x_3412_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3413_);
v___x_3415_ = v___x_3409_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
else
{
lean_object* v_id_3417_; lean_object* v___x_3418_; 
lean_del_object(v___x_3409_);
v_id_3417_ = lean_ctor_get(v_a_3407_, 0);
lean_inc(v_id_3417_);
lean_dec_ref_known(v_a_3407_, 2);
v___x_3418_ = l_Lean_InternalExceptionId_getName(v_id_3417_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
lean_dec(v_id_3417_);
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3418_, 1);
v___x_3420_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__15));
v___x_3421_ = l_Lean_Name_toString(v_a_3419_, v___x_3373_);
v___x_3422_ = lean_string_append(v___x_3420_, v___x_3421_);
lean_dec_ref(v___x_3421_);
v_a_3353_ = v___x_3422_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
lean_dec_ref_known(v___x_3418_, 1);
v___x_3423_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__16));
v___x_3424_ = l_Nat_reprFast(v_id_3417_);
v___x_3425_ = lean_string_append(v___x_3423_, v___x_3424_);
lean_dec_ref(v___x_3424_);
v___x_3426_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__17));
v___x_3427_ = lean_string_append(v___x_3425_, v___x_3426_);
v_a_3353_ = v___x_3427_;
goto v___jp_3352_;
}
}
}
}
}
v___jp_3432_:
{
lean_object* v___x_3434_; lean_object* v_env_3435_; lean_object* v_nextMacroScope_3436_; lean_object* v_ngen_3437_; lean_object* v_auxDeclNGen_3438_; lean_object* v_traceState_3439_; lean_object* v_recordedDeps_3440_; lean_object* v_messages_3441_; lean_object* v_infoState_3442_; lean_object* v_snapshotTasks_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3452_; 
v___x_3434_ = lean_st_ref_take(v___x_3377_);
v_env_3435_ = lean_ctor_get(v___x_3434_, 0);
v_nextMacroScope_3436_ = lean_ctor_get(v___x_3434_, 1);
v_ngen_3437_ = lean_ctor_get(v___x_3434_, 2);
v_auxDeclNGen_3438_ = lean_ctor_get(v___x_3434_, 3);
v_traceState_3439_ = lean_ctor_get(v___x_3434_, 4);
v_recordedDeps_3440_ = lean_ctor_get(v___x_3434_, 6);
v_messages_3441_ = lean_ctor_get(v___x_3434_, 7);
v_infoState_3442_ = lean_ctor_get(v___x_3434_, 8);
v_snapshotTasks_3443_ = lean_ctor_get(v___x_3434_, 9);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3452_ == 0)
{
lean_object* v_unused_3453_; 
v_unused_3453_ = lean_ctor_get(v___x_3434_, 5);
lean_dec(v_unused_3453_);
v___x_3445_ = v___x_3434_;
v_isShared_3446_ = v_isSharedCheck_3452_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_snapshotTasks_3443_);
lean_inc(v_infoState_3442_);
lean_inc(v_messages_3441_);
lean_inc(v_recordedDeps_3440_);
lean_inc(v_traceState_3439_);
lean_inc(v_auxDeclNGen_3438_);
lean_inc(v_ngen_3437_);
lean_inc(v_nextMacroScope_3436_);
lean_inc(v_env_3435_);
lean_dec(v___x_3434_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3452_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v___x_3449_; 
v___x_3447_ = l_Lean_Kernel_enableDiag(v_env_3435_, v___y_3433_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 5, v___x_3369_);
lean_ctor_set(v___x_3445_, 0, v___x_3447_);
v___x_3449_ = v___x_3445_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3447_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_nextMacroScope_3436_);
lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_ngen_3437_);
lean_ctor_set(v_reuseFailAlloc_3451_, 3, v_auxDeclNGen_3438_);
lean_ctor_set(v_reuseFailAlloc_3451_, 4, v_traceState_3439_);
lean_ctor_set(v_reuseFailAlloc_3451_, 5, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3451_, 6, v_recordedDeps_3440_);
lean_ctor_set(v_reuseFailAlloc_3451_, 7, v_messages_3441_);
lean_ctor_set(v_reuseFailAlloc_3451_, 8, v_infoState_3442_);
lean_ctor_set(v_reuseFailAlloc_3451_, 9, v_snapshotTasks_3443_);
v___x_3449_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3450_; 
v___x_3450_ = lean_st_ref_put(v___x_3377_, v___x_3449_);
v_fileName_3379_ = v___x_3356_;
v_fileMap_3380_ = v___x_3357_;
v_currNamespace_3381_ = v_currNamespace_3348_;
v_openDecls_3382_ = v_openDecls_3349_;
v_initHeartbeats_3383_ = v___x_3376_;
v_maxHeartbeats_3384_ = v___x_3359_;
v_quotContext_3385_ = v___x_3360_;
v_currMacroScope_3386_ = v___x_3361_;
v_cancelTk_x3f_3387_ = v_cancelTk_x3f_3350_;
v_inheritedTraceOptions_3388_ = v___x_3430_;
v_currRecDepth_3389_ = v___x_3358_;
v_ref_3390_ = v___x_3362_;
v_suppressElabErrors_3391_ = v___x_3364_;
v_isRecordingDeps_3392_ = v___x_3364_;
goto v___jp_3378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg___boxed(lean_object* v_env_3460_, lean_object* v_act_3461_, lean_object* v_options_3462_, lean_object* v_currNamespace_3463_, lean_object* v_openDecls_3464_, lean_object* v_cancelTk_x3f_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Doc_runMarkdown___redArg(v_env_3460_, v_act_3461_, v_options_3462_, v_currNamespace_3463_, v_openDecls_3464_, v_cancelTk_x3f_3465_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown(lean_object* v_00_u03b1_3468_, lean_object* v_env_3469_, lean_object* v_act_3470_, lean_object* v_options_3471_, lean_object* v_currNamespace_3472_, lean_object* v_openDecls_3473_, lean_object* v_cancelTk_x3f_3474_){
_start:
{
lean_object* v___x_3476_; 
v___x_3476_ = l_Lean_Doc_runMarkdown___redArg(v_env_3469_, v_act_3470_, v_options_3471_, v_currNamespace_3472_, v_openDecls_3473_, v_cancelTk_x3f_3474_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___boxed(lean_object* v_00_u03b1_3477_, lean_object* v_env_3478_, lean_object* v_act_3479_, lean_object* v_options_3480_, lean_object* v_currNamespace_3481_, lean_object* v_openDecls_3482_, lean_object* v_cancelTk_x3f_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_Doc_runMarkdown(v_00_u03b1_3477_, v_env_3478_, v_act_3479_, v_options_3480_, v_currNamespace_3481_, v_openDecls_3482_, v_cancelTk_x3f_3483_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(lean_object* v_x_3486_, size_t v_sz_3487_, size_t v_i_3488_, lean_object* v_bs_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
uint8_t v___x_3494_; 
v___x_3494_ = lean_usize_dec_lt(v_i_3488_, v_sz_3487_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; 
lean_dec_ref(v_x_3486_);
v___x_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3495_, 0, v_bs_3489_);
return v___x_3495_;
}
else
{
lean_object* v_v_3496_; lean_object* v___x_3497_; lean_object* v_bs_x27_3498_; lean_object* v___x_3499_; 
v_v_3496_ = lean_array_uget(v_bs_3489_, v_i_3488_);
v___x_3497_ = lean_unsigned_to_nat(0u);
v_bs_x27_3498_ = lean_array_uset(v_bs_3489_, v_i_3488_, v___x_3497_);
lean_inc_ref(v_x_3486_);
v___x_3499_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3486_, v_v_3496_, v___y_3490_, v___y_3491_, v___y_3492_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; size_t v___x_3501_; size_t v___x_3502_; lean_object* v___x_3503_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v___x_3501_ = ((size_t)1ULL);
v___x_3502_ = lean_usize_add(v_i_3488_, v___x_3501_);
v___x_3503_ = lean_array_uset(v_bs_x27_3498_, v_i_3488_, v_a_3500_);
v_i_3488_ = v___x_3502_;
v_bs_3489_ = v___x_3503_;
goto _start;
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref(v_bs_x27_3498_);
lean_dec_ref(v_x_3486_);
v_a_3505_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3499_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3499_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed(lean_object* v_x_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(v_x_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(lean_object* v_x_3522_, size_t v_sz_3523_, size_t v___x_3524_, lean_object* v_content_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3522_, v_sz_3523_, v___x_3524_, v_content_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3539_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3533_ = v___x_3530_;
v_isShared_3534_ = v_isSharedCheck_3539_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3539_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3535_; lean_object* v___x_3537_; 
v___x_3535_ = l_Lean_Doc_joinInlines(v_a_3531_);
lean_dec(v_a_3531_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v___x_3535_);
v___x_3537_ = v___x_3533_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
v_a_3540_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3530_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3530_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed(lean_object* v_x_3548_, lean_object* v_sz_3549_, lean_object* v___x_3550_, lean_object* v_content_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
size_t v_sz_boxed_3556_; size_t v___x_3984__boxed_3557_; lean_object* v_res_3558_; 
v_sz_boxed_3556_ = lean_unbox_usize(v_sz_3549_);
lean_dec(v_sz_3549_);
v___x_3984__boxed_3557_ = lean_unbox_usize(v___x_3550_);
lean_dec(v___x_3550_);
v_res_3558_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(v_x_3548_, v_sz_boxed_3556_, v___x_3984__boxed_3557_, v_content_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(lean_object* v_x_3559_, lean_object* v_x_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v_pieces_3566_; lean_object* v_pieces_3570_; 
switch(lean_obj_tag(v_x_3560_))
{
case 0:
{
lean_object* v_string_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
lean_dec_ref(v_x_3559_);
v_string_3573_ = lean_ctor_get(v_x_3560_, 0);
lean_inc_ref(v_string_3573_);
lean_dec_ref_known(v_x_3560_, 1);
v___x_3574_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_3573_);
lean_dec_ref(v_string_3573_);
v___x_3575_ = lean_unsigned_to_nat(1u);
v___x_3576_ = lean_mk_empty_array_with_capacity(v___x_3575_);
v___x_3577_ = lean_array_push(v___x_3576_, v___x_3574_);
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
return v___x_3578_;
}
case 1:
{
lean_object* v_content_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3634_; 
v_content_3579_ = lean_ctor_get(v_x_3560_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_x_3560_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3581_ = v_x_3560_;
v_isShared_3582_ = v_isSharedCheck_3634_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_content_3579_);
lean_dec(v_x_3560_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3634_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set_tag(v___x_3581_, 9);
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_content_3579_);
v___x_3584_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; lean_object* v_snd_3586_; lean_object* v_fst_3587_; lean_object* v_fst_3588_; lean_object* v_snd_3589_; lean_object* v_pieces_3591_; uint8_t v_inEmph_3599_; uint8_t v_inBold_3600_; uint8_t v_inLink_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3632_; 
v___x_3585_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3584_);
v_snd_3586_ = lean_ctor_get(v___x_3585_, 1);
lean_inc(v_snd_3586_);
v_fst_3587_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_fst_3587_);
lean_dec_ref(v___x_3585_);
v_fst_3588_ = lean_ctor_get(v_snd_3586_, 0);
lean_inc(v_fst_3588_);
v_snd_3589_ = lean_ctor_get(v_snd_3586_, 1);
lean_inc(v_snd_3589_);
lean_dec(v_snd_3586_);
v_inEmph_3599_ = lean_ctor_get_uint8(v_x_3559_, 0);
v_inBold_3600_ = lean_ctor_get_uint8(v_x_3559_, 1);
v_inLink_3601_ = lean_ctor_get_uint8(v_x_3559_, 2);
v_isSharedCheck_3632_ = !lean_is_exclusive(v_x_3559_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3603_ = v_x_3559_;
v_isShared_3604_ = v_isSharedCheck_3632_;
goto v_resetjp_3602_;
}
else
{
lean_dec(v_x_3559_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3632_;
goto v_resetjp_3602_;
}
v___jp_3590_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; uint8_t v___x_3594_; 
v___x_3592_ = lean_string_utf8_byte_size(v_snd_3589_);
v___x_3593_ = lean_unsigned_to_nat(0u);
v___x_3594_ = lean_nat_dec_eq(v___x_3592_, v___x_3593_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3595_ = lean_unsigned_to_nat(1u);
v___x_3596_ = lean_mk_empty_array_with_capacity(v___x_3595_);
v___x_3597_ = lean_array_push(v___x_3596_, v_snd_3589_);
v___x_3598_ = lean_array_push(v_pieces_3591_, v___x_3597_);
v_pieces_3570_ = v___x_3598_;
goto v___jp_3569_;
}
else
{
lean_dec(v_snd_3589_);
v_pieces_3570_ = v_pieces_3591_;
goto v___jp_3569_;
}
}
v_resetjp_3602_:
{
uint8_t v___x_3605_; lean_object* v___x_3607_; 
v___x_3605_ = 1;
if (v_isShared_3604_ == 0)
{
v___x_3607_ = v___x_3603_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3631_, 1, v_inBold_3600_);
lean_ctor_set_uint8(v_reuseFailAlloc_3631_, 2, v_inLink_3601_);
v___x_3607_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3608_; 
lean_ctor_set_uint8(v___x_3607_, 0, v___x_3605_);
v___x_3608_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3607_, v_fst_3588_, v_a_3561_, v_a_3562_, v_a_3563_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v_pieces_3611_; lean_object* v_pieces_3618_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
v___x_3623_ = lean_unsigned_to_nat(0u);
v___x_3624_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3625_ = lean_string_utf8_byte_size(v_fst_3587_);
v___x_3626_ = lean_nat_dec_eq(v___x_3625_, v___x_3623_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3627_ = lean_unsigned_to_nat(1u);
v___x_3628_ = lean_mk_empty_array_with_capacity(v___x_3627_);
v___x_3629_ = lean_array_push(v___x_3628_, v_fst_3587_);
v___x_3630_ = lean_array_push(v___x_3624_, v___x_3629_);
v_pieces_3618_ = v___x_3630_;
goto v___jp_3617_;
}
else
{
lean_dec(v_fst_3587_);
v_pieces_3618_ = v___x_3624_;
goto v___jp_3617_;
}
v___jp_3610_:
{
lean_object* v___x_3612_; 
v___x_3612_ = lean_array_push(v_pieces_3611_, v_a_3609_);
if (v_inEmph_3599_ == 0)
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3613_ = lean_unsigned_to_nat(1u);
v___x_3614_ = lean_mk_empty_array_with_capacity(v___x_3613_);
lean_dec_ref(v___x_3614_);
v___x_3615_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3616_ = lean_array_push(v___x_3612_, v___x_3615_);
v_pieces_3591_ = v___x_3616_;
goto v___jp_3590_;
}
else
{
v_pieces_3591_ = v___x_3612_;
goto v___jp_3590_;
}
}
v___jp_3617_:
{
if (v_inEmph_3599_ == 0)
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3619_ = lean_unsigned_to_nat(1u);
v___x_3620_ = lean_mk_empty_array_with_capacity(v___x_3619_);
lean_dec_ref(v___x_3620_);
v___x_3621_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3622_ = lean_array_push(v_pieces_3618_, v___x_3621_);
v_pieces_3611_ = v___x_3622_;
goto v___jp_3610_;
}
else
{
v_pieces_3611_ = v_pieces_3618_;
goto v___jp_3610_;
}
}
}
else
{
lean_dec(v_snd_3589_);
lean_dec(v_fst_3587_);
return v___x_3608_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3690_; 
v_content_3635_ = lean_ctor_get(v_x_3560_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_x_3560_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3637_ = v_x_3560_;
v_isShared_3638_ = v_isSharedCheck_3690_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_content_3635_);
lean_dec(v_x_3560_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3690_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set_tag(v___x_3637_, 9);
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_content_3635_);
v___x_3640_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3641_; lean_object* v_snd_3642_; lean_object* v_fst_3643_; lean_object* v_fst_3644_; lean_object* v_snd_3645_; lean_object* v_pieces_3647_; uint8_t v_inEmph_3655_; uint8_t v_inBold_3656_; uint8_t v_inLink_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3688_; 
v___x_3641_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3640_);
v_snd_3642_ = lean_ctor_get(v___x_3641_, 1);
lean_inc(v_snd_3642_);
v_fst_3643_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_fst_3643_);
lean_dec_ref(v___x_3641_);
v_fst_3644_ = lean_ctor_get(v_snd_3642_, 0);
lean_inc(v_fst_3644_);
v_snd_3645_ = lean_ctor_get(v_snd_3642_, 1);
lean_inc(v_snd_3645_);
lean_dec(v_snd_3642_);
v_inEmph_3655_ = lean_ctor_get_uint8(v_x_3559_, 0);
v_inBold_3656_ = lean_ctor_get_uint8(v_x_3559_, 1);
v_inLink_3657_ = lean_ctor_get_uint8(v_x_3559_, 2);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_x_3559_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3659_ = v_x_3559_;
v_isShared_3660_ = v_isSharedCheck_3688_;
goto v_resetjp_3658_;
}
else
{
lean_dec(v_x_3559_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3688_;
goto v_resetjp_3658_;
}
v___jp_3646_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v___x_3648_ = lean_string_utf8_byte_size(v_snd_3645_);
v___x_3649_ = lean_unsigned_to_nat(0u);
v___x_3650_ = lean_nat_dec_eq(v___x_3648_, v___x_3649_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3651_ = lean_unsigned_to_nat(1u);
v___x_3652_ = lean_mk_empty_array_with_capacity(v___x_3651_);
v___x_3653_ = lean_array_push(v___x_3652_, v_snd_3645_);
v___x_3654_ = lean_array_push(v_pieces_3647_, v___x_3653_);
v_pieces_3566_ = v___x_3654_;
goto v___jp_3565_;
}
else
{
lean_dec(v_snd_3645_);
v_pieces_3566_ = v_pieces_3647_;
goto v___jp_3565_;
}
}
v_resetjp_3658_:
{
uint8_t v___x_3661_; lean_object* v___x_3663_; 
v___x_3661_ = 1;
if (v_isShared_3660_ == 0)
{
v___x_3663_ = v___x_3659_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, 0, v_inEmph_3655_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, 2, v_inLink_3657_);
v___x_3663_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; 
lean_ctor_set_uint8(v___x_3663_, 1, v___x_3661_);
v___x_3664_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3663_, v_fst_3644_, v_a_3561_, v_a_3562_, v_a_3563_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v_pieces_3667_; lean_object* v_pieces_3674_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3664_, 1);
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3680_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3681_ = lean_string_utf8_byte_size(v_fst_3643_);
v___x_3682_ = lean_nat_dec_eq(v___x_3681_, v___x_3679_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3683_ = lean_unsigned_to_nat(1u);
v___x_3684_ = lean_mk_empty_array_with_capacity(v___x_3683_);
v___x_3685_ = lean_array_push(v___x_3684_, v_fst_3643_);
v___x_3686_ = lean_array_push(v___x_3680_, v___x_3685_);
v_pieces_3674_ = v___x_3686_;
goto v___jp_3673_;
}
else
{
lean_dec(v_fst_3643_);
v_pieces_3674_ = v___x_3680_;
goto v___jp_3673_;
}
v___jp_3666_:
{
lean_object* v___x_3668_; 
v___x_3668_ = lean_array_push(v_pieces_3667_, v_a_3665_);
if (v_inBold_3656_ == 0)
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3669_ = lean_unsigned_to_nat(1u);
v___x_3670_ = lean_mk_empty_array_with_capacity(v___x_3669_);
lean_dec_ref(v___x_3670_);
v___x_3671_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3672_ = lean_array_push(v___x_3668_, v___x_3671_);
v_pieces_3647_ = v___x_3672_;
goto v___jp_3646_;
}
else
{
v_pieces_3647_ = v___x_3668_;
goto v___jp_3646_;
}
}
v___jp_3673_:
{
if (v_inBold_3656_ == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3675_ = lean_unsigned_to_nat(1u);
v___x_3676_ = lean_mk_empty_array_with_capacity(v___x_3675_);
lean_dec_ref(v___x_3676_);
v___x_3677_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3678_ = lean_array_push(v_pieces_3674_, v___x_3677_);
v_pieces_3667_ = v___x_3678_;
goto v___jp_3666_;
}
else
{
v_pieces_3667_ = v_pieces_3674_;
goto v___jp_3666_;
}
}
}
else
{
lean_dec(v_snd_3645_);
lean_dec(v_fst_3643_);
return v___x_3664_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
lean_dec_ref(v_x_3559_);
v_string_3691_ = lean_ctor_get(v_x_3560_, 0);
lean_inc_ref(v_string_3691_);
lean_dec_ref_known(v_x_3560_, 1);
v___x_3692_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_3691_);
v___x_3693_ = lean_unsigned_to_nat(1u);
v___x_3694_ = lean_mk_empty_array_with_capacity(v___x_3693_);
v___x_3695_ = lean_array_push(v___x_3694_, v___x_3692_);
v___x_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3695_);
return v___x_3696_;
}
case 4:
{
uint8_t v_mode_3697_; 
lean_dec_ref(v_x_3559_);
v_mode_3697_ = lean_ctor_get_uint8(v_x_3560_, sizeof(void*)*1);
if (v_mode_3697_ == 0)
{
lean_object* v_string_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v_string_3698_ = lean_ctor_get(v_x_3560_, 0);
lean_inc_ref(v_string_3698_);
lean_dec_ref_known(v_x_3560_, 1);
v___x_3699_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_3700_ = lean_string_append(v___x_3699_, v_string_3698_);
lean_dec_ref(v_string_3698_);
v___x_3701_ = lean_string_append(v___x_3700_, v___x_3699_);
v___x_3702_ = lean_unsigned_to_nat(1u);
v___x_3703_ = lean_mk_empty_array_with_capacity(v___x_3702_);
v___x_3704_ = lean_array_push(v___x_3703_, v___x_3701_);
v___x_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
return v___x_3705_;
}
else
{
lean_object* v_string_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v_string_3706_ = lean_ctor_get(v_x_3560_, 0);
lean_inc_ref(v_string_3706_);
lean_dec_ref_known(v_x_3560_, 1);
v___x_3707_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_3708_ = lean_string_append(v___x_3707_, v_string_3706_);
lean_dec_ref(v_string_3706_);
v___x_3709_ = lean_string_append(v___x_3708_, v___x_3707_);
v___x_3710_ = lean_unsigned_to_nat(1u);
v___x_3711_ = lean_mk_empty_array_with_capacity(v___x_3710_);
v___x_3712_ = lean_array_push(v___x_3711_, v___x_3709_);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
return v___x_3713_;
}
}
case 5:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
lean_dec_ref_known(v_x_3560_, 1);
lean_dec_ref(v_x_3559_);
v___x_3714_ = lean_unsigned_to_nat(2u);
v___x_3715_ = lean_mk_empty_array_with_capacity(v___x_3714_);
lean_dec_ref(v___x_3715_);
v___x_3716_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
return v___x_3717_;
}
case 6:
{
uint8_t v_inLink_3718_; 
v_inLink_3718_ = lean_ctor_get_uint8(v_x_3559_, 2);
if (v_inLink_3718_ == 0)
{
lean_object* v_content_3719_; lean_object* v_url_3720_; uint8_t v_inEmph_3721_; uint8_t v_inBold_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3753_; 
v_content_3719_ = lean_ctor_get(v_x_3560_, 0);
lean_inc_ref(v_content_3719_);
v_url_3720_ = lean_ctor_get(v_x_3560_, 1);
lean_inc_ref(v_url_3720_);
lean_dec_ref_known(v_x_3560_, 2);
v_inEmph_3721_ = lean_ctor_get_uint8(v_x_3559_, 0);
v_inBold_3722_ = lean_ctor_get_uint8(v_x_3559_, 1);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_x_3559_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3724_ = v_x_3559_;
v_isShared_3725_ = v_isSharedCheck_3753_;
goto v_resetjp_3723_;
}
else
{
lean_dec(v_x_3559_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3753_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
uint8_t v___x_3726_; lean_object* v___x_3728_; 
v___x_3726_ = 1;
if (v_isShared_3725_ == 0)
{
v___x_3728_ = v___x_3724_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3752_, 0, v_inEmph_3721_);
lean_ctor_set_uint8(v_reuseFailAlloc_3752_, 1, v_inBold_3722_);
v___x_3728_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
lean_ctor_set_uint8(v___x_3728_, 2, v___x_3726_);
v___x_3729_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3729_, 0, v_content_3719_);
v___x_3730_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3728_, v___x_3729_, v_a_3561_, v_a_3562_, v_a_3563_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3751_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3733_ = v___x_3730_;
v_isShared_3734_ = v_isSharedCheck_3751_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3730_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3751_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3735_ = lean_unsigned_to_nat(1u);
v___x_3736_ = lean_mk_empty_array_with_capacity(v___x_3735_);
v___x_3737_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3738_ = lean_string_append(v___x_3737_, v_url_3720_);
lean_dec_ref(v_url_3720_);
v___x_3739_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3740_ = lean_string_append(v___x_3738_, v___x_3739_);
v___x_3741_ = lean_array_push(v___x_3736_, v___x_3740_);
v___x_3742_ = lean_unsigned_to_nat(3u);
v___x_3743_ = lean_mk_empty_array_with_capacity(v___x_3742_);
lean_dec_ref(v___x_3743_);
v___x_3744_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_3745_ = lean_array_push(v___x_3744_, v_a_3731_);
v___x_3746_ = lean_array_push(v___x_3745_, v___x_3741_);
v___x_3747_ = l_Lean_Doc_joinInlines(v___x_3746_);
lean_dec_ref(v___x_3746_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 0, v___x_3747_);
v___x_3749_ = v___x_3733_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
else
{
lean_dec_ref(v_url_3720_);
return v___x_3730_;
}
}
}
}
else
{
lean_object* v_content_3754_; size_t v_sz_3755_; size_t v___x_3756_; lean_object* v___x_3757_; 
v_content_3754_ = lean_ctor_get(v_x_3560_, 0);
lean_inc_ref(v_content_3754_);
lean_dec_ref_known(v_x_3560_, 2);
v_sz_3755_ = lean_array_size(v_content_3754_);
v___x_3756_ = ((size_t)0ULL);
v___x_3757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3559_, v_sz_3755_, v___x_3756_, v_content_3754_, v_a_3561_, v_a_3562_, v_a_3563_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3766_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3760_ = v___x_3757_;
v_isShared_3761_ = v_isSharedCheck_3766_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3757_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3766_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3762_; lean_object* v___x_3764_; 
v___x_3762_ = l_Lean_Doc_joinInlines(v_a_3758_);
lean_dec(v_a_3758_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 0, v___x_3762_);
v___x_3764_ = v___x_3760_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
v_a_3767_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3757_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3757_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
}
case 7:
{
lean_object* v_name_3775_; lean_object* v_content_3776_; size_t v_sz_3777_; size_t v___x_3778_; lean_object* v___x_3779_; 
v_name_3775_ = lean_ctor_get(v_x_3560_, 0);
lean_inc_ref(v_name_3775_);
v_content_3776_ = lean_ctor_get(v_x_3560_, 1);
lean_inc_ref(v_content_3776_);
lean_dec_ref_known(v_x_3560_, 2);
v_sz_3777_ = lean_array_size(v_content_3776_);
v___x_3778_ = ((size_t)0ULL);
v___x_3779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3559_, v_sz_3777_, v___x_3778_, v_content_3776_, v_a_3561_, v_a_3562_, v_a_3563_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v___x_3781_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_3782_ = l_Lean_Doc_joinInlines(v_a_3780_);
lean_dec(v_a_3780_);
v___x_3783_ = lean_array_to_list(v___x_3782_);
v___x_3784_ = l_String_intercalate(v___x_3781_, v___x_3783_);
lean_inc_ref(v_name_3775_);
v___x_3785_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_3775_, v___x_3784_, v_a_3561_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3799_; 
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; 
v_unused_3800_ = lean_ctor_get(v___x_3785_, 0);
lean_dec(v_unused_3800_);
v___x_3787_ = v___x_3785_;
v_isShared_3788_ = v_isSharedCheck_3799_;
goto v_resetjp_3786_;
}
else
{
lean_dec(v___x_3785_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3799_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3789_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_3790_ = lean_string_append(v___x_3789_, v_name_3775_);
lean_dec_ref(v_name_3775_);
v___x_3791_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_3792_ = lean_string_append(v___x_3790_, v___x_3791_);
v___x_3793_ = lean_unsigned_to_nat(1u);
v___x_3794_ = lean_mk_empty_array_with_capacity(v___x_3793_);
v___x_3795_ = lean_array_push(v___x_3794_, v___x_3792_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3795_);
v___x_3797_ = v___x_3787_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec_ref(v_name_3775_);
v_a_3801_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3785_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3785_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec_ref(v_name_3775_);
v_a_3809_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3779_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3779_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
case 8:
{
lean_object* v_alt_3817_; lean_object* v_url_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
lean_dec_ref(v_x_3559_);
v_alt_3817_ = lean_ctor_get(v_x_3560_, 0);
lean_inc_ref(v_alt_3817_);
v_url_3818_ = lean_ctor_get(v_x_3560_, 1);
lean_inc_ref(v_url_3818_);
lean_dec_ref_known(v_x_3560_, 2);
v___x_3819_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_3820_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_3817_);
lean_dec_ref(v_alt_3817_);
v___x_3821_ = lean_string_append(v___x_3819_, v___x_3820_);
lean_dec_ref(v___x_3820_);
v___x_3822_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3823_ = lean_string_append(v___x_3821_, v___x_3822_);
v___x_3824_ = lean_string_append(v___x_3823_, v_url_3818_);
lean_dec_ref(v_url_3818_);
v___x_3825_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3826_ = lean_string_append(v___x_3824_, v___x_3825_);
v___x_3827_ = lean_unsigned_to_nat(1u);
v___x_3828_ = lean_mk_empty_array_with_capacity(v___x_3827_);
v___x_3829_ = lean_array_push(v___x_3828_, v___x_3826_);
v___x_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
return v___x_3830_;
}
case 9:
{
lean_object* v_content_3831_; size_t v_sz_3832_; size_t v___x_3833_; lean_object* v___x_3834_; 
v_content_3831_ = lean_ctor_get(v_x_3560_, 0);
lean_inc_ref(v_content_3831_);
lean_dec_ref_known(v_x_3560_, 1);
v_sz_3832_ = lean_array_size(v_content_3831_);
v___x_3833_ = ((size_t)0ULL);
v___x_3834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3559_, v_sz_3832_, v___x_3833_, v_content_3831_, v_a_3561_, v_a_3562_, v_a_3563_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3843_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3837_ = v___x_3834_;
v_isShared_3838_ = v_isSharedCheck_3843_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3843_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; lean_object* v___x_3841_; 
v___x_3839_ = l_Lean_Doc_joinInlines(v_a_3835_);
lean_dec(v_a_3835_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v___x_3839_);
v___x_3841_ = v___x_3837_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
v_a_3844_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3834_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3834_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
default: 
{
lean_object* v_container_3852_; 
v_container_3852_ = lean_ctor_get(v_x_3560_, 0);
if (lean_obj_tag(v_container_3852_) == 0)
{
lean_object* v_content_3853_; lean_object* v_val_3854_; lean_object* v___f_3855_; size_t v_sz_3856_; size_t v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v_fallback_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_inc_ref(v_container_3852_);
v_content_3853_ = lean_ctor_get(v_x_3560_, 1);
lean_inc_ref_n(v_content_3853_, 2);
lean_dec_ref_known(v_x_3560_, 2);
v_val_3854_ = lean_ctor_get(v_container_3852_, 0);
lean_inc(v_val_3854_);
lean_dec_ref_known(v_container_3852_, 1);
lean_inc_ref_n(v_x_3559_, 2);
v___f_3855_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3855_, 0, v_x_3559_);
v_sz_3856_ = lean_array_size(v_content_3853_);
v___x_3857_ = ((size_t)0ULL);
v___x_3858_ = lean_box_usize(v_sz_3856_);
v___x_3859_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
v_fallback_3860_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v_fallback_3860_, 0, v_x_3559_);
lean_closure_set(v_fallback_3860_, 1, v___x_3858_);
lean_closure_set(v_fallback_3860_, 2, v___x_3859_);
lean_closure_set(v_fallback_3860_, 3, v_content_3853_);
v___x_3861_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3854_);
v___x_3862_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_3861_, v_a_3562_, v_a_3563_);
lean_dec(v___x_3861_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_a_3863_; 
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref_known(v___x_3862_, 1);
if (lean_obj_tag(v_a_3863_) == 0)
{
lean_object* v___x_3864_; 
lean_dec_ref(v_fallback_3860_);
lean_dec_ref(v___f_3855_);
lean_dec(v_val_3854_);
v___x_3864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3559_, v_sz_3856_, v___x_3857_, v_content_3853_, v_a_3561_, v_a_3562_, v_a_3563_);
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
lean_object* v_val_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
lean_dec_ref(v_x_3559_);
v_val_3882_ = lean_ctor_get(v_a_3863_, 0);
lean_inc(v_val_3882_);
lean_dec_ref_known(v_a_3863_, 1);
v___x_3883_ = lean_apply_3(v_val_3882_, v___f_3855_, v_val_3854_, v_content_3853_);
v___x_3884_ = l_Lean_Doc_withRendererFallback(v_fallback_3860_, v___x_3883_, v_a_3561_, v_a_3562_, v_a_3563_);
return v___x_3884_;
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
lean_dec_ref(v_fallback_3860_);
lean_dec_ref(v___f_3855_);
lean_dec(v_val_3854_);
lean_dec_ref(v_content_3853_);
lean_dec_ref(v_x_3559_);
v_a_3885_ = lean_ctor_get(v___x_3862_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3862_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3862_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3862_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
else
{
lean_object* v_content_3893_; size_t v_sz_3894_; size_t v___x_3895_; lean_object* v___x_3896_; 
v_content_3893_ = lean_ctor_get(v_x_3560_, 1);
lean_inc_ref(v_content_3893_);
lean_dec_ref_known(v_x_3560_, 2);
v_sz_3894_ = lean_array_size(v_content_3893_);
v___x_3895_ = ((size_t)0ULL);
v___x_3896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3559_, v_sz_3894_, v___x_3895_, v_content_3893_, v_a_3561_, v_a_3562_, v_a_3563_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3905_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3899_ = v___x_3896_;
v_isShared_3900_ = v_isSharedCheck_3905_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3896_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3905_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3901_ = l_Lean_Doc_joinInlines(v_a_3897_);
lean_dec(v_a_3897_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v___x_3901_);
v___x_3903_ = v___x_3899_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3901_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
v_a_3906_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3896_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3896_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
}
}
v___jp_3565_:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = l_Lean_Doc_joinInlines(v_pieces_3566_);
lean_dec_ref(v_pieces_3566_);
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
return v___x_3568_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(lean_object* v_x_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3921_, lean_object* v_sz_3922_, lean_object* v_i_3923_, lean_object* v_bs_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
size_t v_sz_boxed_3929_; size_t v_i_boxed_3930_; lean_object* v_res_3931_; 
v_sz_boxed_3929_ = lean_unbox_usize(v_sz_3922_);
lean_dec(v_sz_3922_);
v_i_boxed_3930_ = lean_unbox_usize(v_i_3923_);
lean_dec(v_i_3923_);
v_res_3931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3921_, v_sz_boxed_3929_, v_i_boxed_3930_, v_bs_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed(lean_object* v_x_3932_, lean_object* v_x_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3932_, v_x_3933_, v_a_3934_, v_a_3935_, v_a_3936_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(lean_object* v___x_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0___boxed(lean_object* v___x_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(v___x_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(lean_object* v_x_3953_, lean_object* v_x_3954_){
_start:
{
lean_object* v_zero_3955_; uint8_t v_isZero_3956_; 
v_zero_3955_ = lean_unsigned_to_nat(0u);
v_isZero_3956_ = lean_nat_dec_eq(v_x_3953_, v_zero_3955_);
if (v_isZero_3956_ == 1)
{
lean_dec(v_x_3953_);
return v_x_3954_;
}
else
{
uint32_t v___x_3957_; lean_object* v_one_3958_; lean_object* v_n_3959_; lean_object* v___x_3960_; 
v___x_3957_ = 32;
v_one_3958_ = lean_unsigned_to_nat(1u);
v_n_3959_ = lean_nat_sub(v_x_3953_, v_one_3958_);
lean_dec(v_x_3953_);
v___x_3960_ = lean_string_push(v_x_3954_, v___x_3957_);
v_x_3953_ = v_n_3959_;
v_x_3954_ = v___x_3960_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(size_t v_sz_3962_, size_t v_i_3963_, lean_object* v_bs_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
uint8_t v___x_3969_; 
v___x_3969_ = lean_usize_dec_lt(v_i_3963_, v_sz_3962_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3970_; 
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v_bs_3964_);
return v___x_3970_;
}
else
{
lean_object* v_v_3971_; lean_object* v___x_3972_; lean_object* v_bs_x27_3973_; size_t v_sz_3974_; size_t v___x_3975_; lean_object* v___x_3976_; 
v_v_3971_ = lean_array_uget(v_bs_3964_, v_i_3963_);
v___x_3972_ = lean_unsigned_to_nat(0u);
v_bs_x27_3973_ = lean_array_uset(v_bs_3964_, v_i_3963_, v___x_3972_);
v_sz_3974_ = lean_array_size(v_v_3971_);
v___x_3975_ = ((size_t)0ULL);
v___x_3976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_3974_, v___x_3975_, v_v_3971_, v___y_3965_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; size_t v___x_3982_; size_t v___x_3983_; lean_object* v___x_3984_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v___x_3978_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_3979_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_3980_ = l_Lean_Doc_joinBlocks(v_a_3977_);
lean_dec(v_a_3977_);
v___x_3981_ = l_Lean_Doc_prefixListLines(v___x_3978_, v___x_3979_, v___x_3980_);
v___x_3982_ = ((size_t)1ULL);
v___x_3983_ = lean_usize_add(v_i_3963_, v___x_3982_);
v___x_3984_ = lean_array_uset(v_bs_x27_3973_, v_i_3963_, v___x_3981_);
v_i_3963_ = v___x_3983_;
v_bs_3964_ = v___x_3984_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_3973_);
return v___x_3976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(lean_object* v_as_3986_, size_t v_sz_3987_, size_t v_i_3988_, lean_object* v_b_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
uint8_t v___x_3994_; 
v___x_3994_ = lean_usize_dec_lt(v_i_3988_, v_sz_3987_);
if (v___x_3994_ == 0)
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3995_, 0, v_b_3989_);
return v___x_3995_;
}
else
{
lean_object* v_fst_3996_; lean_object* v_snd_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4031_; 
v_fst_3996_ = lean_ctor_get(v_b_3989_, 0);
v_snd_3997_ = lean_ctor_get(v_b_3989_, 1);
v_isSharedCheck_4031_ = !lean_is_exclusive(v_b_3989_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_3999_ = v_b_3989_;
v_isShared_4000_ = v_isSharedCheck_4031_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_snd_3997_);
lean_inc(v_fst_3996_);
lean_dec(v_b_3989_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4031_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4001_; lean_object* v_a_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; size_t v_sz_4009_; size_t v___x_4010_; lean_object* v___x_4011_; 
v___x_4001_ = lean_unsigned_to_nat(1u);
v_a_4002_ = lean_array_uget_borrowed(v_as_3986_, v_i_3988_);
lean_inc(v_snd_3997_);
v___x_4003_ = l_Nat_reprFast(v_snd_3997_);
v___x_4004_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_4005_ = lean_string_append(v___x_4003_, v___x_4004_);
v___x_4006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4007_ = lean_string_utf8_byte_size(v___x_4005_);
v___x_4008_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(v___x_4007_, v___x_4006_);
v_sz_4009_ = lean_array_size(v_a_4002_);
v___x_4010_ = ((size_t)0ULL);
lean_inc(v_a_4002_);
v___x_4011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4009_, v___x_4010_, v_a_4002_, v___y_3990_, v___y_3991_, v___y_3992_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4018_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v___x_4011_, 1);
v___x_4013_ = l_Lean_Doc_joinBlocks(v_a_4012_);
lean_dec(v_a_4012_);
v___x_4014_ = l_Lean_Doc_prefixListLines(v___x_4005_, v___x_4008_, v___x_4013_);
v___x_4015_ = lean_array_push(v_fst_3996_, v___x_4014_);
v___x_4016_ = lean_nat_add(v_snd_3997_, v___x_4001_);
lean_dec(v_snd_3997_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 1, v___x_4016_);
lean_ctor_set(v___x_3999_, 0, v___x_4015_);
v___x_4018_ = v___x_3999_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4015_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v___x_4016_);
v___x_4018_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
size_t v___x_4019_; size_t v___x_4020_; 
v___x_4019_ = ((size_t)1ULL);
v___x_4020_ = lean_usize_add(v_i_3988_, v___x_4019_);
v_i_3988_ = v___x_4020_;
v_b_3989_ = v___x_4018_;
goto _start;
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_dec_ref(v___x_4008_);
lean_dec_ref(v___x_4005_);
lean_del_object(v___x_3999_);
lean_dec(v_snd_3997_);
lean_dec(v_fst_3996_);
v_a_4023_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4011_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4011_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(size_t v_sz_4032_, size_t v_i_4033_, lean_object* v_bs_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
uint8_t v___x_4039_; 
v___x_4039_ = lean_usize_dec_lt(v_i_4033_, v_sz_4032_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4040_; 
v___x_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4040_, 0, v_bs_4034_);
return v___x_4040_;
}
else
{
lean_object* v_v_4041_; lean_object* v___x_4042_; lean_object* v_term_4043_; lean_object* v_desc_4044_; lean_object* v___x_4045_; lean_object* v_bs_x27_4046_; lean_object* v_a_4048_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v_v_4041_ = lean_array_uget_borrowed(v_bs_4034_, v_i_4033_);
v___x_4042_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_4043_ = lean_ctor_get(v_v_4041_, 0);
lean_inc_ref(v_term_4043_);
v_desc_4044_ = lean_ctor_get(v_v_4041_, 1);
lean_inc_ref(v_desc_4044_);
v___x_4045_ = lean_unsigned_to_nat(0u);
v_bs_x27_4046_ = lean_array_uset(v_bs_4034_, v_i_4033_, v___x_4045_);
v___x_4053_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4053_, 0, v_term_4043_);
v___x_4054_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4042_, v___x_4053_, v___y_4035_, v___y_4036_, v___y_4037_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; size_t v_sz_4056_; size_t v___x_4057_; lean_object* v___x_4058_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
lean_inc(v_a_4055_);
lean_dec_ref_known(v___x_4054_, 1);
v_sz_4056_ = lean_array_size(v_desc_4044_);
v___x_4057_ = ((size_t)0ULL);
lean_inc_ref(v_desc_4044_);
v___x_4058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4056_, v___x_4057_, v_desc_4044_, v___y_4035_, v___y_4036_, v___y_4037_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v___y_4061_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; uint8_t v___x_4074_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4058_, 1);
v___x_4065_ = lean_unsigned_to_nat(1u);
v___x_4066_ = lean_mk_empty_array_with_capacity(v___x_4065_);
v___x_4067_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_4068_ = lean_unsigned_to_nat(2u);
v___x_4069_ = lean_mk_empty_array_with_capacity(v___x_4068_);
v___x_4070_ = lean_array_push(v___x_4069_, v_a_4055_);
v___x_4071_ = lean_array_push(v___x_4070_, v___x_4067_);
v___x_4072_ = l_Lean_Doc_joinInlines(v___x_4071_);
lean_dec_ref(v___x_4071_);
v___x_4073_ = lean_array_get_size(v_desc_4044_);
lean_dec_ref(v_desc_4044_);
v___x_4074_ = lean_nat_dec_le(v___x_4073_, v___x_4065_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4075_ = lean_array_push(v___x_4066_, v___x_4072_);
v___x_4076_ = l_Array_append___redArg(v___x_4075_, v_a_4059_);
lean_dec(v_a_4059_);
v___x_4077_ = l_Lean_Doc_joinBlocks(v___x_4076_);
lean_dec_ref(v___x_4076_);
v___y_4061_ = v___x_4077_;
goto v___jp_4060_;
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
lean_dec_ref(v___x_4066_);
v___x_4078_ = l_Lean_Doc_joinBlocks(v_a_4059_);
lean_dec(v_a_4059_);
v___x_4079_ = l_Array_append___redArg(v___x_4072_, v___x_4078_);
lean_dec_ref(v___x_4078_);
v___y_4061_ = v___x_4079_;
goto v___jp_4060_;
}
v___jp_4060_:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4062_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_4063_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_4064_ = l_Lean_Doc_prefixListLines(v___x_4062_, v___x_4063_, v___y_4061_);
v_a_4048_ = v___x_4064_;
goto v___jp_4047_;
}
}
else
{
lean_dec(v_a_4055_);
lean_dec_ref(v_bs_x27_4046_);
lean_dec_ref(v_desc_4044_);
return v___x_4058_;
}
}
else
{
lean_dec_ref(v_desc_4044_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4080_; 
v_a_4080_ = lean_ctor_get(v___x_4054_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4054_, 1);
v_a_4048_ = v_a_4080_;
goto v___jp_4047_;
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec_ref(v_bs_x27_4046_);
v_a_4081_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4054_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4054_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
v___jp_4047_:
{
size_t v___x_4049_; size_t v___x_4050_; lean_object* v___x_4051_; 
v___x_4049_ = ((size_t)1ULL);
v___x_4050_ = lean_usize_add(v_i_4033_, v___x_4049_);
v___x_4051_ = lean_array_uset(v_bs_x27_4046_, v_i_4033_, v_a_4048_);
v_i_4033_ = v___x_4050_;
v_bs_4034_ = v___x_4051_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed(lean_object* v_x_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_x_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
lean_dec(v_a_4092_);
lean_dec_ref(v_a_4091_);
lean_dec(v_a_4090_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed(lean_object* v_sz_4097_, lean_object* v___x_4098_, lean_object* v_content_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
size_t v_sz_boxed_4104_; size_t v___x_4839__boxed_4105_; lean_object* v_res_4106_; 
v_sz_boxed_4104_ = lean_unbox_usize(v_sz_4097_);
lean_dec(v_sz_4097_);
v___x_4839__boxed_4105_ = lean_unbox_usize(v___x_4098_);
lean_dec(v___x_4098_);
v_res_4106_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(v_sz_boxed_4104_, v___x_4839__boxed_4105_, v_content_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(lean_object* v_x_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_){
_start:
{
switch(lean_obj_tag(v_x_4107_))
{
case 0:
{
lean_object* v_contents_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4121_; 
v_contents_4112_ = lean_ctor_get(v_x_4107_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_x_4107_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4114_ = v_x_4107_;
v_isShared_4115_ = v_isSharedCheck_4121_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_contents_4112_);
lean_dec(v_x_4107_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4121_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4116_; lean_object* v___x_4118_; 
v___x_4116_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_4115_ == 0)
{
lean_ctor_set_tag(v___x_4114_, 9);
v___x_4118_ = v___x_4114_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_contents_4112_);
v___x_4118_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
lean_object* v___x_4119_; 
v___x_4119_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4116_, v___x_4118_, v_a_4108_, v_a_4109_, v_a_4110_);
return v___x_4119_;
}
}
}
case 1:
{
lean_object* v_content_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4130_; 
v_content_4122_ = lean_ctor_get(v_x_4107_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v_x_4107_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4124_ = v_x_4107_;
v_isShared_4125_ = v_isSharedCheck_4130_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_content_4122_);
lean_dec(v_x_4107_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4130_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4126_; lean_object* v___x_4128_; 
v___x_4126_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_4122_);
if (v_isShared_4125_ == 0)
{
lean_ctor_set_tag(v___x_4124_, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4126_);
v___x_4128_ = v___x_4124_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v___x_4126_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
case 2:
{
lean_object* v_items_4131_; size_t v_sz_4132_; size_t v___x_4133_; lean_object* v___x_4134_; 
v_items_4131_ = lean_ctor_get(v_x_4107_, 0);
lean_inc_ref(v_items_4131_);
lean_dec_ref_known(v_x_4107_, 1);
v_sz_4132_ = lean_array_size(v_items_4131_);
v___x_4133_ = ((size_t)0ULL);
v___x_4134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_4132_, v___x_4133_, v_items_4131_, v_a_4108_, v_a_4109_, v_a_4110_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4143_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4137_ = v___x_4134_;
v_isShared_4138_ = v_isSharedCheck_4143_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4134_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4143_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4139_; lean_object* v___x_4141_; 
v___x_4139_ = l_Lean_Doc_joinBlocks(v_a_4135_);
lean_dec(v_a_4135_);
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 0, v___x_4139_);
v___x_4141_ = v___x_4137_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4139_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
v_a_4144_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4134_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4134_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
case 3:
{
lean_object* v_start_4152_; lean_object* v_items_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4187_; 
v_start_4152_ = lean_ctor_get(v_x_4107_, 0);
v_items_4153_ = lean_ctor_get(v_x_4107_, 1);
v_isSharedCheck_4187_ = !lean_is_exclusive(v_x_4107_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4155_ = v_x_4107_;
v_isShared_4156_ = v_isSharedCheck_4187_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_items_4153_);
lean_inc(v_start_4152_);
lean_dec(v_x_4107_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4187_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v_out_4157_; lean_object* v___y_4159_; lean_object* v___x_4184_; lean_object* v___x_4185_; uint8_t v___x_4186_; 
v_out_4157_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_4184_ = lean_unsigned_to_nat(1u);
v___x_4185_ = l_Int_toNat(v_start_4152_);
lean_dec(v_start_4152_);
v___x_4186_ = lean_nat_dec_le(v___x_4184_, v___x_4185_);
if (v___x_4186_ == 0)
{
lean_dec(v___x_4185_);
v___y_4159_ = v___x_4184_;
goto v___jp_4158_;
}
else
{
v___y_4159_ = v___x_4185_;
goto v___jp_4158_;
}
v___jp_4158_:
{
lean_object* v___x_4161_; 
if (v_isShared_4156_ == 0)
{
lean_ctor_set_tag(v___x_4155_, 0);
lean_ctor_set(v___x_4155_, 1, v___y_4159_);
lean_ctor_set(v___x_4155_, 0, v_out_4157_);
v___x_4161_ = v___x_4155_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_out_4157_);
lean_ctor_set(v_reuseFailAlloc_4183_, 1, v___y_4159_);
v___x_4161_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
size_t v_sz_4162_; size_t v___x_4163_; lean_object* v___x_4164_; 
v_sz_4162_ = lean_array_size(v_items_4153_);
v___x_4163_ = ((size_t)0ULL);
v___x_4164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_items_4153_, v_sz_4162_, v___x_4163_, v___x_4161_, v_a_4108_, v_a_4109_, v_a_4110_);
lean_dec_ref(v_items_4153_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4174_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4167_ = v___x_4164_;
v_isShared_4168_ = v_isSharedCheck_4174_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4164_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4174_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v_fst_4169_; lean_object* v___x_4170_; lean_object* v___x_4172_; 
v_fst_4169_ = lean_ctor_get(v_a_4165_, 0);
lean_inc(v_fst_4169_);
lean_dec(v_a_4165_);
v___x_4170_ = l_Lean_Doc_joinBlocks(v_fst_4169_);
lean_dec(v_fst_4169_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v___x_4170_);
v___x_4172_ = v___x_4167_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
v_a_4175_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4164_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4164_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_4188_; size_t v_sz_4189_; size_t v___x_4190_; lean_object* v___x_4191_; 
v_items_4188_ = lean_ctor_get(v_x_4107_, 0);
lean_inc_ref(v_items_4188_);
lean_dec_ref_known(v_x_4107_, 1);
v_sz_4189_ = lean_array_size(v_items_4188_);
v___x_4190_ = ((size_t)0ULL);
v___x_4191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_4189_, v___x_4190_, v_items_4188_, v_a_4108_, v_a_4109_, v_a_4110_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4200_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4194_ = v___x_4191_;
v_isShared_4195_ = v_isSharedCheck_4200_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4191_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4200_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4196_; lean_object* v___x_4198_; 
v___x_4196_ = l_Lean_Doc_joinBlocks(v_a_4192_);
lean_dec(v_a_4192_);
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 0, v___x_4196_);
v___x_4198_ = v___x_4194_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4196_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
else
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
v_a_4201_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4191_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4191_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
case 5:
{
lean_object* v_items_4209_; size_t v_sz_4210_; size_t v___x_4211_; lean_object* v___x_4212_; 
v_items_4209_ = lean_ctor_get(v_x_4107_, 0);
lean_inc_ref(v_items_4209_);
lean_dec_ref_known(v_x_4107_, 1);
v_sz_4210_ = lean_array_size(v_items_4209_);
v___x_4211_ = ((size_t)0ULL);
v___x_4212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4210_, v___x_4211_, v_items_4209_, v_a_4108_, v_a_4109_, v_a_4110_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4223_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4215_ = v___x_4212_;
v_isShared_4216_ = v_isSharedCheck_4223_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4212_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4223_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4221_; 
v___x_4217_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_4218_ = l_Lean_Doc_joinBlocks(v_a_4213_);
lean_dec(v_a_4213_);
v___x_4219_ = l_Lean_Doc_prefixLines(v___x_4217_, v___x_4218_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v___x_4219_);
v___x_4221_ = v___x_4215_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
v_a_4224_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4212_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4212_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
case 6:
{
lean_object* v_content_4232_; size_t v_sz_4233_; size_t v___x_4234_; lean_object* v___x_4235_; 
v_content_4232_ = lean_ctor_get(v_x_4107_, 0);
lean_inc_ref(v_content_4232_);
lean_dec_ref_known(v_x_4107_, 1);
v_sz_4233_ = lean_array_size(v_content_4232_);
v___x_4234_ = ((size_t)0ULL);
v___x_4235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4233_, v___x_4234_, v_content_4232_, v_a_4108_, v_a_4109_, v_a_4110_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4244_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4238_ = v___x_4235_;
v_isShared_4239_ = v_isSharedCheck_4244_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4235_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4244_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4240_; lean_object* v___x_4242_; 
v___x_4240_ = l_Lean_Doc_joinBlocks(v_a_4236_);
lean_dec(v_a_4236_);
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 0, v___x_4240_);
v___x_4242_ = v___x_4238_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4240_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
v_a_4245_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4235_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4235_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
default: 
{
lean_object* v_container_4253_; 
v_container_4253_ = lean_ctor_get(v_x_4107_, 0);
if (lean_obj_tag(v_container_4253_) == 0)
{
lean_object* v_content_4254_; lean_object* v_val_4255_; lean_object* v___f_4256_; lean_object* v___f_4257_; size_t v_sz_4258_; size_t v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v_fallback_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
lean_inc_ref(v_container_4253_);
v_content_4254_ = lean_ctor_get(v_x_4107_, 1);
lean_inc_ref_n(v_content_4254_, 2);
lean_dec_ref_known(v_x_4107_, 2);
v_val_4255_ = lean_ctor_get(v_container_4253_, 0);
lean_inc(v_val_4255_);
lean_dec_ref_known(v_container_4253_, 1);
v___f_4256_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed), 5, 0);
v___f_4257_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___closed__0));
v_sz_4258_ = lean_array_size(v_content_4254_);
v___x_4259_ = ((size_t)0ULL);
v___x_4260_ = lean_box_usize(v_sz_4258_);
v___x_4261_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
v_fallback_4262_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_fallback_4262_, 0, v___x_4260_);
lean_closure_set(v_fallback_4262_, 1, v___x_4261_);
lean_closure_set(v_fallback_4262_, 2, v_content_4254_);
v___x_4263_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_4255_);
v___x_4264_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_4263_, v_a_4109_, v_a_4110_);
lean_dec(v___x_4263_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4265_);
lean_dec_ref_known(v___x_4264_, 1);
if (lean_obj_tag(v_a_4265_) == 0)
{
lean_object* v___x_4266_; 
lean_dec_ref(v_fallback_4262_);
lean_dec_ref(v___f_4256_);
lean_dec(v_val_4255_);
v___x_4266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4258_, v___x_4259_, v_content_4254_, v_a_4108_, v_a_4109_, v_a_4110_);
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
lean_object* v_val_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v_val_4284_ = lean_ctor_get(v_a_4265_, 0);
lean_inc(v_val_4284_);
lean_dec_ref_known(v_a_4265_, 1);
v___x_4285_ = lean_apply_4(v_val_4284_, v___f_4257_, v___f_4256_, v_val_4255_, v_content_4254_);
v___x_4286_ = l_Lean_Doc_withRendererFallback(v_fallback_4262_, v___x_4285_, v_a_4108_, v_a_4109_, v_a_4110_);
return v___x_4286_;
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
lean_dec_ref(v_fallback_4262_);
lean_dec_ref(v___f_4256_);
lean_dec(v_val_4255_);
lean_dec_ref(v_content_4254_);
v_a_4287_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4264_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4264_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
else
{
lean_object* v_content_4295_; size_t v_sz_4296_; size_t v___x_4297_; lean_object* v___x_4298_; 
v_content_4295_ = lean_ctor_get(v_x_4107_, 1);
lean_inc_ref(v_content_4295_);
lean_dec_ref_known(v_x_4107_, 2);
v_sz_4296_ = lean_array_size(v_content_4295_);
v___x_4297_ = ((size_t)0ULL);
v___x_4298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4296_, v___x_4297_, v_content_4295_, v_a_4108_, v_a_4109_, v_a_4110_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4307_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4301_ = v___x_4298_;
v_isShared_4302_ = v_isSharedCheck_4307_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4298_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4307_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4303_; lean_object* v___x_4305_; 
v___x_4303_ = l_Lean_Doc_joinBlocks(v_a_4299_);
lean_dec(v_a_4299_);
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 0, v___x_4303_);
v___x_4305_ = v___x_4301_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v___x_4303_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
v_a_4308_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4298_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4298_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(size_t v_sz_4316_, size_t v_i_4317_, lean_object* v_bs_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
uint8_t v___x_4323_; 
v___x_4323_ = lean_usize_dec_lt(v_i_4317_, v_sz_4316_);
if (v___x_4323_ == 0)
{
lean_object* v___x_4324_; 
v___x_4324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4324_, 0, v_bs_4318_);
return v___x_4324_;
}
else
{
lean_object* v_v_4325_; lean_object* v___x_4326_; lean_object* v_bs_x27_4327_; lean_object* v___x_4328_; 
v_v_4325_ = lean_array_uget(v_bs_4318_, v_i_4317_);
v___x_4326_ = lean_unsigned_to_nat(0u);
v_bs_x27_4327_ = lean_array_uset(v_bs_4318_, v_i_4317_, v___x_4326_);
v___x_4328_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_v_4325_, v___y_4319_, v___y_4320_, v___y_4321_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; size_t v___x_4330_; size_t v___x_4331_; lean_object* v___x_4332_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4329_);
lean_dec_ref_known(v___x_4328_, 1);
v___x_4330_ = ((size_t)1ULL);
v___x_4331_ = lean_usize_add(v_i_4317_, v___x_4330_);
v___x_4332_ = lean_array_uset(v_bs_x27_4327_, v_i_4317_, v_a_4329_);
v_i_4317_ = v___x_4331_;
v_bs_4318_ = v___x_4332_;
goto _start;
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_dec_ref(v_bs_x27_4327_);
v_a_4334_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4328_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4328_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(size_t v_sz_4342_, size_t v___x_4343_, lean_object* v_content_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
lean_object* v___x_4349_; 
v___x_4349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4342_, v___x_4343_, v_content_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4358_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4352_ = v___x_4349_;
v_isShared_4353_ = v_isSharedCheck_4358_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4349_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4358_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4354_; lean_object* v___x_4356_; 
v___x_4354_ = l_Lean_Doc_joinBlocks(v_a_4350_);
lean_dec(v_a_4350_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v___x_4354_);
v___x_4356_ = v___x_4352_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v___x_4354_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
v_a_4359_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4349_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4349_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2___boxed(lean_object* v_sz_4367_, lean_object* v_i_4368_, lean_object* v_bs_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
size_t v_sz_boxed_4374_; size_t v_i_boxed_4375_; lean_object* v_res_4376_; 
v_sz_boxed_4374_ = lean_unbox_usize(v_sz_4367_);
lean_dec(v_sz_4367_);
v_i_boxed_4375_ = lean_unbox_usize(v_i_4368_);
lean_dec(v_i_4368_);
v_res_4376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_boxed_4374_, v_i_boxed_4375_, v_bs_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5___boxed(lean_object* v_sz_4377_, lean_object* v_i_4378_, lean_object* v_bs_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
size_t v_sz_boxed_4384_; size_t v_i_boxed_4385_; lean_object* v_res_4386_; 
v_sz_boxed_4384_ = lean_unbox_usize(v_sz_4377_);
lean_dec(v_sz_4377_);
v_i_boxed_4385_ = lean_unbox_usize(v_i_4378_);
lean_dec(v_i_4378_);
v_res_4386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_boxed_4384_, v_i_boxed_4385_, v_bs_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7___boxed(lean_object* v_as_4387_, lean_object* v_sz_4388_, lean_object* v_i_4389_, lean_object* v_b_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
size_t v_sz_boxed_4395_; size_t v_i_boxed_4396_; lean_object* v_res_4397_; 
v_sz_boxed_4395_ = lean_unbox_usize(v_sz_4388_);
lean_dec(v_sz_4388_);
v_i_boxed_4396_ = lean_unbox_usize(v_i_4389_);
lean_dec(v_i_4389_);
v_res_4397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_as_4387_, v_sz_boxed_4395_, v_i_boxed_4396_, v_b_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
lean_dec(v___y_4391_);
lean_dec_ref(v_as_4387_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8___boxed(lean_object* v_sz_4398_, lean_object* v_i_4399_, lean_object* v_bs_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
size_t v_sz_boxed_4405_; size_t v_i_boxed_4406_; lean_object* v_res_4407_; 
v_sz_boxed_4405_ = lean_unbox_usize(v_sz_4398_);
lean_dec(v_sz_4398_);
v_i_boxed_4406_ = lean_unbox_usize(v_i_4399_);
lean_dec(v_i_4399_);
v_res_4407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_boxed_4405_, v_i_boxed_4406_, v_bs_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v___y_4401_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(size_t v_sz_4408_, size_t v_i_4409_, lean_object* v_bs_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
uint8_t v___x_4415_; 
v___x_4415_ = lean_usize_dec_lt(v_i_4409_, v_sz_4408_);
if (v___x_4415_ == 0)
{
lean_object* v___x_4416_; 
v___x_4416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4416_, 0, v_bs_4410_);
return v___x_4416_;
}
else
{
lean_object* v_v_4417_; lean_object* v___x_4418_; lean_object* v_bs_x27_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v_v_4417_ = lean_array_uget(v_bs_4410_, v_i_4409_);
v___x_4418_ = lean_unsigned_to_nat(0u);
v_bs_x27_4419_ = lean_array_uset(v_bs_4410_, v_i_4409_, v___x_4418_);
v___x_4420_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_4421_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4420_, v_v_4417_, v___y_4411_, v___y_4412_, v___y_4413_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; size_t v___x_4423_; size_t v___x_4424_; lean_object* v___x_4425_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref_known(v___x_4421_, 1);
v___x_4423_ = ((size_t)1ULL);
v___x_4424_ = lean_usize_add(v_i_4409_, v___x_4423_);
v___x_4425_ = lean_array_uset(v_bs_x27_4419_, v_i_4409_, v_a_4422_);
v_i_4409_ = v___x_4424_;
v_bs_4410_ = v___x_4425_;
goto _start;
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_dec_ref(v_bs_x27_4419_);
v_a_4427_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4421_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4421_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1___boxed(lean_object* v_sz_4435_, lean_object* v_i_4436_, lean_object* v_bs_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
size_t v_sz_boxed_4442_; size_t v_i_boxed_4443_; lean_object* v_res_4444_; 
v_sz_boxed_4442_ = lean_unbox_usize(v_sz_4435_);
lean_dec(v_sz_4435_);
v_i_boxed_4443_ = lean_unbox_usize(v_i_4436_);
lean_dec(v_i_4436_);
v_res_4444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_boxed_4442_, v_i_boxed_4443_, v_bs_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(lean_object* v_x_4445_, lean_object* v_x_4446_){
_start:
{
lean_object* v_zero_4447_; uint8_t v_isZero_4448_; 
v_zero_4447_ = lean_unsigned_to_nat(0u);
v_isZero_4448_ = lean_nat_dec_eq(v_x_4445_, v_zero_4447_);
if (v_isZero_4448_ == 1)
{
lean_dec(v_x_4445_);
return v_x_4446_;
}
else
{
uint32_t v___x_4449_; lean_object* v_one_4450_; lean_object* v_n_4451_; lean_object* v___x_4452_; 
v___x_4449_ = 35;
v_one_4450_ = lean_unsigned_to_nat(1u);
v_n_4451_ = lean_nat_sub(v_x_4445_, v_one_4450_);
lean_dec(v_x_4445_);
v___x_4452_ = lean_string_push(v_x_4446_, v___x_4449_);
v_x_4445_ = v_n_4451_;
v_x_4446_ = v___x_4452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(lean_object* v_level_4454_, lean_object* v_part_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_){
_start:
{
lean_object* v_title_4460_; lean_object* v_content_4461_; lean_object* v_subParts_4462_; size_t v_sz_4463_; size_t v___x_4464_; lean_object* v___x_4465_; 
v_title_4460_ = lean_ctor_get(v_part_4455_, 0);
lean_inc_ref(v_title_4460_);
v_content_4461_ = lean_ctor_get(v_part_4455_, 3);
lean_inc_ref(v_content_4461_);
v_subParts_4462_ = lean_ctor_get(v_part_4455_, 4);
lean_inc_ref(v_subParts_4462_);
lean_dec_ref(v_part_4455_);
v_sz_4463_ = lean_array_size(v_title_4460_);
v___x_4464_ = ((size_t)0ULL);
v___x_4465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_4463_, v___x_4464_, v_title_4460_, v_a_4456_, v_a_4457_, v_a_4458_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v_a_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; size_t v_sz_4478_; lean_object* v___x_4479_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4466_);
lean_dec_ref_known(v___x_4465_, 1);
v___x_4467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4468_ = lean_unsigned_to_nat(1u);
v___x_4469_ = lean_nat_add(v_level_4454_, v___x_4468_);
lean_inc(v___x_4469_);
v___x_4470_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(v___x_4469_, v___x_4467_);
v___x_4471_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_4472_ = lean_string_append(v___x_4470_, v___x_4471_);
v___x_4473_ = lean_mk_empty_array_with_capacity(v___x_4468_);
lean_inc_ref_n(v___x_4473_, 2);
v___x_4474_ = lean_array_push(v___x_4473_, v___x_4472_);
v___x_4475_ = lean_array_push(v___x_4473_, v___x_4474_);
v___x_4476_ = l_Array_append___redArg(v___x_4475_, v_a_4466_);
lean_dec(v_a_4466_);
v___x_4477_ = l_Lean_Doc_joinInlines(v___x_4476_);
lean_dec_ref(v___x_4476_);
v_sz_4478_ = lean_array_size(v_content_4461_);
v___x_4479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4478_, v___x_4464_, v_content_4461_, v_a_4456_, v_a_4457_, v_a_4458_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; size_t v_sz_4481_; lean_object* v___x_4482_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref_known(v___x_4479_, 1);
v_sz_4481_ = lean_array_size(v_subParts_4462_);
v___x_4482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4469_, v_sz_4481_, v___x_4464_, v_subParts_4462_, v_a_4456_, v_a_4457_, v_a_4458_);
lean_dec(v___x_4469_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4494_; 
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4485_ = v___x_4482_;
v_isShared_4486_ = v_isSharedCheck_4494_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_dec(v___x_4482_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4494_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4492_; 
v___x_4487_ = lean_array_push(v___x_4473_, v___x_4477_);
v___x_4488_ = l_Array_append___redArg(v___x_4487_, v_a_4480_);
lean_dec(v_a_4480_);
v___x_4489_ = l_Array_append___redArg(v___x_4488_, v_a_4483_);
lean_dec(v_a_4483_);
v___x_4490_ = l_Lean_Doc_joinBlocks(v___x_4489_);
lean_dec_ref(v___x_4489_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 0, v___x_4490_);
v___x_4492_ = v___x_4485_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4490_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
lean_dec(v_a_4480_);
lean_dec_ref(v___x_4477_);
lean_dec_ref(v___x_4473_);
v_a_4495_ = lean_ctor_get(v___x_4482_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4482_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4482_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
else
{
lean_object* v_a_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4510_; 
lean_dec_ref(v___x_4477_);
lean_dec_ref(v___x_4473_);
lean_dec(v___x_4469_);
lean_dec_ref(v_subParts_4462_);
v_a_4503_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4505_ = v___x_4479_;
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_a_4503_);
lean_dec(v___x_4479_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4508_; 
if (v_isShared_4506_ == 0)
{
v___x_4508_ = v___x_4505_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4503_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
}
}
else
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4518_; 
lean_dec_ref(v_subParts_4462_);
lean_dec_ref(v_content_4461_);
v_a_4511_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4513_ = v___x_4465_;
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v___x_4465_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4516_; 
if (v_isShared_4514_ == 0)
{
v___x_4516_ = v___x_4513_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_a_4511_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(lean_object* v___x_4519_, size_t v_sz_4520_, size_t v_i_4521_, lean_object* v_bs_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
uint8_t v___x_4527_; 
v___x_4527_ = lean_usize_dec_lt(v_i_4521_, v_sz_4520_);
if (v___x_4527_ == 0)
{
lean_object* v___x_4528_; 
v___x_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4528_, 0, v_bs_4522_);
return v___x_4528_;
}
else
{
lean_object* v_v_4529_; lean_object* v___x_4530_; lean_object* v_bs_x27_4531_; lean_object* v___x_4532_; 
v_v_4529_ = lean_array_uget(v_bs_4522_, v_i_4521_);
v___x_4530_ = lean_unsigned_to_nat(0u);
v_bs_x27_4531_ = lean_array_uset(v_bs_4522_, v_i_4521_, v___x_4530_);
v___x_4532_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4519_, v_v_4529_, v___y_4523_, v___y_4524_, v___y_4525_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; size_t v___x_4534_; size_t v___x_4535_; lean_object* v___x_4536_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4533_);
lean_dec_ref_known(v___x_4532_, 1);
v___x_4534_ = ((size_t)1ULL);
v___x_4535_ = lean_usize_add(v_i_4521_, v___x_4534_);
v___x_4536_ = lean_array_uset(v_bs_x27_4531_, v_i_4521_, v_a_4533_);
v_i_4521_ = v___x_4535_;
v_bs_4522_ = v___x_4536_;
goto _start;
}
else
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4545_; 
lean_dec_ref(v_bs_x27_4531_);
v_a_4538_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4540_ = v___x_4532_;
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4532_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4543_; 
if (v_isShared_4541_ == 0)
{
v___x_4543_ = v___x_4540_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg___boxed(lean_object* v___x_4546_, lean_object* v_sz_4547_, lean_object* v_i_4548_, lean_object* v_bs_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
size_t v_sz_boxed_4554_; size_t v_i_boxed_4555_; lean_object* v_res_4556_; 
v_sz_boxed_4554_ = lean_unbox_usize(v_sz_4547_);
lean_dec(v_sz_4547_);
v_i_boxed_4555_ = lean_unbox_usize(v_i_4548_);
lean_dec(v_i_4548_);
v_res_4556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4546_, v_sz_boxed_4554_, v_i_boxed_4555_, v_bs_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec(v___x_4546_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg___boxed(lean_object* v_level_4557_, lean_object* v_part_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4557_, v_part_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v_a_4559_);
lean_dec(v_level_4557_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(size_t v_sz_4564_, size_t v_i_4565_, lean_object* v_bs_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
uint8_t v___x_4571_; 
v___x_4571_ = lean_usize_dec_lt(v_i_4565_, v_sz_4564_);
if (v___x_4571_ == 0)
{
lean_object* v___x_4572_; 
v___x_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4572_, 0, v_bs_4566_);
return v___x_4572_;
}
else
{
lean_object* v_v_4573_; lean_object* v___x_4574_; lean_object* v_bs_x27_4575_; lean_object* v___x_4576_; 
v_v_4573_ = lean_array_uget(v_bs_4566_, v_i_4565_);
v___x_4574_ = lean_unsigned_to_nat(0u);
v_bs_x27_4575_ = lean_array_uset(v_bs_4566_, v_i_4565_, v___x_4574_);
v___x_4576_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4574_, v_v_4573_, v___y_4567_, v___y_4568_, v___y_4569_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_object* v_a_4577_; size_t v___x_4578_; size_t v___x_4579_; lean_object* v___x_4580_; 
v_a_4577_ = lean_ctor_get(v___x_4576_, 0);
lean_inc(v_a_4577_);
lean_dec_ref_known(v___x_4576_, 1);
v___x_4578_ = ((size_t)1ULL);
v___x_4579_ = lean_usize_add(v_i_4565_, v___x_4578_);
v___x_4580_ = lean_array_uset(v_bs_x27_4575_, v_i_4565_, v_a_4577_);
v_i_4565_ = v___x_4579_;
v_bs_4566_ = v___x_4580_;
goto _start;
}
else
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4589_; 
lean_dec_ref(v_bs_x27_4575_);
v_a_4582_ = lean_ctor_get(v___x_4576_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4584_ = v___x_4576_;
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4576_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4587_; 
if (v_isShared_4585_ == 0)
{
v___x_4587_ = v___x_4584_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_a_4582_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3___boxed(lean_object* v_sz_4590_, lean_object* v_i_4591_, lean_object* v_bs_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
size_t v_sz_boxed_4597_; size_t v_i_boxed_4598_; lean_object* v_res_4599_; 
v_sz_boxed_4597_ = lean_unbox_usize(v_sz_4590_);
lean_dec(v_sz_4590_);
v_i_boxed_4598_ = lean_unbox_usize(v_i_4591_);
lean_dec(v_i_4591_);
v_res_4599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_boxed_4597_, v_i_boxed_4598_, v_bs_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4593_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0(lean_object* v_val_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v_text_4605_; lean_object* v_subsections_4606_; size_t v_sz_4607_; size_t v___x_4608_; lean_object* v___x_4609_; 
v_text_4605_ = lean_ctor_get(v_val_4600_, 0);
lean_inc_ref(v_text_4605_);
v_subsections_4606_ = lean_ctor_get(v_val_4600_, 1);
lean_inc_ref(v_subsections_4606_);
lean_dec_ref(v_val_4600_);
v_sz_4607_ = lean_array_size(v_text_4605_);
v___x_4608_ = ((size_t)0ULL);
v___x_4609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4607_, v___x_4608_, v_text_4605_, v___y_4601_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; size_t v_sz_4611_; lean_object* v___x_4612_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc(v_a_4610_);
lean_dec_ref_known(v___x_4609_, 1);
v_sz_4611_ = lean_array_size(v_subsections_4606_);
v___x_4612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_4611_, v___x_4608_, v_subsections_4606_, v___y_4601_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4622_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4615_ = v___x_4612_;
v_isShared_4616_ = v_isSharedCheck_4622_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4612_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4622_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4620_; 
v___x_4617_ = l_Array_append___redArg(v_a_4610_, v_a_4613_);
lean_dec(v_a_4613_);
v___x_4618_ = l_Lean_Doc_joinBlocks(v___x_4617_);
lean_dec_ref(v___x_4617_);
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
else
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
lean_dec(v_a_4610_);
v_a_4623_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4612_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4612_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
lean_dec_ref(v_subsections_4606_);
v_a_4631_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4609_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4609_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0___boxed(lean_object* v_val_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Lean_findSimpleDocString_x3f___lam__0(v_val_4639_, v___y_4640_, v___y_4641_, v___y_4642_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
lean_dec(v___y_4640_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_4645_, lean_object* v_declName_4646_, uint8_t v_includeBuiltin_4647_, lean_object* v_options_4648_, lean_object* v_currNamespace_4649_, lean_object* v_openDecls_4650_, lean_object* v_cancelTk_x3f_4651_){
_start:
{
lean_object* v___x_4653_; 
lean_inc_ref(v_env_4645_);
v___x_4653_ = l_Lean_findInternalDocString_x3f(v_env_4645_, v_declName_4646_, v_includeBuiltin_4647_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4697_; 
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4656_ = v___x_4653_;
v_isShared_4657_ = v_isSharedCheck_4697_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4653_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4697_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
if (lean_obj_tag(v_a_4654_) == 0)
{
lean_object* v___x_4658_; lean_object* v___x_4660_; 
lean_dec(v_cancelTk_x3f_4651_);
lean_dec(v_openDecls_4650_);
lean_dec(v_currNamespace_4649_);
lean_dec_ref(v_options_4648_);
lean_dec_ref(v_env_4645_);
v___x_4658_ = lean_box(0);
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 0, v___x_4658_);
v___x_4660_ = v___x_4656_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4658_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
else
{
lean_object* v_val_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4696_; 
v_val_4662_ = lean_ctor_get(v_a_4654_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v_a_4654_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4664_ = v_a_4654_;
v_isShared_4665_ = v_isSharedCheck_4696_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_val_4662_);
lean_dec(v_a_4654_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4696_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
if (lean_obj_tag(v_val_4662_) == 0)
{
lean_object* v_val_4666_; lean_object* v___x_4668_; 
lean_dec(v_cancelTk_x3f_4651_);
lean_dec(v_openDecls_4650_);
lean_dec(v_currNamespace_4649_);
lean_dec_ref(v_options_4648_);
lean_dec_ref(v_env_4645_);
v_val_4666_ = lean_ctor_get(v_val_4662_, 0);
lean_inc(v_val_4666_);
lean_dec_ref_known(v_val_4662_, 1);
if (v_isShared_4665_ == 0)
{
lean_ctor_set(v___x_4664_, 0, v_val_4666_);
v___x_4668_ = v___x_4664_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_val_4666_);
v___x_4668_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
lean_object* v___x_4670_; 
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 0, v___x_4668_);
v___x_4670_ = v___x_4656_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v___x_4668_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
}
else
{
lean_object* v_val_4673_; lean_object* v___f_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
lean_del_object(v___x_4656_);
v_val_4673_ = lean_ctor_get(v_val_4662_, 0);
lean_inc(v_val_4673_);
lean_dec_ref_known(v_val_4662_, 1);
v___f_4674_ = lean_alloc_closure((void*)(l_Lean_findSimpleDocString_x3f___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4674_, 0, v_val_4673_);
v___x_4675_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_4675_, 0, v___f_4674_);
v___x_4676_ = l_Lean_Doc_runMarkdown___redArg(v_env_4645_, v___x_4675_, v_options_4648_, v_currNamespace_4649_, v_openDecls_4650_, v_cancelTk_x3f_4651_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4687_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4679_ = v___x_4676_;
v_isShared_4680_ = v_isSharedCheck_4687_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4676_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4687_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4665_ == 0)
{
lean_ctor_set(v___x_4664_, 0, v_a_4677_);
v___x_4682_ = v___x_4664_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
lean_object* v___x_4684_; 
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 0, v___x_4682_);
v___x_4684_ = v___x_4679_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4682_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
else
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4695_; 
lean_del_object(v___x_4664_);
v_a_4688_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4690_ = v___x_4676_;
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4676_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4693_; 
if (v_isShared_4691_ == 0)
{
v___x_4693_ = v___x_4690_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_a_4688_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
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
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4705_; 
lean_dec(v_cancelTk_x3f_4651_);
lean_dec(v_openDecls_4650_);
lean_dec(v_currNamespace_4649_);
lean_dec_ref(v_options_4648_);
lean_dec_ref(v_env_4645_);
v_a_4698_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4700_ = v___x_4653_;
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4653_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4703_; 
if (v_isShared_4701_ == 0)
{
v___x_4703_ = v___x_4700_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_4706_, lean_object* v_declName_4707_, lean_object* v_includeBuiltin_4708_, lean_object* v_options_4709_, lean_object* v_currNamespace_4710_, lean_object* v_openDecls_4711_, lean_object* v_cancelTk_x3f_4712_, lean_object* v_a_4713_){
_start:
{
uint8_t v_includeBuiltin_boxed_4714_; lean_object* v_res_4715_; 
v_includeBuiltin_boxed_4714_ = lean_unbox(v_includeBuiltin_4708_);
v_res_4715_ = l_Lean_findSimpleDocString_x3f(v_env_4706_, v_declName_4707_, v_includeBuiltin_boxed_4714_, v_options_4709_, v_currNamespace_4710_, v_openDecls_4711_, v_cancelTk_x3f_4712_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(lean_object* v_p_4716_, lean_object* v_level_4717_, lean_object* v_part_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_){
_start:
{
lean_object* v___x_4723_; 
v___x_4723_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4717_, v_part_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___boxed(lean_object* v_p_4724_, lean_object* v_level_4725_, lean_object* v_part_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(v_p_4724_, v_level_4725_, v_part_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
lean_dec(v_a_4729_);
lean_dec_ref(v_a_4728_);
lean_dec(v_a_4727_);
lean_dec(v_level_4725_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(lean_object* v_p_4732_, lean_object* v___x_4733_, size_t v_sz_4734_, size_t v_i_4735_, lean_object* v_bs_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v___x_4741_; 
v___x_4741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4733_, v_sz_4734_, v_i_4735_, v_bs_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___boxed(lean_object* v_p_4742_, lean_object* v___x_4743_, lean_object* v_sz_4744_, lean_object* v_i_4745_, lean_object* v_bs_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
size_t v_sz_boxed_4751_; size_t v_i_boxed_4752_; lean_object* v_res_4753_; 
v_sz_boxed_4751_ = lean_unbox_usize(v_sz_4744_);
lean_dec(v_sz_4744_);
v_i_boxed_4752_ = lean_unbox_usize(v_i_4745_);
lean_dec(v_i_4745_);
v_res_4753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(v_p_4742_, v___x_4743_, v_sz_boxed_4751_, v_i_boxed_4752_, v_bs_4746_, v___y_4747_, v___y_4748_, v___y_4749_);
lean_dec(v___y_4749_);
lean_dec_ref(v___y_4748_);
lean_dec(v___y_4747_);
lean_dec(v___x_4743_);
return v_res_4753_;
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
l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2___boxed__const__1 = _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2___boxed__const__1);
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
