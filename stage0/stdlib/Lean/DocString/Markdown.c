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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "​"};
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__10_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__9_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__8_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__9_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__8_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; 
v___x_262_ = ((size_t)0ULL);
v___x_263_ = lean_usize_of_nat(v___x_260_);
v___x_264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_257_, v___x_262_, v___x_263_, v___x_259_);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks___boxed(lean_object* v_blocks_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Doc_joinBlocks(v_blocks_265_);
lean_dec_ref(v_blocks_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(lean_object* v_l_269_, lean_object* v_r_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_271_ = lean_string_utf8_byte_size(v_l_269_);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_dec_le(v___x_272_, v___x_271_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_string_append(v_l_269_, v_r_270_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_275_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_nat_sub(v___x_271_, v___x_272_);
v___x_278_ = lean_string_memcmp(v_l_269_, v___x_275_, v___x_277_, v___x_276_, v___x_272_);
lean_dec(v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
v___x_279_ = lean_string_append(v_l_269_, v_r_270_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_string_utf8_byte_size(v_r_270_);
v___x_281_ = lean_nat_dec_le(v___x_272_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
v___x_282_ = lean_string_append(v_l_269_, v_r_270_);
return v___x_282_;
}
else
{
uint8_t v___x_283_; 
v___x_283_ = lean_string_memcmp(v_r_270_, v___x_275_, v___x_276_, v___x_276_, v___x_272_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_string_append(v_l_269_, v_r_270_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1));
v___x_286_ = lean_string_append(v_l_269_, v___x_285_);
v___x_287_ = lean_string_append(v___x_286_, v_r_270_);
return v___x_287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___boxed(lean_object* v_l_288_, lean_object* v_r_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v_l_288_, v_r_289_);
lean_dec_ref(v_r_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(lean_object* v_as_291_, size_t v_i_292_, size_t v_stop_293_, lean_object* v_b_294_){
_start:
{
lean_object* v___y_296_; uint8_t v___x_300_; 
v___x_300_ = lean_usize_dec_eq(v_i_292_, v_stop_293_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_301_ = lean_array_uget_borrowed(v_as_291_, v_i_292_);
v___x_302_ = lean_array_get_size(v___x_301_);
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_nat_dec_eq(v___x_302_, v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = lean_array_get_size(v_b_294_);
v___x_306_ = lean_nat_dec_eq(v___x_305_, v___x_303_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v_lastIdx_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v_glued_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_307_ = lean_unsigned_to_nat(1u);
v_lastIdx_308_ = lean_nat_sub(v___x_305_, v___x_307_);
v___x_309_ = lean_array_fget_borrowed(v_b_294_, v_lastIdx_308_);
v___x_310_ = lean_array_fget_borrowed(v___x_301_, v___x_303_);
lean_inc(v___x_309_);
v_glued_311_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v___x_309_, v___x_310_);
v___x_312_ = lean_array_fset(v_b_294_, v_lastIdx_308_, v_glued_311_);
lean_dec(v_lastIdx_308_);
v___x_313_ = l_Array_extract___redArg(v___x_301_, v___x_307_, v___x_302_);
v___x_314_ = l_Array_append___redArg(v___x_312_, v___x_313_);
lean_dec_ref(v___x_313_);
v___y_296_ = v___x_314_;
goto v___jp_295_;
}
else
{
lean_dec_ref(v_b_294_);
lean_inc(v___x_301_);
v___y_296_ = v___x_301_;
goto v___jp_295_;
}
}
else
{
v___y_296_ = v_b_294_;
goto v___jp_295_;
}
}
else
{
return v_b_294_;
}
v___jp_295_:
{
size_t v___x_297_; size_t v___x_298_; 
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_add(v_i_292_, v___x_297_);
v_i_292_ = v___x_298_;
v_b_294_ = v___y_296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0___boxed(lean_object* v_as_315_, lean_object* v_i_316_, lean_object* v_stop_317_, lean_object* v_b_318_){
_start:
{
size_t v_i_boxed_319_; size_t v_stop_boxed_320_; lean_object* v_res_321_; 
v_i_boxed_319_ = lean_unbox_usize(v_i_316_);
lean_dec(v_i_316_);
v_stop_boxed_320_ = lean_unbox_usize(v_stop_317_);
lean_dec(v_stop_317_);
v_res_321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_as_315_, v_i_boxed_319_, v_stop_boxed_320_, v_b_318_);
lean_dec_ref(v_as_315_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines(lean_object* v_parts_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_325_ = lean_array_get_size(v_parts_322_);
v___x_326_ = lean_nat_dec_lt(v___x_323_, v___x_325_);
if (v___x_326_ == 0)
{
return v___x_324_;
}
else
{
size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; 
v___x_327_ = ((size_t)0ULL);
v___x_328_ = lean_usize_of_nat(v___x_325_);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_322_, v___x_327_, v___x_328_, v___x_324_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines___boxed(lean_object* v_parts_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Doc_joinInlines(v_parts_330_);
lean_dec_ref(v_parts_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object* v_a_332_, uint8_t v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
uint8_t v_a_19__boxed_346_; lean_object* v_res_347_; 
v_a_19__boxed_346_ = lean_unbox(v_a_340_);
v_res_347_ = l_Lean_Doc_instMarkdownInlineEmpty___lam__0(v_a_339_, v_a_19__boxed_346_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec_ref(v_a_339_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0(lean_object* v_a_350_, lean_object* v_a_351_, uint8_t v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0___boxed(lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
uint8_t v_a_41__boxed_366_; lean_object* v_res_367_; 
v_a_41__boxed_366_ = lean_unbox(v_a_360_);
v_res_367_ = l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0(v_a_358_, v_a_359_, v_a_41__boxed_366_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec_ref(v_a_359_);
lean_dec_ref(v_a_358_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg(){
_start:
{
lean_object* v___f_370_; 
v___f_370_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0));
return v___f_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___boxed(lean_object* v___dummy_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Doc_instMarkdownBlockEmpty___redArg();
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object* v_i_373_){
_start:
{
lean_object* v___f_374_; 
v___f_374_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0));
return v___f_374_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
if (lean_obj_tag(v_x_376_) == 0)
{
uint8_t v___x_377_; 
v___x_377_ = 1;
return v___x_377_;
}
else
{
uint8_t v___x_378_; 
v___x_378_ = 0;
return v___x_378_;
}
}
else
{
if (lean_obj_tag(v_x_376_) == 0)
{
uint8_t v___x_379_; 
v___x_379_ = 0;
return v___x_379_;
}
else
{
lean_object* v_val_380_; lean_object* v_val_381_; uint32_t v___x_382_; uint32_t v___x_383_; uint8_t v___x_384_; 
v_val_380_ = lean_ctor_get(v_x_375_, 0);
v_val_381_ = lean_ctor_get(v_x_376_, 0);
v___x_382_ = lean_unbox_uint32(v_val_380_);
v___x_383_ = lean_unbox_uint32(v_val_381_);
v___x_384_ = lean_uint32_dec_eq(v___x_382_, v___x_383_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1___boxed(lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
uint8_t v_res_387_; lean_object* v_r_388_; 
v_res_387_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_x_385_, v_x_386_);
lean_dec(v_x_386_);
lean_dec(v_x_385_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(lean_object* v_s_389_, uint32_t v_c_390_, lean_object* v_a_391_, uint8_t v_b_392_){
_start:
{
lean_object* v_str_393_; lean_object* v_startInclusive_394_; lean_object* v_endExclusive_395_; lean_object* v___x_396_; uint8_t v_decide_397_; 
v_str_393_ = lean_ctor_get(v_s_389_, 0);
v_startInclusive_394_ = lean_ctor_get(v_s_389_, 1);
v_endExclusive_395_ = lean_ctor_get(v_s_389_, 2);
v___x_396_ = lean_nat_sub(v_endExclusive_395_, v_startInclusive_394_);
v_decide_397_ = lean_nat_dec_eq(v_a_391_, v___x_396_);
lean_dec(v___x_396_);
if (v_decide_397_ == 0)
{
lean_object* v___x_398_; uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_398_ = lean_nat_add(v_startInclusive_394_, v_a_391_);
lean_dec(v_a_391_);
v___x_399_ = lean_string_utf8_get_fast(v_str_393_, v___x_398_);
v___x_400_ = lean_uint32_dec_eq(v___x_399_, v_c_390_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_string_utf8_next_fast(v_str_393_, v___x_398_);
lean_dec(v___x_398_);
v___x_402_ = lean_nat_sub(v___x_401_, v_startInclusive_394_);
v_a_391_ = v___x_402_;
v_b_392_ = v___x_400_;
goto _start;
}
else
{
lean_dec(v___x_398_);
return v___x_400_;
}
}
else
{
lean_dec(v_a_391_);
return v_b_392_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg___boxed(lean_object* v_s_404_, lean_object* v_c_405_, lean_object* v_a_406_, lean_object* v_b_407_){
_start:
{
uint32_t v_c_boxed_408_; uint8_t v_b_boxed_409_; uint8_t v_res_410_; lean_object* v_r_411_; 
v_c_boxed_408_ = lean_unbox_uint32(v_c_405_);
lean_dec(v_c_405_);
v_b_boxed_409_ = lean_unbox(v_b_407_);
v_res_410_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_404_, v_c_boxed_408_, v_a_406_, v_b_boxed_409_);
lean_dec_ref(v_s_404_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(uint32_t v_c_412_, lean_object* v_s_413_){
_start:
{
lean_object* v_searcher_414_; uint8_t v___x_415_; uint8_t v___x_416_; 
v_searcher_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = 0;
v___x_416_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_413_, v_c_412_, v_searcher_414_, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0___boxed(lean_object* v_c_417_, lean_object* v_s_418_){
_start:
{
uint32_t v_c_boxed_419_; uint8_t v_res_420_; lean_object* v_r_421_; 
v_c_boxed_419_ = lean_unbox_uint32(v_c_417_);
lean_dec(v_c_417_);
v_res_420_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_boxed_419_, v_s_418_);
lean_dec_ref(v_s_418_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_427_; lean_object* v___x_428_; 
v___x_427_ = 91;
v___x_428_ = lean_box_uint32(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2___boxed__const__1;
v___x_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(uint32_t v_c_431_, lean_object* v_next_x3f_432_){
_start:
{
uint32_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = 33;
v___x_434_ = lean_uint32_dec_eq(v_c_431_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1));
v___x_436_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_431_, v___x_435_);
return v___x_436_;
}
else
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2);
v___x_438_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_432_, v___x_437_);
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___boxed(lean_object* v_c_439_, lean_object* v_next_x3f_440_){
_start:
{
uint32_t v_c_boxed_441_; uint8_t v_res_442_; lean_object* v_r_443_; 
v_c_boxed_441_ = lean_unbox_uint32(v_c_439_);
lean_dec(v_c_439_);
v_res_442_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_boxed_441_, v_next_x3f_440_);
lean_dec(v_next_x3f_440_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(lean_object* v_s_444_, uint32_t v_c_445_, lean_object* v_inst_446_, lean_object* v_R_447_, lean_object* v_a_448_, uint8_t v_b_449_, lean_object* v_c_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_444_, v_c_445_, v_a_448_, v_b_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___boxed(lean_object* v_s_452_, lean_object* v_c_453_, lean_object* v_inst_454_, lean_object* v_R_455_, lean_object* v_a_456_, lean_object* v_b_457_, lean_object* v_c_458_){
_start:
{
uint32_t v_c_boxed_459_; uint8_t v_b_boxed_460_; uint8_t v_res_461_; lean_object* v_r_462_; 
v_c_boxed_459_ = lean_unbox_uint32(v_c_453_);
lean_dec(v_c_453_);
v_b_boxed_460_ = lean_unbox(v_b_457_);
v_res_461_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(v_s_452_, v_c_boxed_459_, v_inst_454_, v_R_455_, v_a_456_, v_b_boxed_460_, v_c_458_);
lean_dec_ref(v_s_452_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_463_; lean_object* v___x_464_; 
v___x_463_ = 32;
v___x_464_ = lean_box_uint32(v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(lean_object* v_prev_x3f_467_, uint32_t v_c_468_, lean_object* v_next_x3f_469_){
_start:
{
uint8_t v___y_471_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0);
v___x_489_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_469_, v___x_488_);
if (v___x_489_ == 0)
{
if (lean_obj_tag(v_next_x3f_469_) == 0)
{
uint8_t v___x_490_; 
v___x_490_ = 1;
v___y_471_ = v___x_490_;
goto v___jp_470_;
}
else
{
v___y_471_ = v___x_489_;
goto v___jp_470_;
}
}
else
{
v___y_471_ = v___x_489_;
goto v___jp_470_;
}
v___jp_470_:
{
uint32_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 62;
v___x_473_ = lean_uint32_dec_eq(v_c_468_, v___x_472_);
if (v___x_473_ == 0)
{
uint32_t v___x_474_; uint8_t v___x_475_; 
v___x_474_ = 45;
v___x_475_ = lean_uint32_dec_eq(v_c_468_, v___x_474_);
if (v___x_475_ == 0)
{
uint32_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = 43;
v___x_477_ = lean_uint32_dec_eq(v_c_468_, v___x_476_);
if (v___x_477_ == 0)
{
uint32_t v___x_478_; uint8_t v___x_479_; 
v___x_478_ = 46;
v___x_479_ = lean_uint32_dec_eq(v_c_468_, v___x_478_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; 
v___x_480_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_468_, v_next_x3f_469_);
return v___x_480_;
}
else
{
if (lean_obj_tag(v_prev_x3f_467_) == 0)
{
return v___x_477_;
}
else
{
lean_object* v_val_481_; uint32_t v___x_482_; uint32_t v___x_483_; uint8_t v___x_484_; 
v_val_481_ = lean_ctor_get(v_prev_x3f_467_, 0);
v___x_482_ = 48;
v___x_483_ = lean_unbox_uint32(v_val_481_);
v___x_484_ = lean_uint32_dec_le(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
return v___x_484_;
}
else
{
uint32_t v___x_485_; uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_485_ = 57;
v___x_486_ = lean_unbox_uint32(v_val_481_);
v___x_487_ = lean_uint32_dec_le(v___x_486_, v___x_485_);
if (v___x_487_ == 0)
{
return v___x_487_;
}
else
{
return v___y_471_;
}
}
}
}
}
else
{
return v___y_471_;
}
}
else
{
return v___y_471_;
}
}
else
{
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___boxed(lean_object* v_prev_x3f_491_, lean_object* v_c_492_, lean_object* v_next_x3f_493_){
_start:
{
uint32_t v_c_boxed_494_; uint8_t v_res_495_; lean_object* v_r_496_; 
v_c_boxed_494_ = lean_unbox_uint32(v_c_492_);
lean_dec(v_c_492_);
v_res_495_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_prev_x3f_491_, v_c_boxed_494_, v_next_x3f_493_);
lean_dec(v_next_x3f_493_);
lean_dec(v_prev_x3f_491_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(uint32_t v___x_502_, lean_object* v___x_503_, lean_object* v_____r_504_, lean_object* v_s_x27_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint32_t v___x_519_; uint8_t v___x_520_; 
v___x_506_ = lean_string_push(v_s_x27_505_, v___x_502_);
v___x_507_ = lean_box_uint32(v___x_502_);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
v___x_519_ = 48;
v___x_520_ = lean_uint32_dec_le(v___x_519_, v___x_502_);
if (v___x_520_ == 0)
{
goto v___jp_513_;
}
else
{
uint32_t v___x_521_; uint8_t v___x_522_; 
v___x_521_ = 57;
v___x_522_ = lean_uint32_dec_le(v___x_502_, v___x_521_);
if (v___x_522_ == 0)
{
goto v___jp_513_;
}
else
{
goto v___jp_509_;
}
}
v___jp_509_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_503_);
lean_ctor_set(v___x_510_, 1, v___x_508_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_506_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
v___jp_513_:
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1));
v___x_515_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v___x_502_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_503_);
lean_ctor_set(v___x_516_, 1, v___x_508_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_506_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
else
{
goto v___jp_509_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed(lean_object* v___x_523_, lean_object* v___x_524_, lean_object* v_____r_525_, lean_object* v_s_x27_526_){
_start:
{
uint32_t v___x_2072__boxed_527_; lean_object* v_res_528_; 
v___x_2072__boxed_527_ = lean_unbox_uint32(v___x_523_);
lean_dec(v___x_523_);
v_res_528_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_2072__boxed_527_, v___x_524_, v_____r_525_, v_s_x27_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(lean_object* v_s_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___y_532_; lean_object* v_snd_536_; lean_object* v_fst_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_574_; 
v_snd_536_ = lean_ctor_get(v_a_530_, 1);
v_fst_537_ = lean_ctor_get(v_a_530_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v_a_530_);
if (v_isSharedCheck_574_ == 0)
{
v___x_539_ = v_a_530_;
v_isShared_540_ = v_isSharedCheck_574_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_snd_536_);
lean_inc(v_fst_537_);
lean_dec(v_a_530_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_574_;
goto v_resetjp_538_;
}
v___jp_531_:
{
if (lean_obj_tag(v___y_532_) == 0)
{
lean_object* v_a_533_; 
v_a_533_ = lean_ctor_get(v___y_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___y_532_, 1);
return v_a_533_;
}
else
{
lean_object* v_a_534_; 
v_a_534_ = lean_ctor_get(v___y_532_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___y_532_, 1);
v_a_530_ = v_a_534_;
goto _start;
}
}
v_resetjp_538_:
{
lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_573_; 
v_fst_541_ = lean_ctor_get(v_snd_536_, 0);
v_snd_542_ = lean_ctor_get(v_snd_536_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_snd_536_);
if (v_isSharedCheck_573_ == 0)
{
v___x_544_ = v_snd_536_;
v_isShared_545_ = v_isSharedCheck_573_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_snd_542_);
lean_inc(v_fst_541_);
lean_dec(v_snd_536_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_573_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; uint8_t v_decide_547_; 
v___x_546_ = lean_string_utf8_byte_size(v_s_529_);
v_decide_547_ = lean_nat_dec_eq(v_fst_541_, v___x_546_);
if (v_decide_547_ == 0)
{
uint32_t v___x_548_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___f_561_; uint8_t v_decide_562_; 
lean_del_object(v___x_544_);
lean_del_object(v___x_539_);
v___x_548_ = lean_string_utf8_get_fast(v_s_529_, v_fst_541_);
v___x_559_ = lean_string_utf8_next_fast(v_s_529_, v_fst_541_);
lean_dec(v_fst_541_);
v___x_560_ = lean_box_uint32(v___x_548_);
v___f_561_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_561_, 0, v___x_560_);
lean_closure_set(v___f_561_, 1, v___x_559_);
v_decide_562_ = lean_nat_dec_eq(v___x_559_, v___x_546_);
if (v_decide_562_ == 0)
{
uint32_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = lean_string_utf8_get_fast(v_s_529_, v___x_559_);
v___x_564_ = lean_box_uint32(v___x_563_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
v___y_550_ = v___f_561_;
v___y_551_ = v___x_565_;
goto v___jp_549_;
}
else
{
lean_object* v_prev_x3f_566_; 
v_prev_x3f_566_ = lean_box(0);
v___y_550_ = v___f_561_;
v___y_551_ = v_prev_x3f_566_;
goto v___jp_549_;
}
v___jp_549_:
{
uint8_t v___x_552_; 
v___x_552_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_snd_542_, v___x_548_, v___y_551_);
lean_dec(v___y_551_);
lean_dec(v_snd_542_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_box(0);
v___x_554_ = lean_apply_2(v___y_550_, v___x_553_, v_fst_537_);
v___y_532_ = v___x_554_;
goto v___jp_531_;
}
else
{
uint32_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_555_ = 92;
v___x_556_ = lean_string_push(v_fst_537_, v___x_555_);
v___x_557_ = lean_box(0);
v___x_558_ = lean_apply_2(v___y_550_, v___x_557_, v___x_556_);
v___y_532_ = v___x_558_;
goto v___jp_531_;
}
}
}
else
{
lean_object* v___x_568_; 
if (v_isShared_545_ == 0)
{
v___x_568_ = v___x_544_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_fst_541_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_snd_542_);
v___x_568_ = v_reuseFailAlloc_572_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_570_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_568_);
v___x_570_ = v___x_539_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_fst_537_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___boxed(lean_object* v_s_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_575_, v_a_576_);
lean_dec_ref(v_s_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(uint32_t v___x_578_, lean_object* v___x_579_, lean_object* v_____r_580_, lean_object* v_s_x27_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_string_push(v_s_x27_581_, v___x_578_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_579_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0___boxed(lean_object* v___x_585_, lean_object* v___x_586_, lean_object* v_____r_587_, lean_object* v_s_x27_588_){
_start:
{
uint32_t v___x_2198__boxed_589_; lean_object* v_res_590_; 
v___x_2198__boxed_589_ = lean_unbox_uint32(v___x_585_);
lean_dec(v___x_585_);
v_res_590_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_2198__boxed_589_, v___x_586_, v_____r_587_, v_s_x27_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(lean_object* v_s_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___y_594_; lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_624_; 
v_fst_598_ = lean_ctor_get(v_a_592_, 0);
v_snd_599_ = lean_ctor_get(v_a_592_, 1);
v_isSharedCheck_624_ = !lean_is_exclusive(v_a_592_);
if (v_isSharedCheck_624_ == 0)
{
v___x_601_ = v_a_592_;
v_isShared_602_ = v_isSharedCheck_624_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_snd_599_);
lean_inc(v_fst_598_);
lean_dec(v_a_592_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_624_;
goto v_resetjp_600_;
}
v___jp_593_:
{
if (lean_obj_tag(v___y_594_) == 0)
{
lean_object* v_a_595_; 
v_a_595_ = lean_ctor_get(v___y_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___y_594_, 1);
return v_a_595_;
}
else
{
lean_object* v_a_596_; 
v_a_596_ = lean_ctor_get(v___y_594_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___y_594_, 1);
v_a_592_ = v_a_596_;
goto _start;
}
}
v_resetjp_600_:
{
lean_object* v___x_603_; uint8_t v_decide_604_; 
v___x_603_ = lean_string_utf8_byte_size(v_s_591_);
v_decide_604_ = lean_nat_dec_eq(v_snd_599_, v___x_603_);
if (v_decide_604_ == 0)
{
uint32_t v___x_605_; lean_object* v___x_606_; lean_object* v___y_608_; uint8_t v_decide_616_; 
lean_del_object(v___x_601_);
v___x_605_ = lean_string_utf8_get_fast(v_s_591_, v_snd_599_);
v___x_606_ = lean_string_utf8_next_fast(v_s_591_, v_snd_599_);
lean_dec(v_snd_599_);
v_decide_616_ = lean_nat_dec_eq(v___x_606_, v___x_603_);
if (v_decide_616_ == 0)
{
uint32_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = lean_string_utf8_get_fast(v_s_591_, v___x_606_);
v___x_618_ = lean_box_uint32(v___x_617_);
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
v___y_608_ = v___x_619_;
goto v___jp_607_;
}
else
{
lean_object* v_prev_x3f_620_; 
v_prev_x3f_620_ = lean_box(0);
v___y_608_ = v_prev_x3f_620_;
goto v___jp_607_;
}
v___jp_607_:
{
uint8_t v___x_609_; 
v___x_609_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v___x_605_, v___y_608_);
lean_dec(v___y_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_box(0);
v___x_611_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_605_, v___x_606_, v___x_610_, v_fst_598_);
v___y_594_ = v___x_611_;
goto v___jp_593_;
}
else
{
uint32_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_612_ = 92;
v___x_613_ = lean_string_push(v_fst_598_, v___x_612_);
v___x_614_ = lean_box(0);
v___x_615_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_605_, v___x_606_, v___x_614_, v___x_613_);
v___y_594_ = v___x_615_;
goto v___jp_593_;
}
}
}
else
{
lean_object* v___x_622_; 
if (v_isShared_602_ == 0)
{
v___x_622_ = v___x_601_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_fst_598_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_snd_599_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___boxed(lean_object* v_s_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_625_, v_a_626_);
lean_dec_ref(v_s_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object* v_s_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_snd_637_; lean_object* v_fst_638_; lean_object* v_fst_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_648_; 
v___x_635_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1));
v___x_636_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_634_, v___x_635_);
v_snd_637_ = lean_ctor_get(v___x_636_, 1);
lean_inc(v_snd_637_);
v_fst_638_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_fst_638_);
lean_dec_ref(v___x_636_);
v_fst_639_ = lean_ctor_get(v_snd_637_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_snd_637_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; 
v_unused_649_ = lean_ctor_get(v_snd_637_, 1);
lean_dec(v_unused_649_);
v___x_641_ = v_snd_637_;
v_isShared_642_ = v_isSharedCheck_648_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_fst_639_);
lean_dec(v_snd_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_648_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v_fst_639_);
lean_ctor_set(v___x_641_, 0, v_fst_638_);
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_fst_638_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_fst_639_);
v___x_644_ = v_reuseFailAlloc_647_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v_fst_646_; 
v___x_645_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_634_, v___x_644_);
v_fst_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_fst_646_);
lean_dec_ref(v___x_645_);
return v_fst_646_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object* v_s_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_650_);
lean_dec_ref(v_s_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object* v_s_652_, lean_object* v_inst_653_, lean_object* v_a_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_652_, v_a_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object* v_s_656_, lean_object* v_inst_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_656_, v_inst_657_, v_a_658_);
lean_dec_ref(v_s_656_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(lean_object* v_s_660_, lean_object* v_inst_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_660_, v_a_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___boxed(lean_object* v_s_664_, lean_object* v_inst_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(v_s_664_, v_inst_665_, v_a_666_);
lean_dec_ref(v_s_664_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v_str_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_snd_670_; lean_object* v_fst_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_713_; 
v_snd_670_ = lean_ctor_get(v_a_669_, 1);
v_fst_671_ = lean_ctor_get(v_a_669_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v_a_669_);
if (v_isSharedCheck_713_ == 0)
{
v___x_673_ = v_a_669_;
v_isShared_674_ = v_isSharedCheck_713_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_snd_670_);
lean_inc(v_fst_671_);
lean_dec(v_a_669_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_713_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_fst_675_; lean_object* v_snd_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_712_; 
v_fst_675_ = lean_ctor_get(v_snd_670_, 0);
v_snd_676_ = lean_ctor_get(v_snd_670_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_snd_670_);
if (v_isSharedCheck_712_ == 0)
{
v___x_678_ = v_snd_670_;
v_isShared_679_ = v_isSharedCheck_712_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_snd_676_);
lean_inc(v_fst_675_);
lean_dec(v_snd_670_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_712_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; uint8_t v_decide_681_; 
v___x_680_ = lean_string_utf8_byte_size(v_str_668_);
v_decide_681_ = lean_nat_dec_eq(v_snd_676_, v___x_680_);
if (v_decide_681_ == 0)
{
uint32_t v___x_682_; lean_object* v___x_683_; uint32_t v___x_684_; uint8_t v___x_685_; 
v___x_682_ = lean_string_utf8_get_fast(v_str_668_, v_snd_676_);
v___x_683_ = lean_string_utf8_next_fast(v_str_668_, v_snd_676_);
lean_dec(v_snd_676_);
v___x_684_ = 96;
v___x_685_ = lean_uint32_dec_eq(v___x_682_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v_longest_686_; lean_object* v___y_688_; uint8_t v___x_696_; 
v_longest_686_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_nat_dec_le(v_fst_671_, v_fst_675_);
if (v___x_696_ == 0)
{
lean_dec(v_fst_675_);
v___y_688_ = v_fst_671_;
goto v___jp_687_;
}
else
{
lean_dec(v_fst_671_);
v___y_688_ = v_fst_675_;
goto v___jp_687_;
}
v___jp_687_:
{
lean_object* v___x_690_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___x_683_);
lean_ctor_set(v___x_678_, 0, v_longest_686_);
v___x_690_ = v___x_678_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_longest_686_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_683_);
v___x_690_ = v_reuseFailAlloc_695_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v___x_690_);
lean_ctor_set(v___x_673_, 0, v___y_688_);
v___x_692_ = v___x_673_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___y_688_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_690_);
v___x_692_ = v_reuseFailAlloc_694_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v_a_669_ = v___x_692_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_nat_add(v_fst_675_, v___x_697_);
lean_dec(v_fst_675_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___x_683_);
lean_ctor_set(v___x_678_, 0, v___x_698_);
v___x_700_ = v___x_678_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_683_);
v___x_700_ = v_reuseFailAlloc_705_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v___x_700_);
v___x_702_ = v___x_673_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_fst_671_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_700_);
v___x_702_ = v_reuseFailAlloc_704_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
v_a_669_ = v___x_702_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_707_; 
if (v_isShared_679_ == 0)
{
v___x_707_ = v___x_678_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_fst_675_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_snd_676_);
v___x_707_ = v_reuseFailAlloc_711_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v___x_707_);
v___x_709_ = v___x_673_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_fst_671_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v_str_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_714_, v_a_715_);
lean_dec_ref(v_str_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(lean_object* v_str_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v_snd_725_; lean_object* v_fst_726_; lean_object* v_fst_727_; uint8_t v___x_728_; 
v___x_723_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1));
v___x_724_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_722_, v___x_723_);
v_snd_725_ = lean_ctor_get(v___x_724_, 1);
lean_inc(v_snd_725_);
v_fst_726_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_fst_726_);
lean_dec_ref(v___x_724_);
v_fst_727_ = lean_ctor_get(v_snd_725_, 0);
lean_inc(v_fst_727_);
lean_dec(v_snd_725_);
v___x_728_ = lean_nat_dec_le(v_fst_726_, v_fst_727_);
if (v___x_728_ == 0)
{
lean_dec(v_fst_727_);
return v_fst_726_;
}
else
{
lean_dec(v_fst_726_);
return v_fst_727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___boxed(lean_object* v_str_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_729_);
lean_dec_ref(v_str_729_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(lean_object* v_str_731_, lean_object* v_inst_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_731_, v_a_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v_str_735_, lean_object* v_inst_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(v_str_735_, v_inst_736_, v_a_737_);
lean_dec_ref(v_str_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v_zero_741_; uint8_t v_isZero_742_; 
v_zero_741_ = lean_unsigned_to_nat(0u);
v_isZero_742_ = lean_nat_dec_eq(v_x_739_, v_zero_741_);
if (v_isZero_742_ == 1)
{
lean_dec(v_x_739_);
return v_x_740_;
}
else
{
uint32_t v___x_743_; lean_object* v_one_744_; lean_object* v_n_745_; lean_object* v___x_746_; 
v___x_743_ = 96;
v_one_744_ = lean_unsigned_to_nat(1u);
v_n_745_ = lean_nat_sub(v_x_739_, v_one_744_);
lean_dec(v_x_739_);
v___x_746_ = lean_string_push(v_x_740_, v___x_743_);
v_x_739_ = v_n_745_;
v_x_740_ = v___x_746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(lean_object* v_atLeast_748_, lean_object* v_str_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___y_752_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_756_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_749_);
v___x_757_ = lean_nat_dec_le(v_atLeast_748_, v___x_756_);
if (v___x_757_ == 0)
{
lean_dec(v___x_756_);
v___y_752_ = v_atLeast_748_;
goto v___jp_751_;
}
else
{
lean_dec(v_atLeast_748_);
v___y_752_ = v___x_756_;
goto v___jp_751_;
}
v___jp_751_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_add(v___y_752_, v___x_753_);
lean_dec(v___y_752_);
v___x_755_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(v___x_754_, v___x_750_);
return v___x_755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor___boxed(lean_object* v_atLeast_758_, lean_object* v_str_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v_atLeast_758_, v_str_759_);
lean_dec_ref(v_str_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object* v_str_762_){
_start:
{
lean_object* v___x_763_; lean_object* v_backticks_764_; lean_object* v___y_766_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v_backticks_764_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_763_, v_str_762_);
v___x_780_ = lean_string_utf8_byte_size(v_str_762_);
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_dec_le(v___x_781_, v___x_780_);
if (v___x_782_ == 0)
{
goto v___jp_773_;
}
else
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_784_ = lean_string_memcmp(v_str_762_, v___x_783_, v___x_763_, v___x_763_, v___x_781_);
if (v___x_784_ == 0)
{
goto v___jp_773_;
}
else
{
goto v___jp_769_;
}
}
v___jp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
lean_inc_ref(v_backticks_764_);
v___x_767_ = lean_string_append(v_backticks_764_, v___y_766_);
lean_dec_ref(v___y_766_);
v___x_768_ = lean_string_append(v___x_767_, v_backticks_764_);
lean_dec_ref(v_backticks_764_);
return v___x_768_;
}
v___jp_769_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_771_ = lean_string_append(v___x_770_, v_str_762_);
lean_dec_ref(v_str_762_);
v___x_772_ = lean_string_append(v___x_771_, v___x_770_);
v___y_766_ = v___x_772_;
goto v___jp_765_;
}
v___jp_773_:
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_774_ = lean_string_utf8_byte_size(v_str_762_);
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = lean_nat_dec_le(v___x_775_, v___x_774_);
if (v___x_776_ == 0)
{
v___y_766_ = v_str_762_;
goto v___jp_765_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_777_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_778_ = lean_nat_sub(v___x_774_, v___x_775_);
v___x_779_ = lean_string_memcmp(v_str_762_, v___x_777_, v___x_778_, v___x_763_, v___x_775_);
lean_dec(v___x_778_);
if (v___x_779_ == 0)
{
v___y_766_ = v_str_762_;
goto v___jp_765_;
}
else
{
goto v___jp_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg(){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___closed__0));
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___boxed(lean_object* v___dummy_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg();
return v_res_790_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg();
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(lean_object* v_s_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___boxed(lean_object* v_s_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v_s_794_);
lean_dec_ref(v_s_794_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(lean_object* v_str_796_, lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v_a_799_, lean_object* v_b_800_){
_start:
{
lean_object* v_it_802_; lean_object* v_startInclusive_803_; lean_object* v_endExclusive_804_; 
if (lean_obj_tag(v_a_799_) == 0)
{
lean_object* v_currPos_808_; lean_object* v_searcher_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_832_; 
v_currPos_808_ = lean_ctor_get(v_a_799_, 0);
v_searcher_809_ = lean_ctor_get(v_a_799_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_a_799_);
if (v_isSharedCheck_832_ == 0)
{
v___x_811_ = v_a_799_;
v_isShared_812_ = v_isSharedCheck_832_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_searcher_809_);
lean_inc(v_currPos_808_);
lean_dec(v_a_799_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_832_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
uint8_t v_decide_813_; 
v_decide_813_ = lean_nat_dec_eq(v_searcher_809_, v___x_798_);
if (v_decide_813_ == 0)
{
uint32_t v___x_814_; uint32_t v___x_815_; uint8_t v___x_816_; 
v___x_814_ = 10;
v___x_815_ = lean_string_utf8_get_fast(v_str_796_, v_searcher_809_);
v___x_816_ = lean_uint32_dec_eq(v___x_815_, v___x_814_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = lean_string_utf8_next_fast(v_str_796_, v_searcher_809_);
lean_dec(v_searcher_809_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 1, v___x_817_);
v___x_819_ = v___x_811_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_currPos_808_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_817_);
v___x_819_ = v_reuseFailAlloc_821_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
v_a_799_ = v___x_819_;
goto _start;
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_slice_825_; lean_object* v_nextIt_827_; 
v___x_822_ = lean_string_utf8_next_fast(v_str_796_, v_searcher_809_);
v___x_823_ = lean_nat_sub(v___x_822_, v_searcher_809_);
v___x_824_ = lean_nat_add(v_searcher_809_, v___x_823_);
lean_dec(v___x_823_);
v_slice_825_ = l_String_Slice_subslice_x21(v___x_797_, v_currPos_808_, v_searcher_809_);
lean_inc(v___x_824_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 1, v___x_824_);
lean_ctor_set(v___x_811_, 0, v___x_824_);
v_nextIt_827_ = v___x_811_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_824_);
v_nextIt_827_ = v_reuseFailAlloc_830_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v_startInclusive_828_; lean_object* v_endExclusive_829_; 
v_startInclusive_828_ = lean_ctor_get(v_slice_825_, 0);
lean_inc(v_startInclusive_828_);
v_endExclusive_829_ = lean_ctor_get(v_slice_825_, 1);
lean_inc(v_endExclusive_829_);
lean_dec_ref(v_slice_825_);
v_it_802_ = v_nextIt_827_;
v_startInclusive_803_ = v_startInclusive_828_;
v_endExclusive_804_ = v_endExclusive_829_;
goto v___jp_801_;
}
}
}
else
{
lean_object* v___x_831_; 
lean_del_object(v___x_811_);
lean_dec(v_searcher_809_);
v___x_831_ = lean_box(1);
lean_inc(v___x_798_);
v_it_802_ = v___x_831_;
v_startInclusive_803_ = v_currPos_808_;
v_endExclusive_804_ = v___x_798_;
goto v___jp_801_;
}
}
}
else
{
lean_dec(v___x_798_);
return v_b_800_;
}
v___jp_801_:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_string_utf8_extract_fast(v_str_796_, v_startInclusive_803_, v_endExclusive_804_);
lean_dec(v_endExclusive_804_);
lean_dec(v_startInclusive_803_);
v___x_806_ = lean_array_push(v_b_800_, v___x_805_);
v_a_799_ = v_it_802_;
v_b_800_ = v___x_806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg___boxed(lean_object* v_str_833_, lean_object* v___x_834_, lean_object* v___x_835_, lean_object* v_a_836_, lean_object* v_b_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_833_, v___x_834_, v___x_835_, v_a_836_, v_b_837_);
lean_dec_ref(v___x_834_);
lean_dec_ref(v_str_833_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(lean_object* v_str_839_){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_string_utf8_byte_size(v_str_839_);
lean_inc_ref(v_str_839_);
v___x_842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_842_, 0, v_str_839_);
lean_ctor_set(v___x_842_, 1, v___x_840_);
lean_ctor_set(v___x_842_, 2, v___x_841_);
v___x_843_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0);
v___x_844_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_845_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_839_, v___x_842_, v___x_841_, v___x_843_, v___x_844_);
lean_dec_ref_known(v___x_842_, 3);
lean_dec_ref(v_str_839_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(lean_object* v_str_846_, lean_object* v___x_847_, lean_object* v___x_848_, lean_object* v_inst_849_, lean_object* v_R_850_, lean_object* v_a_851_, lean_object* v_b_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_846_, v___x_847_, v___x_848_, v_a_851_, v_b_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___boxed(lean_object* v_str_854_, lean_object* v___x_855_, lean_object* v___x_856_, lean_object* v_inst_857_, lean_object* v_R_858_, lean_object* v_a_859_, lean_object* v_b_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(v_str_854_, v___x_855_, v___x_856_, v_inst_857_, v_R_858_, v_a_859_, v_b_860_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v_str_854_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(lean_object* v_str_862_){
_start:
{
lean_object* v___x_863_; lean_object* v_fence_864_; lean_object* v___y_866_; lean_object* v_body_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_863_ = lean_unsigned_to_nat(2u);
v_fence_864_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_863_, v_str_862_);
v_body_872_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(v_str_862_);
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_array_get_size(v_body_872_);
v___x_875_ = lean_nat_dec_lt(v___x_873_, v___x_874_);
if (v___x_875_ == 0)
{
v___y_866_ = v_body_872_;
goto v___jp_865_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_877_ = lean_unsigned_to_nat(1u);
v___x_878_ = lean_nat_sub(v___x_874_, v___x_877_);
v___x_879_ = lean_array_get_borrowed(v___x_876_, v_body_872_, v___x_878_);
lean_dec(v___x_878_);
v___x_880_ = lean_string_utf8_byte_size(v___x_879_);
v___x_881_ = lean_nat_dec_eq(v___x_880_, v___x_873_);
if (v___x_881_ == 0)
{
v___y_866_ = v_body_872_;
goto v___jp_865_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = lean_array_pop(v_body_872_);
v___y_866_ = v___x_882_;
goto v___jp_865_;
}
}
v___jp_865_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_mk_empty_array_with_capacity(v___x_867_);
v___x_869_ = lean_array_push(v___x_868_, v_fence_864_);
lean_inc_ref(v___x_869_);
v___x_870_ = l_Array_append___redArg(v___x_869_, v___y_866_);
lean_dec_ref(v___y_866_);
v___x_871_ = l_Array_append___redArg(v___x_870_, v___x_869_);
lean_dec_ref(v___x_869_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_883_, lean_object* v_pos_884_){
_start:
{
lean_object* v_str_885_; lean_object* v_startInclusive_886_; lean_object* v_endExclusive_887_; lean_object* v___x_888_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v_decide_899_; 
v_str_885_ = lean_ctor_get(v_s_883_, 0);
v_startInclusive_886_ = lean_ctor_get(v_s_883_, 1);
v_endExclusive_887_ = lean_ctor_get(v_s_883_, 2);
v___x_888_ = lean_nat_add(v_startInclusive_886_, v_pos_884_);
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = lean_nat_sub(v_endExclusive_887_, v___x_888_);
v_decide_899_ = lean_nat_dec_eq(v___x_897_, v___x_898_);
lean_dec(v___x_898_);
if (v_decide_899_ == 0)
{
uint32_t v___x_900_; uint32_t v___x_901_; uint8_t v___x_902_; 
v___x_900_ = lean_string_utf8_get_fast(v_str_885_, v___x_888_);
v___x_901_ = 32;
v___x_902_ = lean_uint32_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
uint32_t v___x_903_; uint8_t v___x_904_; 
v___x_903_ = 9;
v___x_904_ = lean_uint32_dec_eq(v___x_900_, v___x_903_);
if (v___x_904_ == 0)
{
uint32_t v___x_905_; uint8_t v___x_906_; 
v___x_905_ = 13;
v___x_906_ = lean_uint32_dec_eq(v___x_900_, v___x_905_);
if (v___x_906_ == 0)
{
uint32_t v___x_907_; uint8_t v___x_908_; 
v___x_907_ = 10;
v___x_908_ = lean_uint32_dec_eq(v___x_900_, v___x_907_);
if (v___x_908_ == 0)
{
lean_dec(v___x_888_);
return v_pos_884_;
}
else
{
goto v___jp_889_;
}
}
else
{
goto v___jp_889_;
}
}
else
{
goto v___jp_889_;
}
}
else
{
goto v___jp_889_;
}
}
else
{
lean_dec(v___x_888_);
return v_pos_884_;
}
v___jp_889_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_890_ = lean_string_utf8_next_fast(v_str_885_, v___x_888_);
v___x_891_ = lean_nat_sub(v___x_890_, v___x_888_);
lean_dec(v___x_888_);
v___x_892_ = lean_nat_add(v_pos_884_, v___x_891_);
lean_dec(v___x_891_);
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_nat_add(v_pos_884_, v___x_893_);
v___x_895_ = lean_nat_dec_le(v___x_894_, v___x_892_);
lean_dec(v___x_894_);
if (v___x_895_ == 0)
{
lean_dec(v___x_892_);
return v_pos_884_;
}
else
{
lean_dec(v_pos_884_);
v_pos_884_ = v___x_892_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object* v_s_909_, lean_object* v_pos_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_909_, v_pos_910_);
lean_dec_ref(v_s_909_);
return v_res_911_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Doc_Inline_empty___redArg();
return v___x_912_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object* v_a_916_){
_start:
{
if (lean_obj_tag(v_a_916_) == 0)
{
lean_object* v___x_917_; 
v___x_917_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
return v___x_917_;
}
else
{
lean_object* v_head_918_; 
v_head_918_ = lean_ctor_get(v_a_916_, 0);
lean_inc(v_head_918_);
switch(lean_obj_tag(v_head_918_))
{
case 0:
{
lean_object* v_tail_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_963_; 
v_tail_919_ = lean_ctor_get(v_a_916_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_a_916_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v_a_916_, 0);
lean_dec(v_unused_964_);
v___x_921_ = v_a_916_;
v_isShared_922_ = v_isSharedCheck_963_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_tail_919_);
lean_dec(v_a_916_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_963_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_string_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_962_; 
v_string_923_ = lean_ctor_get(v_head_918_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v_head_918_);
if (v_isSharedCheck_962_ == 0)
{
v___x_925_ = v_head_918_;
v_isShared_926_ = v_isSharedCheck_962_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_string_923_);
lean_dec(v_head_918_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_962_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v_decide_931_; 
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_string_utf8_byte_size(v_string_923_);
lean_inc_ref(v_string_923_);
v___x_929_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_929_, 0, v_string_923_);
lean_ctor_set(v___x_929_, 1, v___x_927_);
lean_ctor_set(v___x_929_, 2, v___x_928_);
v___x_930_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_929_, v___x_927_);
lean_dec_ref_known(v___x_929_, 3);
v_decide_931_ = lean_nat_dec_eq(v___x_930_, v___x_928_);
if (v_decide_931_ == 0)
{
lean_object* v_s1_932_; lean_object* v_s2_933_; lean_object* v___x_935_; 
v_s1_932_ = lean_string_utf8_extract_fast(v_string_923_, v___x_927_, v___x_930_);
v_s2_933_ = lean_string_utf8_extract_fast(v_string_923_, v___x_930_, v___x_928_);
lean_dec(v___x_930_);
lean_dec_ref(v_string_923_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v_s2_933_);
v___x_935_ = v___x_925_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_s2_933_);
v___x_935_ = v_reuseFailAlloc_950_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_936_ = lean_array_mk(v_tail_919_);
v___x_937_ = lean_array_get_size(v___x_936_);
v___x_938_ = lean_nat_dec_eq(v___x_937_, v___x_927_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_mk_empty_array_with_capacity(v___x_939_);
v___x_941_ = lean_array_push(v___x_940_, v___x_935_);
v___x_942_ = l_Array_append___redArg(v___x_941_, v___x_936_);
lean_dec_ref(v___x_936_);
v___x_943_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 0);
lean_ctor_set(v___x_921_, 1, v___x_943_);
lean_ctor_set(v___x_921_, 0, v_s1_932_);
v___x_945_ = v___x_921_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_s1_932_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
else
{
lean_object* v___x_948_; 
lean_dec_ref(v___x_936_);
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 0);
lean_ctor_set(v___x_921_, 1, v___x_935_);
lean_ctor_set(v___x_921_, 0, v_s1_932_);
v___x_948_ = v___x_921_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_s1_932_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_935_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v___x_951_; lean_object* v_fst_952_; lean_object* v_snd_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_961_; 
lean_dec(v___x_930_);
lean_del_object(v___x_925_);
lean_del_object(v___x_921_);
v___x_951_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_919_);
v_fst_952_ = lean_ctor_get(v___x_951_, 0);
v_snd_953_ = lean_ctor_get(v___x_951_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_961_ == 0)
{
v___x_955_ = v___x_951_;
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_snd_953_);
lean_inc(v_fst_952_);
lean_dec(v___x_951_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = lean_string_append(v_string_923_, v_fst_952_);
lean_dec(v_fst_952_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_snd_953_);
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
}
}
case 9:
{
lean_object* v_tail_965_; lean_object* v_content_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_tail_965_ = lean_ctor_get(v_a_916_, 1);
lean_inc(v_tail_965_);
lean_dec_ref_known(v_a_916_, 2);
v_content_966_ = lean_ctor_get(v_head_918_, 0);
lean_inc_ref(v_content_966_);
lean_dec_ref_known(v_head_918_, 1);
v___x_967_ = lean_array_to_list(v_content_966_);
v___x_968_ = l_List_appendTR___redArg(v___x_967_, v_tail_965_);
v_a_916_ = v___x_968_;
goto _start;
}
default: 
{
lean_object* v_tail_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1008_; 
v_tail_970_ = lean_ctor_get(v_a_916_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_a_916_);
if (v_isSharedCheck_1008_ == 0)
{
lean_object* v_unused_1009_; 
v_unused_1009_ = lean_ctor_get(v_a_916_, 0);
lean_dec(v_unused_1009_);
v___x_972_ = v_a_916_;
v_isShared_973_ = v_isSharedCheck_1008_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_tail_970_);
lean_dec(v_a_916_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1008_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_975_ = lean_array_mk(v_tail_970_);
if (lean_obj_tag(v_head_918_) == 9)
{
lean_object* v_content_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v_content_976_ = lean_ctor_get(v_head_918_, 0);
v___x_977_ = lean_array_get_size(v_content_976_);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_nat_dec_eq(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_980_ = lean_array_get_size(v___x_975_);
v___x_981_ = lean_nat_dec_eq(v___x_980_, v___x_978_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_985_; 
lean_inc_ref(v_content_976_);
lean_dec_ref_known(v_head_918_, 1);
v___x_982_ = l_Array_append___redArg(v_content_976_, v___x_975_);
lean_dec_ref(v___x_975_);
v___x_983_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 0);
lean_ctor_set(v___x_972_, 1, v___x_983_);
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_985_ = v___x_972_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
else
{
lean_object* v___x_988_; 
lean_dec_ref(v___x_975_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 0);
lean_ctor_set(v___x_972_, 1, v_head_918_);
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_988_ = v___x_972_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_head_918_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_992_; 
lean_dec_ref_known(v_head_918_, 1);
v___x_990_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_975_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 0);
lean_ctor_set(v___x_972_, 1, v___x_990_);
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_992_ = v___x_972_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_994_ = lean_array_get_size(v___x_975_);
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_nat_dec_eq(v___x_994_, v___x_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_mk_empty_array_with_capacity(v___x_997_);
v___x_999_ = lean_array_push(v___x_998_, v_head_918_);
v___x_1000_ = l_Array_append___redArg(v___x_999_, v___x_975_);
lean_dec_ref(v___x_975_);
v___x_1001_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 0);
lean_ctor_set(v___x_972_, 1, v___x_1001_);
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_1003_ = v___x_972_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
else
{
lean_object* v___x_1006_; 
lean_dec_ref(v___x_975_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 0);
lean_ctor_set(v___x_972_, 1, v_head_918_);
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_1006_ = v___x_972_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_head_918_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_1013_){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_inline_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_1017_, lean_object* v_inline_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_1020_, lean_object* v_pos_1021_){
_start:
{
lean_object* v_str_1022_; lean_object* v_startInclusive_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v_decide_1027_; 
v_str_1022_ = lean_ctor_get(v_s_1020_, 0);
v_startInclusive_1023_ = lean_ctor_get(v_s_1020_, 1);
v___x_1024_ = lean_nat_add(v_startInclusive_1023_, v_pos_1021_);
v___x_1025_ = lean_nat_sub(v___x_1024_, v_startInclusive_1023_);
v___x_1026_ = lean_unsigned_to_nat(0u);
v_decide_1027_ = lean_nat_dec_eq(v___x_1025_, v___x_1026_);
if (v_decide_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1036_; uint32_t v___x_1037_; uint32_t v___x_1038_; uint8_t v___x_1039_; 
lean_inc(v_startInclusive_1023_);
lean_inc_ref(v_str_1022_);
v___x_1028_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1028_, 0, v_str_1022_);
lean_ctor_set(v___x_1028_, 1, v_startInclusive_1023_);
lean_ctor_set(v___x_1028_, 2, v___x_1024_);
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_sub(v___x_1025_, v___x_1029_);
lean_dec(v___x_1025_);
v___x_1031_ = l_String_Slice_posLE(v___x_1028_, v___x_1030_);
lean_dec_ref_known(v___x_1028_, 3);
v___x_1036_ = lean_nat_add(v_startInclusive_1023_, v___x_1031_);
v___x_1037_ = lean_string_utf8_get_fast(v_str_1022_, v___x_1036_);
lean_dec(v___x_1036_);
v___x_1038_ = 32;
v___x_1039_ = lean_uint32_dec_eq(v___x_1037_, v___x_1038_);
if (v___x_1039_ == 0)
{
uint32_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = 9;
v___x_1041_ = lean_uint32_dec_eq(v___x_1037_, v___x_1040_);
if (v___x_1041_ == 0)
{
uint32_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = 13;
v___x_1043_ = lean_uint32_dec_eq(v___x_1037_, v___x_1042_);
if (v___x_1043_ == 0)
{
uint32_t v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = 10;
v___x_1045_ = lean_uint32_dec_eq(v___x_1037_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_dec(v___x_1031_);
return v_pos_1021_;
}
else
{
goto v___jp_1032_;
}
}
else
{
goto v___jp_1032_;
}
}
else
{
goto v___jp_1032_;
}
}
else
{
goto v___jp_1032_;
}
v___jp_1032_:
{
lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = lean_nat_add(v___x_1031_, v___x_1029_);
v___x_1034_ = lean_nat_dec_le(v___x_1033_, v_pos_1021_);
lean_dec(v___x_1033_);
if (v___x_1034_ == 0)
{
lean_dec(v___x_1031_);
return v_pos_1021_;
}
else
{
lean_dec(v_pos_1021_);
v_pos_1021_ = v___x_1031_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1025_);
lean_dec(v___x_1024_);
return v_pos_1021_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_1046_, lean_object* v_pos_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_1046_, v_pos_1047_);
lean_dec_ref(v_s_1046_);
return v_res_1048_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1050_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v___x_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_xs_1052_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1053_ = lean_array_get_size(v_xs_1052_);
v___x_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = lean_nat_dec_eq(v___x_1053_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = lean_unsigned_to_nat(1u);
v___x_1057_ = lean_nat_sub(v___x_1053_, v___x_1056_);
v___x_1058_ = lean_array_fget(v_xs_1052_, v___x_1057_);
lean_dec(v___x_1057_);
switch(lean_obj_tag(v___x_1058_))
{
case 0:
{
lean_object* v_string_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1089_; 
v_string_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1089_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_string_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1089_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v_decide_1066_; 
v___x_1063_ = lean_string_utf8_byte_size(v_string_1059_);
lean_inc_ref(v_string_1059_);
v___x_1064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1064_, 0, v_string_1059_);
lean_ctor_set(v___x_1064_, 1, v___x_1054_);
lean_ctor_set(v___x_1064_, 2, v___x_1063_);
v___x_1065_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_1064_, v___x_1054_);
v_decide_1066_ = lean_nat_dec_eq(v___x_1065_, v___x_1063_);
lean_dec(v___x_1065_);
if (v_decide_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1067_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_1064_, v___x_1063_);
lean_dec_ref_known(v___x_1064_, 3);
v___x_1068_ = lean_array_pop(v_xs_1052_);
v___x_1069_ = lean_string_utf8_extract_fast(v_string_1059_, v___x_1054_, v___x_1067_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1069_);
v___x_1071_ = v___x_1061_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1072_ = lean_array_push(v___x_1068_, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
v___x_1074_ = lean_string_utf8_extract_fast(v_string_1059_, v___x_1067_, v___x_1063_);
lean_dec(v___x_1067_);
lean_dec_ref(v_string_1059_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
return v___x_1075_;
}
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v_fst_1079_; lean_object* v_snd_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref_known(v___x_1064_, 3);
lean_del_object(v___x_1061_);
v___x_1077_ = lean_array_pop(v_xs_1052_);
v___x_1078_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1077_);
v_fst_1079_ = lean_ctor_get(v___x_1078_, 0);
v_snd_1080_ = lean_ctor_get(v___x_1078_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1082_ = v___x_1078_;
v_isShared_1083_ = v_isSharedCheck_1088_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_snd_1080_);
lean_inc(v_fst_1079_);
lean_dec(v___x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1088_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1084_ = lean_string_append(v_snd_1080_, v_string_1059_);
lean_dec_ref(v_string_1059_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 1, v___x_1084_);
v___x_1086_ = v___x_1082_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_fst_1079_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
case 9:
{
lean_object* v_content_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_content_1090_ = lean_ctor_get(v___x_1058_, 0);
lean_inc_ref(v_content_1090_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1091_ = lean_array_pop(v_xs_1052_);
v___x_1092_ = l_Array_append___redArg(v___x_1091_, v_content_1090_);
lean_dec_ref(v_content_1090_);
v_xs_1052_ = v___x_1092_;
goto _start;
}
default: 
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v___x_1058_);
v___x_1094_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_xs_1052_);
v___x_1095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
return v___x_1096_;
}
}
}
else
{
lean_object* v___x_1097_; 
lean_dec_ref(v_xs_1052_);
v___x_1097_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_1097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_1098_, lean_object* v_xs_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_xs_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1102_ = lean_unsigned_to_nat(1u);
v___x_1103_ = lean_mk_empty_array_with_capacity(v___x_1102_);
v___x_1104_ = lean_array_push(v___x_1103_, v_inline_1101_);
v___x_1105_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_1106_, lean_object* v_inline_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v_fst_1111_; lean_object* v_snd_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1120_; 
v___x_1110_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1109_);
v_fst_1111_ = lean_ctor_get(v___x_1110_, 0);
v_snd_1112_ = lean_ctor_get(v___x_1110_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1114_ = v___x_1110_;
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1112_);
lean_inc(v_fst_1111_);
lean_dec(v___x_1110_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1116_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_1112_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1116_);
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_fst_1111_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_1121_, lean_object* v_inline_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_1122_);
return v___x_1123_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_instMonadEIO___redArg();
return v___x_1124_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0);
v___x_1126_ = l_StateRefT_x27_instMonad___redArg(v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13));
v___x_1156_ = lean_unsigned_to_nat(3u);
v___x_1157_ = lean_mk_empty_array_with_capacity(v___x_1156_);
v___x_1158_ = lean_array_push(v___x_1157_, v___x_1155_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object* v_inst_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1161_, v_x_1162_, v_x_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_pieces_1177_; lean_object* v_pieces_1181_; lean_object* v___x_1184_; lean_object* v_toApplicative_1185_; lean_object* v_toFunctor_1186_; lean_object* v_toSeq_1187_; lean_object* v_toSeqLeft_1188_; lean_object* v_toSeqRight_1189_; lean_object* v___f_1190_; lean_object* v___f_1191_; lean_object* v___f_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; lean_object* v___f_1195_; lean_object* v___f_1196_; lean_object* v___f_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1184_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1185_ = lean_ctor_get(v___x_1184_, 0);
v_toFunctor_1186_ = lean_ctor_get(v_toApplicative_1185_, 0);
v_toSeq_1187_ = lean_ctor_get(v_toApplicative_1185_, 2);
v_toSeqLeft_1188_ = lean_ctor_get(v_toApplicative_1185_, 3);
v_toSeqRight_1189_ = lean_ctor_get(v_toApplicative_1185_, 4);
v___f_1190_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1191_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1186_, 2);
v___f_1192_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1192_, 0, v_toFunctor_1186_);
v___f_1193_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1193_, 0, v_toFunctor_1186_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___f_1192_);
lean_ctor_set(v___x_1194_, 1, v___f_1193_);
lean_inc(v_toSeqRight_1189_);
v___f_1195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1195_, 0, v_toSeqRight_1189_);
lean_inc(v_toSeqLeft_1188_);
v___f_1196_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1196_, 0, v_toSeqLeft_1188_);
lean_inc(v_toSeq_1187_);
v___f_1197_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1197_, 0, v_toSeq_1187_);
v___x_1198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1194_);
lean_ctor_set(v___x_1198_, 1, v___f_1190_);
lean_ctor_set(v___x_1198_, 2, v___f_1197_);
lean_ctor_set(v___x_1198_, 3, v___f_1196_);
lean_ctor_set(v___x_1198_, 4, v___f_1195_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v___f_1191_);
v___x_1200_ = l_StateRefT_x27_instMonad___redArg(v___x_1199_);
switch(lean_obj_tag(v_x_1171_))
{
case 0:
{
lean_object* v_string_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_x_1170_);
lean_dec_ref(v_inst_1169_);
v_string_1201_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_string_1201_);
lean_dec_ref_known(v_x_1171_, 1);
v___x_1202_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1201_);
lean_dec_ref(v_string_1201_);
v___x_1203_ = lean_unsigned_to_nat(1u);
v___x_1204_ = lean_mk_empty_array_with_capacity(v___x_1203_);
v___x_1205_ = lean_array_push(v___x_1204_, v___x_1202_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
case 1:
{
lean_object* v_content_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v___x_1200_);
v_content_1207_ = lean_ctor_get(v_x_1171_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1209_ = v_x_1171_;
v_isShared_1210_ = v_isSharedCheck_1258_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_content_1207_);
lean_dec(v_x_1171_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1258_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 9);
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_content_1207_);
v___x_1212_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; lean_object* v_snd_1214_; lean_object* v_fst_1215_; lean_object* v_fst_1216_; lean_object* v_snd_1217_; lean_object* v_pieces_1219_; uint8_t v_inEmph_1227_; uint8_t v_inBold_1228_; uint8_t v_inLink_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1256_; 
v___x_1213_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1212_);
v_snd_1214_ = lean_ctor_get(v___x_1213_, 1);
lean_inc(v_snd_1214_);
v_fst_1215_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_fst_1215_);
lean_dec_ref(v___x_1213_);
v_fst_1216_ = lean_ctor_get(v_snd_1214_, 0);
lean_inc(v_fst_1216_);
v_snd_1217_ = lean_ctor_get(v_snd_1214_, 1);
lean_inc(v_snd_1217_);
lean_dec(v_snd_1214_);
v_inEmph_1227_ = lean_ctor_get_uint8(v_x_1170_, 0);
v_inBold_1228_ = lean_ctor_get_uint8(v_x_1170_, 1);
v_inLink_1229_ = lean_ctor_get_uint8(v_x_1170_, 2);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_x_1170_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1231_ = v_x_1170_;
v_isShared_1232_ = v_isSharedCheck_1256_;
goto v_resetjp_1230_;
}
else
{
lean_dec(v_x_1170_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1256_;
goto v_resetjp_1230_;
}
v___jp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1220_ = lean_string_utf8_byte_size(v_snd_1217_);
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_nat_dec_eq(v___x_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = lean_mk_empty_array_with_capacity(v___x_1223_);
v___x_1225_ = lean_array_push(v___x_1224_, v_snd_1217_);
v___x_1226_ = lean_array_push(v_pieces_1219_, v___x_1225_);
v_pieces_1181_ = v___x_1226_;
goto v___jp_1180_;
}
else
{
lean_dec(v_snd_1217_);
v_pieces_1181_ = v_pieces_1219_;
goto v___jp_1180_;
}
}
v_resetjp_1230_:
{
uint8_t v___x_1233_; lean_object* v___x_1235_; 
v___x_1233_ = 1;
if (v_isShared_1232_ == 0)
{
v___x_1235_ = v___x_1231_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1255_, 1, v_inBold_1228_);
lean_ctor_set_uint8(v_reuseFailAlloc_1255_, 2, v_inLink_1229_);
v___x_1235_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; 
lean_ctor_set_uint8(v___x_1235_, 0, v___x_1233_);
v___x_1236_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1169_, v___x_1235_, v_fst_1216_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v_pieces_1239_; lean_object* v_pieces_1244_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1249_ = lean_string_utf8_byte_size(v_fst_1215_);
v___x_1250_ = lean_nat_dec_eq(v___x_1249_, v___x_1247_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = lean_mk_empty_array_with_capacity(v___x_1251_);
v___x_1253_ = lean_array_push(v___x_1252_, v_fst_1215_);
v___x_1254_ = lean_array_push(v___x_1248_, v___x_1253_);
v_pieces_1244_ = v___x_1254_;
goto v___jp_1243_;
}
else
{
lean_dec(v_fst_1215_);
v_pieces_1244_ = v___x_1248_;
goto v___jp_1243_;
}
v___jp_1238_:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_array_push(v_pieces_1239_, v_a_1237_);
if (v_inEmph_1227_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1242_ = lean_array_push(v___x_1240_, v___x_1241_);
v_pieces_1219_ = v___x_1242_;
goto v___jp_1218_;
}
else
{
v_pieces_1219_ = v___x_1240_;
goto v___jp_1218_;
}
}
v___jp_1243_:
{
if (v_inEmph_1227_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1246_ = lean_array_push(v_pieces_1244_, v___x_1245_);
v_pieces_1239_ = v___x_1246_;
goto v___jp_1238_;
}
else
{
v_pieces_1239_ = v_pieces_1244_;
goto v___jp_1238_;
}
}
}
else
{
lean_dec(v_snd_1217_);
lean_dec(v_fst_1215_);
return v___x_1236_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v___x_1200_);
v_content_1259_ = lean_ctor_get(v_x_1171_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1261_ = v_x_1171_;
v_isShared_1262_ = v_isSharedCheck_1310_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_content_1259_);
lean_dec(v_x_1171_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1310_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set_tag(v___x_1261_, 9);
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_content_1259_);
v___x_1264_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v_snd_1266_; lean_object* v_fst_1267_; lean_object* v_fst_1268_; lean_object* v_snd_1269_; lean_object* v_pieces_1271_; uint8_t v_inEmph_1279_; uint8_t v_inBold_1280_; uint8_t v_inLink_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1308_; 
v___x_1265_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1264_);
v_snd_1266_ = lean_ctor_get(v___x_1265_, 1);
lean_inc(v_snd_1266_);
v_fst_1267_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_fst_1267_);
lean_dec_ref(v___x_1265_);
v_fst_1268_ = lean_ctor_get(v_snd_1266_, 0);
lean_inc(v_fst_1268_);
v_snd_1269_ = lean_ctor_get(v_snd_1266_, 1);
lean_inc(v_snd_1269_);
lean_dec(v_snd_1266_);
v_inEmph_1279_ = lean_ctor_get_uint8(v_x_1170_, 0);
v_inBold_1280_ = lean_ctor_get_uint8(v_x_1170_, 1);
v_inLink_1281_ = lean_ctor_get_uint8(v_x_1170_, 2);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_x_1170_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1283_ = v_x_1170_;
v_isShared_1284_ = v_isSharedCheck_1308_;
goto v_resetjp_1282_;
}
else
{
lean_dec(v_x_1170_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1308_;
goto v_resetjp_1282_;
}
v___jp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = lean_string_utf8_byte_size(v_snd_1269_);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_nat_dec_eq(v___x_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1275_ = lean_unsigned_to_nat(1u);
v___x_1276_ = lean_mk_empty_array_with_capacity(v___x_1275_);
v___x_1277_ = lean_array_push(v___x_1276_, v_snd_1269_);
v___x_1278_ = lean_array_push(v_pieces_1271_, v___x_1277_);
v_pieces_1177_ = v___x_1278_;
goto v___jp_1176_;
}
else
{
lean_dec(v_snd_1269_);
v_pieces_1177_ = v_pieces_1271_;
goto v___jp_1176_;
}
}
v_resetjp_1282_:
{
uint8_t v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = 1;
if (v_isShared_1284_ == 0)
{
v___x_1287_ = v___x_1283_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 0, v_inEmph_1279_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 2, v_inLink_1281_);
v___x_1287_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; 
lean_ctor_set_uint8(v___x_1287_, 1, v___x_1285_);
v___x_1288_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1169_, v___x_1287_, v_fst_1268_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v_pieces_1291_; lean_object* v_pieces_1296_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1301_ = lean_string_utf8_byte_size(v_fst_1267_);
v___x_1302_ = lean_nat_dec_eq(v___x_1301_, v___x_1299_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1303_ = lean_unsigned_to_nat(1u);
v___x_1304_ = lean_mk_empty_array_with_capacity(v___x_1303_);
v___x_1305_ = lean_array_push(v___x_1304_, v_fst_1267_);
v___x_1306_ = lean_array_push(v___x_1300_, v___x_1305_);
v_pieces_1296_ = v___x_1306_;
goto v___jp_1295_;
}
else
{
lean_dec(v_fst_1267_);
v_pieces_1296_ = v___x_1300_;
goto v___jp_1295_;
}
v___jp_1290_:
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_array_push(v_pieces_1291_, v_a_1289_);
if (v_inBold_1280_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1294_ = lean_array_push(v___x_1292_, v___x_1293_);
v_pieces_1271_ = v___x_1294_;
goto v___jp_1270_;
}
else
{
v_pieces_1271_ = v___x_1292_;
goto v___jp_1270_;
}
}
v___jp_1295_:
{
if (v_inBold_1280_ == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1298_ = lean_array_push(v_pieces_1296_, v___x_1297_);
v_pieces_1291_ = v___x_1298_;
goto v___jp_1290_;
}
else
{
v_pieces_1291_ = v_pieces_1296_;
goto v___jp_1290_;
}
}
}
else
{
lean_dec(v_snd_1269_);
lean_dec(v_fst_1267_);
return v___x_1288_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_x_1170_);
lean_dec_ref(v_inst_1169_);
v_string_1311_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_string_1311_);
lean_dec_ref_known(v_x_1171_, 1);
v___x_1312_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1311_);
v___x_1313_ = lean_unsigned_to_nat(1u);
v___x_1314_ = lean_mk_empty_array_with_capacity(v___x_1313_);
v___x_1315_ = lean_array_push(v___x_1314_, v___x_1312_);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
return v___x_1316_;
}
case 4:
{
uint8_t v_mode_1317_; 
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_x_1170_);
lean_dec_ref(v_inst_1169_);
v_mode_1317_ = lean_ctor_get_uint8(v_x_1171_, sizeof(void*)*1);
if (v_mode_1317_ == 0)
{
lean_object* v_string_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_string_1318_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_string_1318_);
lean_dec_ref_known(v_x_1171_, 1);
v___x_1319_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_1320_ = lean_string_append(v___x_1319_, v_string_1318_);
lean_dec_ref(v_string_1318_);
v___x_1321_ = lean_string_append(v___x_1320_, v___x_1319_);
v___x_1322_ = lean_unsigned_to_nat(1u);
v___x_1323_ = lean_mk_empty_array_with_capacity(v___x_1322_);
v___x_1324_ = lean_array_push(v___x_1323_, v___x_1321_);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
else
{
lean_object* v_string_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_string_1326_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_string_1326_);
lean_dec_ref_known(v_x_1171_, 1);
v___x_1327_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_1328_ = lean_string_append(v___x_1327_, v_string_1326_);
lean_dec_ref(v_string_1326_);
v___x_1329_ = lean_string_append(v___x_1328_, v___x_1327_);
v___x_1330_ = lean_unsigned_to_nat(1u);
v___x_1331_ = lean_mk_empty_array_with_capacity(v___x_1330_);
v___x_1332_ = lean_array_push(v___x_1331_, v___x_1329_);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
case 5:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_dec_ref_known(v_x_1171_, 1);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_x_1170_);
lean_dec_ref(v_inst_1169_);
v___x_1334_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
case 6:
{
uint8_t v_inLink_1336_; 
v_inLink_1336_ = lean_ctor_get_uint8(v_x_1170_, 2);
if (v_inLink_1336_ == 0)
{
lean_object* v_content_1337_; lean_object* v_url_1338_; uint8_t v_inEmph_1339_; uint8_t v_inBold_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v___x_1200_);
v_content_1337_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_content_1337_);
v_url_1338_ = lean_ctor_get(v_x_1171_, 1);
lean_inc_ref(v_url_1338_);
lean_dec_ref_known(v_x_1171_, 2);
v_inEmph_1339_ = lean_ctor_get_uint8(v_x_1170_, 0);
v_inBold_1340_ = lean_ctor_get_uint8(v_x_1170_, 1);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_x_1170_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1342_ = v_x_1170_;
v_isShared_1343_ = v_isSharedCheck_1369_;
goto v_resetjp_1341_;
}
else
{
lean_dec(v_x_1170_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1369_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
uint8_t v___x_1344_; lean_object* v___x_1346_; 
v___x_1344_ = 1;
if (v_isShared_1343_ == 0)
{
v___x_1346_ = v___x_1342_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, 0, v_inEmph_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, 1, v_inBold_1340_);
v___x_1346_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_ctor_set_uint8(v___x_1346_, 2, v___x_1344_);
v___x_1347_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1347_, 0, v_content_1337_);
v___x_1348_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1169_, v___x_1346_, v___x_1347_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1367_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1367_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1367_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1353_ = lean_unsigned_to_nat(1u);
v___x_1354_ = lean_mk_empty_array_with_capacity(v___x_1353_);
v___x_1355_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1356_ = lean_string_append(v___x_1355_, v_url_1338_);
lean_dec_ref(v_url_1338_);
v___x_1357_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1358_ = lean_string_append(v___x_1356_, v___x_1357_);
v___x_1359_ = lean_array_push(v___x_1354_, v___x_1358_);
v___x_1360_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_1361_ = lean_array_push(v___x_1360_, v_a_1349_);
v___x_1362_ = lean_array_push(v___x_1361_, v___x_1359_);
v___x_1363_ = l_Lean_Doc_joinInlines(v___x_1362_);
lean_dec_ref(v___x_1362_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1363_);
v___x_1365_ = v___x_1351_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_dec_ref(v_url_1338_);
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_content_1370_; lean_object* v___x_1371_; size_t v_sz_1372_; size_t v___x_1373_; lean_object* v___x_4024__overap_1374_; lean_object* v___x_1375_; 
v_content_1370_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_content_1370_);
lean_dec_ref_known(v_x_1171_, 2);
v___x_1371_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1371_, 0, v_inst_1169_);
lean_closure_set(v___x_1371_, 1, v_x_1170_);
v_sz_1372_ = lean_array_size(v_content_1370_);
v___x_1373_ = ((size_t)0ULL);
v___x_4024__overap_1374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1200_, v___x_1371_, v_sz_1372_, v___x_1373_, v_content_1370_);
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
lean_inc(v_a_1172_);
v___x_1375_ = lean_apply_4(v___x_4024__overap_1374_, v_a_1172_, v_a_1173_, v_a_1174_, lean_box(0));
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1384_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1384_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1384_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1380_ = l_Lean_Doc_joinInlines(v_a_1376_);
lean_dec(v_a_1376_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1380_);
v___x_1382_ = v___x_1378_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
v_a_1385_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1375_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1375_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
case 7:
{
lean_object* v_name_1393_; lean_object* v_content_1394_; lean_object* v___x_1395_; size_t v_sz_1396_; size_t v___x_1397_; lean_object* v___x_4027__overap_1398_; lean_object* v___x_1399_; 
v_name_1393_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_name_1393_);
v_content_1394_ = lean_ctor_get(v_x_1171_, 1);
lean_inc_ref(v_content_1394_);
lean_dec_ref_known(v_x_1171_, 2);
v___x_1395_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1395_, 0, v_inst_1169_);
lean_closure_set(v___x_1395_, 1, v_x_1170_);
v_sz_1396_ = lean_array_size(v_content_1394_);
v___x_1397_ = ((size_t)0ULL);
v___x_4027__overap_1398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1200_, v___x_1395_, v_sz_1396_, v___x_1397_, v_content_1394_);
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
lean_inc(v_a_1172_);
v___x_1399_ = lean_apply_4(v___x_4027__overap_1398_, v_a_1172_, v_a_1173_, v_a_1174_, lean_box(0));
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1401_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_1402_ = l_Lean_Doc_joinInlines(v_a_1400_);
lean_dec(v_a_1400_);
v___x_1403_ = lean_array_to_list(v___x_1402_);
v___x_1404_ = l_String_intercalate(v___x_1401_, v___x_1403_);
lean_inc_ref(v_name_1393_);
v___x_1405_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_1393_, v___x_1404_, v_a_1172_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1419_; 
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v___x_1405_, 0);
lean_dec(v_unused_1420_);
v___x_1407_ = v___x_1405_;
v_isShared_1408_ = v_isSharedCheck_1419_;
goto v_resetjp_1406_;
}
else
{
lean_dec(v___x_1405_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1419_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1409_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_1410_ = lean_string_append(v___x_1409_, v_name_1393_);
lean_dec_ref(v_name_1393_);
v___x_1411_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_1412_ = lean_string_append(v___x_1410_, v___x_1411_);
v___x_1413_ = lean_unsigned_to_nat(1u);
v___x_1414_ = lean_mk_empty_array_with_capacity(v___x_1413_);
v___x_1415_ = lean_array_push(v___x_1414_, v___x_1412_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1415_);
v___x_1417_ = v___x_1407_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec_ref(v_name_1393_);
v_a_1421_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1405_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1405_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec_ref(v_name_1393_);
v_a_1429_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1399_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1399_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
case 8:
{
lean_object* v_alt_1437_; lean_object* v_url_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_x_1170_);
lean_dec_ref(v_inst_1169_);
v_alt_1437_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_alt_1437_);
v_url_1438_ = lean_ctor_get(v_x_1171_, 1);
lean_inc_ref(v_url_1438_);
lean_dec_ref_known(v_x_1171_, 2);
v___x_1439_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_1440_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1437_);
lean_dec_ref(v_alt_1437_);
v___x_1441_ = lean_string_append(v___x_1439_, v___x_1440_);
lean_dec_ref(v___x_1440_);
v___x_1442_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1443_ = lean_string_append(v___x_1441_, v___x_1442_);
v___x_1444_ = lean_string_append(v___x_1443_, v_url_1438_);
lean_dec_ref(v_url_1438_);
v___x_1445_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1446_ = lean_string_append(v___x_1444_, v___x_1445_);
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_mk_empty_array_with_capacity(v___x_1447_);
v___x_1449_ = lean_array_push(v___x_1448_, v___x_1446_);
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
case 9:
{
lean_object* v_content_1451_; lean_object* v___x_1452_; size_t v_sz_1453_; size_t v___x_1454_; lean_object* v___x_4030__overap_1455_; lean_object* v___x_1456_; 
v_content_1451_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_content_1451_);
lean_dec_ref_known(v_x_1171_, 1);
v___x_1452_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1452_, 0, v_inst_1169_);
lean_closure_set(v___x_1452_, 1, v_x_1170_);
v_sz_1453_ = lean_array_size(v_content_1451_);
v___x_1454_ = ((size_t)0ULL);
v___x_4030__overap_1455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1200_, v___x_1452_, v_sz_1453_, v___x_1454_, v_content_1451_);
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
lean_inc(v_a_1172_);
v___x_1456_ = lean_apply_4(v___x_4030__overap_1455_, v_a_1172_, v_a_1173_, v_a_1174_, lean_box(0));
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1465_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1461_ = l_Lean_Doc_joinInlines(v_a_1457_);
lean_dec(v_a_1457_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1461_);
v___x_1463_ = v___x_1459_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
v_a_1466_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1456_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1456_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
default: 
{
lean_object* v_container_1474_; lean_object* v_content_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec_ref(v___x_1200_);
v_container_1474_ = lean_ctor_get(v_x_1171_, 0);
lean_inc(v_container_1474_);
v_content_1475_ = lean_ctor_get(v_x_1171_, 1);
lean_inc_ref(v_content_1475_);
lean_dec_ref_known(v_x_1171_, 2);
lean_inc_ref(v_inst_1169_);
v___x_1476_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1476_, 0, v_inst_1169_);
lean_closure_set(v___x_1476_, 1, v_x_1170_);
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
lean_inc(v_a_1172_);
v___x_1477_ = lean_apply_7(v_inst_1169_, v___x_1476_, v_container_1474_, v_content_1475_, v_a_1172_, v_a_1173_, v_a_1174_, lean_box(0));
return v___x_1477_;
}
}
v___jp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = l_Lean_Doc_joinInlines(v_pieces_1177_);
lean_dec_ref(v_pieces_1177_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
v___jp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = l_Lean_Doc_joinInlines(v_pieces_1181_);
lean_dec_ref(v_pieces_1181_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1478_, lean_object* v_inst_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1479_, v_x_1480_, v_x_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object* v_i_1487_, lean_object* v_inst_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(v_i_1487_, v_inst_1488_, v_x_1489_, v_x_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1503_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1496_, v___x_1502_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object* v_inst_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(v_inst_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
lean_dec(v_a_1506_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1511_, lean_object* v_inst_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1519_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1512_, v___x_1518_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object* v_i_1520_, lean_object* v_inst_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(v_i_1520_, v_inst_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1529_, 0, lean_box(0));
lean_closure_set(v___x_1529_, 1, v_inst_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1530_, lean_object* v_inst_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1532_, 0, lean_box(0));
lean_closure_set(v___x_1532_, 1, v_inst_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(uint32_t v___x_1533_, lean_object* v_s_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_string_push(v_s_1534_, v___x_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object* v___x_1536_, lean_object* v_s_1537_){
_start:
{
uint32_t v___x_2520__boxed_1538_; lean_object* v_res_1539_; 
v___x_2520__boxed_1538_ = lean_unbox_uint32(v___x_1536_);
lean_dec(v___x_1536_);
v_res_1539_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v___x_2520__boxed_1538_, v_s_1537_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed(lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v___x_1544_, lean_object* v_item_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(v_inst_1542_, v_inst_1543_, v___x_1544_, v_item_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
return v_res_1550_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___f_1553_; 
v___x_1552_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___f_1553_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1553_, 0, v___x_1552_);
return v___f_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v___x_1556_, lean_object* v___x_1557_, lean_object* v_a_1558_, lean_object* v_x_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_fst_1565_; lean_object* v_snd_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1606_; 
v_fst_1565_ = lean_ctor_get(v___y_1560_, 0);
v_snd_1566_ = lean_ctor_get(v___y_1560_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___y_1560_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1568_ = v___y_1560_;
v_isShared_1569_ = v_isSharedCheck_1606_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_snd_1566_);
lean_inc(v_fst_1565_);
lean_dec(v___y_1560_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1606_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; size_t v_sz_1578_; size_t v___x_1579_; lean_object* v___x_2461__overap_1580_; lean_object* v___x_1581_; 
lean_inc(v_snd_1566_);
v___x_1570_ = l_Nat_reprFast(v_snd_1566_);
v___x_1571_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_1572_ = lean_string_append(v___x_1570_, v___x_1571_);
v___x_1573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_1574_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1);
v___x_1575_ = lean_string_utf8_byte_size(v___x_1572_);
v___x_1576_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1574_, v___x_1575_, v___x_1573_);
v___x_1577_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1577_, 0, v_inst_1554_);
lean_closure_set(v___x_1577_, 1, v_inst_1555_);
v_sz_1578_ = lean_array_size(v_a_1558_);
v___x_1579_ = ((size_t)0ULL);
v___x_2461__overap_1580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1556_, v___x_1577_, v_sz_1578_, v___x_1579_, v_a_1558_);
lean_inc(v___y_1563_);
lean_inc_ref(v___y_1562_);
lean_inc(v___y_1561_);
v___x_1581_ = lean_apply_4(v___x_2461__overap_1580_, v___y_1561_, v___y_1562_, v___y_1563_, lean_box(0));
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1597_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1597_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1597_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1586_ = l_Lean_Doc_joinBlocks(v_a_1582_);
lean_dec(v_a_1582_);
v___x_1587_ = l_Lean_Doc_prefixListLines(v___x_1572_, v___x_1576_, v___x_1586_);
v___x_1588_ = lean_array_push(v_fst_1565_, v___x_1587_);
v___x_1589_ = lean_nat_add(v_snd_1566_, v___x_1557_);
lean_dec(v_snd_1566_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v___x_1589_);
lean_ctor_set(v___x_1568_, 0, v___x_1588_);
v___x_1591_ = v___x_1568_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1592_);
v___x_1594_ = v___x_1584_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v___x_1576_);
lean_dec_ref(v___x_1572_);
lean_del_object(v___x_1568_);
lean_dec(v_snd_1566_);
lean_dec(v_fst_1565_);
v_a_1598_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1581_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1581_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v___x_1609_, lean_object* v___x_1610_, lean_object* v_a_1611_, lean_object* v_x_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1607_, v_inst_1608_, v___x_1609_, v___x_1610_, v_a_1611_, v_x_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec(v___x_1610_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v___x_1626_, lean_object* v_item_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; lean_object* v_term_1633_; lean_object* v_desc_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1632_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_1633_ = lean_ctor_get(v_item_1627_, 0);
lean_inc_ref(v_term_1633_);
v_desc_1634_ = lean_ctor_get(v_item_1627_, 1);
lean_inc_ref(v_desc_1634_);
lean_dec_ref(v_item_1627_);
v___x_1635_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1635_, 0, v_term_1633_);
lean_inc_ref(v_inst_1624_);
v___x_1636_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1624_, v___x_1632_, v___x_1635_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; size_t v_sz_1639_; size_t v___x_1640_; lean_object* v___x_2489__overap_1641_; lean_object* v___x_1642_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1638_, 0, v_inst_1624_);
lean_closure_set(v___x_1638_, 1, v_inst_1625_);
v_sz_1639_ = lean_array_size(v_desc_1634_);
v___x_1640_ = ((size_t)0ULL);
lean_inc_ref(v_desc_1634_);
v___x_2489__overap_1641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1626_, v___x_1638_, v_sz_1639_, v___x_1640_, v_desc_1634_);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
lean_inc(v___y_1628_);
v___x_1642_ = lean_apply_4(v___x_2489__overap_1641_, v___y_1628_, v___y_1629_, v___y_1630_, lean_box(0));
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1670_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1670_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1670_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___y_1648_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1655_ = lean_unsigned_to_nat(1u);
v___x_1656_ = lean_mk_empty_array_with_capacity(v___x_1655_);
v___x_1657_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_1658_ = lean_unsigned_to_nat(2u);
v___x_1659_ = lean_mk_empty_array_with_capacity(v___x_1658_);
v___x_1660_ = lean_array_push(v___x_1659_, v_a_1637_);
v___x_1661_ = lean_array_push(v___x_1660_, v___x_1657_);
v___x_1662_ = l_Lean_Doc_joinInlines(v___x_1661_);
lean_dec_ref(v___x_1661_);
v___x_1663_ = lean_array_get_size(v_desc_1634_);
lean_dec_ref(v_desc_1634_);
v___x_1664_ = lean_nat_dec_le(v___x_1663_, v___x_1655_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = lean_array_push(v___x_1656_, v___x_1662_);
v___x_1666_ = l_Array_append___redArg(v___x_1665_, v_a_1643_);
lean_dec(v_a_1643_);
v___x_1667_ = l_Lean_Doc_joinBlocks(v___x_1666_);
lean_dec_ref(v___x_1666_);
v___y_1648_ = v___x_1667_;
goto v___jp_1647_;
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v___x_1656_);
v___x_1668_ = l_Lean_Doc_joinBlocks(v_a_1643_);
lean_dec(v_a_1643_);
v___x_1669_ = l_Array_append___redArg(v___x_1662_, v___x_1668_);
lean_dec_ref(v___x_1668_);
v___y_1648_ = v___x_1669_;
goto v___jp_1647_;
}
v___jp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1649_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1650_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1651_ = l_Lean_Doc_prefixListLines(v___x_1649_, v___x_1650_, v___y_1648_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1651_);
v___x_1653_ = v___x_1645_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_a_1637_);
lean_dec_ref(v_desc_1634_);
v_a_1671_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1642_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1642_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_dec_ref(v_desc_1634_);
lean_dec_ref(v___x_1626_);
lean_dec_ref(v_inst_1625_);
lean_dec_ref(v_inst_1624_);
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1679_, lean_object* v_inst_1680_, lean_object* v___x_1681_, lean_object* v_item_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1679_, v_inst_1680_, v___x_1681_, v_item_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_x_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v___x_1696_; lean_object* v_toApplicative_1697_; lean_object* v_toFunctor_1698_; lean_object* v_toSeq_1699_; lean_object* v_toSeqLeft_1700_; lean_object* v_toSeqRight_1701_; lean_object* v___f_1702_; lean_object* v___f_1703_; lean_object* v___f_1704_; lean_object* v___f_1705_; lean_object* v___x_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___f_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1696_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1697_ = lean_ctor_get(v___x_1696_, 0);
v_toFunctor_1698_ = lean_ctor_get(v_toApplicative_1697_, 0);
v_toSeq_1699_ = lean_ctor_get(v_toApplicative_1697_, 2);
v_toSeqLeft_1700_ = lean_ctor_get(v_toApplicative_1697_, 3);
v_toSeqRight_1701_ = lean_ctor_get(v_toApplicative_1697_, 4);
v___f_1702_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1703_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1698_, 2);
v___f_1704_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1704_, 0, v_toFunctor_1698_);
v___f_1705_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1705_, 0, v_toFunctor_1698_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___f_1704_);
lean_ctor_set(v___x_1706_, 1, v___f_1705_);
lean_inc(v_toSeqRight_1701_);
v___f_1707_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1707_, 0, v_toSeqRight_1701_);
lean_inc(v_toSeqLeft_1700_);
v___f_1708_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1708_, 0, v_toSeqLeft_1700_);
lean_inc(v_toSeq_1699_);
v___f_1709_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1709_, 0, v_toSeq_1699_);
v___x_1710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1706_);
lean_ctor_set(v___x_1710_, 1, v___f_1702_);
lean_ctor_set(v___x_1710_, 2, v___f_1709_);
lean_ctor_set(v___x_1710_, 3, v___f_1708_);
lean_ctor_set(v___x_1710_, 4, v___f_1707_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
lean_ctor_set(v___x_1711_, 1, v___f_1703_);
v___x_1712_ = l_StateRefT_x27_instMonad___redArg(v___x_1711_);
switch(lean_obj_tag(v_x_1691_))
{
case 0:
{
lean_object* v_contents_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref(v___x_1712_);
lean_dec_ref(v_inst_1690_);
v_contents_1713_ = lean_ctor_get(v_x_1691_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_x_1691_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1715_ = v_x_1691_;
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_contents_1713_);
lean_dec(v_x_1691_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_1716_ == 0)
{
lean_ctor_set_tag(v___x_1715_, 9);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_contents_1713_);
v___x_1719_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; 
v___x_1720_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1689_, v___x_1717_, v___x_1719_, v_a_1692_, v_a_1693_, v_a_1694_);
return v___x_1720_;
}
}
}
case 1:
{
lean_object* v_content_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v___x_1712_);
lean_dec_ref(v_inst_1690_);
lean_dec_ref(v_inst_1689_);
v_content_1723_ = lean_ctor_get(v_x_1691_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_x_1691_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1725_ = v_x_1691_;
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_content_1723_);
lean_dec(v_x_1691_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_1723_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set_tag(v___x_1725_, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
case 2:
{
lean_object* v_items_1732_; lean_object* v___f_1733_; size_t v_sz_1734_; size_t v___x_1735_; lean_object* v___x_2384__overap_1736_; lean_object* v___x_1737_; 
v_items_1732_ = lean_ctor_get(v_x_1691_, 0);
lean_inc_ref(v_items_1732_);
lean_dec_ref_known(v_x_1691_, 1);
lean_inc_ref(v___x_1712_);
v___f_1733_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1733_, 0, v_inst_1689_);
lean_closure_set(v___f_1733_, 1, v_inst_1690_);
lean_closure_set(v___f_1733_, 2, v___x_1712_);
v_sz_1734_ = lean_array_size(v_items_1732_);
v___x_1735_ = ((size_t)0ULL);
v___x_2384__overap_1736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1712_, v___f_1733_, v_sz_1734_, v___x_1735_, v_items_1732_);
lean_inc(v_a_1694_);
lean_inc_ref(v_a_1693_);
lean_inc(v_a_1692_);
v___x_1737_ = lean_apply_4(v___x_2384__overap_1736_, v_a_1692_, v_a_1693_, v_a_1694_, lean_box(0));
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1746_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1746_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1746_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1742_ = l_Lean_Doc_joinBlocks(v_a_1738_);
lean_dec(v_a_1738_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1742_);
v___x_1744_ = v___x_1740_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_a_1747_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1737_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1737_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
case 3:
{
lean_object* v_start_1755_; lean_object* v_items_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1792_; 
v_start_1755_ = lean_ctor_get(v_x_1691_, 0);
v_items_1756_ = lean_ctor_get(v_x_1691_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_x_1691_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1758_ = v_x_1691_;
v_isShared_1759_ = v_isSharedCheck_1792_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_items_1756_);
lean_inc(v_start_1755_);
lean_dec(v_x_1691_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1792_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_out_1760_; lean_object* v___x_1761_; lean_object* v___f_1762_; lean_object* v___y_1764_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_out_1760_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1761_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_1712_);
v___f_1762_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1762_, 0, v_inst_1689_);
lean_closure_set(v___f_1762_, 1, v_inst_1690_);
lean_closure_set(v___f_1762_, 2, v___x_1712_);
lean_closure_set(v___f_1762_, 3, v___x_1761_);
v___x_1790_ = l_Int_toNat(v_start_1755_);
lean_dec(v_start_1755_);
v___x_1791_ = lean_nat_dec_le(v___x_1761_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_dec(v___x_1790_);
v___y_1764_ = v___x_1761_;
goto v___jp_1763_;
}
else
{
v___y_1764_ = v___x_1790_;
goto v___jp_1763_;
}
v___jp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set_tag(v___x_1758_, 0);
lean_ctor_set(v___x_1758_, 1, v___y_1764_);
lean_ctor_set(v___x_1758_, 0, v_out_1760_);
v___x_1766_ = v___x_1758_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_out_1760_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v___y_1764_);
v___x_1766_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
size_t v_sz_1767_; size_t v___x_1768_; lean_object* v___x_2200__overap_1769_; lean_object* v___x_1770_; 
v_sz_1767_ = lean_array_size(v_items_1756_);
v___x_1768_ = ((size_t)0ULL);
v___x_2200__overap_1769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1712_, v_items_1756_, v___f_1762_, v_sz_1767_, v___x_1768_, v___x_1766_);
lean_inc(v_a_1694_);
lean_inc_ref(v_a_1693_);
lean_inc(v_a_1692_);
v___x_1770_ = lean_apply_4(v___x_2200__overap_1769_, v_a_1692_, v_a_1693_, v_a_1694_, lean_box(0));
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1780_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1780_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1780_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v_fst_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
v_fst_1775_ = lean_ctor_get(v_a_1771_, 0);
lean_inc(v_fst_1775_);
lean_dec(v_a_1771_);
v___x_1776_ = l_Lean_Doc_joinBlocks(v_fst_1775_);
lean_dec(v_fst_1775_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1776_);
v___x_1778_ = v___x_1773_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1770_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1770_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_1793_; lean_object* v___f_1794_; size_t v_sz_1795_; size_t v___x_1796_; lean_object* v___x_2390__overap_1797_; lean_object* v___x_1798_; 
v_items_1793_ = lean_ctor_get(v_x_1691_, 0);
lean_inc_ref(v_items_1793_);
lean_dec_ref_known(v_x_1691_, 1);
lean_inc_ref(v___x_1712_);
v___f_1794_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 8, 3);
lean_closure_set(v___f_1794_, 0, v_inst_1689_);
lean_closure_set(v___f_1794_, 1, v_inst_1690_);
lean_closure_set(v___f_1794_, 2, v___x_1712_);
v_sz_1795_ = lean_array_size(v_items_1793_);
v___x_1796_ = ((size_t)0ULL);
v___x_2390__overap_1797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1712_, v___f_1794_, v_sz_1795_, v___x_1796_, v_items_1793_);
lean_inc(v_a_1694_);
lean_inc_ref(v_a_1693_);
lean_inc(v_a_1692_);
v___x_1798_ = lean_apply_4(v___x_2390__overap_1797_, v_a_1692_, v_a_1693_, v_a_1694_, lean_box(0));
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1807_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1807_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1807_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = l_Lean_Doc_joinBlocks(v_a_1799_);
lean_dec(v_a_1799_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1803_);
v___x_1805_ = v___x_1801_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
v_a_1808_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1798_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1798_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
case 5:
{
lean_object* v_items_1816_; lean_object* v___x_1817_; size_t v_sz_1818_; size_t v___x_1819_; lean_object* v___x_2393__overap_1820_; lean_object* v___x_1821_; 
v_items_1816_ = lean_ctor_get(v_x_1691_, 0);
lean_inc_ref(v_items_1816_);
lean_dec_ref_known(v_x_1691_, 1);
v___x_1817_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1817_, 0, v_inst_1689_);
lean_closure_set(v___x_1817_, 1, v_inst_1690_);
v_sz_1818_ = lean_array_size(v_items_1816_);
v___x_1819_ = ((size_t)0ULL);
v___x_2393__overap_1820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1712_, v___x_1817_, v_sz_1818_, v___x_1819_, v_items_1816_);
lean_inc(v_a_1694_);
lean_inc_ref(v_a_1693_);
lean_inc(v_a_1692_);
v___x_1821_ = lean_apply_4(v___x_2393__overap_1820_, v_a_1692_, v_a_1693_, v_a_1694_, lean_box(0));
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1832_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1832_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1832_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1826_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_1827_ = l_Lean_Doc_joinBlocks(v_a_1822_);
lean_dec(v_a_1822_);
v___x_1828_ = l_Lean_Doc_prefixLines(v___x_1826_, v___x_1827_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1828_);
v___x_1830_ = v___x_1824_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
v_a_1833_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1821_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1821_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
case 6:
{
lean_object* v_content_1841_; lean_object* v___x_1842_; size_t v_sz_1843_; size_t v___x_1844_; lean_object* v___x_2396__overap_1845_; lean_object* v___x_1846_; 
v_content_1841_ = lean_ctor_get(v_x_1691_, 0);
lean_inc_ref(v_content_1841_);
lean_dec_ref_known(v_x_1691_, 1);
v___x_1842_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1842_, 0, v_inst_1689_);
lean_closure_set(v___x_1842_, 1, v_inst_1690_);
v_sz_1843_ = lean_array_size(v_content_1841_);
v___x_1844_ = ((size_t)0ULL);
v___x_2396__overap_1845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1712_, v___x_1842_, v_sz_1843_, v___x_1844_, v_content_1841_);
lean_inc(v_a_1694_);
lean_inc_ref(v_a_1693_);
lean_inc(v_a_1692_);
v___x_1846_ = lean_apply_4(v___x_2396__overap_1845_, v_a_1692_, v_a_1693_, v_a_1694_, lean_box(0));
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1855_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = l_Lean_Doc_joinBlocks(v_a_1847_);
lean_dec(v_a_1847_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1851_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_a_1856_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1846_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1846_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
default: 
{
lean_object* v_container_1864_; lean_object* v_content_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec_ref(v___x_1712_);
v_container_1864_ = lean_ctor_get(v_x_1691_, 0);
lean_inc(v_container_1864_);
v_content_1865_ = lean_ctor_get(v_x_1691_, 1);
lean_inc_ref(v_content_1865_);
lean_dec_ref_known(v_x_1691_, 2);
v___x_1866_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc_ref(v_inst_1689_);
v___x_1867_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed), 8, 3);
lean_closure_set(v___x_1867_, 0, lean_box(0));
lean_closure_set(v___x_1867_, 1, v_inst_1689_);
lean_closure_set(v___x_1867_, 2, v___x_1866_);
lean_inc_ref(v_inst_1690_);
v___x_1868_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1868_, 0, v_inst_1689_);
lean_closure_set(v___x_1868_, 1, v_inst_1690_);
lean_inc(v_a_1694_);
lean_inc_ref(v_a_1693_);
lean_inc(v_a_1692_);
v___x_1869_ = lean_apply_8(v_inst_1690_, v___x_1867_, v___x_1868_, v_container_1864_, v_content_1865_, v_a_1692_, v_a_1693_, v_a_1694_, lean_box(0));
return v___x_1869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed(lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_x_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1870_, v_inst_1871_, v_x_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v_inst_1878_, lean_object* v_inst_1879_, lean_object* v___x_1880_, lean_object* v_item_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; size_t v_sz_1887_; size_t v___x_1888_; lean_object* v___x_2428__overap_1889_; lean_object* v___x_1890_; 
v___x_1886_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1886_, 0, v_inst_1878_);
lean_closure_set(v___x_1886_, 1, v_inst_1879_);
v_sz_1887_ = lean_array_size(v_item_1881_);
v___x_1888_ = ((size_t)0ULL);
v___x_2428__overap_1889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1880_, v___x_1886_, v_sz_1887_, v___x_1888_, v_item_1881_);
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1883_);
lean_inc(v___y_1882_);
v___x_1890_ = lean_apply_4(v___x_2428__overap_1889_, v___y_1882_, v___y_1883_, v___y_1884_, lean_box(0));
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1902_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1902_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1902_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1895_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1896_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1897_ = l_Lean_Doc_joinBlocks(v_a_1891_);
lean_dec(v_a_1891_);
v___x_1898_ = l_Lean_Doc_prefixListLines(v___x_1895_, v___x_1896_, v___x_1897_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1898_);
v___x_1900_ = v___x_1893_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
v_a_1903_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1890_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1890_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1911_, lean_object* v_b_1912_, lean_object* v_inst_1913_, lean_object* v_inst_1914_, lean_object* v_x_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1913_, v_inst_1914_, v_x_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object* v_i_1921_, lean_object* v_b_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_x_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(v_i_1921_, v_b_1922_, v_inst_1923_, v_inst_1924_, v_x_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_a_1926_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1931_, lean_object* v_inst_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1931_, v_inst_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1939_, lean_object* v_inst_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1939_, v_inst_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1947_, lean_object* v_b_1948_, lean_object* v_inst_1949_, lean_object* v_inst_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1949_, v_inst_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1957_, lean_object* v_b_1958_, lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1957_, v_b_1958_, v_inst_1959_, v_inst_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1967_, lean_object* v_inst_1968_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_1969_, 0, lean_box(0));
lean_closure_set(v___x_1969_, 1, lean_box(0));
lean_closure_set(v___x_1969_, 2, v_inst_1967_);
lean_closure_set(v___x_1969_, 3, v_inst_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1970_, lean_object* v_b_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_1974_, 0, lean_box(0));
lean_closure_set(v___x_1974_, 1, lean_box(0));
lean_closure_set(v___x_1974_, 2, v_inst_1972_);
lean_closure_set(v___x_1974_, 3, v_inst_1973_);
return v___x_1974_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = 35;
v___x_1976_ = lean_box_uint32(v___x_1975_);
return v___x_1976_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___f_1978_; 
v___x_1977_ = l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1978_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1978_, 0, v___x_1977_);
return v___f_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_level_1981_, lean_object* v_part_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_Doc_partMarkdown___redArg(v_inst_1979_, v_inst_1980_, v_level_1981_, v_part_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec(v_level_1981_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg(lean_object* v_inst_1988_, lean_object* v_inst_1989_, lean_object* v_level_1990_, lean_object* v_part_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v___x_1996_; lean_object* v_toApplicative_1997_; lean_object* v_toFunctor_1998_; lean_object* v_toSeq_1999_; lean_object* v_toSeqLeft_2000_; lean_object* v_toSeqRight_2001_; lean_object* v___f_2002_; lean_object* v___f_2003_; lean_object* v___f_2004_; lean_object* v___f_2005_; lean_object* v___x_2006_; lean_object* v___f_2007_; lean_object* v___f_2008_; lean_object* v___f_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v_title_2013_; lean_object* v_content_2014_; lean_object* v_subParts_2015_; lean_object* v___x_2016_; size_t v_sz_2017_; size_t v___x_2018_; lean_object* v___x_684__overap_2019_; lean_object* v___x_2020_; 
v___x_1996_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1997_ = lean_ctor_get(v___x_1996_, 0);
v_toFunctor_1998_ = lean_ctor_get(v_toApplicative_1997_, 0);
v_toSeq_1999_ = lean_ctor_get(v_toApplicative_1997_, 2);
v_toSeqLeft_2000_ = lean_ctor_get(v_toApplicative_1997_, 3);
v_toSeqRight_2001_ = lean_ctor_get(v_toApplicative_1997_, 4);
v___f_2002_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2003_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1998_, 2);
v___f_2004_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2004_, 0, v_toFunctor_1998_);
v___f_2005_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2005_, 0, v_toFunctor_1998_);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___f_2004_);
lean_ctor_set(v___x_2006_, 1, v___f_2005_);
lean_inc(v_toSeqRight_2001_);
v___f_2007_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2007_, 0, v_toSeqRight_2001_);
lean_inc(v_toSeqLeft_2000_);
v___f_2008_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2008_, 0, v_toSeqLeft_2000_);
lean_inc(v_toSeq_1999_);
v___f_2009_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2009_, 0, v_toSeq_1999_);
v___x_2010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2006_);
lean_ctor_set(v___x_2010_, 1, v___f_2002_);
lean_ctor_set(v___x_2010_, 2, v___f_2009_);
lean_ctor_set(v___x_2010_, 3, v___f_2008_);
lean_ctor_set(v___x_2010_, 4, v___f_2007_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v___f_2003_);
v___x_2012_ = l_StateRefT_x27_instMonad___redArg(v___x_2011_);
v_title_2013_ = lean_ctor_get(v_part_1991_, 0);
lean_inc_ref(v_title_2013_);
v_content_2014_ = lean_ctor_get(v_part_1991_, 3);
lean_inc_ref(v_content_2014_);
v_subParts_2015_ = lean_ctor_get(v_part_1991_, 4);
lean_inc_ref(v_subParts_2015_);
lean_dec_ref(v_part_1991_);
lean_inc_ref(v_inst_1988_);
v___x_2016_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_2016_, 0, lean_box(0));
lean_closure_set(v___x_2016_, 1, v_inst_1988_);
v_sz_2017_ = lean_array_size(v_title_2013_);
v___x_2018_ = ((size_t)0ULL);
lean_inc_ref(v___x_2012_);
v___x_684__overap_2019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2012_, v___x_2016_, v_sz_2017_, v___x_2018_, v_title_2013_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
lean_inc(v_a_1992_);
v___x_2020_ = lean_apply_4(v___x_684__overap_2019_, v_a_1992_, v_a_1993_, v_a_1994_, lean_box(0));
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2022_; lean_object* v___f_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; size_t v_sz_2035_; lean_object* v___x_687__overap_2036_; lean_object* v___x_2037_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_2023_ = lean_obj_once(&l_Lean_Doc_partMarkdown___redArg___closed__0, &l_Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_partMarkdown___redArg___closed__0);
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2025_ = lean_nat_add(v_level_1990_, v___x_2024_);
lean_inc(v___x_2025_);
v___x_2026_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_2023_, v___x_2025_, v___x_2022_);
v___x_2027_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_2028_ = lean_string_append(v___x_2026_, v___x_2027_);
v___x_2029_ = lean_mk_empty_array_with_capacity(v___x_2024_);
lean_inc_ref_n(v___x_2029_, 2);
v___x_2030_ = lean_array_push(v___x_2029_, v___x_2028_);
v___x_2031_ = lean_array_push(v___x_2029_, v___x_2030_);
v___x_2032_ = l_Array_append___redArg(v___x_2031_, v_a_2021_);
lean_dec(v_a_2021_);
v___x_2033_ = l_Lean_Doc_joinInlines(v___x_2032_);
lean_dec_ref(v___x_2032_);
lean_inc_ref(v_inst_1989_);
lean_inc_ref(v_inst_1988_);
v___x_2034_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_2034_, 0, lean_box(0));
lean_closure_set(v___x_2034_, 1, lean_box(0));
lean_closure_set(v___x_2034_, 2, v_inst_1988_);
lean_closure_set(v___x_2034_, 3, v_inst_1989_);
v_sz_2035_ = lean_array_size(v_content_2014_);
lean_inc_ref(v___x_2012_);
v___x_687__overap_2036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2012_, v___x_2034_, v_sz_2035_, v___x_2018_, v_content_2014_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
lean_inc(v_a_1992_);
v___x_2037_ = lean_apply_4(v___x_687__overap_2036_, v_a_1992_, v_a_1993_, v_a_1994_, lean_box(0));
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2039_; size_t v_sz_2040_; lean_object* v___x_690__overap_2041_; lean_object* v___x_2042_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v___x_2039_ = lean_alloc_closure((void*)(l_Lean_Doc_partMarkdown___redArg___boxed), 8, 3);
lean_closure_set(v___x_2039_, 0, v_inst_1988_);
lean_closure_set(v___x_2039_, 1, v_inst_1989_);
lean_closure_set(v___x_2039_, 2, v___x_2025_);
v_sz_2040_ = lean_array_size(v_subParts_2015_);
v___x_690__overap_2041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2012_, v___x_2039_, v_sz_2040_, v___x_2018_, v_subParts_2015_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
lean_inc(v_a_1992_);
v___x_2042_ = lean_apply_4(v___x_690__overap_2041_, v_a_1992_, v_a_1993_, v_a_1994_, lean_box(0));
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2054_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2054_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2054_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2047_ = lean_array_push(v___x_2029_, v___x_2033_);
v___x_2048_ = l_Array_append___redArg(v___x_2047_, v_a_2038_);
lean_dec(v_a_2038_);
v___x_2049_ = l_Array_append___redArg(v___x_2048_, v_a_2043_);
lean_dec(v_a_2043_);
v___x_2050_ = l_Lean_Doc_joinBlocks(v___x_2049_);
lean_dec_ref(v___x_2049_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2050_);
v___x_2052_ = v___x_2045_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v_a_2038_);
lean_dec_ref(v___x_2033_);
lean_dec_ref(v___x_2029_);
v_a_2055_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2042_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2042_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref(v___x_2033_);
lean_dec_ref(v___x_2029_);
lean_dec(v___x_2025_);
lean_dec_ref(v_subParts_2015_);
lean_dec_ref(v___x_2012_);
lean_dec_ref(v_inst_1989_);
lean_dec_ref(v_inst_1988_);
v_a_2063_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2037_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2037_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec_ref(v_subParts_2015_);
lean_dec_ref(v_content_2014_);
lean_dec_ref(v___x_2012_);
lean_dec_ref(v_inst_1989_);
lean_dec_ref(v_inst_1988_);
v_a_2071_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2020_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2020_);
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
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown(lean_object* v_i_2079_, lean_object* v_b_2080_, lean_object* v_p_2081_, lean_object* v_inst_2082_, lean_object* v_inst_2083_, lean_object* v_level_2084_, lean_object* v_part_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2082_, v_inst_2083_, v_level_2084_, v_part_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___boxed(lean_object* v_i_2091_, lean_object* v_b_2092_, lean_object* v_p_2093_, lean_object* v_inst_2094_, lean_object* v_inst_2095_, lean_object* v_level_2096_, lean_object* v_part_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_Doc_partMarkdown(v_i_2091_, v_b_2092_, v_p_2093_, v_inst_2094_, v_inst_2095_, v_level_2096_, v_part_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec(v_level_2096_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_part_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2103_, v_inst_2104_, v___x_2110_, v_part_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_part_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_2112_, v_inst_2113_, v_part_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_2120_, lean_object* v_inst_2121_){
_start:
{
lean_object* v___f_2122_; 
v___f_2122_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2122_, 0, v_inst_2120_);
lean_closure_set(v___f_2122_, 1, v_inst_2121_);
return v___f_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_2123_, lean_object* v_b_2124_, lean_object* v_p_2125_, lean_object* v_inst_2126_, lean_object* v_inst_2127_){
_start:
{
lean_object* v___f_2128_; 
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2128_, 0, v_inst_2126_);
lean_closure_set(v___f_2128_, 1, v_inst_2127_);
return v___f_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg(lean_object* v_inst_2129_, lean_object* v_f_2130_, lean_object* v_go_2131_, lean_object* v_val_2132_, lean_object* v_content_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v___x_2138_; lean_object* v_toApplicative_2139_; lean_object* v_toFunctor_2140_; lean_object* v_toSeq_2141_; lean_object* v_toSeqLeft_2142_; lean_object* v_toSeqRight_2143_; lean_object* v___f_2144_; lean_object* v___f_2145_; lean_object* v___f_2146_; lean_object* v___f_2147_; lean_object* v___x_2148_; lean_object* v___f_2149_; lean_object* v___f_2150_; lean_object* v___f_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2138_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2139_ = lean_ctor_get(v___x_2138_, 0);
v_toFunctor_2140_ = lean_ctor_get(v_toApplicative_2139_, 0);
v_toSeq_2141_ = lean_ctor_get(v_toApplicative_2139_, 2);
v_toSeqLeft_2142_ = lean_ctor_get(v_toApplicative_2139_, 3);
v_toSeqRight_2143_ = lean_ctor_get(v_toApplicative_2139_, 4);
v___f_2144_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2145_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2140_, 2);
v___f_2146_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2146_, 0, v_toFunctor_2140_);
v___f_2147_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2147_, 0, v_toFunctor_2140_);
v___x_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___f_2146_);
lean_ctor_set(v___x_2148_, 1, v___f_2147_);
lean_inc(v_toSeqRight_2143_);
v___f_2149_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2149_, 0, v_toSeqRight_2143_);
lean_inc(v_toSeqLeft_2142_);
v___f_2150_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2150_, 0, v_toSeqLeft_2142_);
lean_inc(v_toSeq_2141_);
v___f_2151_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2151_, 0, v_toSeq_2141_);
v___x_2152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2148_);
lean_ctor_set(v___x_2152_, 1, v___f_2144_);
lean_ctor_set(v___x_2152_, 2, v___f_2151_);
lean_ctor_set(v___x_2152_, 3, v___f_2150_);
lean_ctor_set(v___x_2152_, 4, v___f_2149_);
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
lean_ctor_set(v___x_2153_, 1, v___f_2145_);
v___x_2154_ = l_StateRefT_x27_instMonad___redArg(v___x_2153_);
v___x_2155_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2132_, v_inst_2129_);
if (lean_obj_tag(v___x_2155_) == 0)
{
size_t v_sz_2156_; size_t v___x_2157_; lean_object* v___x_236__overap_2158_; lean_object* v___x_2159_; 
lean_dec_ref(v_f_2130_);
v_sz_2156_ = lean_array_size(v_content_2133_);
v___x_2157_ = ((size_t)0ULL);
v___x_236__overap_2158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2154_, v_go_2131_, v_sz_2156_, v___x_2157_, v_content_2133_);
lean_inc(v_a_2136_);
lean_inc_ref(v_a_2135_);
lean_inc(v_a_2134_);
v___x_2159_ = lean_apply_4(v___x_236__overap_2158_, v_a_2134_, v_a_2135_, v_a_2136_, lean_box(0));
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2168_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2164_ = l_Lean_Doc_joinInlines(v_a_2160_);
lean_dec(v_a_2160_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2164_);
v___x_2166_ = v___x_2162_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_a_2169_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2159_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2159_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v_val_2177_; lean_object* v___x_2178_; 
lean_dec_ref(v___x_2154_);
v_val_2177_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_val_2177_);
lean_dec_ref_known(v___x_2155_, 1);
lean_inc(v_a_2136_);
lean_inc_ref(v_a_2135_);
lean_inc(v_a_2134_);
v___x_2178_ = lean_apply_7(v_f_2130_, v_go_2131_, v_val_2177_, v_content_2133_, v_a_2134_, v_a_2135_, v_a_2136_, lean_box(0));
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg___boxed(lean_object* v_inst_2179_, lean_object* v_f_2180_, lean_object* v_go_2181_, lean_object* v_val_2182_, lean_object* v_content_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2179_, v_f_2180_, v_go_2181_, v_val_2182_, v_content_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec(v_val_2182_);
lean_dec(v_inst_2179_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer(lean_object* v_00_u03b1_2189_, lean_object* v_inst_2190_, lean_object* v_f_2191_, lean_object* v_go_2192_, lean_object* v_val_2193_, lean_object* v_content_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2190_, v_f_2191_, v_go_2192_, v_val_2193_, v_content_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___boxed(lean_object* v_00_u03b1_2200_, lean_object* v_inst_2201_, lean_object* v_f_2202_, lean_object* v_go_2203_, lean_object* v_val_2204_, lean_object* v_content_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_Doc_mkInlineMdRenderer(v_00_u03b1_2200_, v_inst_2201_, v_f_2202_, v_go_2203_, v_val_2204_, v_content_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
lean_dec(v_a_2206_);
lean_dec(v_val_2204_);
lean_dec(v_inst_2201_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg(lean_object* v_inst_2211_, lean_object* v_f_2212_, lean_object* v_goI_2213_, lean_object* v_goB_2214_, lean_object* v_val_2215_, lean_object* v_content_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v___x_2221_; lean_object* v_toApplicative_2222_; lean_object* v_toFunctor_2223_; lean_object* v_toSeq_2224_; lean_object* v_toSeqLeft_2225_; lean_object* v_toSeqRight_2226_; lean_object* v___f_2227_; lean_object* v___f_2228_; lean_object* v___f_2229_; lean_object* v___f_2230_; lean_object* v___x_2231_; lean_object* v___f_2232_; lean_object* v___f_2233_; lean_object* v___f_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2221_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2222_ = lean_ctor_get(v___x_2221_, 0);
v_toFunctor_2223_ = lean_ctor_get(v_toApplicative_2222_, 0);
v_toSeq_2224_ = lean_ctor_get(v_toApplicative_2222_, 2);
v_toSeqLeft_2225_ = lean_ctor_get(v_toApplicative_2222_, 3);
v_toSeqRight_2226_ = lean_ctor_get(v_toApplicative_2222_, 4);
v___f_2227_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2228_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2223_, 2);
v___f_2229_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2229_, 0, v_toFunctor_2223_);
v___f_2230_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2230_, 0, v_toFunctor_2223_);
v___x_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___f_2229_);
lean_ctor_set(v___x_2231_, 1, v___f_2230_);
lean_inc(v_toSeqRight_2226_);
v___f_2232_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2232_, 0, v_toSeqRight_2226_);
lean_inc(v_toSeqLeft_2225_);
v___f_2233_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2233_, 0, v_toSeqLeft_2225_);
lean_inc(v_toSeq_2224_);
v___f_2234_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2234_, 0, v_toSeq_2224_);
v___x_2235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2231_);
lean_ctor_set(v___x_2235_, 1, v___f_2227_);
lean_ctor_set(v___x_2235_, 2, v___f_2234_);
lean_ctor_set(v___x_2235_, 3, v___f_2233_);
lean_ctor_set(v___x_2235_, 4, v___f_2232_);
v___x_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
lean_ctor_set(v___x_2236_, 1, v___f_2228_);
v___x_2237_ = l_StateRefT_x27_instMonad___redArg(v___x_2236_);
v___x_2238_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2215_, v_inst_2211_);
if (lean_obj_tag(v___x_2238_) == 0)
{
size_t v_sz_2239_; size_t v___x_2240_; lean_object* v___x_236__overap_2241_; lean_object* v___x_2242_; 
lean_dec_ref(v_goI_2213_);
lean_dec_ref(v_f_2212_);
v_sz_2239_ = lean_array_size(v_content_2216_);
v___x_2240_ = ((size_t)0ULL);
v___x_236__overap_2241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2237_, v_goB_2214_, v_sz_2239_, v___x_2240_, v_content_2216_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc(v_a_2217_);
v___x_2242_ = lean_apply_4(v___x_236__overap_2241_, v_a_2217_, v_a_2218_, v_a_2219_, lean_box(0));
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2251_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2251_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2251_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2247_ = l_Lean_Doc_joinBlocks(v_a_2243_);
lean_dec(v_a_2243_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2247_);
v___x_2249_ = v___x_2245_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
v_a_2252_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2242_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2242_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_object* v_val_2260_; lean_object* v___x_2261_; 
lean_dec_ref(v___x_2237_);
v_val_2260_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_val_2260_);
lean_dec_ref_known(v___x_2238_, 1);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc(v_a_2217_);
v___x_2261_ = lean_apply_8(v_f_2212_, v_goI_2213_, v_goB_2214_, v_val_2260_, v_content_2216_, v_a_2217_, v_a_2218_, v_a_2219_, lean_box(0));
return v___x_2261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg___boxed(lean_object* v_inst_2262_, lean_object* v_f_2263_, lean_object* v_goI_2264_, lean_object* v_goB_2265_, lean_object* v_val_2266_, lean_object* v_content_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2262_, v_f_2263_, v_goI_2264_, v_goB_2265_, v_val_2266_, v_content_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec(v_val_2266_);
lean_dec(v_inst_2262_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer(lean_object* v_00_u03b1_2273_, lean_object* v_inst_2274_, lean_object* v_f_2275_, lean_object* v_goI_2276_, lean_object* v_goB_2277_, lean_object* v_val_2278_, lean_object* v_content_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2274_, v_f_2275_, v_goI_2276_, v_goB_2277_, v_val_2278_, v_content_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___boxed(lean_object* v_00_u03b1_2285_, lean_object* v_inst_2286_, lean_object* v_f_2287_, lean_object* v_goI_2288_, lean_object* v_goB_2289_, lean_object* v_val_2290_, lean_object* v_content_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Doc_mkBlockMdRenderer(v_00_u03b1_2285_, v_inst_2286_, v_f_2287_, v_goI_2288_, v_goB_2289_, v_val_2290_, v_content_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec(v_val_2290_);
lean_dec(v_inst_2286_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(lean_object* v_as_2301_, size_t v_i_2302_, size_t v_stop_2303_, lean_object* v_b_2304_){
_start:
{
uint8_t v___x_2305_; 
v___x_2305_ = lean_usize_dec_eq(v_i_2302_, v_stop_2303_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; lean_object* v_fst_2307_; lean_object* v_snd_2308_; lean_object* v___x_2309_; size_t v___x_2310_; size_t v___x_2311_; 
v___x_2306_ = lean_array_uget_borrowed(v_as_2301_, v_i_2302_);
v_fst_2307_ = lean_ctor_get(v___x_2306_, 0);
v_snd_2308_ = lean_ctor_get(v___x_2306_, 1);
lean_inc(v_snd_2308_);
lean_inc(v_fst_2307_);
v___x_2309_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2307_, v_snd_2308_, v_b_2304_);
v___x_2310_ = ((size_t)1ULL);
v___x_2311_ = lean_usize_add(v_i_2302_, v___x_2310_);
v_i_2302_ = v___x_2311_;
v_b_2304_ = v___x_2309_;
goto _start;
}
else
{
return v_b_2304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0___boxed(lean_object* v_as_2313_, lean_object* v_i_2314_, lean_object* v_stop_2315_, lean_object* v_b_2316_){
_start:
{
size_t v_i_boxed_2317_; size_t v_stop_boxed_2318_; lean_object* v_res_2319_; 
v_i_boxed_2317_ = lean_unbox_usize(v_i_2314_);
lean_dec(v_i_2314_);
v_stop_boxed_2318_ = lean_unbox_usize(v_stop_2315_);
lean_dec(v_stop_2315_);
v_res_2319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v_as_2313_, v_i_boxed_2317_, v_stop_boxed_2318_, v_b_2316_);
lean_dec_ref(v_as_2313_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(lean_object* v_as_2320_, size_t v_i_2321_, size_t v_stop_2322_, lean_object* v_b_2323_){
_start:
{
lean_object* v___y_2325_; uint8_t v___x_2329_; 
v___x_2329_ = lean_usize_dec_eq(v_i_2321_, v_stop_2322_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2330_ = lean_array_uget_borrowed(v_as_2320_, v_i_2321_);
v___x_2331_ = lean_unsigned_to_nat(0u);
v___x_2332_ = lean_array_get_size(v___x_2330_);
v___x_2333_ = lean_nat_dec_lt(v___x_2331_, v___x_2332_);
if (v___x_2333_ == 0)
{
v___y_2325_ = v_b_2323_;
goto v___jp_2324_;
}
else
{
size_t v___x_2334_; size_t v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = lean_usize_of_nat(v___x_2332_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2330_, v___x_2334_, v___x_2335_, v_b_2323_);
v___y_2325_ = v___x_2336_;
goto v___jp_2324_;
}
}
else
{
return v_b_2323_;
}
v___jp_2324_:
{
size_t v___x_2326_; size_t v___x_2327_; 
v___x_2326_ = ((size_t)1ULL);
v___x_2327_ = lean_usize_add(v_i_2321_, v___x_2326_);
v_i_2321_ = v___x_2327_;
v_b_2323_ = v___y_2325_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1___boxed(lean_object* v_as_2337_, lean_object* v_i_2338_, lean_object* v_stop_2339_, lean_object* v_b_2340_){
_start:
{
size_t v_i_boxed_2341_; size_t v_stop_boxed_2342_; lean_object* v_res_2343_; 
v_i_boxed_2341_ = lean_unbox_usize(v_i_2338_);
lean_dec(v_i_2338_);
v_stop_boxed_2342_ = lean_unbox_usize(v_stop_2339_);
lean_dec(v_stop_2339_);
v_res_2343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_as_2337_, v_i_boxed_2341_, v_stop_boxed_2342_, v_b_2340_);
lean_dec_ref(v_as_2337_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(lean_object* v_init_2344_, lean_object* v_es_2345_){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = lean_array_get_size(v_es_2345_);
v___x_2348_ = lean_nat_dec_lt(v___x_2346_, v___x_2347_);
if (v___x_2348_ == 0)
{
return v_init_2344_;
}
else
{
size_t v___x_2349_; size_t v___x_2350_; lean_object* v___x_2351_; 
v___x_2349_ = ((size_t)0ULL);
v___x_2350_ = lean_usize_of_nat(v___x_2347_);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2345_, v___x_2349_, v___x_2350_, v_init_2344_);
return v___x_2351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries___boxed(lean_object* v_init_2352_, lean_object* v_es_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v_init_2352_, v_es_2353_);
lean_dec_ref(v_es_2353_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_2355_, lean_object* v_x_2356_){
_start:
{
if (lean_obj_tag(v_x_2356_) == 0)
{
lean_object* v_k_2357_; lean_object* v_v_2358_; lean_object* v_l_2359_; lean_object* v_r_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v_k_2357_ = lean_ctor_get(v_x_2356_, 1);
v_v_2358_ = lean_ctor_get(v_x_2356_, 2);
v_l_2359_ = lean_ctor_get(v_x_2356_, 3);
v_r_2360_ = lean_ctor_get(v_x_2356_, 4);
v___x_2361_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2355_, v_l_2359_);
lean_inc(v_v_2358_);
lean_inc(v_k_2357_);
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v_k_2357_);
lean_ctor_set(v___x_2362_, 1, v_v_2358_);
v___x_2363_ = lean_array_push(v___x_2361_, v___x_2362_);
v_init_2355_ = v___x_2363_;
v_x_2356_ = v_r_2360_;
goto _start;
}
else
{
return v_init_2355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_2365_, lean_object* v_x_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2365_, v_x_2366_);
lean_dec(v_x_2366_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2370_){
_start:
{
lean_object* v_current_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v_current_2371_ = lean_ctor_get(v_s_2370_, 1);
v___x_2372_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2373_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2372_, v_current_2371_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_s_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_s_2374_);
lean_dec_ref(v_s_2374_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2376_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_box(0);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2378_);
lean_dec_ref(v_x_2378_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2380_, lean_object* v_s_2381_){
_start:
{
lean_object* v_current_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_current_2382_ = lean_ctor_get(v_s_2381_, 1);
v___x_2383_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2384_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2383_, v_current_2382_);
lean_inc_ref_n(v___x_2384_, 2);
v___x_2385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
lean_ctor_set(v___x_2385_, 2, v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2386_, lean_object* v_s_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2386_, v_s_2387_);
lean_dec_ref(v_s_2387_);
lean_dec_ref(v_x_2386_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2389_, lean_object* v_x_2390_){
_start:
{
lean_object* v_fst_2391_; lean_object* v_snd_2392_; lean_object* v_imported_2393_; lean_object* v_current_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2402_; 
v_fst_2391_ = lean_ctor_get(v_x_2390_, 0);
lean_inc(v_fst_2391_);
v_snd_2392_ = lean_ctor_get(v_x_2390_, 1);
lean_inc(v_snd_2392_);
lean_dec_ref(v_x_2390_);
v_imported_2393_ = lean_ctor_get(v_s_2389_, 0);
v_current_2394_ = lean_ctor_get(v_s_2389_, 1);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_s_2389_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2396_ = v_s_2389_;
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_current_2394_);
lean_inc(v_imported_2393_);
lean_dec(v_s_2389_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2398_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2391_, v_snd_2392_, v_current_2394_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 1, v___x_2398_);
v___x_2400_ = v___x_2396_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_imported_2393_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2403_, lean_object* v_es_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_inc(v___x_2403_);
v___x_2407_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v___x_2403_, v_es_2404_);
v___x_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
lean_ctor_set(v___x_2408_, 1, v___x_2403_);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2410_, lean_object* v_es_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2410_, v_es_2411_, v___y_2412_);
lean_dec_ref(v___y_2412_);
lean_dec_ref(v_es_2411_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2418_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2451_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_a_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_();
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(lean_object* v_init_2454_, lean_object* v_t_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2454_, v_t_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_2457_, lean_object* v_t_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(v_init_2457_, v_t_2458_);
lean_dec(v_t_2458_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_));
v___x_2480_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2____boxed(lean_object* v_a_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_();
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = lean_box(1);
v___x_2485_ = lean_st_mk_ref(v___x_2484_);
v___x_2486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2____boxed(lean_object* v_a_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_();
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = lean_box(1);
v___x_2491_ = lean_st_mk_ref(v___x_2490_);
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2____boxed(lean_object* v_a_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_();
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer(lean_object* v_type_2495_, lean_object* v_r_2496_){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2498_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2499_ = lean_st_ref_take(v___x_2498_);
v___x_2500_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2495_, v_r_2496_, v___x_2499_);
v___x_2501_ = lean_st_ref_put(v___x_2498_, v___x_2500_);
v___x_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer___boxed(lean_object* v_type_2503_, lean_object* v_r_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_Doc_addBuiltinInlineMdRenderer(v_type_2503_, v_r_2504_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer(lean_object* v_type_2507_, lean_object* v_r_2508_){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2510_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2511_ = lean_st_ref_take(v___x_2510_);
v___x_2512_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2507_, v_r_2508_, v___x_2511_);
v___x_2513_ = lean_st_ref_put(v___x_2510_, v___x_2512_);
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer___boxed(lean_object* v_type_2515_, lean_object* v_r_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_Doc_addBuiltinBlockMdRenderer(v_type_2515_, v_r_2516_);
return v_res_2518_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2519_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2523_ = lean_unsigned_to_nat(0u);
v___x_2524_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
lean_ctor_set(v___x_2524_, 2, v___x_2523_);
lean_ctor_set(v___x_2524_, 3, v___x_2523_);
lean_ctor_set(v___x_2524_, 4, v___x_2522_);
lean_ctor_set(v___x_2524_, 5, v___x_2522_);
lean_ctor_set(v___x_2524_, 6, v___x_2522_);
lean_ctor_set(v___x_2524_, 7, v___x_2522_);
lean_ctor_set(v___x_2524_, 8, v___x_2522_);
lean_ctor_set(v___x_2524_, 9, v___x_2522_);
lean_ctor_set(v___x_2524_, 10, v___x_2522_);
return v___x_2524_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = lean_unsigned_to_nat(32u);
v___x_2526_ = lean_mk_empty_array_with_capacity(v___x_2525_);
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2528_ = ((size_t)5ULL);
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = lean_unsigned_to_nat(32u);
v___x_2531_ = lean_mk_empty_array_with_capacity(v___x_2530_);
v___x_2532_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_2533_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v___x_2531_);
lean_ctor_set(v___x_2533_, 2, v___x_2529_);
lean_ctor_set(v___x_2533_, 3, v___x_2529_);
lean_ctor_set_usize(v___x_2533_, 4, v___x_2528_);
return v___x_2533_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2534_ = lean_box(1);
v___x_2535_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_2536_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v___x_2535_);
lean_ctor_set(v___x_2537_, 2, v___x_2534_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___x_2542_; lean_object* v_toCold_2543_; lean_object* v_env_2544_; lean_object* v_options_2545_; uint8_t v___x_2546_; lean_object* v_env_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2542_ = lean_st_ref_get(v___y_2540_);
v_toCold_2543_ = lean_ctor_get(v___y_2539_, 0);
v_env_2544_ = lean_ctor_get(v___x_2542_, 0);
lean_inc_ref(v_env_2544_);
lean_dec(v___x_2542_);
v_options_2545_ = lean_ctor_get(v_toCold_2543_, 2);
v___x_2546_ = 0;
v_env_2547_ = l_Lean_Environment_setRecordingDeps(v_env_2544_, v___x_2546_);
v___x_2548_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_2549_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_2545_);
v___x_2550_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2550_, 0, v_env_2547_);
lean_ctor_set(v___x_2550_, 1, v___x_2548_);
lean_ctor_set(v___x_2550_, 2, v___x_2549_);
lean_ctor_set(v___x_2550_, 3, v_options_2545_);
v___x_2551_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
lean_ctor_set(v___x_2551_, 1, v_msgData_2538_);
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_ref_2562_; lean_object* v___x_2563_; lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2572_; 
v_ref_2562_ = lean_ctor_get(v___y_2559_, 2);
v___x_2563_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_2558_, v___y_2559_, v___y_2560_);
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2572_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2572_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v___x_2570_; 
lean_inc(v_ref_2562_);
v___x_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2568_, 0, v_ref_2562_);
lean_ctor_set(v___x_2568_, 1, v_a_2564_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 1);
lean_ctor_set(v___x_2566_, 0, v___x_2568_);
v___x_2570_ = v___x_2566_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(lean_object* v_x_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
if (lean_obj_tag(v_x_2578_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v_a_2582_ = lean_ctor_get(v_x_2578_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v_x_2578_, 1);
v___x_2583_ = l_Lean_stringToMessageData(v_a_2582_);
v___x_2584_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v___x_2583_, v___y_2579_, v___y_2580_);
return v___x_2584_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
v_a_2585_ = lean_ctor_get(v_x_2578_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_x_2578_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v_x_2578_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v_x_2578_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 0);
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2597_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_box(0);
v___x_2599_ = l_Lean_Elab_abortCommandExceptionId;
v___x_2600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v___x_2598_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(lean_object* v_constName_2606_, uint8_t v_checkMeta_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2611_; lean_object* v_env_2612_; uint8_t v___x_2613_; 
v___x_2611_ = lean_st_ref_get(v___y_2609_);
v_env_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc_ref(v_env_2612_);
lean_dec(v___x_2611_);
lean_inc(v_constName_2606_);
v___x_2613_ = lean_has_compile_error(v_env_2612_, v_constName_2606_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; lean_object* v_env_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2614_ = lean_st_ref_get(v___y_2609_);
v_env_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc_ref(v_env_2615_);
lean_dec(v___x_2614_);
v___x_2616_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2608_);
v___x_2617_ = l_Lean_Environment_evalConst___redArg(v_env_2615_, v___x_2616_, v_constName_2606_, v_checkMeta_2607_);
lean_dec(v_constName_2606_);
lean_dec_ref(v___x_2616_);
lean_dec_ref(v_env_2615_);
v___x_2618_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2617_, v___y_2608_, v___y_2609_);
return v___x_2618_;
}
else
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v___x_2620_; lean_object* v_env_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec_ref_known(v___x_2619_, 1);
v___x_2620_ = lean_st_ref_get(v___y_2609_);
v_env_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc_ref(v_env_2621_);
lean_dec(v___x_2620_);
v___x_2622_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2608_);
v___x_2623_ = l_Lean_Environment_evalConst___redArg(v_env_2621_, v___x_2622_, v_constName_2606_, v_checkMeta_2607_);
lean_dec(v_constName_2606_);
lean_dec_ref(v___x_2622_);
lean_dec_ref(v_env_2621_);
v___x_2624_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2623_, v___y_2608_, v___y_2609_);
return v___x_2624_;
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_constName_2606_);
v_a_2625_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2619_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2619_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg___boxed(lean_object* v_constName_2633_, lean_object* v_checkMeta_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
uint8_t v_checkMeta_boxed_2638_; lean_object* v_res_2639_; 
v_checkMeta_boxed_2638_ = lean_unbox(v_checkMeta_2634_);
v_res_2639_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2633_, v_checkMeta_boxed_2638_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(lean_object* v_type_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v_val_2647_; lean_object* v_env_2667_; lean_object* v___x_2668_; lean_object* v_toEnvExtension_2669_; lean_object* v_asyncMode_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v_imported_2674_; lean_object* v_current_2675_; lean_object* v___x_2676_; 
v___x_2644_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2645_ = lean_st_ref_get(v_a_2642_);
v_env_2667_ = lean_ctor_get(v___x_2645_, 0);
lean_inc_ref(v_env_2667_);
lean_dec(v___x_2645_);
v___x_2668_ = l_Lean_Doc_docInlineMdExt;
v_toEnvExtension_2669_ = lean_ctor_get(v___x_2668_, 0);
v_asyncMode_2670_ = lean_ctor_get(v_toEnvExtension_2669_, 2);
v___x_2671_ = lean_box(0);
v___x_2672_ = 0;
v___x_2673_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2644_, v___x_2668_, v_env_2667_, v_asyncMode_2670_, v___x_2671_, v___x_2672_);
v_imported_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_imported_2674_);
v_current_2675_ = lean_ctor_get(v___x_2673_, 1);
lean_inc(v_current_2675_);
lean_dec(v___x_2673_);
v___x_2676_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2675_, v_type_2640_);
lean_dec(v_current_2675_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2674_, v_type_2640_);
lean_dec(v_imported_2674_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2678_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2679_ = lean_st_ref_get(v___x_2678_);
v___x_2680_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2679_, v_type_2640_);
lean_dec(v___x_2679_);
v___x_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
return v___x_2681_;
}
else
{
lean_object* v_val_2682_; 
v_val_2682_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_val_2682_);
lean_dec_ref_known(v___x_2677_, 1);
v_val_2647_ = v_val_2682_;
goto v___jp_2646_;
}
}
else
{
lean_object* v_val_2683_; 
lean_dec(v_imported_2674_);
v_val_2683_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_val_2683_);
lean_dec_ref_known(v___x_2676_, 1);
v_val_2647_ = v_val_2683_;
goto v___jp_2646_;
}
v___jp_2646_:
{
uint8_t v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = 1;
v___x_2649_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2647_, v___x_2648_, v_a_2641_, v_a_2642_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2658_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2658_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2658_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v___x_2656_; 
v___x_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2654_, 0, v_a_2650_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2654_);
v___x_2656_ = v___x_2652_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_a_2659_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2649_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2649_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe___boxed(lean_object* v_type_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v_type_2684_, v_a_2685_, v_a_2686_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_type_2684_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(v_00_u03b1_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(lean_object* v_00_u03b1_2699_, lean_object* v_constName_2700_, uint8_t v_checkMeta_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2700_, v_checkMeta_2701_, v___y_2702_, v___y_2703_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___boxed(lean_object* v_00_u03b1_2706_, lean_object* v_constName_2707_, lean_object* v_checkMeta_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
uint8_t v_checkMeta_boxed_2712_; lean_object* v_res_2713_; 
v_checkMeta_boxed_2712_ = lean_unbox(v_checkMeta_2708_);
v_res_2713_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(v_00_u03b1_2706_, v_constName_2707_, v_checkMeta_boxed_2712_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_2714_, lean_object* v_x_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2715_, v___y_2716_, v___y_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(v_00_u03b1_2720_, v_x_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2726_, lean_object* v_msg_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2727_, v___y_2728_, v___y_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2732_, lean_object* v_msg_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_2732_, v_msg_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(lean_object* v_typeName_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v_val_2745_; lean_object* v_env_2765_; lean_object* v___x_2766_; lean_object* v_toEnvExtension_2767_; lean_object* v_asyncMode_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; lean_object* v___x_2771_; lean_object* v_imported_2772_; lean_object* v_current_2773_; lean_object* v___x_2774_; 
v___x_2742_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2743_ = lean_st_ref_get(v_a_2740_);
v_env_2765_ = lean_ctor_get(v___x_2743_, 0);
lean_inc_ref(v_env_2765_);
lean_dec(v___x_2743_);
v___x_2766_ = l_Lean_Doc_docBlockMdExt;
v_toEnvExtension_2767_ = lean_ctor_get(v___x_2766_, 0);
v_asyncMode_2768_ = lean_ctor_get(v_toEnvExtension_2767_, 2);
v___x_2769_ = lean_box(0);
v___x_2770_ = 0;
v___x_2771_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2742_, v___x_2766_, v_env_2765_, v_asyncMode_2768_, v___x_2769_, v___x_2770_);
v_imported_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_imported_2772_);
v_current_2773_ = lean_ctor_get(v___x_2771_, 1);
lean_inc(v_current_2773_);
lean_dec(v___x_2771_);
v___x_2774_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2773_, v_typeName_2738_);
lean_dec(v_current_2773_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2772_, v_typeName_2738_);
lean_dec(v_imported_2772_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2776_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2777_ = lean_st_ref_get(v___x_2776_);
v___x_2778_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2777_, v_typeName_2738_);
lean_dec(v___x_2777_);
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
return v___x_2779_;
}
else
{
lean_object* v_val_2780_; 
v_val_2780_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_val_2780_);
lean_dec_ref_known(v___x_2775_, 1);
v_val_2745_ = v_val_2780_;
goto v___jp_2744_;
}
}
else
{
lean_object* v_val_2781_; 
lean_dec(v_imported_2772_);
v_val_2781_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_val_2781_);
lean_dec_ref_known(v___x_2774_, 1);
v_val_2745_ = v_val_2781_;
goto v___jp_2744_;
}
v___jp_2744_:
{
uint8_t v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = 1;
v___x_2747_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2745_, v___x_2746_, v_a_2739_, v_a_2740_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2756_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2756_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2756_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; lean_object* v___x_2754_; 
v___x_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2752_, 0, v_a_2748_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2752_);
v___x_2754_ = v___x_2750_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
v_a_2757_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2747_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2747_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe___boxed(lean_object* v_typeName_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v_typeName_2782_, v_a_2783_, v_a_2784_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_typeName_2782_);
return v_res_2786_;
}
}
static lean_object* _init_l_Lean_Doc_mdRendererHeartbeats(void){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_unsigned_to_nat(200000u);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg(lean_object* v_x_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v___x_2793_; lean_object* v_toCold_2794_; lean_object* v_currRecDepth_2795_; lean_object* v_ref_2796_; uint16_t v_optionFlags_2797_; uint8_t v_suppressElabErrors_2798_; uint8_t v_checkDeprecated_2799_; uint8_t v_isRecordingDeps_2800_; lean_object* v_fileName_2801_; lean_object* v_fileMap_2802_; lean_object* v_options_2803_; lean_object* v_maxRecDepth_2804_; lean_object* v_currNamespace_2805_; lean_object* v_openDecls_2806_; lean_object* v_quotContext_2807_; lean_object* v_currMacroScope_2808_; lean_object* v_cancelTk_x3f_2809_; lean_object* v_inheritedTraceOptions_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2793_ = lean_io_get_num_heartbeats();
v_toCold_2794_ = lean_ctor_get(v_a_2790_, 0);
v_currRecDepth_2795_ = lean_ctor_get(v_a_2790_, 1);
v_ref_2796_ = lean_ctor_get(v_a_2790_, 2);
v_optionFlags_2797_ = lean_ctor_get_uint16(v_a_2790_, sizeof(void*)*3);
v_suppressElabErrors_2798_ = lean_ctor_get_uint8(v_a_2790_, sizeof(void*)*3 + 2);
v_checkDeprecated_2799_ = lean_ctor_get_uint8(v_a_2790_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2800_ = lean_ctor_get_uint8(v_a_2790_, sizeof(void*)*3 + 4);
v_fileName_2801_ = lean_ctor_get(v_toCold_2794_, 0);
v_fileMap_2802_ = lean_ctor_get(v_toCold_2794_, 1);
v_options_2803_ = lean_ctor_get(v_toCold_2794_, 2);
v_maxRecDepth_2804_ = lean_ctor_get(v_toCold_2794_, 3);
v_currNamespace_2805_ = lean_ctor_get(v_toCold_2794_, 4);
v_openDecls_2806_ = lean_ctor_get(v_toCold_2794_, 5);
v_quotContext_2807_ = lean_ctor_get(v_toCold_2794_, 8);
v_currMacroScope_2808_ = lean_ctor_get(v_toCold_2794_, 9);
v_cancelTk_x3f_2809_ = lean_ctor_get(v_toCold_2794_, 10);
v_inheritedTraceOptions_2810_ = lean_ctor_get(v_toCold_2794_, 11);
v___x_2811_ = lean_unsigned_to_nat(200000u);
lean_inc_ref(v_inheritedTraceOptions_2810_);
lean_inc(v_cancelTk_x3f_2809_);
lean_inc(v_currMacroScope_2808_);
lean_inc(v_quotContext_2807_);
lean_inc(v_openDecls_2806_);
lean_inc(v_currNamespace_2805_);
lean_inc(v_maxRecDepth_2804_);
lean_inc_ref(v_options_2803_);
lean_inc_ref(v_fileMap_2802_);
lean_inc_ref(v_fileName_2801_);
v___x_2812_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2812_, 0, v_fileName_2801_);
lean_ctor_set(v___x_2812_, 1, v_fileMap_2802_);
lean_ctor_set(v___x_2812_, 2, v_options_2803_);
lean_ctor_set(v___x_2812_, 3, v_maxRecDepth_2804_);
lean_ctor_set(v___x_2812_, 4, v_currNamespace_2805_);
lean_ctor_set(v___x_2812_, 5, v_openDecls_2806_);
lean_ctor_set(v___x_2812_, 6, v___x_2793_);
lean_ctor_set(v___x_2812_, 7, v___x_2811_);
lean_ctor_set(v___x_2812_, 8, v_quotContext_2807_);
lean_ctor_set(v___x_2812_, 9, v_currMacroScope_2808_);
lean_ctor_set(v___x_2812_, 10, v_cancelTk_x3f_2809_);
lean_ctor_set(v___x_2812_, 11, v_inheritedTraceOptions_2810_);
lean_inc(v_ref_2796_);
lean_inc(v_currRecDepth_2795_);
v___x_2813_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
lean_ctor_set(v___x_2813_, 1, v_currRecDepth_2795_);
lean_ctor_set(v___x_2813_, 2, v_ref_2796_);
lean_ctor_set_uint16(v___x_2813_, sizeof(void*)*3, v_optionFlags_2797_);
lean_ctor_set_uint8(v___x_2813_, sizeof(void*)*3 + 2, v_suppressElabErrors_2798_);
lean_ctor_set_uint8(v___x_2813_, sizeof(void*)*3 + 3, v_checkDeprecated_2799_);
lean_ctor_set_uint8(v___x_2813_, sizeof(void*)*3 + 4, v_isRecordingDeps_2800_);
lean_inc(v_a_2791_);
lean_inc(v_a_2789_);
v___x_2814_ = lean_apply_4(v_x_2788_, v_a_2789_, v___x_2813_, v_a_2791_, lean_box(0));
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg___boxed(lean_object* v_x_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget(lean_object* v_00_u03b1_2821_, lean_object* v_x_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___boxed(lean_object* v_00_u03b1_2828_, lean_object* v_x_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_Doc_withMdRendererBudget(v_00_u03b1_2828_, v_x_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback(lean_object* v_fallback_2835_, lean_object* v_act_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = lean_st_ref_get(v_a_2837_);
v___x_2842_ = l_Lean_Doc_withMdRendererBudget___redArg(v_act_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_dec(v___x_2841_);
lean_dec_ref(v_fallback_2835_);
return v___x_2842_;
}
else
{
lean_object* v_a_2843_; uint8_t v___x_2844_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v___x_2844_ = l_Lean_Exception_isInterrupt(v_a_2843_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_dec_ref_known(v___x_2842_, 1);
v___x_2845_ = lean_st_ref_swap(v_a_2837_, v___x_2841_);
lean_dec(v___x_2845_);
lean_inc(v_a_2839_);
lean_inc_ref(v_a_2838_);
lean_inc(v_a_2837_);
v___x_2846_ = lean_apply_4(v_fallback_2835_, v_a_2837_, v_a_2838_, v_a_2839_, lean_box(0));
return v___x_2846_;
}
else
{
lean_dec(v___x_2841_);
lean_dec_ref(v_fallback_2835_);
return v___x_2842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback___boxed(lean_object* v_fallback_2847_, lean_object* v_act_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_Doc_withRendererFallback(v_fallback_2847_, v_act_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0(lean_object* v_____do__lift_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = l_Lean_Doc_joinInlines(v_____do__lift_2854_);
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0___boxed(lean_object* v_____do__lift_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__0(v_____do__lift_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v_____do__lift_2861_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1(lean_object* v___x_2867_, lean_object* v___x_2868_, lean_object* v___f_2869_, lean_object* v_go_2870_, lean_object* v_container_2871_, lean_object* v_content_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
if (lean_obj_tag(v_container_2871_) == 0)
{
lean_object* v_val_2877_; size_t v_sz_2878_; size_t v___x_2879_; lean_object* v___x_2880_; lean_object* v_fallback_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v_val_2877_ = lean_ctor_get(v_container_2871_, 0);
lean_inc(v_val_2877_);
lean_dec_ref_known(v_container_2871_, 1);
v_sz_2878_ = lean_array_size(v_content_2872_);
v___x_2879_ = ((size_t)0ULL);
lean_inc_ref(v_content_2872_);
lean_inc_ref(v_go_2870_);
lean_inc_ref(v___x_2867_);
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2867_, v_go_2870_, v_sz_2878_, v___x_2879_, v_content_2872_);
lean_inc_ref(v___f_2869_);
v_fallback_2881_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_2881_, 0, lean_box(0));
lean_closure_set(v_fallback_2881_, 1, lean_box(0));
lean_closure_set(v_fallback_2881_, 2, v___x_2868_);
lean_closure_set(v_fallback_2881_, 3, lean_box(0));
lean_closure_set(v_fallback_2881_, 4, lean_box(0));
lean_closure_set(v_fallback_2881_, 5, v___x_2880_);
lean_closure_set(v_fallback_2881_, 6, v___f_2869_);
v___x_2882_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2877_);
v___x_2883_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_2882_, v___y_2874_, v___y_2875_);
lean_dec(v___x_2882_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
if (lean_obj_tag(v_a_2884_) == 0)
{
lean_object* v___x_543__overap_2885_; lean_object* v___x_2886_; 
lean_dec_ref(v_fallback_2881_);
lean_dec(v_val_2877_);
v___x_543__overap_2885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2867_, v_go_2870_, v_sz_2878_, v___x_2879_, v_content_2872_);
lean_inc(v___y_2875_);
lean_inc_ref(v___y_2874_);
lean_inc(v___y_2873_);
v___x_2886_ = lean_apply_4(v___x_543__overap_2885_, v___y_2873_, v___y_2874_, v___y_2875_, lean_box(0));
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v___x_2888_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
lean_inc(v___y_2875_);
lean_inc_ref(v___y_2874_);
lean_inc(v___y_2873_);
v___x_2888_ = lean_apply_5(v___f_2869_, v_a_2887_, v___y_2873_, v___y_2874_, v___y_2875_, lean_box(0));
return v___x_2888_;
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec_ref(v___f_2869_);
v_a_2889_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2886_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2886_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
else
{
lean_object* v_val_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
lean_dec_ref(v___f_2869_);
lean_dec_ref(v___x_2867_);
v_val_2897_ = lean_ctor_get(v_a_2884_, 0);
lean_inc(v_val_2897_);
lean_dec_ref_known(v_a_2884_, 1);
v___x_2898_ = lean_apply_3(v_val_2897_, v_go_2870_, v_val_2877_, v_content_2872_);
v___x_2899_ = l_Lean_Doc_withRendererFallback(v_fallback_2881_, v___x_2898_, v___y_2873_, v___y_2874_, v___y_2875_);
return v___x_2899_;
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec_ref(v_fallback_2881_);
lean_dec(v_val_2877_);
lean_dec_ref(v_content_2872_);
lean_dec_ref(v_go_2870_);
lean_dec_ref(v___f_2869_);
lean_dec_ref(v___x_2867_);
v_a_2900_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2883_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2883_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
size_t v_sz_2908_; size_t v___x_2909_; lean_object* v___x_558__overap_2910_; lean_object* v___x_2911_; 
lean_dec_ref_known(v_container_2871_, 1);
lean_dec_ref(v___f_2869_);
lean_dec_ref(v___x_2868_);
v_sz_2908_ = lean_array_size(v_content_2872_);
v___x_2909_ = ((size_t)0ULL);
v___x_558__overap_2910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2867_, v_go_2870_, v_sz_2908_, v___x_2909_, v_content_2872_);
lean_inc(v___y_2875_);
lean_inc_ref(v___y_2874_);
lean_inc(v___y_2873_);
v___x_2911_ = lean_apply_4(v___x_558__overap_2910_, v___y_2873_, v___y_2874_, v___y_2875_, lean_box(0));
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2920_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = l_Lean_Doc_joinInlines(v_a_2912_);
lean_dec(v_a_2912_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
v_a_2921_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2911_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2911_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed(lean_object* v___x_2929_, lean_object* v___x_2930_, lean_object* v___f_2931_, lean_object* v_go_2932_, lean_object* v_container_2933_, lean_object* v_content_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__1(v___x_2929_, v___x_2930_, v___f_2931_, v_go_2932_, v_container_2933_, v_content_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
return v_res_2939_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownInlineElabInline(void){
_start:
{
lean_object* v___x_2941_; lean_object* v_toApplicative_2942_; lean_object* v_toFunctor_2943_; lean_object* v_toSeq_2944_; lean_object* v_toSeqLeft_2945_; lean_object* v_toSeqRight_2946_; lean_object* v___f_2947_; lean_object* v___f_2948_; lean_object* v___f_2949_; lean_object* v___f_2950_; lean_object* v___f_2951_; lean_object* v___x_2952_; lean_object* v___f_2953_; lean_object* v___f_2954_; lean_object* v___f_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___f_2959_; 
v___x_2941_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2942_ = lean_ctor_get(v___x_2941_, 0);
v_toFunctor_2943_ = lean_ctor_get(v_toApplicative_2942_, 0);
v_toSeq_2944_ = lean_ctor_get(v_toApplicative_2942_, 2);
v_toSeqLeft_2945_ = lean_ctor_get(v_toApplicative_2942_, 3);
v_toSeqRight_2946_ = lean_ctor_get(v_toApplicative_2942_, 4);
v___f_2947_ = ((lean_object*)(l_Lean_Doc_instMarkdownInlineElabInline___closed__0));
v___f_2948_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2949_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2943_, 2);
v___f_2950_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2950_, 0, v_toFunctor_2943_);
v___f_2951_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2951_, 0, v_toFunctor_2943_);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___f_2950_);
lean_ctor_set(v___x_2952_, 1, v___f_2951_);
lean_inc(v_toSeqRight_2946_);
v___f_2953_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2953_, 0, v_toSeqRight_2946_);
lean_inc(v_toSeqLeft_2945_);
v___f_2954_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2954_, 0, v_toSeqLeft_2945_);
lean_inc(v_toSeq_2944_);
v___f_2955_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2955_, 0, v_toSeq_2944_);
v___x_2956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2952_);
lean_ctor_set(v___x_2956_, 1, v___f_2948_);
lean_ctor_set(v___x_2956_, 2, v___f_2955_);
lean_ctor_set(v___x_2956_, 3, v___f_2954_);
lean_ctor_set(v___x_2956_, 4, v___f_2953_);
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
lean_ctor_set(v___x_2957_, 1, v___f_2949_);
lean_inc_ref(v___x_2957_);
v___x_2958_ = l_StateRefT_x27_instMonad___redArg(v___x_2957_);
v___f_2959_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2959_, 0, v___x_2958_);
lean_closure_set(v___f_2959_, 1, v___x_2957_);
lean_closure_set(v___f_2959_, 2, v___f_2947_);
return v___f_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v_____do__lift_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = l_Lean_Doc_joinBlocks(v_____do__lift_2960_);
v___x_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object* v_____do__lift_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(v_____do__lift_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v_____do__lift_2967_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object* v___x_2973_, lean_object* v___x_2974_, lean_object* v___f_2975_, lean_object* v_goI_2976_, lean_object* v_goB_2977_, lean_object* v_container_2978_, lean_object* v_content_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
if (lean_obj_tag(v_container_2978_) == 0)
{
lean_object* v_val_2984_; size_t v_sz_2985_; size_t v___x_2986_; lean_object* v___x_2987_; lean_object* v_fallback_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v_val_2984_ = lean_ctor_get(v_container_2978_, 0);
lean_inc(v_val_2984_);
lean_dec_ref_known(v_container_2978_, 1);
v_sz_2985_ = lean_array_size(v_content_2979_);
v___x_2986_ = ((size_t)0ULL);
lean_inc_ref(v_content_2979_);
lean_inc_ref(v_goB_2977_);
lean_inc_ref(v___x_2973_);
v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2973_, v_goB_2977_, v_sz_2985_, v___x_2986_, v_content_2979_);
lean_inc_ref(v___f_2975_);
v_fallback_2988_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_2988_, 0, lean_box(0));
lean_closure_set(v_fallback_2988_, 1, lean_box(0));
lean_closure_set(v_fallback_2988_, 2, v___x_2974_);
lean_closure_set(v_fallback_2988_, 3, lean_box(0));
lean_closure_set(v_fallback_2988_, 4, lean_box(0));
lean_closure_set(v_fallback_2988_, 5, v___x_2987_);
lean_closure_set(v_fallback_2988_, 6, v___f_2975_);
v___x_2989_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2984_);
v___x_2990_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_2989_, v___y_2981_, v___y_2982_);
lean_dec(v___x_2989_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
if (lean_obj_tag(v_a_2991_) == 0)
{
lean_object* v___x_543__overap_2992_; lean_object* v___x_2993_; 
lean_dec_ref(v_fallback_2988_);
lean_dec(v_val_2984_);
lean_dec_ref(v_goI_2976_);
v___x_543__overap_2992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2973_, v_goB_2977_, v_sz_2985_, v___x_2986_, v_content_2979_);
lean_inc(v___y_2982_);
lean_inc_ref(v___y_2981_);
lean_inc(v___y_2980_);
v___x_2993_ = lean_apply_4(v___x_543__overap_2992_, v___y_2980_, v___y_2981_, v___y_2982_, lean_box(0));
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
lean_inc(v___y_2982_);
lean_inc_ref(v___y_2981_);
lean_inc(v___y_2980_);
v___x_2995_ = lean_apply_5(v___f_2975_, v_a_2994_, v___y_2980_, v___y_2981_, v___y_2982_, lean_box(0));
return v___x_2995_;
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref(v___f_2975_);
v_a_2996_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2993_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2993_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
else
{
lean_object* v_val_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
lean_dec_ref(v___f_2975_);
lean_dec_ref(v___x_2973_);
v_val_3004_ = lean_ctor_get(v_a_2991_, 0);
lean_inc(v_val_3004_);
lean_dec_ref_known(v_a_2991_, 1);
v___x_3005_ = lean_apply_4(v_val_3004_, v_goI_2976_, v_goB_2977_, v_val_2984_, v_content_2979_);
v___x_3006_ = l_Lean_Doc_withRendererFallback(v_fallback_2988_, v___x_3005_, v___y_2980_, v___y_2981_, v___y_2982_);
return v___x_3006_;
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec_ref(v_fallback_2988_);
lean_dec(v_val_2984_);
lean_dec_ref(v_content_2979_);
lean_dec_ref(v_goB_2977_);
lean_dec_ref(v_goI_2976_);
lean_dec_ref(v___f_2975_);
lean_dec_ref(v___x_2973_);
v_a_3007_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2990_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2990_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
size_t v_sz_3015_; size_t v___x_3016_; lean_object* v___x_558__overap_3017_; lean_object* v___x_3018_; 
lean_dec_ref_known(v_container_2978_, 1);
lean_dec_ref(v_goI_2976_);
lean_dec_ref(v___f_2975_);
lean_dec_ref(v___x_2974_);
v_sz_3015_ = lean_array_size(v_content_2979_);
v___x_3016_ = ((size_t)0ULL);
v___x_558__overap_3017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2973_, v_goB_2977_, v_sz_3015_, v___x_3016_, v_content_2979_);
lean_inc(v___y_2982_);
lean_inc_ref(v___y_2981_);
lean_inc(v___y_2980_);
v___x_3018_ = lean_apply_4(v___x_558__overap_3017_, v___y_2980_, v___y_2981_, v___y_2982_, lean_box(0));
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3027_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3021_ = v___x_3018_;
v_isShared_3022_ = v_isSharedCheck_3027_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3018_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3027_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3023_ = l_Lean_Doc_joinBlocks(v_a_3019_);
lean_dec(v_a_3019_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3023_);
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
v_a_3028_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3018_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3018_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object* v___x_3036_, lean_object* v___x_3037_, lean_object* v___f_3038_, lean_object* v_goI_3039_, lean_object* v_goB_3040_, lean_object* v_container_3041_, lean_object* v_content_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_3036_, v___x_3037_, v___f_3038_, v_goI_3039_, v_goB_3040_, v_container_3041_, v_content_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
return v_res_3047_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownBlockElabInlineElabBlock(void){
_start:
{
lean_object* v___x_3049_; lean_object* v_toApplicative_3050_; lean_object* v_toFunctor_3051_; lean_object* v_toSeq_3052_; lean_object* v_toSeqLeft_3053_; lean_object* v_toSeqRight_3054_; lean_object* v___f_3055_; lean_object* v___f_3056_; lean_object* v___f_3057_; lean_object* v___f_3058_; lean_object* v___f_3059_; lean_object* v___x_3060_; lean_object* v___f_3061_; lean_object* v___f_3062_; lean_object* v___f_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___f_3067_; 
v___x_3049_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3050_ = lean_ctor_get(v___x_3049_, 0);
v_toFunctor_3051_ = lean_ctor_get(v_toApplicative_3050_, 0);
v_toSeq_3052_ = lean_ctor_get(v_toApplicative_3050_, 2);
v_toSeqLeft_3053_ = lean_ctor_get(v_toApplicative_3050_, 3);
v_toSeqRight_3054_ = lean_ctor_get(v_toApplicative_3050_, 4);
v___f_3055_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___closed__0));
v___f_3056_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3057_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3051_, 2);
v___f_3058_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3058_, 0, v_toFunctor_3051_);
v___f_3059_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3059_, 0, v_toFunctor_3051_);
v___x_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___f_3058_);
lean_ctor_set(v___x_3060_, 1, v___f_3059_);
lean_inc(v_toSeqRight_3054_);
v___f_3061_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3061_, 0, v_toSeqRight_3054_);
lean_inc(v_toSeqLeft_3053_);
v___f_3062_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3062_, 0, v_toSeqLeft_3053_);
lean_inc(v_toSeq_3052_);
v___f_3063_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3063_, 0, v_toSeq_3052_);
v___x_3064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3060_);
lean_ctor_set(v___x_3064_, 1, v___f_3056_);
lean_ctor_set(v___x_3064_, 2, v___f_3063_);
lean_ctor_set(v___x_3064_, 3, v___f_3062_);
lean_ctor_set(v___x_3064_, 4, v___f_3061_);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v___f_3057_);
lean_inc_ref(v___x_3065_);
v___x_3066_ = l_StateRefT_x27_instMonad___redArg(v___x_3065_);
v___f_3067_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3067_, 0, v___x_3066_);
lean_closure_set(v___f_3067_, 1, v___x_3065_);
lean_closure_set(v___f_3067_, 2, v___f_3055_);
return v___f_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0(lean_object* v___x_3068_, lean_object* v___x_3069_, lean_object* v_part_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = l_Lean_Doc_partMarkdown___redArg(v___x_3068_, v___x_3069_, v___x_3075_, v_part_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed(lean_object* v___x_3077_, lean_object* v___x_3078_, lean_object* v_part_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__0(v___x_3077_, v___x_3078_, v_part_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1(lean_object* v___x_3085_, lean_object* v___x_3086_, lean_object* v___x_3087_, lean_object* v___f_3088_, lean_object* v_x_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_text_3094_; lean_object* v_subsections_3095_; lean_object* v___x_3096_; size_t v_sz_3097_; size_t v___x_3098_; lean_object* v___x_443__overap_3099_; lean_object* v___x_3100_; 
v_text_3094_ = lean_ctor_get(v_x_3089_, 0);
lean_inc_ref(v_text_3094_);
v_subsections_3095_ = lean_ctor_get(v_x_3089_, 1);
lean_inc_ref(v_subsections_3095_);
lean_dec_ref(v_x_3089_);
v___x_3096_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3096_, 0, lean_box(0));
lean_closure_set(v___x_3096_, 1, lean_box(0));
lean_closure_set(v___x_3096_, 2, v___x_3085_);
lean_closure_set(v___x_3096_, 3, v___x_3086_);
v_sz_3097_ = lean_array_size(v_text_3094_);
v___x_3098_ = ((size_t)0ULL);
lean_inc_ref(v___x_3087_);
v___x_443__overap_3099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3087_, v___x_3096_, v_sz_3097_, v___x_3098_, v_text_3094_);
lean_inc(v___y_3092_);
lean_inc_ref(v___y_3091_);
lean_inc(v___y_3090_);
v___x_3100_ = lean_apply_4(v___x_443__overap_3099_, v___y_3090_, v___y_3091_, v___y_3092_, lean_box(0));
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; size_t v_sz_3102_; lean_object* v___x_446__overap_3103_; lean_object* v___x_3104_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3100_, 1);
v_sz_3102_ = lean_array_size(v_subsections_3095_);
v___x_446__overap_3103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3087_, v___f_3088_, v_sz_3102_, v___x_3098_, v_subsections_3095_);
lean_inc(v___y_3092_);
lean_inc_ref(v___y_3091_);
lean_inc(v___y_3090_);
v___x_3104_ = lean_apply_4(v___x_446__overap_3103_, v___y_3090_, v___y_3091_, v___y_3092_, lean_box(0));
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3114_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3114_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3114_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3109_ = l_Array_append___redArg(v_a_3101_, v_a_3105_);
lean_dec(v_a_3105_);
v___x_3110_ = l_Lean_Doc_joinBlocks(v___x_3109_);
lean_dec_ref(v___x_3109_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v___x_3110_);
v___x_3112_ = v___x_3107_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3110_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec(v_a_3101_);
v_a_3115_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3104_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3104_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v_subsections_3095_);
lean_dec_ref(v___f_3088_);
lean_dec_ref(v___x_3087_);
v_a_3123_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3100_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3100_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed(lean_object* v___x_3131_, lean_object* v___x_3132_, lean_object* v___x_3133_, lean_object* v___f_3134_, lean_object* v_x_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__1(v___x_3131_, v___x_3132_, v___x_3133_, v___f_3134_, v_x_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
return v_res_3140_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0(void){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___f_3143_; 
v___x_3141_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3142_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3143_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3143_, 0, v___x_3142_);
lean_closure_set(v___f_3143_, 1, v___x_3141_);
return v___f_3143_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString(void){
_start:
{
lean_object* v___x_3144_; lean_object* v_toApplicative_3145_; lean_object* v_toFunctor_3146_; lean_object* v_toSeq_3147_; lean_object* v_toSeqLeft_3148_; lean_object* v_toSeqRight_3149_; lean_object* v___f_3150_; lean_object* v___f_3151_; lean_object* v___f_3152_; lean_object* v___f_3153_; lean_object* v___x_3154_; lean_object* v___f_3155_; lean_object* v___f_3156_; lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___f_3163_; lean_object* v___f_3164_; 
v___x_3144_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3145_ = lean_ctor_get(v___x_3144_, 0);
v_toFunctor_3146_ = lean_ctor_get(v_toApplicative_3145_, 0);
v_toSeq_3147_ = lean_ctor_get(v_toApplicative_3145_, 2);
v_toSeqLeft_3148_ = lean_ctor_get(v_toApplicative_3145_, 3);
v_toSeqRight_3149_ = lean_ctor_get(v_toApplicative_3145_, 4);
v___f_3150_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3151_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3146_, 2);
v___f_3152_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3152_, 0, v_toFunctor_3146_);
v___f_3153_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3153_, 0, v_toFunctor_3146_);
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___f_3152_);
lean_ctor_set(v___x_3154_, 1, v___f_3153_);
lean_inc(v_toSeqRight_3149_);
v___f_3155_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3155_, 0, v_toSeqRight_3149_);
lean_inc(v_toSeqLeft_3148_);
v___f_3156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3156_, 0, v_toSeqLeft_3148_);
lean_inc(v_toSeq_3147_);
v___f_3157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3157_, 0, v_toSeq_3147_);
v___x_3158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3154_);
lean_ctor_set(v___x_3158_, 1, v___f_3150_);
lean_ctor_set(v___x_3158_, 2, v___f_3157_);
lean_ctor_set(v___x_3158_, 3, v___f_3156_);
lean_ctor_set(v___x_3158_, 4, v___f_3155_);
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
lean_ctor_set(v___x_3159_, 1, v___f_3151_);
v___x_3160_ = l_StateRefT_x27_instMonad___redArg(v___x_3159_);
v___x_3161_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3162_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3163_ = lean_obj_once(&l_Lean_Doc_instToMarkdownVersoDocString___closed__0, &l_Lean_Doc_instToMarkdownVersoDocString___closed__0_once, _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0);
v___f_3164_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3164_, 0, v___x_3161_);
lean_closure_set(v___f_3164_, 1, v___x_3162_);
lean_closure_set(v___f_3164_, 2, v___x_3160_);
lean_closure_set(v___f_3164_, 3, v___f_3163_);
return v___f_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0(lean_object* v___x_3165_, lean_object* v___x_3166_, lean_object* v_x_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_snd_3172_; lean_object* v_fst_3173_; lean_object* v_snd_3174_; lean_object* v___x_3175_; 
v_snd_3172_ = lean_ctor_get(v_x_3167_, 1);
lean_inc(v_snd_3172_);
v_fst_3173_ = lean_ctor_get(v_x_3167_, 0);
lean_inc(v_fst_3173_);
lean_dec_ref(v_x_3167_);
v_snd_3174_ = lean_ctor_get(v_snd_3172_, 1);
lean_inc(v_snd_3174_);
lean_dec(v_snd_3172_);
v___x_3175_ = l_Lean_Doc_partMarkdown___redArg(v___x_3165_, v___x_3166_, v_fst_3173_, v_snd_3174_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v_fst_3173_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_3176_, lean_object* v___x_3177_, lean_object* v_x_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_Doc_instToMarkdownSnippet___lam__0(v___x_3176_, v___x_3177_, v_x_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1(lean_object* v___x_3184_, lean_object* v___x_3185_, lean_object* v___x_3186_, lean_object* v___f_3187_, lean_object* v_x_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_text_3193_; lean_object* v_sections_3194_; lean_object* v___x_3195_; size_t v_sz_3196_; size_t v___x_3197_; lean_object* v___x_490__overap_3198_; lean_object* v___x_3199_; 
v_text_3193_ = lean_ctor_get(v_x_3188_, 0);
lean_inc_ref(v_text_3193_);
v_sections_3194_ = lean_ctor_get(v_x_3188_, 1);
lean_inc_ref(v_sections_3194_);
lean_dec_ref(v_x_3188_);
v___x_3195_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3195_, 0, lean_box(0));
lean_closure_set(v___x_3195_, 1, lean_box(0));
lean_closure_set(v___x_3195_, 2, v___x_3184_);
lean_closure_set(v___x_3195_, 3, v___x_3185_);
v_sz_3196_ = lean_array_size(v_text_3193_);
v___x_3197_ = ((size_t)0ULL);
lean_inc_ref(v___x_3186_);
v___x_490__overap_3198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3186_, v___x_3195_, v_sz_3196_, v___x_3197_, v_text_3193_);
lean_inc(v___y_3191_);
lean_inc_ref(v___y_3190_);
lean_inc(v___y_3189_);
v___x_3199_ = lean_apply_4(v___x_490__overap_3198_, v___y_3189_, v___y_3190_, v___y_3191_, lean_box(0));
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; size_t v_sz_3201_; lean_object* v___x_493__overap_3202_; lean_object* v___x_3203_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3199_, 1);
v_sz_3201_ = lean_array_size(v_sections_3194_);
v___x_493__overap_3202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3186_, v___f_3187_, v_sz_3201_, v___x_3197_, v_sections_3194_);
lean_inc(v___y_3191_);
lean_inc_ref(v___y_3190_);
lean_inc(v___y_3189_);
v___x_3203_ = lean_apply_4(v___x_493__overap_3202_, v___y_3189_, v___y_3190_, v___y_3191_, lean_box(0));
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3213_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3213_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3213_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3211_; 
v___x_3208_ = l_Array_append___redArg(v_a_3200_, v_a_3204_);
lean_dec(v_a_3204_);
v___x_3209_ = l_Lean_Doc_joinBlocks(v___x_3208_);
lean_dec_ref(v___x_3208_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3209_);
v___x_3211_ = v___x_3206_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3209_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec(v_a_3200_);
v_a_3214_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3203_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3203_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec_ref(v_sections_3194_);
lean_dec_ref(v___f_3187_);
lean_dec_ref(v___x_3186_);
v_a_3222_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3199_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3199_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_3230_, lean_object* v___x_3231_, lean_object* v___x_3232_, lean_object* v___f_3233_, lean_object* v_x_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_Doc_instToMarkdownSnippet___lam__1(v___x_3230_, v___x_3231_, v___x_3232_, v___f_3233_, v_x_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
return v_res_3239_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___f_3242_; 
v___x_3240_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3241_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3242_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3242_, 0, v___x_3241_);
lean_closure_set(v___f_3242_, 1, v___x_3240_);
return v___f_3242_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet(void){
_start:
{
lean_object* v___x_3243_; lean_object* v_toApplicative_3244_; lean_object* v_toFunctor_3245_; lean_object* v_toSeq_3246_; lean_object* v_toSeqLeft_3247_; lean_object* v_toSeqRight_3248_; lean_object* v___f_3249_; lean_object* v___f_3250_; lean_object* v___f_3251_; lean_object* v___f_3252_; lean_object* v___x_3253_; lean_object* v___f_3254_; lean_object* v___f_3255_; lean_object* v___f_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___f_3262_; lean_object* v___f_3263_; 
v___x_3243_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3244_ = lean_ctor_get(v___x_3243_, 0);
v_toFunctor_3245_ = lean_ctor_get(v_toApplicative_3244_, 0);
v_toSeq_3246_ = lean_ctor_get(v_toApplicative_3244_, 2);
v_toSeqLeft_3247_ = lean_ctor_get(v_toApplicative_3244_, 3);
v_toSeqRight_3248_ = lean_ctor_get(v_toApplicative_3244_, 4);
v___f_3249_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3250_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3245_, 2);
v___f_3251_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3251_, 0, v_toFunctor_3245_);
v___f_3252_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3252_, 0, v_toFunctor_3245_);
v___x_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___f_3251_);
lean_ctor_set(v___x_3253_, 1, v___f_3252_);
lean_inc(v_toSeqRight_3248_);
v___f_3254_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3254_, 0, v_toSeqRight_3248_);
lean_inc(v_toSeqLeft_3247_);
v___f_3255_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3255_, 0, v_toSeqLeft_3247_);
lean_inc(v_toSeq_3246_);
v___f_3256_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3256_, 0, v_toSeq_3246_);
v___x_3257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3253_);
lean_ctor_set(v___x_3257_, 1, v___f_3249_);
lean_ctor_set(v___x_3257_, 2, v___f_3256_);
lean_ctor_set(v___x_3257_, 3, v___f_3255_);
lean_ctor_set(v___x_3257_, 4, v___f_3254_);
v___x_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
lean_ctor_set(v___x_3258_, 1, v___f_3250_);
v___x_3259_ = l_StateRefT_x27_instMonad___redArg(v___x_3258_);
v___x_3260_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3261_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3262_ = lean_obj_once(&l_Lean_Doc_instToMarkdownSnippet___closed__0, &l_Lean_Doc_instToMarkdownSnippet___closed__0_once, _init_l_Lean_Doc_instToMarkdownSnippet___closed__0);
v___f_3263_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3263_, 0, v___x_3260_);
lean_closure_set(v___f_3263_, 1, v___x_3261_);
lean_closure_set(v___f_3263_, 2, v___x_3259_);
lean_closure_set(v___f_3263_, 3, v___f_3262_);
return v___f_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(lean_object* v_opts_3264_, lean_object* v_opt_3265_){
_start:
{
lean_object* v_name_3266_; lean_object* v_defValue_3267_; lean_object* v_map_3268_; lean_object* v___x_3269_; 
v_name_3266_ = lean_ctor_get(v_opt_3265_, 0);
v_defValue_3267_ = lean_ctor_get(v_opt_3265_, 1);
v_map_3268_ = lean_ctor_get(v_opts_3264_, 0);
v___x_3269_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3268_, v_name_3266_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_inc(v_defValue_3267_);
return v_defValue_3267_;
}
else
{
lean_object* v_val_3270_; 
v_val_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_val_3270_);
lean_dec_ref_known(v___x_3269_, 1);
if (lean_obj_tag(v_val_3270_) == 3)
{
lean_object* v_v_3271_; 
v_v_3271_ = lean_ctor_get(v_val_3270_, 0);
lean_inc(v_v_3271_);
lean_dec_ref_known(v_val_3270_, 1);
return v_v_3271_;
}
else
{
lean_dec(v_val_3270_);
lean_inc(v_defValue_3267_);
return v_defValue_3267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0___boxed(lean_object* v_opts_3272_, lean_object* v_opt_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_opts_3272_, v_opt_3273_);
lean_dec_ref(v_opt_3273_);
lean_dec_ref(v_opts_3272_);
return v_res_3274_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3276_ = lean_unsigned_to_nat(1u);
v___x_3277_ = l_Lean_firstFrontendMacroScope;
v___x_3278_ = lean_nat_add(v___x_3277_, v___x_3276_);
return v___x_3278_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__6(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3289_ = lean_unsigned_to_nat(32u);
v___x_3290_ = lean_mk_empty_array_with_capacity(v___x_3289_);
v___x_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
return v___x_3291_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__7(void){
_start:
{
size_t v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3292_ = ((size_t)5ULL);
v___x_3293_ = lean_unsigned_to_nat(0u);
v___x_3294_ = lean_unsigned_to_nat(32u);
v___x_3295_ = lean_mk_empty_array_with_capacity(v___x_3294_);
v___x_3296_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__6, &l_Lean_Doc_runMarkdown___redArg___closed__6_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__6);
v___x_3297_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
lean_ctor_set(v___x_3297_, 1, v___x_3295_);
lean_ctor_set(v___x_3297_, 2, v___x_3293_);
lean_ctor_set(v___x_3297_, 3, v___x_3293_);
lean_ctor_set_usize(v___x_3297_, 4, v___x_3292_);
return v___x_3297_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__8(void){
_start:
{
lean_object* v___x_3298_; uint64_t v___x_3299_; lean_object* v___x_3300_; 
v___x_3298_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3299_ = 0ULL;
v___x_3300_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set_uint64(v___x_3300_, sizeof(void*)*1, v___x_3299_);
return v___x_3300_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__9(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
return v___x_3302_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__10(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__9, &l_Lean_Doc_runMarkdown___redArg___closed__9_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__9);
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
return v___x_3304_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__12(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3307_ = lean_unsigned_to_nat(0u);
v___x_3308_ = l_Lean_Options_empty;
v___x_3309_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__11));
v___x_3310_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
lean_ctor_set(v___x_3310_, 1, v___x_3308_);
lean_ctor_set(v___x_3310_, 2, v___x_3309_);
lean_ctor_set(v___x_3310_, 3, v___x_3307_);
lean_ctor_set(v___x_3310_, 4, v___x_3307_);
lean_ctor_set(v___x_3310_, 5, v___x_3307_);
lean_ctor_set(v___x_3310_, 6, v___x_3309_);
lean_ctor_set(v___x_3310_, 7, v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__13(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3311_ = l_Lean_NameSet_empty;
v___x_3312_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
lean_ctor_set(v___x_3313_, 2, v___x_3311_);
return v___x_3313_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__14(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; lean_object* v___x_3317_; 
v___x_3314_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3315_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__9, &l_Lean_Doc_runMarkdown___redArg___closed__9_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__9);
v___x_3316_ = 1;
v___x_3317_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3317_, 0, v___x_3315_);
lean_ctor_set(v___x_3317_, 1, v___x_3315_);
lean_ctor_set(v___x_3317_, 2, v___x_3314_);
lean_ctor_set_uint8(v___x_3317_, sizeof(void*)*3, v___x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg(lean_object* v_env_3321_, lean_object* v_act_3322_, lean_object* v_options_3323_, lean_object* v_currNamespace_3324_, lean_object* v_openDecls_3325_, lean_object* v_cancelTk_x3f_3326_){
_start:
{
lean_object* v_a_3329_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; uint16_t v___x_3339_; uint8_t v___x_3340_; uint8_t v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v_fileName_3356_; lean_object* v_fileMap_3357_; lean_object* v_currNamespace_3358_; lean_object* v_openDecls_3359_; lean_object* v_initHeartbeats_3360_; lean_object* v_maxHeartbeats_3361_; lean_object* v_quotContext_3362_; lean_object* v_currMacroScope_3363_; lean_object* v_cancelTk_x3f_3364_; lean_object* v_inheritedTraceOptions_3365_; lean_object* v_currRecDepth_3366_; lean_object* v_ref_3367_; uint8_t v_suppressElabErrors_3368_; uint8_t v_checkDeprecated_3369_; uint8_t v_isRecordingDeps_3370_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; uint8_t v___y_3411_; lean_object* v_env_3432_; uint8_t v___x_3433_; uint16_t v___x_3434_; uint16_t v___x_3435_; uint16_t v___x_3436_; uint8_t v___x_3437_; 
v___x_3332_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__0));
v___x_3333_ = l_Lean_instInhabitedFileMap_default;
v___x_3334_ = lean_unsigned_to_nat(0u);
v___x_3335_ = l_Lean_Core_getMaxHeartbeats(v_options_3323_);
v___x_3336_ = lean_box(0);
v___x_3337_ = l_Lean_firstFrontendMacroScope;
v___x_3338_ = lean_box(0);
v___x_3339_ = l_Lean_OptionFlags_ofOptions(v_options_3323_);
v___x_3340_ = 0;
v___x_3341_ = 0;
v___x_3342_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3343_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__4));
v___x_3344_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__5));
v___x_3345_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__8, &l_Lean_Doc_runMarkdown___redArg___closed__8_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__8);
v___x_3346_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__10, &l_Lean_Doc_runMarkdown___redArg___closed__10_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__10);
v___x_3347_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__11));
v___x_3348_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__12, &l_Lean_Doc_runMarkdown___redArg___closed__12_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__12);
v___x_3349_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__13, &l_Lean_Doc_runMarkdown___redArg___closed__13_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__13);
v___x_3350_ = 1;
v___x_3351_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__14, &l_Lean_Doc_runMarkdown___redArg___closed__14_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__14);
v___x_3352_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3352_, 0, v_env_3321_);
lean_ctor_set(v___x_3352_, 1, v___x_3342_);
lean_ctor_set(v___x_3352_, 2, v___x_3343_);
lean_ctor_set(v___x_3352_, 3, v___x_3344_);
lean_ctor_set(v___x_3352_, 4, v___x_3345_);
lean_ctor_set(v___x_3352_, 5, v___x_3346_);
lean_ctor_set(v___x_3352_, 6, v___x_3348_);
lean_ctor_set(v___x_3352_, 7, v___x_3349_);
lean_ctor_set(v___x_3352_, 8, v___x_3351_);
lean_ctor_set(v___x_3352_, 9, v___x_3347_);
v___x_3353_ = lean_io_get_num_heartbeats();
v___x_3354_ = lean_st_mk_ref(v___x_3352_);
v___x_3407_ = l_Lean_inheritedTraceOptions;
v___x_3408_ = lean_st_ref_get(v___x_3407_);
v___x_3409_ = lean_st_ref_get(v___x_3354_);
v_env_3432_ = lean_ctor_get(v___x_3409_, 0);
lean_inc_ref(v_env_3432_);
lean_dec(v___x_3409_);
v___x_3433_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3432_);
lean_dec_ref(v_env_3432_);
v___x_3434_ = 512;
v___x_3435_ = lean_uint16_land(v___x_3339_, v___x_3434_);
v___x_3436_ = 0;
v___x_3437_ = lean_uint16_dec_eq(v___x_3435_, v___x_3436_);
if (v___x_3437_ == 0)
{
if (v___x_3433_ == 0)
{
v___y_3411_ = v___x_3350_;
goto v___jp_3410_;
}
else
{
v_fileName_3356_ = v___x_3332_;
v_fileMap_3357_ = v___x_3333_;
v_currNamespace_3358_ = v_currNamespace_3324_;
v_openDecls_3359_ = v_openDecls_3325_;
v_initHeartbeats_3360_ = v___x_3353_;
v_maxHeartbeats_3361_ = v___x_3335_;
v_quotContext_3362_ = v___x_3336_;
v_currMacroScope_3363_ = v___x_3337_;
v_cancelTk_x3f_3364_ = v_cancelTk_x3f_3326_;
v_inheritedTraceOptions_3365_ = v___x_3408_;
v_currRecDepth_3366_ = v___x_3334_;
v_ref_3367_ = v___x_3338_;
v_suppressElabErrors_3368_ = v___x_3340_;
v_checkDeprecated_3369_ = v___x_3341_;
v_isRecordingDeps_3370_ = v___x_3340_;
goto v___jp_3355_;
}
}
else
{
if (v___x_3433_ == 0)
{
v_fileName_3356_ = v___x_3332_;
v_fileMap_3357_ = v___x_3333_;
v_currNamespace_3358_ = v_currNamespace_3324_;
v_openDecls_3359_ = v_openDecls_3325_;
v_initHeartbeats_3360_ = v___x_3353_;
v_maxHeartbeats_3361_ = v___x_3335_;
v_quotContext_3362_ = v___x_3336_;
v_currMacroScope_3363_ = v___x_3337_;
v_cancelTk_x3f_3364_ = v_cancelTk_x3f_3326_;
v_inheritedTraceOptions_3365_ = v___x_3408_;
v_currRecDepth_3366_ = v___x_3334_;
v_ref_3367_ = v___x_3338_;
v_suppressElabErrors_3368_ = v___x_3340_;
v_checkDeprecated_3369_ = v___x_3341_;
v_isRecordingDeps_3370_ = v___x_3340_;
goto v___jp_3355_;
}
else
{
v___y_3411_ = v___x_3340_;
goto v___jp_3410_;
}
}
v___jp_3328_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = lean_mk_io_user_error(v_a_3329_);
v___x_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
return v___x_3331_;
}
v___jp_3355_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3371_ = l_Lean_maxRecDepth;
v___x_3372_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_options_3323_, v___x_3371_);
lean_inc(v_currMacroScope_3363_);
lean_inc(v_quotContext_3362_);
lean_inc_ref(v_fileMap_3357_);
lean_inc_ref(v_fileName_3356_);
v___x_3373_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3373_, 0, v_fileName_3356_);
lean_ctor_set(v___x_3373_, 1, v_fileMap_3357_);
lean_ctor_set(v___x_3373_, 2, v_options_3323_);
lean_ctor_set(v___x_3373_, 3, v___x_3372_);
lean_ctor_set(v___x_3373_, 4, v_currNamespace_3358_);
lean_ctor_set(v___x_3373_, 5, v_openDecls_3359_);
lean_ctor_set(v___x_3373_, 6, v_initHeartbeats_3360_);
lean_ctor_set(v___x_3373_, 7, v_maxHeartbeats_3361_);
lean_ctor_set(v___x_3373_, 8, v_quotContext_3362_);
lean_ctor_set(v___x_3373_, 9, v_currMacroScope_3363_);
lean_ctor_set(v___x_3373_, 10, v_cancelTk_x3f_3364_);
lean_ctor_set(v___x_3373_, 11, v_inheritedTraceOptions_3365_);
lean_inc(v_ref_3367_);
v___x_3374_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
lean_ctor_set(v___x_3374_, 1, v_currRecDepth_3366_);
lean_ctor_set(v___x_3374_, 2, v_ref_3367_);
lean_ctor_set_uint16(v___x_3374_, sizeof(void*)*3, v___x_3339_);
lean_ctor_set_uint8(v___x_3374_, sizeof(void*)*3 + 2, v_suppressElabErrors_3368_);
lean_ctor_set_uint8(v___x_3374_, sizeof(void*)*3 + 3, v_checkDeprecated_3369_);
lean_ctor_set_uint8(v___x_3374_, sizeof(void*)*3 + 4, v_isRecordingDeps_3370_);
lean_inc(v___x_3354_);
v___x_3375_ = lean_apply_3(v_act_3322_, v___x_3374_, v___x_3354_, lean_box(0));
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3384_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3378_ = v___x_3375_;
v_isShared_3379_ = v_isSharedCheck_3384_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3375_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3384_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3380_; lean_object* v___x_3382_; 
v___x_3380_ = lean_st_ref_get(v___x_3354_);
lean_dec(v___x_3354_);
lean_dec(v___x_3380_);
if (v_isShared_3379_ == 0)
{
v___x_3382_ = v___x_3378_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3376_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3406_; 
lean_dec(v___x_3354_);
v_a_3385_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3387_ = v___x_3375_;
v_isShared_3388_ = v_isSharedCheck_3406_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3375_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3406_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
if (lean_obj_tag(v_a_3385_) == 0)
{
lean_object* v_msg_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3393_; 
v_msg_3389_ = lean_ctor_get(v_a_3385_, 1);
lean_inc_ref(v_msg_3389_);
lean_dec_ref_known(v_a_3385_, 2);
v___x_3390_ = l_Lean_MessageData_toString(v_msg_3389_);
v___x_3391_ = lean_mk_io_user_error(v___x_3390_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3391_);
v___x_3393_ = v___x_3387_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
else
{
lean_object* v_id_3395_; lean_object* v___x_3396_; 
lean_del_object(v___x_3387_);
v_id_3395_ = lean_ctor_get(v_a_3385_, 0);
lean_inc(v_id_3395_);
lean_dec_ref_known(v_a_3385_, 2);
v___x_3396_ = l_Lean_InternalExceptionId_getName(v_id_3395_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec(v_id_3395_);
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3396_, 1);
v___x_3398_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__15));
v___x_3399_ = l_Lean_Name_toString(v_a_3397_, v___x_3350_);
v___x_3400_ = lean_string_append(v___x_3398_, v___x_3399_);
lean_dec_ref(v___x_3399_);
v_a_3329_ = v___x_3400_;
goto v___jp_3328_;
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_dec_ref_known(v___x_3396_, 1);
v___x_3401_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__16));
v___x_3402_ = l_Nat_reprFast(v_id_3395_);
v___x_3403_ = lean_string_append(v___x_3401_, v___x_3402_);
lean_dec_ref(v___x_3402_);
v___x_3404_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__17));
v___x_3405_ = lean_string_append(v___x_3403_, v___x_3404_);
v_a_3329_ = v___x_3405_;
goto v___jp_3328_;
}
}
}
}
}
v___jp_3410_:
{
lean_object* v___x_3412_; lean_object* v_env_3413_; lean_object* v_nextMacroScope_3414_; lean_object* v_ngen_3415_; lean_object* v_auxDeclNGen_3416_; lean_object* v_traceState_3417_; lean_object* v_recordedDeps_3418_; lean_object* v_messages_3419_; lean_object* v_infoState_3420_; lean_object* v_snapshotTasks_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3430_; 
v___x_3412_ = lean_st_ref_take(v___x_3354_);
v_env_3413_ = lean_ctor_get(v___x_3412_, 0);
v_nextMacroScope_3414_ = lean_ctor_get(v___x_3412_, 1);
v_ngen_3415_ = lean_ctor_get(v___x_3412_, 2);
v_auxDeclNGen_3416_ = lean_ctor_get(v___x_3412_, 3);
v_traceState_3417_ = lean_ctor_get(v___x_3412_, 4);
v_recordedDeps_3418_ = lean_ctor_get(v___x_3412_, 6);
v_messages_3419_ = lean_ctor_get(v___x_3412_, 7);
v_infoState_3420_ = lean_ctor_get(v___x_3412_, 8);
v_snapshotTasks_3421_ = lean_ctor_get(v___x_3412_, 9);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3430_ == 0)
{
lean_object* v_unused_3431_; 
v_unused_3431_ = lean_ctor_get(v___x_3412_, 5);
lean_dec(v_unused_3431_);
v___x_3423_ = v___x_3412_;
v_isShared_3424_ = v_isSharedCheck_3430_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_snapshotTasks_3421_);
lean_inc(v_infoState_3420_);
lean_inc(v_messages_3419_);
lean_inc(v_recordedDeps_3418_);
lean_inc(v_traceState_3417_);
lean_inc(v_auxDeclNGen_3416_);
lean_inc(v_ngen_3415_);
lean_inc(v_nextMacroScope_3414_);
lean_inc(v_env_3413_);
lean_dec(v___x_3412_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3430_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3425_ = l_Lean_Kernel_enableDiag(v_env_3413_, v___y_3411_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 5, v___x_3346_);
lean_ctor_set(v___x_3423_, 0, v___x_3425_);
v___x_3427_ = v___x_3423_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3425_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v_nextMacroScope_3414_);
lean_ctor_set(v_reuseFailAlloc_3429_, 2, v_ngen_3415_);
lean_ctor_set(v_reuseFailAlloc_3429_, 3, v_auxDeclNGen_3416_);
lean_ctor_set(v_reuseFailAlloc_3429_, 4, v_traceState_3417_);
lean_ctor_set(v_reuseFailAlloc_3429_, 5, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3429_, 6, v_recordedDeps_3418_);
lean_ctor_set(v_reuseFailAlloc_3429_, 7, v_messages_3419_);
lean_ctor_set(v_reuseFailAlloc_3429_, 8, v_infoState_3420_);
lean_ctor_set(v_reuseFailAlloc_3429_, 9, v_snapshotTasks_3421_);
v___x_3427_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3428_; 
v___x_3428_ = lean_st_ref_put(v___x_3354_, v___x_3427_);
v_fileName_3356_ = v___x_3332_;
v_fileMap_3357_ = v___x_3333_;
v_currNamespace_3358_ = v_currNamespace_3324_;
v_openDecls_3359_ = v_openDecls_3325_;
v_initHeartbeats_3360_ = v___x_3353_;
v_maxHeartbeats_3361_ = v___x_3335_;
v_quotContext_3362_ = v___x_3336_;
v_currMacroScope_3363_ = v___x_3337_;
v_cancelTk_x3f_3364_ = v_cancelTk_x3f_3326_;
v_inheritedTraceOptions_3365_ = v___x_3408_;
v_currRecDepth_3366_ = v___x_3334_;
v_ref_3367_ = v___x_3338_;
v_suppressElabErrors_3368_ = v___x_3340_;
v_checkDeprecated_3369_ = v___x_3341_;
v_isRecordingDeps_3370_ = v___x_3340_;
goto v___jp_3355_;
}
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
lean_object* v_v_3474_; lean_object* v___x_3475_; lean_object* v_bs_x27_3476_; lean_object* v___x_3477_; 
v_v_3474_ = lean_array_uget(v_bs_3467_, v_i_3466_);
v___x_3475_ = lean_unsigned_to_nat(0u);
v_bs_x27_3476_ = lean_array_uset(v_bs_3467_, v_i_3466_, v___x_3475_);
lean_inc_ref(v_x_3464_);
v___x_3477_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3464_, v_v_3474_, v___y_3468_, v___y_3469_, v___y_3470_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; size_t v___x_3479_; size_t v___x_3480_; lean_object* v___x_3481_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
v___x_3479_ = ((size_t)1ULL);
v___x_3480_ = lean_usize_add(v_i_3466_, v___x_3479_);
v___x_3481_ = lean_array_uset(v_bs_x27_3476_, v_i_3466_, v_a_3478_);
v_i_3466_ = v___x_3480_;
v_bs_3467_ = v___x_3481_;
goto _start;
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v_bs_x27_3476_);
lean_dec_ref(v_x_3464_);
v_a_3483_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3477_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3477_);
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
size_t v_sz_boxed_3534_; size_t v___x_3985__boxed_3535_; lean_object* v_res_3536_; 
v_sz_boxed_3534_ = lean_unbox_usize(v_sz_3527_);
lean_dec(v_sz_3527_);
v___x_3985__boxed_3535_ = lean_unbox_usize(v___x_3528_);
lean_dec(v___x_3528_);
v_res_3536_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(v_x_3526_, v_sz_boxed_3534_, v___x_3985__boxed_3535_, v_content_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
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
lean_object* v_container_3830_; 
v_container_3830_ = lean_ctor_get(v_x_3538_, 0);
if (lean_obj_tag(v_container_3830_) == 0)
{
lean_object* v_content_3831_; lean_object* v_val_3832_; lean_object* v___f_3833_; size_t v_sz_3834_; size_t v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v_fallback_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
lean_inc_ref(v_container_3830_);
v_content_3831_ = lean_ctor_get(v_x_3538_, 1);
lean_inc_ref_n(v_content_3831_, 2);
lean_dec_ref_known(v_x_3538_, 2);
v_val_3832_ = lean_ctor_get(v_container_3830_, 0);
lean_inc(v_val_3832_);
lean_dec_ref_known(v_container_3830_, 1);
lean_inc_ref_n(v_x_3537_, 2);
v___f_3833_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3833_, 0, v_x_3537_);
v_sz_3834_ = lean_array_size(v_content_3831_);
v___x_3835_ = ((size_t)0ULL);
v___x_3836_ = lean_box_usize(v_sz_3834_);
v___x_3837_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
v_fallback_3838_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v_fallback_3838_, 0, v_x_3537_);
lean_closure_set(v_fallback_3838_, 1, v___x_3836_);
lean_closure_set(v_fallback_3838_, 2, v___x_3837_);
lean_closure_set(v_fallback_3838_, 3, v_content_3831_);
v___x_3839_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3832_);
v___x_3840_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_3839_, v_a_3540_, v_a_3541_);
lean_dec(v___x_3839_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
if (lean_obj_tag(v_a_3841_) == 0)
{
lean_object* v___x_3842_; 
lean_dec_ref(v_fallback_3838_);
lean_dec_ref(v___f_3833_);
lean_dec(v_val_3832_);
v___x_3842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3537_, v_sz_3834_, v___x_3835_, v_content_3831_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3851_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3845_ = v___x_3842_;
v_isShared_3846_ = v_isSharedCheck_3851_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3851_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3847_; lean_object* v___x_3849_; 
v___x_3847_ = l_Lean_Doc_joinInlines(v_a_3843_);
lean_dec(v_a_3843_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3847_);
v___x_3849_ = v___x_3845_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
v_a_3852_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3842_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3842_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
else
{
lean_object* v_val_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_dec_ref(v_x_3537_);
v_val_3860_ = lean_ctor_get(v_a_3841_, 0);
lean_inc(v_val_3860_);
lean_dec_ref_known(v_a_3841_, 1);
v___x_3861_ = lean_apply_3(v_val_3860_, v___f_3833_, v_val_3832_, v_content_3831_);
v___x_3862_ = l_Lean_Doc_withRendererFallback(v_fallback_3838_, v___x_3861_, v_a_3539_, v_a_3540_, v_a_3541_);
return v___x_3862_;
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_dec_ref(v_fallback_3838_);
lean_dec_ref(v___f_3833_);
lean_dec(v_val_3832_);
lean_dec_ref(v_content_3831_);
lean_dec_ref(v_x_3537_);
v_a_3863_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3840_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3840_);
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
else
{
lean_object* v_content_3871_; size_t v_sz_3872_; size_t v___x_3873_; lean_object* v___x_3874_; 
v_content_3871_ = lean_ctor_get(v_x_3538_, 1);
lean_inc_ref(v_content_3871_);
lean_dec_ref_known(v_x_3538_, 2);
v_sz_3872_ = lean_array_size(v_content_3871_);
v___x_3873_ = ((size_t)0ULL);
v___x_3874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3537_, v_sz_3872_, v___x_3873_, v_content_3871_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3883_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3877_ = v___x_3874_;
v_isShared_3878_ = v_isSharedCheck_3883_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3883_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3879_; lean_object* v___x_3881_; 
v___x_3879_ = l_Lean_Doc_joinInlines(v_a_3875_);
lean_dec(v_a_3875_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v___x_3879_);
v___x_3881_ = v___x_3877_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
v_a_3884_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3874_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3874_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(lean_object* v_x_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3899_, lean_object* v_sz_3900_, lean_object* v_i_3901_, lean_object* v_bs_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
size_t v_sz_boxed_3907_; size_t v_i_boxed_3908_; lean_object* v_res_3909_; 
v_sz_boxed_3907_ = lean_unbox_usize(v_sz_3900_);
lean_dec(v_sz_3900_);
v_i_boxed_3908_ = lean_unbox_usize(v_i_3901_);
lean_dec(v_i_3901_);
v_res_3909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3899_, v_sz_boxed_3907_, v_i_boxed_3908_, v_bs_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed(lean_object* v_x_3910_, lean_object* v_x_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3910_, v_x_3911_, v_a_3912_, v_a_3913_, v_a_3914_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3912_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(lean_object* v___x_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0___boxed(lean_object* v___x_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(v___x_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(lean_object* v_x_3931_, lean_object* v_x_3932_){
_start:
{
lean_object* v_zero_3933_; uint8_t v_isZero_3934_; 
v_zero_3933_ = lean_unsigned_to_nat(0u);
v_isZero_3934_ = lean_nat_dec_eq(v_x_3931_, v_zero_3933_);
if (v_isZero_3934_ == 1)
{
lean_dec(v_x_3931_);
return v_x_3932_;
}
else
{
uint32_t v___x_3935_; lean_object* v_one_3936_; lean_object* v_n_3937_; lean_object* v___x_3938_; 
v___x_3935_ = 32;
v_one_3936_ = lean_unsigned_to_nat(1u);
v_n_3937_ = lean_nat_sub(v_x_3931_, v_one_3936_);
lean_dec(v_x_3931_);
v___x_3938_ = lean_string_push(v_x_3932_, v___x_3935_);
v_x_3931_ = v_n_3937_;
v_x_3932_ = v___x_3938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(size_t v_sz_3940_, size_t v_i_3941_, lean_object* v_bs_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
uint8_t v___x_3947_; 
v___x_3947_ = lean_usize_dec_lt(v_i_3941_, v_sz_3940_);
if (v___x_3947_ == 0)
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v_bs_3942_);
return v___x_3948_;
}
else
{
lean_object* v_v_3949_; lean_object* v___x_3950_; lean_object* v_bs_x27_3951_; size_t v_sz_3952_; size_t v___x_3953_; lean_object* v___x_3954_; 
v_v_3949_ = lean_array_uget(v_bs_3942_, v_i_3941_);
v___x_3950_ = lean_unsigned_to_nat(0u);
v_bs_x27_3951_ = lean_array_uset(v_bs_3942_, v_i_3941_, v___x_3950_);
v_sz_3952_ = lean_array_size(v_v_3949_);
v___x_3953_ = ((size_t)0ULL);
v___x_3954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_3952_, v___x_3953_, v_v_3949_, v___y_3943_, v___y_3944_, v___y_3945_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; size_t v___x_3960_; size_t v___x_3961_; lean_object* v___x_3962_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___x_3954_, 1);
v___x_3956_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_3957_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_3958_ = l_Lean_Doc_joinBlocks(v_a_3955_);
lean_dec(v_a_3955_);
v___x_3959_ = l_Lean_Doc_prefixListLines(v___x_3956_, v___x_3957_, v___x_3958_);
v___x_3960_ = ((size_t)1ULL);
v___x_3961_ = lean_usize_add(v_i_3941_, v___x_3960_);
v___x_3962_ = lean_array_uset(v_bs_x27_3951_, v_i_3941_, v___x_3959_);
v_i_3941_ = v___x_3961_;
v_bs_3942_ = v___x_3962_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_3951_);
return v___x_3954_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(lean_object* v_as_3964_, size_t v_sz_3965_, size_t v_i_3966_, lean_object* v_b_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
uint8_t v___x_3972_; 
v___x_3972_ = lean_usize_dec_lt(v_i_3966_, v_sz_3965_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; 
v___x_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3973_, 0, v_b_3967_);
return v___x_3973_;
}
else
{
lean_object* v_fst_3974_; lean_object* v_snd_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_4009_; 
v_fst_3974_ = lean_ctor_get(v_b_3967_, 0);
v_snd_3975_ = lean_ctor_get(v_b_3967_, 1);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_b_3967_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3977_ = v_b_3967_;
v_isShared_3978_ = v_isSharedCheck_4009_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_snd_3975_);
lean_inc(v_fst_3974_);
lean_dec(v_b_3967_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_4009_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v_a_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; size_t v_sz_3987_; size_t v___x_3988_; lean_object* v___x_3989_; 
v___x_3979_ = lean_unsigned_to_nat(1u);
v_a_3980_ = lean_array_uget_borrowed(v_as_3964_, v_i_3966_);
lean_inc(v_snd_3975_);
v___x_3981_ = l_Nat_reprFast(v_snd_3975_);
v___x_3982_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_3983_ = lean_string_append(v___x_3981_, v___x_3982_);
v___x_3984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_3985_ = lean_string_utf8_byte_size(v___x_3983_);
v___x_3986_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(v___x_3985_, v___x_3984_);
v_sz_3987_ = lean_array_size(v_a_3980_);
v___x_3988_ = ((size_t)0ULL);
lean_inc(v_a_3980_);
v___x_3989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_3987_, v___x_3988_, v_a_3980_, v___y_3968_, v___y_3969_, v___y_3970_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3996_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref_known(v___x_3989_, 1);
v___x_3991_ = l_Lean_Doc_joinBlocks(v_a_3990_);
lean_dec(v_a_3990_);
v___x_3992_ = l_Lean_Doc_prefixListLines(v___x_3983_, v___x_3986_, v___x_3991_);
v___x_3993_ = lean_array_push(v_fst_3974_, v___x_3992_);
v___x_3994_ = lean_nat_add(v_snd_3975_, v___x_3979_);
lean_dec(v_snd_3975_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 1, v___x_3994_);
lean_ctor_set(v___x_3977_, 0, v___x_3993_);
v___x_3996_ = v___x_3977_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3993_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
size_t v___x_3997_; size_t v___x_3998_; 
v___x_3997_ = ((size_t)1ULL);
v___x_3998_ = lean_usize_add(v_i_3966_, v___x_3997_);
v_i_3966_ = v___x_3998_;
v_b_3967_ = v___x_3996_;
goto _start;
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec_ref(v___x_3986_);
lean_dec_ref(v___x_3983_);
lean_del_object(v___x_3977_);
lean_dec(v_snd_3975_);
lean_dec(v_fst_3974_);
v_a_4001_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3989_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3989_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(size_t v_sz_4010_, size_t v_i_4011_, lean_object* v_bs_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
uint8_t v___x_4017_; 
v___x_4017_ = lean_usize_dec_lt(v_i_4011_, v_sz_4010_);
if (v___x_4017_ == 0)
{
lean_object* v___x_4018_; 
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v_bs_4012_);
return v___x_4018_;
}
else
{
lean_object* v_v_4019_; lean_object* v___x_4020_; lean_object* v_term_4021_; lean_object* v_desc_4022_; lean_object* v___x_4023_; lean_object* v_bs_x27_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v_v_4019_ = lean_array_uget_borrowed(v_bs_4012_, v_i_4011_);
v___x_4020_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_4021_ = lean_ctor_get(v_v_4019_, 0);
lean_inc_ref(v_term_4021_);
v_desc_4022_ = lean_ctor_get(v_v_4019_, 1);
lean_inc_ref(v_desc_4022_);
v___x_4023_ = lean_unsigned_to_nat(0u);
v_bs_x27_4024_ = lean_array_uset(v_bs_4012_, v_i_4011_, v___x_4023_);
v___x_4025_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4025_, 0, v_term_4021_);
v___x_4026_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4020_, v___x_4025_, v___y_4013_, v___y_4014_, v___y_4015_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; size_t v_sz_4028_; size_t v___x_4029_; lean_object* v___x_4030_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref_known(v___x_4026_, 1);
v_sz_4028_ = lean_array_size(v_desc_4022_);
v___x_4029_ = ((size_t)0ULL);
lean_inc_ref(v_desc_4022_);
v___x_4030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4028_, v___x_4029_, v_desc_4022_, v___y_4013_, v___y_4014_, v___y_4015_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___y_4033_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; uint8_t v___x_4050_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
lean_dec_ref_known(v___x_4030_, 1);
v___x_4041_ = lean_unsigned_to_nat(1u);
v___x_4042_ = lean_mk_empty_array_with_capacity(v___x_4041_);
v___x_4043_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_4044_ = lean_unsigned_to_nat(2u);
v___x_4045_ = lean_mk_empty_array_with_capacity(v___x_4044_);
v___x_4046_ = lean_array_push(v___x_4045_, v_a_4027_);
v___x_4047_ = lean_array_push(v___x_4046_, v___x_4043_);
v___x_4048_ = l_Lean_Doc_joinInlines(v___x_4047_);
lean_dec_ref(v___x_4047_);
v___x_4049_ = lean_array_get_size(v_desc_4022_);
lean_dec_ref(v_desc_4022_);
v___x_4050_ = lean_nat_dec_le(v___x_4049_, v___x_4041_);
if (v___x_4050_ == 0)
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4051_ = lean_array_push(v___x_4042_, v___x_4048_);
v___x_4052_ = l_Array_append___redArg(v___x_4051_, v_a_4031_);
lean_dec(v_a_4031_);
v___x_4053_ = l_Lean_Doc_joinBlocks(v___x_4052_);
lean_dec_ref(v___x_4052_);
v___y_4033_ = v___x_4053_;
goto v___jp_4032_;
}
else
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
lean_dec_ref(v___x_4042_);
v___x_4054_ = l_Lean_Doc_joinBlocks(v_a_4031_);
lean_dec(v_a_4031_);
v___x_4055_ = l_Array_append___redArg(v___x_4048_, v___x_4054_);
lean_dec_ref(v___x_4054_);
v___y_4033_ = v___x_4055_;
goto v___jp_4032_;
}
v___jp_4032_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; size_t v___x_4037_; size_t v___x_4038_; lean_object* v___x_4039_; 
v___x_4034_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_4035_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_4036_ = l_Lean_Doc_prefixListLines(v___x_4034_, v___x_4035_, v___y_4033_);
v___x_4037_ = ((size_t)1ULL);
v___x_4038_ = lean_usize_add(v_i_4011_, v___x_4037_);
v___x_4039_ = lean_array_uset(v_bs_x27_4024_, v_i_4011_, v___x_4036_);
v_i_4011_ = v___x_4038_;
v_bs_4012_ = v___x_4039_;
goto _start;
}
}
else
{
lean_dec(v_a_4027_);
lean_dec_ref(v_bs_x27_4024_);
lean_dec_ref(v_desc_4022_);
return v___x_4030_;
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec_ref(v_bs_x27_4024_);
lean_dec_ref(v_desc_4022_);
v_a_4056_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4026_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4026_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed(lean_object* v_x_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_x_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
lean_dec(v_a_4067_);
lean_dec_ref(v_a_4066_);
lean_dec(v_a_4065_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed(lean_object* v_sz_4072_, lean_object* v___x_4073_, lean_object* v_content_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
size_t v_sz_boxed_4079_; size_t v___x_4840__boxed_4080_; lean_object* v_res_4081_; 
v_sz_boxed_4079_ = lean_unbox_usize(v_sz_4072_);
lean_dec(v_sz_4072_);
v___x_4840__boxed_4080_ = lean_unbox_usize(v___x_4073_);
lean_dec(v___x_4073_);
v_res_4081_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(v_sz_boxed_4079_, v___x_4840__boxed_4080_, v_content_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(lean_object* v_x_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_){
_start:
{
switch(lean_obj_tag(v_x_4082_))
{
case 0:
{
lean_object* v_contents_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4096_; 
v_contents_4087_ = lean_ctor_get(v_x_4082_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_x_4082_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4089_ = v_x_4082_;
v_isShared_4090_ = v_isSharedCheck_4096_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_contents_4087_);
lean_dec(v_x_4082_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4096_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4091_; lean_object* v___x_4093_; 
v___x_4091_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_4090_ == 0)
{
lean_ctor_set_tag(v___x_4089_, 9);
v___x_4093_ = v___x_4089_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_contents_4087_);
v___x_4093_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
lean_object* v___x_4094_; 
v___x_4094_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4091_, v___x_4093_, v_a_4083_, v_a_4084_, v_a_4085_);
return v___x_4094_;
}
}
}
case 1:
{
lean_object* v_content_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4105_; 
v_content_4097_ = lean_ctor_get(v_x_4082_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_x_4082_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4099_ = v_x_4082_;
v_isShared_4100_ = v_isSharedCheck_4105_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_content_4097_);
lean_dec(v_x_4082_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4105_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4101_; lean_object* v___x_4103_; 
v___x_4101_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_4097_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set_tag(v___x_4099_, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4101_);
v___x_4103_ = v___x_4099_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v___x_4101_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
case 2:
{
lean_object* v_items_4106_; size_t v_sz_4107_; size_t v___x_4108_; lean_object* v___x_4109_; 
v_items_4106_ = lean_ctor_get(v_x_4082_, 0);
lean_inc_ref(v_items_4106_);
lean_dec_ref_known(v_x_4082_, 1);
v_sz_4107_ = lean_array_size(v_items_4106_);
v___x_4108_ = ((size_t)0ULL);
v___x_4109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_4107_, v___x_4108_, v_items_4106_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4118_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4112_ = v___x_4109_;
v_isShared_4113_ = v_isSharedCheck_4118_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4109_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4118_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4114_; lean_object* v___x_4116_; 
v___x_4114_ = l_Lean_Doc_joinBlocks(v_a_4110_);
lean_dec(v_a_4110_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 0, v___x_4114_);
v___x_4116_ = v___x_4112_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4114_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
v_a_4119_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4109_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4109_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
case 3:
{
lean_object* v_start_4127_; lean_object* v_items_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4162_; 
v_start_4127_ = lean_ctor_get(v_x_4082_, 0);
v_items_4128_ = lean_ctor_get(v_x_4082_, 1);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_x_4082_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4130_ = v_x_4082_;
v_isShared_4131_ = v_isSharedCheck_4162_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_items_4128_);
lean_inc(v_start_4127_);
lean_dec(v_x_4082_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4162_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v_out_4132_; lean_object* v___y_4134_; lean_object* v___x_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; 
v_out_4132_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_4159_ = lean_unsigned_to_nat(1u);
v___x_4160_ = l_Int_toNat(v_start_4127_);
lean_dec(v_start_4127_);
v___x_4161_ = lean_nat_dec_le(v___x_4159_, v___x_4160_);
if (v___x_4161_ == 0)
{
lean_dec(v___x_4160_);
v___y_4134_ = v___x_4159_;
goto v___jp_4133_;
}
else
{
v___y_4134_ = v___x_4160_;
goto v___jp_4133_;
}
v___jp_4133_:
{
lean_object* v___x_4136_; 
if (v_isShared_4131_ == 0)
{
lean_ctor_set_tag(v___x_4130_, 0);
lean_ctor_set(v___x_4130_, 1, v___y_4134_);
lean_ctor_set(v___x_4130_, 0, v_out_4132_);
v___x_4136_ = v___x_4130_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_out_4132_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v___y_4134_);
v___x_4136_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
size_t v_sz_4137_; size_t v___x_4138_; lean_object* v___x_4139_; 
v_sz_4137_ = lean_array_size(v_items_4128_);
v___x_4138_ = ((size_t)0ULL);
v___x_4139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_items_4128_, v_sz_4137_, v___x_4138_, v___x_4136_, v_a_4083_, v_a_4084_, v_a_4085_);
lean_dec_ref(v_items_4128_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4149_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4142_ = v___x_4139_;
v_isShared_4143_ = v_isSharedCheck_4149_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4139_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4149_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v_fst_4144_; lean_object* v___x_4145_; lean_object* v___x_4147_; 
v_fst_4144_ = lean_ctor_get(v_a_4140_, 0);
lean_inc(v_fst_4144_);
lean_dec(v_a_4140_);
v___x_4145_ = l_Lean_Doc_joinBlocks(v_fst_4144_);
lean_dec(v_fst_4144_);
if (v_isShared_4143_ == 0)
{
lean_ctor_set(v___x_4142_, 0, v___x_4145_);
v___x_4147_ = v___x_4142_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
v_a_4150_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4139_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4139_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_4163_; size_t v_sz_4164_; size_t v___x_4165_; lean_object* v___x_4166_; 
v_items_4163_ = lean_ctor_get(v_x_4082_, 0);
lean_inc_ref(v_items_4163_);
lean_dec_ref_known(v_x_4082_, 1);
v_sz_4164_ = lean_array_size(v_items_4163_);
v___x_4165_ = ((size_t)0ULL);
v___x_4166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_4164_, v___x_4165_, v_items_4163_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4175_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4169_ = v___x_4166_;
v_isShared_4170_ = v_isSharedCheck_4175_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4166_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4175_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4171_; lean_object* v___x_4173_; 
v___x_4171_ = l_Lean_Doc_joinBlocks(v_a_4167_);
lean_dec(v_a_4167_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 0, v___x_4171_);
v___x_4173_ = v___x_4169_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
v_a_4176_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4166_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4166_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
case 5:
{
lean_object* v_items_4184_; size_t v_sz_4185_; size_t v___x_4186_; lean_object* v___x_4187_; 
v_items_4184_ = lean_ctor_get(v_x_4082_, 0);
lean_inc_ref(v_items_4184_);
lean_dec_ref_known(v_x_4082_, 1);
v_sz_4185_ = lean_array_size(v_items_4184_);
v___x_4186_ = ((size_t)0ULL);
v___x_4187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4185_, v___x_4186_, v_items_4184_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4198_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4190_ = v___x_4187_;
v_isShared_4191_ = v_isSharedCheck_4198_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4187_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4198_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4196_; 
v___x_4192_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_4193_ = l_Lean_Doc_joinBlocks(v_a_4188_);
lean_dec(v_a_4188_);
v___x_4194_ = l_Lean_Doc_prefixLines(v___x_4192_, v___x_4193_);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v___x_4194_);
v___x_4196_ = v___x_4190_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4194_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
v_a_4199_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4187_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4187_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
case 6:
{
lean_object* v_content_4207_; size_t v_sz_4208_; size_t v___x_4209_; lean_object* v___x_4210_; 
v_content_4207_ = lean_ctor_get(v_x_4082_, 0);
lean_inc_ref(v_content_4207_);
lean_dec_ref_known(v_x_4082_, 1);
v_sz_4208_ = lean_array_size(v_content_4207_);
v___x_4209_ = ((size_t)0ULL);
v___x_4210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4208_, v___x_4209_, v_content_4207_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4219_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4213_ = v___x_4210_;
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4215_; lean_object* v___x_4217_; 
v___x_4215_ = l_Lean_Doc_joinBlocks(v_a_4211_);
lean_dec(v_a_4211_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4215_);
v___x_4217_ = v___x_4213_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
else
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
v_a_4220_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4222_ = v___x_4210_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4210_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4220_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
default: 
{
lean_object* v_container_4228_; 
v_container_4228_ = lean_ctor_get(v_x_4082_, 0);
if (lean_obj_tag(v_container_4228_) == 0)
{
lean_object* v_content_4229_; lean_object* v_val_4230_; lean_object* v___f_4231_; lean_object* v___f_4232_; size_t v_sz_4233_; size_t v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v_fallback_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
lean_inc_ref(v_container_4228_);
v_content_4229_ = lean_ctor_get(v_x_4082_, 1);
lean_inc_ref_n(v_content_4229_, 2);
lean_dec_ref_known(v_x_4082_, 2);
v_val_4230_ = lean_ctor_get(v_container_4228_, 0);
lean_inc(v_val_4230_);
lean_dec_ref_known(v_container_4228_, 1);
v___f_4231_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed), 5, 0);
v___f_4232_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___closed__0));
v_sz_4233_ = lean_array_size(v_content_4229_);
v___x_4234_ = ((size_t)0ULL);
v___x_4235_ = lean_box_usize(v_sz_4233_);
v___x_4236_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
v_fallback_4237_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_fallback_4237_, 0, v___x_4235_);
lean_closure_set(v_fallback_4237_, 1, v___x_4236_);
lean_closure_set(v_fallback_4237_, 2, v_content_4229_);
v___x_4238_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_4230_);
v___x_4239_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_4238_, v_a_4084_, v_a_4085_);
lean_dec(v___x_4238_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v_a_4240_; 
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_a_4240_);
lean_dec_ref_known(v___x_4239_, 1);
if (lean_obj_tag(v_a_4240_) == 0)
{
lean_object* v___x_4241_; 
lean_dec_ref(v_fallback_4237_);
lean_dec_ref(v___f_4231_);
lean_dec(v_val_4230_);
v___x_4241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4233_, v___x_4234_, v_content_4229_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4250_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4244_ = v___x_4241_;
v_isShared_4245_ = v_isSharedCheck_4250_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4241_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4250_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4246_; lean_object* v___x_4248_; 
v___x_4246_ = l_Lean_Doc_joinBlocks(v_a_4242_);
lean_dec(v_a_4242_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4246_);
v___x_4248_ = v___x_4244_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4246_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
v_a_4251_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4241_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4241_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
else
{
lean_object* v_val_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v_val_4259_ = lean_ctor_get(v_a_4240_, 0);
lean_inc(v_val_4259_);
lean_dec_ref_known(v_a_4240_, 1);
v___x_4260_ = lean_apply_4(v_val_4259_, v___f_4232_, v___f_4231_, v_val_4230_, v_content_4229_);
v___x_4261_ = l_Lean_Doc_withRendererFallback(v_fallback_4237_, v___x_4260_, v_a_4083_, v_a_4084_, v_a_4085_);
return v___x_4261_;
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
lean_dec_ref(v_fallback_4237_);
lean_dec_ref(v___f_4231_);
lean_dec(v_val_4230_);
lean_dec_ref(v_content_4229_);
v_a_4262_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4239_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4239_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
else
{
lean_object* v_content_4270_; size_t v_sz_4271_; size_t v___x_4272_; lean_object* v___x_4273_; 
v_content_4270_ = lean_ctor_get(v_x_4082_, 1);
lean_inc_ref(v_content_4270_);
lean_dec_ref_known(v_x_4082_, 2);
v_sz_4271_ = lean_array_size(v_content_4270_);
v___x_4272_ = ((size_t)0ULL);
v___x_4273_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4271_, v___x_4272_, v_content_4270_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4282_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4276_ = v___x_4273_;
v_isShared_4277_ = v_isSharedCheck_4282_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4273_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4282_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4278_; lean_object* v___x_4280_; 
v___x_4278_ = l_Lean_Doc_joinBlocks(v_a_4274_);
lean_dec(v_a_4274_);
if (v_isShared_4277_ == 0)
{
lean_ctor_set(v___x_4276_, 0, v___x_4278_);
v___x_4280_ = v___x_4276_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4278_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
v_a_4283_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4273_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4273_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(size_t v_sz_4291_, size_t v_i_4292_, lean_object* v_bs_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
uint8_t v___x_4298_; 
v___x_4298_ = lean_usize_dec_lt(v_i_4292_, v_sz_4291_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4299_; 
v___x_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4299_, 0, v_bs_4293_);
return v___x_4299_;
}
else
{
lean_object* v_v_4300_; lean_object* v___x_4301_; lean_object* v_bs_x27_4302_; lean_object* v___x_4303_; 
v_v_4300_ = lean_array_uget(v_bs_4293_, v_i_4292_);
v___x_4301_ = lean_unsigned_to_nat(0u);
v_bs_x27_4302_ = lean_array_uset(v_bs_4293_, v_i_4292_, v___x_4301_);
v___x_4303_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_v_4300_, v___y_4294_, v___y_4295_, v___y_4296_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; size_t v___x_4305_; size_t v___x_4306_; lean_object* v___x_4307_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
lean_dec_ref_known(v___x_4303_, 1);
v___x_4305_ = ((size_t)1ULL);
v___x_4306_ = lean_usize_add(v_i_4292_, v___x_4305_);
v___x_4307_ = lean_array_uset(v_bs_x27_4302_, v_i_4292_, v_a_4304_);
v_i_4292_ = v___x_4306_;
v_bs_4293_ = v___x_4307_;
goto _start;
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec_ref(v_bs_x27_4302_);
v_a_4309_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4303_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4303_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(size_t v_sz_4317_, size_t v___x_4318_, lean_object* v_content_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4317_, v___x_4318_, v_content_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4333_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4327_ = v___x_4324_;
v_isShared_4328_ = v_isSharedCheck_4333_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4324_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4333_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4329_; lean_object* v___x_4331_; 
v___x_4329_ = l_Lean_Doc_joinBlocks(v_a_4325_);
lean_dec(v_a_4325_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4329_);
v___x_4331_ = v___x_4327_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4329_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
v_a_4334_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4324_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4324_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2___boxed(lean_object* v_sz_4342_, lean_object* v_i_4343_, lean_object* v_bs_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
size_t v_sz_boxed_4349_; size_t v_i_boxed_4350_; lean_object* v_res_4351_; 
v_sz_boxed_4349_ = lean_unbox_usize(v_sz_4342_);
lean_dec(v_sz_4342_);
v_i_boxed_4350_ = lean_unbox_usize(v_i_4343_);
lean_dec(v_i_4343_);
v_res_4351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_boxed_4349_, v_i_boxed_4350_, v_bs_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___y_4345_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5___boxed(lean_object* v_sz_4352_, lean_object* v_i_4353_, lean_object* v_bs_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
size_t v_sz_boxed_4359_; size_t v_i_boxed_4360_; lean_object* v_res_4361_; 
v_sz_boxed_4359_ = lean_unbox_usize(v_sz_4352_);
lean_dec(v_sz_4352_);
v_i_boxed_4360_ = lean_unbox_usize(v_i_4353_);
lean_dec(v_i_4353_);
v_res_4361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_boxed_4359_, v_i_boxed_4360_, v_bs_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7___boxed(lean_object* v_as_4362_, lean_object* v_sz_4363_, lean_object* v_i_4364_, lean_object* v_b_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
size_t v_sz_boxed_4370_; size_t v_i_boxed_4371_; lean_object* v_res_4372_; 
v_sz_boxed_4370_ = lean_unbox_usize(v_sz_4363_);
lean_dec(v_sz_4363_);
v_i_boxed_4371_ = lean_unbox_usize(v_i_4364_);
lean_dec(v_i_4364_);
v_res_4372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_as_4362_, v_sz_boxed_4370_, v_i_boxed_4371_, v_b_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v_as_4362_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8___boxed(lean_object* v_sz_4373_, lean_object* v_i_4374_, lean_object* v_bs_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_){
_start:
{
size_t v_sz_boxed_4380_; size_t v_i_boxed_4381_; lean_object* v_res_4382_; 
v_sz_boxed_4380_ = lean_unbox_usize(v_sz_4373_);
lean_dec(v_sz_4373_);
v_i_boxed_4381_ = lean_unbox_usize(v_i_4374_);
lean_dec(v_i_4374_);
v_res_4382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_boxed_4380_, v_i_boxed_4381_, v_bs_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4376_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(size_t v_sz_4383_, size_t v_i_4384_, lean_object* v_bs_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
uint8_t v___x_4390_; 
v___x_4390_ = lean_usize_dec_lt(v_i_4384_, v_sz_4383_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; 
v___x_4391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4391_, 0, v_bs_4385_);
return v___x_4391_;
}
else
{
lean_object* v_v_4392_; lean_object* v___x_4393_; lean_object* v_bs_x27_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v_v_4392_ = lean_array_uget(v_bs_4385_, v_i_4384_);
v___x_4393_ = lean_unsigned_to_nat(0u);
v_bs_x27_4394_ = lean_array_uset(v_bs_4385_, v_i_4384_, v___x_4393_);
v___x_4395_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_4396_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4395_, v_v_4392_, v___y_4386_, v___y_4387_, v___y_4388_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; size_t v___x_4398_; size_t v___x_4399_; lean_object* v___x_4400_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_a_4397_);
lean_dec_ref_known(v___x_4396_, 1);
v___x_4398_ = ((size_t)1ULL);
v___x_4399_ = lean_usize_add(v_i_4384_, v___x_4398_);
v___x_4400_ = lean_array_uset(v_bs_x27_4394_, v_i_4384_, v_a_4397_);
v_i_4384_ = v___x_4399_;
v_bs_4385_ = v___x_4400_;
goto _start;
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_dec_ref(v_bs_x27_4394_);
v_a_4402_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4396_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4396_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1___boxed(lean_object* v_sz_4410_, lean_object* v_i_4411_, lean_object* v_bs_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
size_t v_sz_boxed_4417_; size_t v_i_boxed_4418_; lean_object* v_res_4419_; 
v_sz_boxed_4417_ = lean_unbox_usize(v_sz_4410_);
lean_dec(v_sz_4410_);
v_i_boxed_4418_ = lean_unbox_usize(v_i_4411_);
lean_dec(v_i_4411_);
v_res_4419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_boxed_4417_, v_i_boxed_4418_, v_bs_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
lean_dec(v___y_4415_);
lean_dec_ref(v___y_4414_);
lean_dec(v___y_4413_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(lean_object* v_x_4420_, lean_object* v_x_4421_){
_start:
{
lean_object* v_zero_4422_; uint8_t v_isZero_4423_; 
v_zero_4422_ = lean_unsigned_to_nat(0u);
v_isZero_4423_ = lean_nat_dec_eq(v_x_4420_, v_zero_4422_);
if (v_isZero_4423_ == 1)
{
lean_dec(v_x_4420_);
return v_x_4421_;
}
else
{
uint32_t v___x_4424_; lean_object* v_one_4425_; lean_object* v_n_4426_; lean_object* v___x_4427_; 
v___x_4424_ = 35;
v_one_4425_ = lean_unsigned_to_nat(1u);
v_n_4426_ = lean_nat_sub(v_x_4420_, v_one_4425_);
lean_dec(v_x_4420_);
v___x_4427_ = lean_string_push(v_x_4421_, v___x_4424_);
v_x_4420_ = v_n_4426_;
v_x_4421_ = v___x_4427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(lean_object* v_level_4429_, lean_object* v_part_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_){
_start:
{
lean_object* v_title_4435_; lean_object* v_content_4436_; lean_object* v_subParts_4437_; size_t v_sz_4438_; size_t v___x_4439_; lean_object* v___x_4440_; 
v_title_4435_ = lean_ctor_get(v_part_4430_, 0);
lean_inc_ref(v_title_4435_);
v_content_4436_ = lean_ctor_get(v_part_4430_, 3);
lean_inc_ref(v_content_4436_);
v_subParts_4437_ = lean_ctor_get(v_part_4430_, 4);
lean_inc_ref(v_subParts_4437_);
lean_dec_ref(v_part_4430_);
v_sz_4438_ = lean_array_size(v_title_4435_);
v___x_4439_ = ((size_t)0ULL);
v___x_4440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_4438_, v___x_4439_, v_title_4435_, v_a_4431_, v_a_4432_, v_a_4433_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_a_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; size_t v_sz_4453_; lean_object* v___x_4454_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
lean_dec_ref_known(v___x_4440_, 1);
v___x_4442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4443_ = lean_unsigned_to_nat(1u);
v___x_4444_ = lean_nat_add(v_level_4429_, v___x_4443_);
lean_inc(v___x_4444_);
v___x_4445_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(v___x_4444_, v___x_4442_);
v___x_4446_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_4447_ = lean_string_append(v___x_4445_, v___x_4446_);
v___x_4448_ = lean_mk_empty_array_with_capacity(v___x_4443_);
lean_inc_ref_n(v___x_4448_, 2);
v___x_4449_ = lean_array_push(v___x_4448_, v___x_4447_);
v___x_4450_ = lean_array_push(v___x_4448_, v___x_4449_);
v___x_4451_ = l_Array_append___redArg(v___x_4450_, v_a_4441_);
lean_dec(v_a_4441_);
v___x_4452_ = l_Lean_Doc_joinInlines(v___x_4451_);
lean_dec_ref(v___x_4451_);
v_sz_4453_ = lean_array_size(v_content_4436_);
v___x_4454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4453_, v___x_4439_, v_content_4436_, v_a_4431_, v_a_4432_, v_a_4433_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; size_t v_sz_4456_; lean_object* v___x_4457_; 
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_a_4455_);
lean_dec_ref_known(v___x_4454_, 1);
v_sz_4456_ = lean_array_size(v_subParts_4437_);
v___x_4457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4444_, v_sz_4456_, v___x_4439_, v_subParts_4437_, v_a_4431_, v_a_4432_, v_a_4433_);
lean_dec(v___x_4444_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4469_; 
v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4460_ = v___x_4457_;
v_isShared_4461_ = v_isSharedCheck_4469_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4457_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4469_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4467_; 
v___x_4462_ = lean_array_push(v___x_4448_, v___x_4452_);
v___x_4463_ = l_Array_append___redArg(v___x_4462_, v_a_4455_);
lean_dec(v_a_4455_);
v___x_4464_ = l_Array_append___redArg(v___x_4463_, v_a_4458_);
lean_dec(v_a_4458_);
v___x_4465_ = l_Lean_Doc_joinBlocks(v___x_4464_);
lean_dec_ref(v___x_4464_);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 0, v___x_4465_);
v___x_4467_ = v___x_4460_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4465_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec(v_a_4455_);
lean_dec_ref(v___x_4452_);
lean_dec_ref(v___x_4448_);
v_a_4470_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4457_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4457_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
lean_dec_ref(v___x_4452_);
lean_dec_ref(v___x_4448_);
lean_dec(v___x_4444_);
lean_dec_ref(v_subParts_4437_);
v_a_4478_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4454_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4454_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
lean_dec_ref(v_subParts_4437_);
lean_dec_ref(v_content_4436_);
v_a_4486_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4440_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4440_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(lean_object* v___x_4494_, size_t v_sz_4495_, size_t v_i_4496_, lean_object* v_bs_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
uint8_t v___x_4502_; 
v___x_4502_ = lean_usize_dec_lt(v_i_4496_, v_sz_4495_);
if (v___x_4502_ == 0)
{
lean_object* v___x_4503_; 
v___x_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4503_, 0, v_bs_4497_);
return v___x_4503_;
}
else
{
lean_object* v_v_4504_; lean_object* v___x_4505_; lean_object* v_bs_x27_4506_; lean_object* v___x_4507_; 
v_v_4504_ = lean_array_uget(v_bs_4497_, v_i_4496_);
v___x_4505_ = lean_unsigned_to_nat(0u);
v_bs_x27_4506_ = lean_array_uset(v_bs_4497_, v_i_4496_, v___x_4505_);
v___x_4507_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4494_, v_v_4504_, v___y_4498_, v___y_4499_, v___y_4500_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; size_t v___x_4509_; size_t v___x_4510_; lean_object* v___x_4511_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4508_);
lean_dec_ref_known(v___x_4507_, 1);
v___x_4509_ = ((size_t)1ULL);
v___x_4510_ = lean_usize_add(v_i_4496_, v___x_4509_);
v___x_4511_ = lean_array_uset(v_bs_x27_4506_, v_i_4496_, v_a_4508_);
v_i_4496_ = v___x_4510_;
v_bs_4497_ = v___x_4511_;
goto _start;
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
lean_dec_ref(v_bs_x27_4506_);
v_a_4513_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4507_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4507_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg___boxed(lean_object* v___x_4521_, lean_object* v_sz_4522_, lean_object* v_i_4523_, lean_object* v_bs_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
size_t v_sz_boxed_4529_; size_t v_i_boxed_4530_; lean_object* v_res_4531_; 
v_sz_boxed_4529_ = lean_unbox_usize(v_sz_4522_);
lean_dec(v_sz_4522_);
v_i_boxed_4530_ = lean_unbox_usize(v_i_4523_);
lean_dec(v_i_4523_);
v_res_4531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4521_, v_sz_boxed_4529_, v_i_boxed_4530_, v_bs_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec(v___x_4521_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg___boxed(lean_object* v_level_4532_, lean_object* v_part_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4532_, v_part_4533_, v_a_4534_, v_a_4535_, v_a_4536_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
lean_dec(v_a_4534_);
lean_dec(v_level_4532_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(size_t v_sz_4539_, size_t v_i_4540_, lean_object* v_bs_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
uint8_t v___x_4546_; 
v___x_4546_ = lean_usize_dec_lt(v_i_4540_, v_sz_4539_);
if (v___x_4546_ == 0)
{
lean_object* v___x_4547_; 
v___x_4547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4547_, 0, v_bs_4541_);
return v___x_4547_;
}
else
{
lean_object* v_v_4548_; lean_object* v___x_4549_; lean_object* v_bs_x27_4550_; lean_object* v___x_4551_; 
v_v_4548_ = lean_array_uget(v_bs_4541_, v_i_4540_);
v___x_4549_ = lean_unsigned_to_nat(0u);
v_bs_x27_4550_ = lean_array_uset(v_bs_4541_, v_i_4540_, v___x_4549_);
v___x_4551_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4549_, v_v_4548_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v_a_4552_; size_t v___x_4553_; size_t v___x_4554_; lean_object* v___x_4555_; 
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
lean_dec_ref_known(v___x_4551_, 1);
v___x_4553_ = ((size_t)1ULL);
v___x_4554_ = lean_usize_add(v_i_4540_, v___x_4553_);
v___x_4555_ = lean_array_uset(v_bs_x27_4550_, v_i_4540_, v_a_4552_);
v_i_4540_ = v___x_4554_;
v_bs_4541_ = v___x_4555_;
goto _start;
}
else
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
lean_dec_ref(v_bs_x27_4550_);
v_a_4557_ = lean_ctor_get(v___x_4551_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4559_ = v___x_4551_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4551_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4557_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3___boxed(lean_object* v_sz_4565_, lean_object* v_i_4566_, lean_object* v_bs_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
size_t v_sz_boxed_4572_; size_t v_i_boxed_4573_; lean_object* v_res_4574_; 
v_sz_boxed_4572_ = lean_unbox_usize(v_sz_4565_);
lean_dec(v_sz_4565_);
v_i_boxed_4573_ = lean_unbox_usize(v_i_4566_);
lean_dec(v_i_4566_);
v_res_4574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_boxed_4572_, v_i_boxed_4573_, v_bs_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0(lean_object* v_val_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v_text_4580_; lean_object* v_subsections_4581_; size_t v_sz_4582_; size_t v___x_4583_; lean_object* v___x_4584_; 
v_text_4580_ = lean_ctor_get(v_val_4575_, 0);
lean_inc_ref(v_text_4580_);
v_subsections_4581_ = lean_ctor_get(v_val_4575_, 1);
lean_inc_ref(v_subsections_4581_);
lean_dec_ref(v_val_4575_);
v_sz_4582_ = lean_array_size(v_text_4580_);
v___x_4583_ = ((size_t)0ULL);
v___x_4584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4582_, v___x_4583_, v_text_4580_, v___y_4576_, v___y_4577_, v___y_4578_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_object* v_a_4585_; size_t v_sz_4586_; lean_object* v___x_4587_; 
v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
lean_inc(v_a_4585_);
lean_dec_ref_known(v___x_4584_, 1);
v_sz_4586_ = lean_array_size(v_subsections_4581_);
v___x_4587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_4586_, v___x_4583_, v_subsections_4581_, v___y_4576_, v___y_4577_, v___y_4578_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4597_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4590_ = v___x_4587_;
v_isShared_4591_ = v_isSharedCheck_4597_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4587_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4597_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4595_; 
v___x_4592_ = l_Array_append___redArg(v_a_4585_, v_a_4588_);
lean_dec(v_a_4588_);
v___x_4593_ = l_Lean_Doc_joinBlocks(v___x_4592_);
lean_dec_ref(v___x_4592_);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 0, v___x_4593_);
v___x_4595_ = v___x_4590_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4593_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
else
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4605_; 
lean_dec(v_a_4585_);
v_a_4598_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4600_ = v___x_4587_;
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4587_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4603_; 
if (v_isShared_4601_ == 0)
{
v___x_4603_ = v___x_4600_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_a_4598_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
}
}
else
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4613_; 
lean_dec_ref(v_subsections_4581_);
v_a_4606_ = lean_ctor_get(v___x_4584_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4608_ = v___x_4584_;
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4584_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4611_; 
if (v_isShared_4609_ == 0)
{
v___x_4611_ = v___x_4608_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4606_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0___boxed(lean_object* v_val_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l_Lean_findSimpleDocString_x3f___lam__0(v_val_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_4620_, lean_object* v_declName_4621_, uint8_t v_includeBuiltin_4622_, lean_object* v_options_4623_, lean_object* v_currNamespace_4624_, lean_object* v_openDecls_4625_, lean_object* v_cancelTk_x3f_4626_){
_start:
{
lean_object* v___x_4628_; 
lean_inc_ref(v_env_4620_);
v___x_4628_ = l_Lean_findInternalDocString_x3f(v_env_4620_, v_declName_4621_, v_includeBuiltin_4622_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4672_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4631_ = v___x_4628_;
v_isShared_4632_ = v_isSharedCheck_4672_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4628_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4672_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
if (lean_obj_tag(v_a_4629_) == 0)
{
lean_object* v___x_4633_; lean_object* v___x_4635_; 
lean_dec(v_cancelTk_x3f_4626_);
lean_dec(v_openDecls_4625_);
lean_dec(v_currNamespace_4624_);
lean_dec_ref(v_options_4623_);
lean_dec_ref(v_env_4620_);
v___x_4633_ = lean_box(0);
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 0, v___x_4633_);
v___x_4635_ = v___x_4631_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
else
{
lean_object* v_val_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4671_; 
v_val_4637_ = lean_ctor_get(v_a_4629_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v_a_4629_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4639_ = v_a_4629_;
v_isShared_4640_ = v_isSharedCheck_4671_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_val_4637_);
lean_dec(v_a_4629_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4671_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
if (lean_obj_tag(v_val_4637_) == 0)
{
lean_object* v_val_4641_; lean_object* v___x_4643_; 
lean_dec(v_cancelTk_x3f_4626_);
lean_dec(v_openDecls_4625_);
lean_dec(v_currNamespace_4624_);
lean_dec_ref(v_options_4623_);
lean_dec_ref(v_env_4620_);
v_val_4641_ = lean_ctor_get(v_val_4637_, 0);
lean_inc(v_val_4641_);
lean_dec_ref_known(v_val_4637_, 1);
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 0, v_val_4641_);
v___x_4643_ = v___x_4639_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_val_4641_);
v___x_4643_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
lean_object* v___x_4645_; 
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 0, v___x_4643_);
v___x_4645_ = v___x_4631_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v___x_4643_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
else
{
lean_object* v_val_4648_; lean_object* v___f_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
lean_del_object(v___x_4631_);
v_val_4648_ = lean_ctor_get(v_val_4637_, 0);
lean_inc(v_val_4648_);
lean_dec_ref_known(v_val_4637_, 1);
v___f_4649_ = lean_alloc_closure((void*)(l_Lean_findSimpleDocString_x3f___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4649_, 0, v_val_4648_);
v___x_4650_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_4650_, 0, v___f_4649_);
v___x_4651_ = l_Lean_Doc_runMarkdown___redArg(v_env_4620_, v___x_4650_, v_options_4623_, v_currNamespace_4624_, v_openDecls_4625_, v_cancelTk_x3f_4626_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4662_; 
v_a_4652_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4654_ = v___x_4651_;
v_isShared_4655_ = v_isSharedCheck_4662_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4651_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4662_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 0, v_a_4652_);
v___x_4657_ = v___x_4639_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
lean_object* v___x_4659_; 
if (v_isShared_4655_ == 0)
{
lean_ctor_set(v___x_4654_, 0, v___x_4657_);
v___x_4659_ = v___x_4654_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4657_);
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
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
lean_del_object(v___x_4639_);
v_a_4663_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4651_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4651_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
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
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
lean_dec(v_cancelTk_x3f_4626_);
lean_dec(v_openDecls_4625_);
lean_dec(v_currNamespace_4624_);
lean_dec_ref(v_options_4623_);
lean_dec_ref(v_env_4620_);
v_a_4673_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4675_ = v___x_4628_;
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4628_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_4681_, lean_object* v_declName_4682_, lean_object* v_includeBuiltin_4683_, lean_object* v_options_4684_, lean_object* v_currNamespace_4685_, lean_object* v_openDecls_4686_, lean_object* v_cancelTk_x3f_4687_, lean_object* v_a_4688_){
_start:
{
uint8_t v_includeBuiltin_boxed_4689_; lean_object* v_res_4690_; 
v_includeBuiltin_boxed_4689_ = lean_unbox(v_includeBuiltin_4683_);
v_res_4690_ = l_Lean_findSimpleDocString_x3f(v_env_4681_, v_declName_4682_, v_includeBuiltin_boxed_4689_, v_options_4684_, v_currNamespace_4685_, v_openDecls_4686_, v_cancelTk_x3f_4687_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(lean_object* v_p_4691_, lean_object* v_level_4692_, lean_object* v_part_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4692_, v_part_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___boxed(lean_object* v_p_4699_, lean_object* v_level_4700_, lean_object* v_part_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(v_p_4699_, v_level_4700_, v_part_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
lean_dec(v_a_4704_);
lean_dec_ref(v_a_4703_);
lean_dec(v_a_4702_);
lean_dec(v_level_4700_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(lean_object* v_p_4707_, lean_object* v___x_4708_, size_t v_sz_4709_, size_t v_i_4710_, lean_object* v_bs_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_){
_start:
{
lean_object* v___x_4716_; 
v___x_4716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4708_, v_sz_4709_, v_i_4710_, v_bs_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___boxed(lean_object* v_p_4717_, lean_object* v___x_4718_, lean_object* v_sz_4719_, lean_object* v_i_4720_, lean_object* v_bs_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
size_t v_sz_boxed_4726_; size_t v_i_boxed_4727_; lean_object* v_res_4728_; 
v_sz_boxed_4726_ = lean_unbox_usize(v_sz_4719_);
lean_dec(v_sz_4719_);
v_i_boxed_4727_ = lean_unbox_usize(v_i_4720_);
lean_dec(v_i_4720_);
v_res_4728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(v_p_4717_, v___x_4718_, v_sz_boxed_4726_, v_i_boxed_4727_, v_bs_4721_, v___y_4722_, v___y_4723_, v___y_4724_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___y_4722_);
lean_dec(v___x_4718_);
return v_res_4728_;
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
