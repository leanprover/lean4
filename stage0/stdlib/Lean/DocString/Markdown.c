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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(lean_object* v_name_1_, lean_object* v_body_2_, lean_object* v_a_3_){
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
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_body_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_res_11_;
v_res_11_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_1_, v_body_2_, v_a_3_);
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg___boxed(lean_object* v_name_12_, lean_object* v_body_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_12_, v_body_13_, v_a_14_);
lean_dec(v_a_14_);
return v_res_16_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote(lean_object* v_name_17_, lean_object* v_body_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_17_, v_body_18_, v_a_19_);
return v___x_23_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_17_ = stack[0].m_obj;
lean_object* v_body_18_ = stack[1].m_obj;
lean_object* v_a_19_ = stack[2].m_obj;
lean_object* v_a_20_ = stack[3].m_obj;
lean_object* v_a_21_ = stack[4].m_obj;
lean_object* v_res_24_;
v_res_24_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote(v_name_17_, v_body_18_, v_a_19_, v_a_20_, v_a_21_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___boxed(lean_object* v_name_25_, lean_object* v_body_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote(v_name_25_, v_body_26_, v_a_27_, v_a_28_, v_a_29_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
lean_dec(v_a_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0(lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
if (lean_obj_tag(v_a_38_) == 0)
{
lean_object* v___x_40_; 
v___x_40_ = l_List_reverse___redArg(v_a_39_);
return v___x_40_;
}
else
{
lean_object* v_head_41_; lean_object* v_tail_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_57_; 
v_head_41_ = lean_ctor_get(v_a_38_, 0);
v_tail_42_ = lean_ctor_get(v_a_38_, 1);
v_isSharedCheck_57_ = !lean_is_exclusive(v_a_38_);
if (v_isSharedCheck_57_ == 0)
{
v___x_44_ = v_a_38_;
v_isShared_45_ = v_isSharedCheck_57_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_tail_42_);
lean_inc(v_head_41_);
lean_dec(v_a_38_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_57_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v_fst_46_; lean_object* v_snd_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_54_; 
v_fst_46_ = lean_ctor_get(v_head_41_, 0);
lean_inc(v_fst_46_);
v_snd_47_ = lean_ctor_get(v_head_41_, 1);
lean_inc(v_snd_47_);
lean_dec(v_head_41_);
v___x_48_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_49_ = lean_string_append(v___x_48_, v_fst_46_);
lean_dec(v_fst_46_);
v___x_50_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__1));
v___x_51_ = lean_string_append(v___x_49_, v___x_50_);
v___x_52_ = lean_string_append(v___x_51_, v_snd_47_);
lean_dec(v_snd_47_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v_a_39_);
lean_ctor_set(v___x_44_, 0, v___x_52_);
v___x_54_ = v___x_44_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_52_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_a_39_);
v___x_54_ = v_reuseFailAlloc_56_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
v_a_38_ = v_tail_42_;
v_a_39_ = v___x_54_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Doc_MarkdownM_run_x27(lean_object* v_act_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__0));
v___x_68_ = lean_st_mk_ref(v___x_67_);
lean_inc(v_a_64_);
lean_inc_ref(v_a_63_);
lean_inc(v___x_68_);
v___x_69_ = lean_apply_4(v_act_62_, v___x_68_, v_a_63_, v_a_64_, lean_box(0));
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_93_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_93_ == 0)
{
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_93_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_93_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_74_ = lean_st_ref_get(v___x_68_);
lean_dec(v___x_68_);
v___x_75_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_76_ = lean_array_to_list(v_a_70_);
v___x_77_ = l_String_intercalate(v___x_75_, v___x_76_);
v___x_78_ = lean_array_get_size(v___x_74_);
v___x_79_ = lean_nat_dec_eq(v___x_78_, v___x_66_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_80_ = lean_array_to_list(v___x_74_);
v___x_81_ = lean_box(0);
v___x_82_ = l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0(v___x_80_, v___x_81_);
v___x_83_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__2));
v___x_84_ = lean_string_append(v___x_77_, v___x_83_);
v___x_85_ = l_String_intercalate(v___x_83_, v___x_82_);
v___x_86_ = lean_string_append(v___x_84_, v___x_85_);
lean_dec_ref(v___x_85_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_86_);
v___x_88_ = v___x_72_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
else
{
lean_object* v___x_91_; 
lean_dec(v___x_74_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_77_);
v___x_91_ = v___x_72_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_77_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec(v___x_68_);
v_a_94_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_69_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_69_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_MarkdownM_run_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_62_ = stack[0].m_obj;
lean_object* v_a_63_ = stack[1].m_obj;
lean_object* v_a_64_ = stack[2].m_obj;
lean_object* v_res_102_;
v_res_102_ = l_Lean_Doc_MarkdownM_run_x27(v_act_62_, v_a_63_, v_a_64_);
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_MarkdownM_run_x27___boxed(lean_object* v_act_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Doc_MarkdownM_run_x27(v_act_103_, v_a_104_, v_a_105_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(lean_object* v_s_108_, lean_object* v_pos_109_){
_start:
{
lean_object* v_str_110_; lean_object* v_startInclusive_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v_decide_115_; 
v_str_110_ = lean_ctor_get(v_s_108_, 0);
v_startInclusive_111_ = lean_ctor_get(v_s_108_, 1);
v___x_112_ = lean_nat_add(v_startInclusive_111_, v_pos_109_);
v___x_113_ = lean_nat_sub(v___x_112_, v_startInclusive_111_);
v___x_114_ = lean_unsigned_to_nat(0u);
v_decide_115_ = lean_nat_dec_eq(v___x_113_, v___x_114_);
if (v_decide_115_ == 0)
{
uint32_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint32_t v___x_122_; uint8_t v___x_123_; 
v___x_116_ = 32;
lean_inc(v_startInclusive_111_);
lean_inc_ref(v_str_110_);
v___x_117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_117_, 0, v_str_110_);
lean_ctor_set(v___x_117_, 1, v_startInclusive_111_);
lean_ctor_set(v___x_117_, 2, v___x_112_);
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_sub(v___x_113_, v___x_118_);
lean_dec(v___x_113_);
v___x_120_ = l_String_Slice_posLE(v___x_117_, v___x_119_);
lean_dec_ref_known(v___x_117_, 3);
v___x_121_ = lean_nat_add(v_startInclusive_111_, v___x_120_);
v___x_122_ = lean_string_utf8_get_fast(v_str_110_, v___x_121_);
lean_dec(v___x_121_);
v___x_123_ = lean_uint32_dec_eq(v___x_122_, v___x_116_);
if (v___x_123_ == 0)
{
lean_dec(v___x_120_);
return v_pos_109_;
}
else
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_nat_add(v___x_120_, v___x_118_);
v___x_125_ = lean_nat_dec_le(v___x_124_, v_pos_109_);
lean_dec(v___x_124_);
if (v___x_125_ == 0)
{
lean_dec(v___x_120_);
return v_pos_109_;
}
else
{
lean_dec(v_pos_109_);
v_pos_109_ = v___x_120_;
goto _start;
}
}
}
else
{
lean_dec(v___x_113_);
lean_dec(v___x_112_);
return v_pos_109_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0___boxed(lean_object* v_s_127_, lean_object* v_pos_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(v_s_127_, v_pos_128_);
lean_dec_ref(v_s_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(lean_object* v_s_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_string_utf8_byte_size(v_s_130_);
lean_inc_ref(v_s_130_);
v___x_133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_133_, 0, v_s_130_);
lean_ctor_set(v___x_133_, 1, v___x_131_);
lean_ctor_set(v___x_133_, 2, v___x_132_);
v___x_134_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(v___x_133_, v___x_132_);
lean_dec_ref_known(v___x_133_, 3);
v___x_135_ = lean_string_utf8_extract_fast(v_s_130_, v___x_131_, v___x_134_);
lean_dec(v___x_134_);
lean_dec_ref(v_s_130_);
return v___x_135_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(lean_object* v_p_136_, lean_object* v_pTrim_137_, size_t v_sz_138_, size_t v_i_139_, lean_object* v_bs_140_){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = lean_usize_dec_lt(v_i_139_, v_sz_138_);
if (v___x_141_ == 0)
{
lean_dec_ref(v_pTrim_137_);
lean_dec_ref(v_p_136_);
return v_bs_140_;
}
else
{
lean_object* v_v_142_; lean_object* v___x_143_; lean_object* v_bs_x27_144_; lean_object* v___y_146_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_v_142_ = lean_array_uget(v_bs_140_, v_i_139_);
v___x_143_ = lean_unsigned_to_nat(0u);
v_bs_x27_144_ = lean_array_uset(v_bs_140_, v_i_139_, v___x_143_);
v___x_151_ = lean_string_utf8_byte_size(v_v_142_);
v___x_152_ = lean_nat_dec_eq(v___x_151_, v___x_143_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
lean_inc_ref(v_p_136_);
v___x_153_ = lean_string_append(v_p_136_, v_v_142_);
lean_dec(v_v_142_);
v___y_146_ = v___x_153_;
goto v___jp_145_;
}
else
{
lean_dec(v_v_142_);
lean_inc_ref(v_pTrim_137_);
v___y_146_ = v_pTrim_137_;
goto v___jp_145_;
}
v___jp_145_:
{
size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_add(v_i_139_, v___x_147_);
v___x_149_ = lean_array_uset(v_bs_x27_144_, v_i_139_, v___y_146_);
v_i_139_ = v___x_148_;
v_bs_140_ = v___x_149_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_136_ = stack[0].m_obj;
lean_object* v_pTrim_137_ = stack[1].m_obj;
size_t v_sz_138_ = stack[2].m_num;
size_t v_i_139_ = stack[3].m_num;
lean_object* v_bs_140_ = stack[4].m_obj;
lean_object* v_res_154_;
v_res_154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(v_p_136_, v_pTrim_137_, v_sz_138_, v_i_139_, v_bs_140_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0___boxed(lean_object* v_p_155_, lean_object* v_pTrim_156_, lean_object* v_sz_157_, lean_object* v_i_158_, lean_object* v_bs_159_){
_start:
{
size_t v_sz_boxed_160_; size_t v_i_boxed_161_; lean_object* v_res_162_; 
v_sz_boxed_160_ = lean_unbox_usize(v_sz_157_);
lean_dec(v_sz_157_);
v_i_boxed_161_ = lean_unbox_usize(v_i_158_);
lean_dec(v_i_158_);
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(v_p_155_, v_pTrim_156_, v_sz_boxed_160_, v_i_boxed_161_, v_bs_159_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_prefixLines(lean_object* v_p_163_, lean_object* v_lines_164_){
_start:
{
lean_object* v_pTrim_165_; size_t v_sz_166_; size_t v___x_167_; lean_object* v___x_168_; 
lean_inc_ref(v_p_163_);
v_pTrim_165_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_p_163_);
v_sz_166_ = lean_array_size(v_lines_164_);
v___x_167_ = ((size_t)0ULL);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(v_p_163_, v_pTrim_165_, v_sz_166_, v___x_167_, v_lines_164_);
return v___x_168_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(lean_object* v_rest_169_, lean_object* v_restTrim_170_, lean_object* v_head_171_, lean_object* v_headTrim_172_, size_t v_sz_173_, size_t v_i_174_, lean_object* v_bs_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = lean_usize_dec_lt(v_i_174_, v_sz_173_);
if (v___x_176_ == 0)
{
lean_dec_ref(v_headTrim_172_);
lean_dec_ref(v_head_171_);
lean_dec_ref(v_restTrim_170_);
lean_dec_ref(v_rest_169_);
return v_bs_175_;
}
else
{
lean_object* v_v_177_; lean_object* v___x_178_; lean_object* v_bs_x27_179_; lean_object* v___y_181_; lean_object* v_fst_187_; lean_object* v_snd_188_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_v_177_ = lean_array_uget(v_bs_175_, v_i_174_);
v___x_178_ = lean_unsigned_to_nat(0u);
v_bs_x27_179_ = lean_array_uset(v_bs_175_, v_i_174_, v___x_178_);
v___x_192_ = lean_usize_to_nat(v_i_174_);
v___x_193_ = lean_nat_dec_eq(v___x_192_, v___x_178_);
lean_dec(v___x_192_);
if (v___x_193_ == 0)
{
lean_inc_ref(v_restTrim_170_);
lean_inc_ref(v_rest_169_);
v_fst_187_ = v_rest_169_;
v_snd_188_ = v_restTrim_170_;
goto v___jp_186_;
}
else
{
lean_inc_ref(v_headTrim_172_);
lean_inc_ref(v_head_171_);
v_fst_187_ = v_head_171_;
v_snd_188_ = v_headTrim_172_;
goto v___jp_186_;
}
v___jp_180_:
{
size_t v___x_182_; size_t v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((size_t)1ULL);
v___x_183_ = lean_usize_add(v_i_174_, v___x_182_);
v___x_184_ = lean_array_uset(v_bs_x27_179_, v_i_174_, v___y_181_);
v_i_174_ = v___x_183_;
v_bs_175_ = v___x_184_;
goto _start;
}
v___jp_186_:
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = lean_string_utf8_byte_size(v_v_177_);
v___x_190_ = lean_nat_dec_eq(v___x_189_, v___x_178_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
lean_dec_ref(v_snd_188_);
v___x_191_ = lean_string_append(v_fst_187_, v_v_177_);
lean_dec(v_v_177_);
v___y_181_ = v___x_191_;
goto v___jp_180_;
}
else
{
lean_dec_ref(v_fst_187_);
lean_dec(v_v_177_);
v___y_181_ = v_snd_188_;
goto v___jp_180_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_rest_169_ = stack[0].m_obj;
lean_object* v_restTrim_170_ = stack[1].m_obj;
lean_object* v_head_171_ = stack[2].m_obj;
lean_object* v_headTrim_172_ = stack[3].m_obj;
size_t v_sz_173_ = stack[4].m_num;
size_t v_i_174_ = stack[5].m_num;
lean_object* v_bs_175_ = stack[6].m_obj;
lean_object* v_res_194_;
v_res_194_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_169_, v_restTrim_170_, v_head_171_, v_headTrim_172_, v_sz_173_, v_i_174_, v_bs_175_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg___boxed(lean_object* v_rest_195_, lean_object* v_restTrim_196_, lean_object* v_head_197_, lean_object* v_headTrim_198_, lean_object* v_sz_199_, lean_object* v_i_200_, lean_object* v_bs_201_){
_start:
{
size_t v_sz_boxed_202_; size_t v_i_boxed_203_; lean_object* v_res_204_; 
v_sz_boxed_202_ = lean_unbox_usize(v_sz_199_);
lean_dec(v_sz_199_);
v_i_boxed_203_ = lean_unbox_usize(v_i_200_);
lean_dec(v_i_200_);
v_res_204_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_195_, v_restTrim_196_, v_head_197_, v_headTrim_198_, v_sz_boxed_202_, v_i_boxed_203_, v_bs_201_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_prefixListLines(lean_object* v_head_205_, lean_object* v_rest_206_, lean_object* v_lines_207_){
_start:
{
lean_object* v_headTrim_208_; lean_object* v_restTrim_209_; size_t v_sz_210_; size_t v___x_211_; lean_object* v___x_212_; 
lean_inc_ref(v_head_205_);
v_headTrim_208_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_head_205_);
lean_inc_ref(v_rest_206_);
v_restTrim_209_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_rest_206_);
v_sz_210_ = lean_array_size(v_lines_207_);
v___x_211_ = ((size_t)0ULL);
v___x_212_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_206_, v_restTrim_209_, v_head_205_, v_headTrim_208_, v_sz_210_, v___x_211_, v_lines_207_);
return v___x_212_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0(lean_object* v_rest_213_, lean_object* v_restTrim_214_, lean_object* v_head_215_, lean_object* v_headTrim_216_, lean_object* v_as_217_, size_t v_sz_218_, size_t v_i_219_, lean_object* v_bs_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(v_rest_213_, v_restTrim_214_, v_head_215_, v_headTrim_216_, v_sz_218_, v_i_219_, v_bs_220_);
return v___x_221_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_rest_213_ = stack[0].m_obj;
lean_object* v_restTrim_214_ = stack[1].m_obj;
lean_object* v_head_215_ = stack[2].m_obj;
lean_object* v_headTrim_216_ = stack[3].m_obj;
lean_object* v_as_217_ = stack[4].m_obj;
size_t v_sz_218_ = stack[5].m_num;
size_t v_i_219_ = stack[6].m_num;
lean_object* v_bs_220_ = stack[7].m_obj;
lean_object* v_res_222_;
v_res_222_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0(v_rest_213_, v_restTrim_214_, v_head_215_, v_headTrim_216_, v_as_217_, v_sz_218_, v_i_219_, v_bs_220_);
stack->m_obj
 = v_res_222_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0___boxed(lean_object* v_rest_223_, lean_object* v_restTrim_224_, lean_object* v_head_225_, lean_object* v_headTrim_226_, lean_object* v_as_227_, lean_object* v_sz_228_, lean_object* v_i_229_, lean_object* v_bs_230_){
_start:
{
size_t v_sz_boxed_231_; size_t v_i_boxed_232_; lean_object* v_res_233_; 
v_sz_boxed_231_ = lean_unbox_usize(v_sz_228_);
lean_dec(v_sz_228_);
v_i_boxed_232_ = lean_unbox_usize(v_i_229_);
lean_dec(v_i_229_);
v_res_233_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_prefixListLines_spec__0(v_rest_223_, v_restTrim_224_, v_head_225_, v_headTrim_226_, v_as_227_, v_sz_boxed_231_, v_i_boxed_232_, v_bs_230_);
lean_dec_ref(v_as_227_);
return v_res_233_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(lean_object* v_as_235_, size_t v_i_236_, size_t v_stop_237_, lean_object* v_b_238_){
_start:
{
lean_object* v___y_240_; uint8_t v___x_244_; 
v___x_244_ = lean_usize_dec_eq(v_i_236_, v_stop_237_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_245_ = lean_array_uget_borrowed(v_as_235_, v_i_236_);
v___x_246_ = lean_array_get_size(v___x_245_);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_nat_dec_eq(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_array_get_size(v_b_238_);
v___x_250_ = lean_nat_dec_eq(v___x_249_, v___x_247_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_252_ = lean_array_push(v_b_238_, v___x_251_);
v___x_253_ = l_Array_append___redArg(v___x_252_, v___x_245_);
v___y_240_ = v___x_253_;
goto v___jp_239_;
}
else
{
lean_dec_ref(v_b_238_);
lean_inc(v___x_245_);
v___y_240_ = v___x_245_;
goto v___jp_239_;
}
}
else
{
v___y_240_ = v_b_238_;
goto v___jp_239_;
}
}
else
{
return v_b_238_;
}
v___jp_239_:
{
size_t v___x_241_; size_t v___x_242_; 
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_add(v_i_236_, v___x_241_);
v_i_236_ = v___x_242_;
v_b_238_ = v___y_240_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_235_ = stack[0].m_obj;
size_t v_i_236_ = stack[1].m_num;
size_t v_stop_237_ = stack[2].m_num;
lean_object* v_b_238_ = stack[3].m_obj;
lean_object* v_res_254_;
v_res_254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_as_235_, v_i_236_, v_stop_237_, v_b_238_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___boxed(lean_object* v_as_255_, lean_object* v_i_256_, lean_object* v_stop_257_, lean_object* v_b_258_){
_start:
{
size_t v_i_boxed_259_; size_t v_stop_boxed_260_; lean_object* v_res_261_; 
v_i_boxed_259_ = lean_unbox_usize(v_i_256_);
lean_dec(v_i_256_);
v_stop_boxed_260_ = lean_unbox_usize(v_stop_257_);
lean_dec(v_stop_257_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_as_255_, v_i_boxed_259_, v_stop_boxed_260_, v_b_258_);
lean_dec_ref(v_as_255_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks(lean_object* v_blocks_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_267_ = lean_array_get_size(v_blocks_264_);
v___x_268_ = lean_nat_dec_lt(v___x_265_, v___x_267_);
if (v___x_268_ == 0)
{
return v___x_266_;
}
else
{
uint8_t v___x_269_; 
v___x_269_ = lean_nat_dec_le(v___x_267_, v___x_267_);
if (v___x_269_ == 0)
{
if (v___x_268_ == 0)
{
return v___x_266_;
}
else
{
size_t v___x_270_; size_t v___x_271_; lean_object* v___x_272_; 
v___x_270_ = ((size_t)0ULL);
v___x_271_ = lean_usize_of_nat(v___x_267_);
v___x_272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_264_, v___x_270_, v___x_271_, v___x_266_);
return v___x_272_;
}
}
else
{
size_t v___x_273_; size_t v___x_274_; lean_object* v___x_275_; 
v___x_273_ = ((size_t)0ULL);
v___x_274_ = lean_usize_of_nat(v___x_267_);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_264_, v___x_273_, v___x_274_, v___x_266_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinBlocks___boxed(lean_object* v_blocks_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Doc_joinBlocks(v_blocks_276_);
lean_dec_ref(v_blocks_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(lean_object* v_l_280_, lean_object* v_r_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_282_ = lean_string_utf8_byte_size(v_l_280_);
v___x_283_ = lean_unsigned_to_nat(1u);
v___x_284_ = lean_nat_dec_le(v___x_283_, v___x_282_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; 
v___x_285_ = lean_string_append(v_l_280_, v_r_281_);
return v___x_285_;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_286_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_nat_sub(v___x_282_, v___x_283_);
v___x_289_ = lean_string_memcmp(v_l_280_, v___x_286_, v___x_288_, v___x_287_, v___x_283_);
lean_dec(v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
v___x_290_ = lean_string_append(v_l_280_, v_r_281_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_string_utf8_byte_size(v_r_281_);
v___x_292_ = lean_nat_dec_le(v___x_283_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
v___x_293_ = lean_string_append(v_l_280_, v_r_281_);
return v___x_293_;
}
else
{
uint8_t v___x_294_; 
v___x_294_ = lean_string_memcmp(v_r_281_, v___x_286_, v___x_287_, v___x_287_, v___x_283_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_string_append(v_l_280_, v_r_281_);
return v___x_295_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1));
v___x_297_ = lean_string_append(v_l_280_, v___x_296_);
v___x_298_ = lean_string_append(v___x_297_, v_r_281_);
return v___x_298_;
}
}
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(lean_object* v_as_302_, size_t v_i_303_, size_t v_stop_304_, lean_object* v_b_305_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_302_ = stack[0].m_obj;
size_t v_i_303_ = stack[1].m_num;
size_t v_stop_304_ = stack[2].m_num;
lean_object* v_b_305_ = stack[3].m_obj;
lean_object* v_res_326_;
v_res_326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_as_302_, v_i_303_, v_stop_304_, v_b_305_);
stack->m_obj
 = v_res_326_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0___boxed(lean_object* v_as_327_, lean_object* v_i_328_, lean_object* v_stop_329_, lean_object* v_b_330_){
_start:
{
size_t v_i_boxed_331_; size_t v_stop_boxed_332_; lean_object* v_res_333_; 
v_i_boxed_331_ = lean_unbox_usize(v_i_328_);
lean_dec(v_i_328_);
v_stop_boxed_332_ = lean_unbox_usize(v_stop_329_);
lean_dec(v_stop_329_);
v_res_333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_as_327_, v_i_boxed_331_, v_stop_boxed_332_, v_b_330_);
lean_dec_ref(v_as_327_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines(lean_object* v_parts_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_337_ = lean_array_get_size(v_parts_334_);
v___x_338_ = lean_nat_dec_lt(v___x_335_, v___x_337_);
if (v___x_338_ == 0)
{
return v___x_336_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = lean_nat_dec_le(v___x_337_, v___x_337_);
if (v___x_339_ == 0)
{
if (v___x_338_ == 0)
{
return v___x_336_;
}
else
{
size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((size_t)0ULL);
v___x_341_ = lean_usize_of_nat(v___x_337_);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_334_, v___x_340_, v___x_341_, v___x_336_);
return v___x_342_;
}
}
else
{
size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_337_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_334_, v___x_343_, v___x_344_, v___x_336_);
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines___boxed(lean_object* v_parts_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Doc_joinInlines(v_parts_346_);
lean_dec_ref(v_parts_346_);
return v_res_347_;
}
}
lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object* v_a_348_, uint8_t v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_Lean_Doc_instMarkdownInlineEmpty___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_348_ = stack[0].m_obj;
uint8_t v_a_349_ = stack[1].m_num;
lean_object* v_a_350_ = stack[2].m_obj;
lean_object* v_a_351_ = stack[3].m_obj;
lean_object* v_a_352_ = stack[4].m_obj;
lean_object* v_a_353_ = stack[5].m_obj;
lean_object* v_res_355_;
v_res_355_ = l_Lean_Doc_instMarkdownInlineEmpty___lam__0(v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
stack->m_obj
 = v_res_355_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
uint8_t v_a_19__boxed_363_; lean_object* v_res_364_; 
v_a_19__boxed_363_ = lean_unbox(v_a_357_);
v_res_364_ = l_Lean_Doc_instMarkdownInlineEmpty___lam__0(v_a_356_, v_a_19__boxed_363_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec_ref(v_a_356_);
return v_res_364_;
}
}
lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0(lean_object* v_a_367_, lean_object* v_a_368_, uint8_t v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_367_ = stack[0].m_obj;
lean_object* v_a_368_ = stack[1].m_obj;
uint8_t v_a_369_ = stack[2].m_num;
lean_object* v_a_370_ = stack[3].m_obj;
lean_object* v_a_371_ = stack[4].m_obj;
lean_object* v_a_372_ = stack[5].m_obj;
lean_object* v_a_373_ = stack[6].m_obj;
lean_object* v_res_375_;
v_res_375_ = l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0(v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
stack->m_obj
 = v_res_375_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0___boxed(lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
uint8_t v_a_41__boxed_384_; lean_object* v_res_385_; 
v_a_41__boxed_384_ = lean_unbox(v_a_378_);
v_res_385_ = l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0(v_a_376_, v_a_377_, v_a_41__boxed_384_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec_ref(v_a_377_);
lean_dec_ref(v_a_376_);
return v_res_385_;
}
}
lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg(){
_start:
{
lean_object* v___f_388_; 
v___f_388_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0));
return v___f_388_;
}
}
LEAN_EXPORT void l_Lean_Doc_instMarkdownBlockEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_389_;
v_res_389_ = l_Lean_Doc_instMarkdownBlockEmpty___redArg();
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___boxed(lean_object* v___dummy_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Doc_instMarkdownBlockEmpty___redArg();
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object* v_i_392_){
_start:
{
lean_object* v___f_393_; 
v___f_393_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0));
return v___f_393_;
}
}
uint8_t l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
if (lean_obj_tag(v_x_395_) == 0)
{
uint8_t v___x_396_; 
v___x_396_ = 1;
return v___x_396_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = 0;
return v___x_397_;
}
}
else
{
if (lean_obj_tag(v_x_395_) == 0)
{
uint8_t v___x_398_; 
v___x_398_ = 0;
return v___x_398_;
}
else
{
lean_object* v_val_399_; lean_object* v_val_400_; uint32_t v___x_401_; uint32_t v___x_402_; uint8_t v___x_403_; 
v_val_399_ = lean_ctor_get(v_x_394_, 0);
v_val_400_ = lean_ctor_get(v_x_395_, 0);
v___x_401_ = lean_unbox_uint32(v_val_399_);
v___x_402_ = lean_unbox_uint32(v_val_400_);
v___x_403_ = lean_uint32_dec_eq(v___x_401_, v___x_402_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_394_ = stack[0].m_obj;
lean_object* v_x_395_ = stack[1].m_obj;
uint8_t v_res_404_;
v_res_404_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_x_394_, v_x_395_);
stack->m_num = v_res_404_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1___boxed(lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_x_405_, v_x_406_);
lean_dec(v_x_406_);
lean_dec(v_x_405_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(lean_object* v_s_409_, uint32_t v_c_410_, lean_object* v_a_411_, uint8_t v_b_412_){
_start:
{
lean_object* v_str_413_; lean_object* v_startInclusive_414_; lean_object* v_endExclusive_415_; lean_object* v___x_416_; uint8_t v_decide_417_; 
v_str_413_ = lean_ctor_get(v_s_409_, 0);
v_startInclusive_414_ = lean_ctor_get(v_s_409_, 1);
v_endExclusive_415_ = lean_ctor_get(v_s_409_, 2);
v___x_416_ = lean_nat_sub(v_endExclusive_415_, v_startInclusive_414_);
v_decide_417_ = lean_nat_dec_eq(v_a_411_, v___x_416_);
lean_dec(v___x_416_);
if (v_decide_417_ == 0)
{
lean_object* v___x_418_; uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_418_ = lean_nat_add(v_startInclusive_414_, v_a_411_);
lean_dec(v_a_411_);
v___x_419_ = lean_string_utf8_get_fast(v_str_413_, v___x_418_);
v___x_420_ = lean_uint32_dec_eq(v___x_419_, v_c_410_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_string_utf8_next_fast(v_str_413_, v___x_418_);
lean_dec(v___x_418_);
v___x_422_ = lean_nat_sub(v___x_421_, v_startInclusive_414_);
v_a_411_ = v___x_422_;
v_b_412_ = v___x_420_;
goto _start;
}
else
{
lean_dec(v___x_418_);
return v___x_420_;
}
}
else
{
lean_dec(v_a_411_);
return v_b_412_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_409_ = stack[0].m_obj;
uint32_t v_c_410_ = stack[1].m_num;
lean_object* v_a_411_ = stack[2].m_obj;
uint8_t v_b_412_ = stack[3].m_num;
uint8_t v_res_424_;
v_res_424_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_409_, v_c_410_, v_a_411_, v_b_412_);
stack->m_num = v_res_424_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg___boxed(lean_object* v_s_425_, lean_object* v_c_426_, lean_object* v_a_427_, lean_object* v_b_428_){
_start:
{
uint32_t v_c_boxed_429_; uint8_t v_b_boxed_430_; uint8_t v_res_431_; lean_object* v_r_432_; 
v_c_boxed_429_ = lean_unbox_uint32(v_c_426_);
lean_dec(v_c_426_);
v_b_boxed_430_ = lean_unbox(v_b_428_);
v_res_431_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_425_, v_c_boxed_429_, v_a_427_, v_b_boxed_430_);
lean_dec_ref(v_s_425_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(uint32_t v_c_433_, lean_object* v_s_434_){
_start:
{
lean_object* v_searcher_435_; uint8_t v___x_436_; uint8_t v___x_437_; 
v_searcher_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = 0;
v___x_437_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_434_, v_c_433_, v_searcher_435_, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_433_ = stack[0].m_num;
lean_object* v_s_434_ = stack[1].m_obj;
uint8_t v_res_438_;
v_res_438_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_433_, v_s_434_);
stack->m_num = v_res_438_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0___boxed(lean_object* v_c_439_, lean_object* v_s_440_){
_start:
{
uint32_t v_c_boxed_441_; uint8_t v_res_442_; lean_object* v_r_443_; 
v_c_boxed_441_ = lean_unbox_uint32(v_c_439_);
lean_dec(v_c_439_);
v_res_442_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_boxed_441_, v_s_440_);
lean_dec_ref(v_s_440_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_449_; lean_object* v___x_450_; 
v___x_449_ = 91;
v___x_450_ = lean_box_uint32(v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2___boxed__const__1;
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(uint32_t v_c_453_, lean_object* v_next_x3f_454_){
_start:
{
uint32_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 33;
v___x_456_ = lean_uint32_dec_eq(v_c_453_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1));
v___x_458_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_453_, v___x_457_);
return v___x_458_;
}
else
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2);
v___x_460_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_454_, v___x_459_);
return v___x_460_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_453_ = stack[0].m_num;
lean_object* v_next_x3f_454_ = stack[1].m_obj;
uint8_t v_res_461_;
v_res_461_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_453_, v_next_x3f_454_);
stack->m_num = v_res_461_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___boxed(lean_object* v_c_462_, lean_object* v_next_x3f_463_){
_start:
{
uint32_t v_c_boxed_464_; uint8_t v_res_465_; lean_object* v_r_466_; 
v_c_boxed_464_ = lean_unbox_uint32(v_c_462_);
lean_dec(v_c_462_);
v_res_465_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_boxed_464_, v_next_x3f_463_);
lean_dec(v_next_x3f_463_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(lean_object* v_s_467_, uint32_t v_c_468_, lean_object* v_inst_469_, lean_object* v_R_470_, lean_object* v_a_471_, uint8_t v_b_472_, lean_object* v_c_473_){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_467_, v_c_468_, v_a_471_, v_b_472_);
return v___x_474_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_467_ = stack[0].m_obj;
uint32_t v_c_468_ = stack[1].m_num;
lean_object* v_a_471_ = stack[4].m_obj;
uint8_t v_b_472_ = stack[5].m_num;
uint8_t v_res_475_;
v_res_475_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(v_s_467_, v_c_468_, lean_box(0), lean_box(0), v_a_471_, v_b_472_, lean_box(0));
stack->m_num = v_res_475_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___boxed(lean_object* v_s_476_, lean_object* v_c_477_, lean_object* v_inst_478_, lean_object* v_R_479_, lean_object* v_a_480_, lean_object* v_b_481_, lean_object* v_c_482_){
_start:
{
uint32_t v_c_boxed_483_; uint8_t v_b_boxed_484_; uint8_t v_res_485_; lean_object* v_r_486_; 
v_c_boxed_483_ = lean_unbox_uint32(v_c_477_);
lean_dec(v_c_477_);
v_b_boxed_484_ = lean_unbox(v_b_481_);
v_res_485_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(v_s_476_, v_c_boxed_483_, v_inst_478_, v_R_479_, v_a_480_, v_b_boxed_484_, v_c_482_);
lean_dec_ref(v_s_476_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_487_; lean_object* v___x_488_; 
v___x_487_ = 32;
v___x_488_ = lean_box_uint32(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(lean_object* v_prev_x3f_491_, uint32_t v_c_492_, lean_object* v_next_x3f_493_){
_start:
{
uint8_t v___y_495_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0);
v___x_513_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_493_, v___x_512_);
if (v___x_513_ == 0)
{
if (lean_obj_tag(v_next_x3f_493_) == 0)
{
uint8_t v___x_514_; 
v___x_514_ = 1;
v___y_495_ = v___x_514_;
goto v___jp_494_;
}
else
{
v___y_495_ = v___x_513_;
goto v___jp_494_;
}
}
else
{
v___y_495_ = v___x_513_;
goto v___jp_494_;
}
v___jp_494_:
{
uint32_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = 62;
v___x_497_ = lean_uint32_dec_eq(v_c_492_, v___x_496_);
if (v___x_497_ == 0)
{
uint32_t v___x_498_; uint8_t v___x_499_; 
v___x_498_ = 45;
v___x_499_ = lean_uint32_dec_eq(v_c_492_, v___x_498_);
if (v___x_499_ == 0)
{
uint32_t v___x_500_; uint8_t v___x_501_; 
v___x_500_ = 43;
v___x_501_ = lean_uint32_dec_eq(v_c_492_, v___x_500_);
if (v___x_501_ == 0)
{
uint32_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = 46;
v___x_503_ = lean_uint32_dec_eq(v_c_492_, v___x_502_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; 
v___x_504_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_492_, v_next_x3f_493_);
return v___x_504_;
}
else
{
if (lean_obj_tag(v_prev_x3f_491_) == 0)
{
return v___x_501_;
}
else
{
lean_object* v_val_505_; uint32_t v___x_506_; uint32_t v___x_507_; uint8_t v___x_508_; 
v_val_505_ = lean_ctor_get(v_prev_x3f_491_, 0);
v___x_506_ = 48;
v___x_507_ = lean_unbox_uint32(v_val_505_);
v___x_508_ = lean_uint32_dec_le(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
return v___x_508_;
}
else
{
uint32_t v___x_509_; uint32_t v___x_510_; uint8_t v___x_511_; 
v___x_509_ = 57;
v___x_510_ = lean_unbox_uint32(v_val_505_);
v___x_511_ = lean_uint32_dec_le(v___x_510_, v___x_509_);
if (v___x_511_ == 0)
{
return v___x_511_;
}
else
{
return v___y_495_;
}
}
}
}
}
else
{
return v___y_495_;
}
}
else
{
return v___y_495_;
}
}
else
{
return v___x_497_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial_0interp(lean_interpreter_value* stack)
{
lean_object* v_prev_x3f_491_ = stack[0].m_obj;
uint32_t v_c_492_ = stack[1].m_num;
lean_object* v_next_x3f_493_ = stack[2].m_obj;
uint8_t v_res_515_;
v_res_515_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_prev_x3f_491_, v_c_492_, v_next_x3f_493_);
stack->m_num = v_res_515_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___boxed(lean_object* v_prev_x3f_516_, lean_object* v_c_517_, lean_object* v_next_x3f_518_){
_start:
{
uint32_t v_c_boxed_519_; uint8_t v_res_520_; lean_object* v_r_521_; 
v_c_boxed_519_ = lean_unbox_uint32(v_c_517_);
lean_dec(v_c_517_);
v_res_520_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_prev_x3f_516_, v_c_boxed_519_, v_next_x3f_518_);
lean_dec(v_next_x3f_518_);
lean_dec(v_prev_x3f_516_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(uint32_t v___x_527_, lean_object* v___x_528_, lean_object* v_____r_529_, lean_object* v_s_x27_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint32_t v___x_544_; uint8_t v___x_545_; 
v___x_531_ = lean_string_push(v_s_x27_530_, v___x_527_);
v___x_532_ = lean_box_uint32(v___x_527_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
v___x_544_ = 48;
v___x_545_ = lean_uint32_dec_le(v___x_544_, v___x_527_);
if (v___x_545_ == 0)
{
goto v___jp_538_;
}
else
{
uint32_t v___x_546_; uint8_t v___x_547_; 
v___x_546_ = 57;
v___x_547_ = lean_uint32_dec_le(v___x_527_, v___x_546_);
if (v___x_547_ == 0)
{
goto v___jp_538_;
}
else
{
goto v___jp_534_;
}
}
v___jp_534_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_528_);
lean_ctor_set(v___x_535_, 1, v___x_533_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_531_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
v___jp_538_:
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1));
v___x_540_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v___x_527_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_528_);
lean_ctor_set(v___x_541_, 1, v___x_533_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_531_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
else
{
goto v___jp_534_;
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v___x_527_ = stack[0].m_num;
lean_object* v___x_528_ = stack[1].m_obj;
lean_object* v_____r_529_ = stack[2].m_obj;
lean_object* v_s_x27_530_ = stack[3].m_obj;
lean_object* v_res_548_;
v_res_548_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_527_, v___x_528_, v_____r_529_, v_s_x27_530_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed(lean_object* v___x_549_, lean_object* v___x_550_, lean_object* v_____r_551_, lean_object* v_s_x27_552_){
_start:
{
uint32_t v___x_2069__boxed_553_; lean_object* v_res_554_; 
v___x_2069__boxed_553_ = lean_unbox_uint32(v___x_549_);
lean_dec(v___x_549_);
v_res_554_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_2069__boxed_553_, v___x_550_, v_____r_551_, v_s_x27_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(lean_object* v_s_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___y_558_; lean_object* v_snd_562_; lean_object* v_fst_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_601_; 
v_snd_562_ = lean_ctor_get(v_a_556_, 1);
v_fst_563_ = lean_ctor_get(v_a_556_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v_a_556_);
if (v_isSharedCheck_601_ == 0)
{
v___x_565_ = v_a_556_;
v_isShared_566_ = v_isSharedCheck_601_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snd_562_);
lean_inc(v_fst_563_);
lean_dec(v_a_556_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_601_;
goto v_resetjp_564_;
}
v___jp_557_:
{
if (lean_obj_tag(v___y_558_) == 0)
{
lean_object* v_a_559_; 
v_a_559_ = lean_ctor_get(v___y_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___y_558_, 1);
return v_a_559_;
}
else
{
lean_object* v_a_560_; 
v_a_560_ = lean_ctor_get(v___y_558_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___y_558_, 1);
v_a_556_ = v_a_560_;
goto _start;
}
}
v_resetjp_564_:
{
lean_object* v_fst_567_; lean_object* v_snd_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_600_; 
v_fst_567_ = lean_ctor_get(v_snd_562_, 0);
v_snd_568_ = lean_ctor_get(v_snd_562_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_snd_562_);
if (v_isSharedCheck_600_ == 0)
{
v___x_570_ = v_snd_562_;
v_isShared_571_ = v_isSharedCheck_600_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_snd_568_);
lean_inc(v_fst_567_);
lean_dec(v_snd_562_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_600_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; uint8_t v_decide_573_; 
v___x_572_ = lean_string_utf8_byte_size(v_s_555_);
v_decide_573_ = lean_nat_dec_eq(v_fst_567_, v___x_572_);
if (v_decide_573_ == 0)
{
uint32_t v___x_574_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___f_587_; uint8_t v_decide_592_; 
lean_del_object(v___x_570_);
lean_del_object(v___x_565_);
v___x_574_ = lean_string_utf8_get_fast(v_s_555_, v_fst_567_);
v___x_585_ = lean_string_utf8_next_fast(v_s_555_, v_fst_567_);
lean_dec(v_fst_567_);
v___x_586_ = lean_box_uint32(v___x_574_);
v___f_587_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_587_, 0, v___x_586_);
lean_closure_set(v___f_587_, 1, v___x_585_);
v_decide_592_ = lean_nat_dec_eq(v___x_585_, v___x_572_);
if (v_decide_592_ == 0)
{
goto v___jp_588_;
}
else
{
if (v_decide_573_ == 0)
{
lean_object* v_prev_x3f_593_; 
v_prev_x3f_593_ = lean_box(0);
v___y_576_ = v___f_587_;
v___y_577_ = v_prev_x3f_593_;
goto v___jp_575_;
}
else
{
goto v___jp_588_;
}
}
v___jp_575_:
{
uint8_t v___x_578_; 
v___x_578_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_snd_568_, v___x_574_, v___y_577_);
lean_dec(v___y_577_);
lean_dec(v_snd_568_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_box(0);
v___x_580_ = lean_apply_2(v___y_576_, v___x_579_, v_fst_563_);
v___y_558_ = v___x_580_;
goto v___jp_557_;
}
else
{
uint32_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = 92;
v___x_582_ = lean_string_push(v_fst_563_, v___x_581_);
v___x_583_ = lean_box(0);
v___x_584_ = lean_apply_2(v___y_576_, v___x_583_, v___x_582_);
v___y_558_ = v___x_584_;
goto v___jp_557_;
}
}
v___jp_588_:
{
uint32_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_string_utf8_get_fast(v_s_555_, v___x_585_);
v___x_590_ = lean_box_uint32(v___x_589_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
v___y_576_ = v___f_587_;
v___y_577_ = v___x_591_;
goto v___jp_575_;
}
}
else
{
lean_object* v___x_595_; 
if (v_isShared_571_ == 0)
{
v___x_595_ = v___x_570_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_fst_567_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_snd_568_);
v___x_595_ = v_reuseFailAlloc_599_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_597_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v___x_595_);
v___x_597_ = v___x_565_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_fst_563_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___boxed(lean_object* v_s_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_602_, v_a_603_);
lean_dec_ref(v_s_602_);
return v_res_604_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(uint32_t v___x_605_, lean_object* v___x_606_, lean_object* v_____r_607_, lean_object* v_s_x27_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_string_push(v_s_x27_608_, v___x_605_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_606_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v___x_605_ = stack[0].m_num;
lean_object* v___x_606_ = stack[1].m_obj;
lean_object* v_____r_607_ = stack[2].m_obj;
lean_object* v_s_x27_608_ = stack[3].m_obj;
lean_object* v_res_612_;
v_res_612_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_605_, v___x_606_, v_____r_607_, v_s_x27_608_);
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0___boxed(lean_object* v___x_613_, lean_object* v___x_614_, lean_object* v_____r_615_, lean_object* v_s_x27_616_){
_start:
{
uint32_t v___x_2265__boxed_617_; lean_object* v_res_618_; 
v___x_2265__boxed_617_ = lean_unbox_uint32(v___x_613_);
lean_dec(v___x_613_);
v_res_618_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_2265__boxed_617_, v___x_614_, v_____r_615_, v_s_x27_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(lean_object* v_s_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___y_622_; lean_object* v_fst_626_; lean_object* v_snd_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_652_; 
v_fst_626_ = lean_ctor_get(v_a_620_, 0);
v_snd_627_ = lean_ctor_get(v_a_620_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_a_620_);
if (v_isSharedCheck_652_ == 0)
{
v___x_629_ = v_a_620_;
v_isShared_630_ = v_isSharedCheck_652_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_snd_627_);
lean_inc(v_fst_626_);
lean_dec(v_a_620_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_652_;
goto v_resetjp_628_;
}
v___jp_621_:
{
if (lean_obj_tag(v___y_622_) == 0)
{
lean_object* v_a_623_; 
v_a_623_ = lean_ctor_get(v___y_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___y_622_, 1);
return v_a_623_;
}
else
{
lean_object* v_a_624_; 
v_a_624_ = lean_ctor_get(v___y_622_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___y_622_, 1);
v_a_620_ = v_a_624_;
goto _start;
}
}
v_resetjp_628_:
{
lean_object* v___x_631_; uint8_t v_decide_632_; 
v___x_631_ = lean_string_utf8_byte_size(v_s_619_);
v_decide_632_ = lean_nat_dec_eq(v_snd_627_, v___x_631_);
if (v_decide_632_ == 0)
{
uint32_t v___x_633_; lean_object* v___x_634_; lean_object* v___y_636_; uint8_t v_decide_644_; 
lean_del_object(v___x_629_);
v___x_633_ = lean_string_utf8_get_fast(v_s_619_, v_snd_627_);
v___x_634_ = lean_string_utf8_next_fast(v_s_619_, v_snd_627_);
lean_dec(v_snd_627_);
v_decide_644_ = lean_nat_dec_eq(v___x_634_, v___x_631_);
if (v_decide_644_ == 0)
{
uint32_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_string_utf8_get_fast(v_s_619_, v___x_634_);
v___x_646_ = lean_box_uint32(v___x_645_);
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
v___y_636_ = v___x_647_;
goto v___jp_635_;
}
else
{
lean_object* v_prev_x3f_648_; 
v_prev_x3f_648_ = lean_box(0);
v___y_636_ = v_prev_x3f_648_;
goto v___jp_635_;
}
v___jp_635_:
{
uint8_t v___x_637_; 
v___x_637_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v___x_633_, v___y_636_);
lean_dec(v___y_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_box(0);
v___x_639_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_633_, v___x_634_, v___x_638_, v_fst_626_);
v___y_622_ = v___x_639_;
goto v___jp_621_;
}
else
{
uint32_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = 92;
v___x_641_ = lean_string_push(v_fst_626_, v___x_640_);
v___x_642_ = lean_box(0);
v___x_643_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_633_, v___x_634_, v___x_642_, v___x_641_);
v___y_622_ = v___x_643_;
goto v___jp_621_;
}
}
}
else
{
lean_object* v___x_650_; 
if (v_isShared_630_ == 0)
{
v___x_650_ = v___x_629_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_fst_626_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_snd_627_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___boxed(lean_object* v_s_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_653_, v_a_654_);
lean_dec_ref(v_s_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object* v_s_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v_snd_665_; lean_object* v_fst_666_; lean_object* v_fst_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_676_; 
v___x_663_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1));
v___x_664_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_662_, v___x_663_);
v_snd_665_ = lean_ctor_get(v___x_664_, 1);
lean_inc(v_snd_665_);
v_fst_666_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_fst_666_);
lean_dec_ref(v___x_664_);
v_fst_667_ = lean_ctor_get(v_snd_665_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v_snd_665_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v_snd_665_, 1);
lean_dec(v_unused_677_);
v___x_669_ = v_snd_665_;
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_fst_667_);
lean_dec(v_snd_665_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v_fst_667_);
lean_ctor_set(v___x_669_, 0, v_fst_666_);
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_fst_666_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_fst_667_);
v___x_672_ = v_reuseFailAlloc_675_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v_fst_674_; 
v___x_673_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_662_, v___x_672_);
v_fst_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_fst_674_);
lean_dec_ref(v___x_673_);
return v_fst_674_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object* v_s_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_678_);
lean_dec_ref(v_s_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object* v_s_680_, lean_object* v_inst_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_680_, v_a_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object* v_s_684_, lean_object* v_inst_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_684_, v_inst_685_, v_a_686_);
lean_dec_ref(v_s_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(lean_object* v_s_688_, lean_object* v_inst_689_, lean_object* v_a_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_688_, v_a_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___boxed(lean_object* v_s_692_, lean_object* v_inst_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(v_s_692_, v_inst_693_, v_a_694_);
lean_dec_ref(v_s_692_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v_str_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_snd_698_; lean_object* v_fst_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_741_; 
v_snd_698_ = lean_ctor_get(v_a_697_, 1);
v_fst_699_ = lean_ctor_get(v_a_697_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_a_697_);
if (v_isSharedCheck_741_ == 0)
{
v___x_701_ = v_a_697_;
v_isShared_702_ = v_isSharedCheck_741_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_snd_698_);
lean_inc(v_fst_699_);
lean_dec(v_a_697_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_741_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_fst_703_; lean_object* v_snd_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_740_; 
v_fst_703_ = lean_ctor_get(v_snd_698_, 0);
v_snd_704_ = lean_ctor_get(v_snd_698_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_snd_698_);
if (v_isSharedCheck_740_ == 0)
{
v___x_706_ = v_snd_698_;
v_isShared_707_ = v_isSharedCheck_740_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_snd_704_);
lean_inc(v_fst_703_);
lean_dec(v_snd_698_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_740_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; uint8_t v_decide_709_; 
v___x_708_ = lean_string_utf8_byte_size(v_str_696_);
v_decide_709_ = lean_nat_dec_eq(v_snd_704_, v___x_708_);
if (v_decide_709_ == 0)
{
uint32_t v___x_710_; lean_object* v___x_711_; uint32_t v___x_712_; uint8_t v___x_713_; 
v___x_710_ = lean_string_utf8_get_fast(v_str_696_, v_snd_704_);
v___x_711_ = lean_string_utf8_next_fast(v_str_696_, v_snd_704_);
lean_dec(v_snd_704_);
v___x_712_ = 96;
v___x_713_ = lean_uint32_dec_eq(v___x_710_, v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v_longest_714_; lean_object* v___y_716_; uint8_t v___x_724_; 
v_longest_714_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_nat_dec_le(v_fst_699_, v_fst_703_);
if (v___x_724_ == 0)
{
lean_dec(v_fst_703_);
v___y_716_ = v_fst_699_;
goto v___jp_715_;
}
else
{
lean_dec(v_fst_699_);
v___y_716_ = v_fst_703_;
goto v___jp_715_;
}
v___jp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_711_);
lean_ctor_set(v___x_706_, 0, v_longest_714_);
v___x_718_ = v___x_706_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_longest_714_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_711_);
v___x_718_ = v_reuseFailAlloc_723_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_718_);
lean_ctor_set(v___x_701_, 0, v___y_716_);
v___x_720_ = v___x_701_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___y_716_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_722_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
v_a_697_ = v___x_720_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v_fst_703_, v___x_725_);
lean_dec(v_fst_703_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_711_);
lean_ctor_set(v___x_706_, 0, v___x_726_);
v___x_728_ = v___x_706_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_711_);
v___x_728_ = v_reuseFailAlloc_733_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_728_);
v___x_730_ = v___x_701_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_fst_699_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_732_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
v_a_697_ = v___x_730_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_735_; 
if (v_isShared_707_ == 0)
{
v___x_735_ = v___x_706_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_fst_703_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_snd_704_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_735_);
v___x_737_ = v___x_701_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_fst_699_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v_str_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_742_, v_a_743_);
lean_dec_ref(v_str_742_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(lean_object* v_str_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v_snd_753_; lean_object* v_fst_754_; lean_object* v_fst_755_; uint8_t v___x_756_; 
v___x_751_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1));
v___x_752_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_750_, v___x_751_);
v_snd_753_ = lean_ctor_get(v___x_752_, 1);
lean_inc(v_snd_753_);
v_fst_754_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_fst_754_);
lean_dec_ref(v___x_752_);
v_fst_755_ = lean_ctor_get(v_snd_753_, 0);
lean_inc(v_fst_755_);
lean_dec(v_snd_753_);
v___x_756_ = lean_nat_dec_le(v_fst_754_, v_fst_755_);
if (v___x_756_ == 0)
{
lean_dec(v_fst_755_);
return v_fst_754_;
}
else
{
lean_dec(v_fst_754_);
return v_fst_755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___boxed(lean_object* v_str_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_757_);
lean_dec_ref(v_str_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(lean_object* v_str_759_, lean_object* v_inst_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_759_, v_a_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v_str_763_, lean_object* v_inst_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(v_str_763_, v_inst_764_, v_a_765_);
lean_dec_ref(v_str_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
lean_object* v_zero_769_; uint8_t v_isZero_770_; 
v_zero_769_ = lean_unsigned_to_nat(0u);
v_isZero_770_ = lean_nat_dec_eq(v_x_767_, v_zero_769_);
if (v_isZero_770_ == 1)
{
lean_dec(v_x_767_);
return v_x_768_;
}
else
{
uint32_t v___x_771_; lean_object* v_one_772_; lean_object* v_n_773_; lean_object* v___x_774_; 
v___x_771_ = 96;
v_one_772_ = lean_unsigned_to_nat(1u);
v_n_773_ = lean_nat_sub(v_x_767_, v_one_772_);
lean_dec(v_x_767_);
v___x_774_ = lean_string_push(v_x_768_, v___x_771_);
v_x_767_ = v_n_773_;
v_x_768_ = v___x_774_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(lean_object* v_atLeast_776_, lean_object* v_str_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___y_780_; lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_784_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_777_);
v___x_785_ = lean_nat_dec_le(v_atLeast_776_, v___x_784_);
if (v___x_785_ == 0)
{
lean_dec(v___x_784_);
v___y_780_ = v_atLeast_776_;
goto v___jp_779_;
}
else
{
lean_dec(v_atLeast_776_);
v___y_780_ = v___x_784_;
goto v___jp_779_;
}
v___jp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v___y_780_, v___x_781_);
lean_dec(v___y_780_);
v___x_783_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(v___x_782_, v___x_778_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor___boxed(lean_object* v_atLeast_786_, lean_object* v_str_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v_atLeast_786_, v_str_787_);
lean_dec_ref(v_str_787_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object* v_str_790_){
_start:
{
lean_object* v___x_791_; lean_object* v_backticks_792_; lean_object* v___y_794_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_791_ = lean_unsigned_to_nat(0u);
v_backticks_792_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_791_, v_str_790_);
v___x_808_ = lean_string_utf8_byte_size(v_str_790_);
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_dec_le(v___x_809_, v___x_808_);
if (v___x_810_ == 0)
{
goto v___jp_801_;
}
else
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_812_ = lean_string_memcmp(v_str_790_, v___x_811_, v___x_791_, v___x_791_, v___x_809_);
if (v___x_812_ == 0)
{
goto v___jp_801_;
}
else
{
goto v___jp_797_;
}
}
v___jp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
lean_inc_ref(v_backticks_792_);
v___x_795_ = lean_string_append(v_backticks_792_, v___y_794_);
lean_dec_ref(v___y_794_);
v___x_796_ = lean_string_append(v___x_795_, v_backticks_792_);
lean_dec_ref(v_backticks_792_);
return v___x_796_;
}
v___jp_797_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_799_ = lean_string_append(v___x_798_, v_str_790_);
lean_dec_ref(v_str_790_);
v___x_800_ = lean_string_append(v___x_799_, v___x_798_);
v___y_794_ = v___x_800_;
goto v___jp_793_;
}
v___jp_801_:
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_802_ = lean_string_utf8_byte_size(v_str_790_);
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = lean_nat_dec_le(v___x_803_, v___x_802_);
if (v___x_804_ == 0)
{
v___y_794_ = v_str_790_;
goto v___jp_793_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_805_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_806_ = lean_nat_sub(v___x_802_, v___x_803_);
v___x_807_ = lean_string_memcmp(v_str_790_, v___x_805_, v___x_806_, v___x_791_, v___x_803_);
lean_dec(v___x_806_);
if (v___x_807_ == 0)
{
v___y_794_ = v_str_790_;
goto v___jp_793_;
}
else
{
goto v___jp_797_;
}
}
}
}
}
lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg(){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___closed__0));
return v___x_816_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_817_;
v_res_817_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg();
stack->m_obj
 = v_res_817_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___boxed(lean_object* v___dummy_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg();
return v_res_819_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg();
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(lean_object* v_s_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___boxed(lean_object* v_s_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v_s_823_);
lean_dec_ref(v_s_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(lean_object* v_str_825_, lean_object* v___x_826_, lean_object* v___x_827_, lean_object* v_a_828_, lean_object* v_b_829_){
_start:
{
lean_object* v_it_831_; lean_object* v_startInclusive_832_; lean_object* v_endExclusive_833_; 
if (lean_obj_tag(v_a_828_) == 0)
{
lean_object* v_currPos_837_; lean_object* v_searcher_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_861_; 
v_currPos_837_ = lean_ctor_get(v_a_828_, 0);
v_searcher_838_ = lean_ctor_get(v_a_828_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v_a_828_);
if (v_isSharedCheck_861_ == 0)
{
v___x_840_ = v_a_828_;
v_isShared_841_ = v_isSharedCheck_861_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_searcher_838_);
lean_inc(v_currPos_837_);
lean_dec(v_a_828_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_861_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
uint8_t v_decide_842_; 
v_decide_842_ = lean_nat_dec_eq(v_searcher_838_, v___x_827_);
if (v_decide_842_ == 0)
{
uint32_t v___x_843_; uint32_t v___x_844_; uint8_t v___x_845_; 
v___x_843_ = 10;
v___x_844_ = lean_string_utf8_get_fast(v_str_825_, v_searcher_838_);
v___x_845_ = lean_uint32_dec_eq(v___x_844_, v___x_843_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_string_utf8_next_fast(v_str_825_, v_searcher_838_);
lean_dec(v_searcher_838_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_846_);
v___x_848_ = v___x_840_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_currPos_837_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_846_);
v___x_848_ = v_reuseFailAlloc_850_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
v_a_828_ = v___x_848_;
goto _start;
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_slice_854_; lean_object* v_nextIt_856_; 
v___x_851_ = lean_string_utf8_next_fast(v_str_825_, v_searcher_838_);
v___x_852_ = lean_nat_sub(v___x_851_, v_searcher_838_);
v___x_853_ = lean_nat_add(v_searcher_838_, v___x_852_);
lean_dec(v___x_852_);
v_slice_854_ = l_String_Slice_subslice_x21(v___x_826_, v_currPos_837_, v_searcher_838_);
lean_inc(v___x_853_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_853_);
lean_ctor_set(v___x_840_, 0, v___x_853_);
v_nextIt_856_ = v___x_840_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___x_853_);
v_nextIt_856_ = v_reuseFailAlloc_859_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v_startInclusive_857_; lean_object* v_endExclusive_858_; 
v_startInclusive_857_ = lean_ctor_get(v_slice_854_, 0);
lean_inc(v_startInclusive_857_);
v_endExclusive_858_ = lean_ctor_get(v_slice_854_, 1);
lean_inc(v_endExclusive_858_);
lean_dec_ref(v_slice_854_);
v_it_831_ = v_nextIt_856_;
v_startInclusive_832_ = v_startInclusive_857_;
v_endExclusive_833_ = v_endExclusive_858_;
goto v___jp_830_;
}
}
}
else
{
lean_object* v___x_860_; 
lean_del_object(v___x_840_);
lean_dec(v_searcher_838_);
v___x_860_ = lean_box(1);
lean_inc(v___x_827_);
v_it_831_ = v___x_860_;
v_startInclusive_832_ = v_currPos_837_;
v_endExclusive_833_ = v___x_827_;
goto v___jp_830_;
}
}
}
else
{
lean_dec(v___x_827_);
return v_b_829_;
}
v___jp_830_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_string_utf8_extract_fast(v_str_825_, v_startInclusive_832_, v_endExclusive_833_);
lean_dec(v_endExclusive_833_);
lean_dec(v_startInclusive_832_);
v___x_835_ = lean_array_push(v_b_829_, v___x_834_);
v_a_828_ = v_it_831_;
v_b_829_ = v___x_835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg___boxed(lean_object* v_str_862_, lean_object* v___x_863_, lean_object* v___x_864_, lean_object* v_a_865_, lean_object* v_b_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_862_, v___x_863_, v___x_864_, v_a_865_, v_b_866_);
lean_dec_ref(v___x_863_);
lean_dec_ref(v_str_862_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(lean_object* v_str_868_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_string_utf8_byte_size(v_str_868_);
lean_inc_ref(v_str_868_);
v___x_871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_871_, 0, v_str_868_);
lean_ctor_set(v___x_871_, 1, v___x_869_);
lean_ctor_set(v___x_871_, 2, v___x_870_);
v___x_872_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0);
v___x_873_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_874_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_868_, v___x_871_, v___x_870_, v___x_872_, v___x_873_);
lean_dec_ref_known(v___x_871_, 3);
lean_dec_ref(v_str_868_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(lean_object* v_str_875_, lean_object* v___x_876_, lean_object* v___x_877_, lean_object* v_inst_878_, lean_object* v_R_879_, lean_object* v_a_880_, lean_object* v_b_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_875_, v___x_876_, v___x_877_, v_a_880_, v_b_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___boxed(lean_object* v_str_883_, lean_object* v___x_884_, lean_object* v___x_885_, lean_object* v_inst_886_, lean_object* v_R_887_, lean_object* v_a_888_, lean_object* v_b_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(v_str_883_, v___x_884_, v___x_885_, v_inst_886_, v_R_887_, v_a_888_, v_b_889_);
lean_dec_ref(v___x_884_);
lean_dec_ref(v_str_883_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(lean_object* v_str_891_){
_start:
{
lean_object* v___x_892_; lean_object* v_fence_893_; lean_object* v___y_895_; lean_object* v_body_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_892_ = lean_unsigned_to_nat(2u);
v_fence_893_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_892_, v_str_891_);
v_body_901_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(v_str_891_);
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_array_get_size(v_body_901_);
v___x_904_ = lean_nat_dec_lt(v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
v___y_895_ = v_body_901_;
goto v___jp_894_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_nat_sub(v___x_903_, v___x_906_);
v___x_908_ = lean_array_get_borrowed(v___x_905_, v_body_901_, v___x_907_);
lean_dec(v___x_907_);
v___x_909_ = lean_string_utf8_byte_size(v___x_908_);
v___x_910_ = lean_nat_dec_eq(v___x_909_, v___x_902_);
if (v___x_910_ == 0)
{
v___y_895_ = v_body_901_;
goto v___jp_894_;
}
else
{
lean_object* v___x_911_; 
v___x_911_ = lean_array_pop(v_body_901_);
v___y_895_ = v___x_911_;
goto v___jp_894_;
}
}
v___jp_894_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_mk_empty_array_with_capacity(v___x_896_);
v___x_898_ = lean_array_push(v___x_897_, v_fence_893_);
lean_inc_ref(v___x_898_);
v___x_899_ = l_Array_append___redArg(v___x_898_, v___y_895_);
lean_dec_ref(v___y_895_);
v___x_900_ = l_Array_append___redArg(v___x_899_, v___x_898_);
lean_dec_ref(v___x_898_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_912_, lean_object* v_pos_913_){
_start:
{
lean_object* v_str_914_; lean_object* v_startInclusive_915_; lean_object* v_endExclusive_916_; lean_object* v___x_917_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v_decide_928_; 
v_str_914_ = lean_ctor_get(v_s_912_, 0);
v_startInclusive_915_ = lean_ctor_get(v_s_912_, 1);
v_endExclusive_916_ = lean_ctor_get(v_s_912_, 2);
v___x_917_ = lean_nat_add(v_startInclusive_915_, v_pos_913_);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_nat_sub(v_endExclusive_916_, v___x_917_);
v_decide_928_ = lean_nat_dec_eq(v___x_926_, v___x_927_);
lean_dec(v___x_927_);
if (v_decide_928_ == 0)
{
uint32_t v___x_929_; uint32_t v___x_930_; uint8_t v___x_931_; 
v___x_929_ = lean_string_utf8_get_fast(v_str_914_, v___x_917_);
v___x_930_ = 32;
v___x_931_ = lean_uint32_dec_eq(v___x_929_, v___x_930_);
if (v___x_931_ == 0)
{
uint32_t v___x_932_; uint8_t v___x_933_; 
v___x_932_ = 9;
v___x_933_ = lean_uint32_dec_eq(v___x_929_, v___x_932_);
if (v___x_933_ == 0)
{
uint32_t v___x_934_; uint8_t v___x_935_; 
v___x_934_ = 13;
v___x_935_ = lean_uint32_dec_eq(v___x_929_, v___x_934_);
if (v___x_935_ == 0)
{
uint32_t v___x_936_; uint8_t v___x_937_; 
v___x_936_ = 10;
v___x_937_ = lean_uint32_dec_eq(v___x_929_, v___x_936_);
if (v___x_937_ == 0)
{
lean_dec(v___x_917_);
return v_pos_913_;
}
else
{
goto v___jp_918_;
}
}
else
{
goto v___jp_918_;
}
}
else
{
goto v___jp_918_;
}
}
else
{
goto v___jp_918_;
}
}
else
{
lean_dec(v___x_917_);
return v_pos_913_;
}
v___jp_918_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_919_ = lean_string_utf8_next_fast(v_str_914_, v___x_917_);
v___x_920_ = lean_nat_sub(v___x_919_, v___x_917_);
lean_dec(v___x_917_);
v___x_921_ = lean_nat_add(v_pos_913_, v___x_920_);
lean_dec(v___x_920_);
v___x_922_ = lean_unsigned_to_nat(1u);
v___x_923_ = lean_nat_add(v_pos_913_, v___x_922_);
v___x_924_ = lean_nat_dec_le(v___x_923_, v___x_921_);
lean_dec(v___x_923_);
if (v___x_924_ == 0)
{
lean_dec(v___x_921_);
return v_pos_913_;
}
else
{
lean_dec(v_pos_913_);
v_pos_913_ = v___x_921_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(lean_object* v_s_938_, lean_object* v_pos_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_938_, v_pos_939_);
lean_dec_ref(v_s_938_);
return v_res_940_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Doc_Inline_empty___redArg();
return v___x_941_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_943_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(lean_object* v_a_945_){
_start:
{
if (lean_obj_tag(v_a_945_) == 0)
{
lean_object* v___x_946_; 
v___x_946_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
return v___x_946_;
}
else
{
lean_object* v_head_947_; 
v_head_947_ = lean_ctor_get(v_a_945_, 0);
lean_inc(v_head_947_);
switch(lean_obj_tag(v_head_947_))
{
case 0:
{
lean_object* v_tail_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_992_; 
v_tail_948_ = lean_ctor_get(v_a_945_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_a_945_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v_a_945_, 0);
lean_dec(v_unused_993_);
v___x_950_ = v_a_945_;
v_isShared_951_ = v_isSharedCheck_992_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_tail_948_);
lean_dec(v_a_945_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_992_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_string_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_991_; 
v_string_952_ = lean_ctor_get(v_head_947_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v_head_947_);
if (v_isSharedCheck_991_ == 0)
{
v___x_954_ = v_head_947_;
v_isShared_955_ = v_isSharedCheck_991_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_string_952_);
lean_dec(v_head_947_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_991_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v_decide_960_; 
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_string_utf8_byte_size(v_string_952_);
lean_inc_ref(v_string_952_);
v___x_958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_958_, 0, v_string_952_);
lean_ctor_set(v___x_958_, 1, v___x_956_);
lean_ctor_set(v___x_958_, 2, v___x_957_);
v___x_959_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_958_, v___x_956_);
lean_dec_ref_known(v___x_958_, 3);
v_decide_960_ = lean_nat_dec_eq(v___x_959_, v___x_957_);
if (v_decide_960_ == 0)
{
lean_object* v_s1_961_; lean_object* v_s2_962_; lean_object* v___x_964_; 
v_s1_961_ = lean_string_utf8_extract_fast(v_string_952_, v___x_956_, v___x_959_);
v_s2_962_ = lean_string_utf8_extract_fast(v_string_952_, v___x_959_, v___x_957_);
lean_dec(v___x_959_);
lean_dec_ref(v_string_952_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v_s2_962_);
v___x_964_ = v___x_954_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_s2_962_);
v___x_964_ = v_reuseFailAlloc_979_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_965_ = lean_array_mk(v_tail_948_);
v___x_966_ = lean_array_get_size(v___x_965_);
v___x_967_ = lean_nat_dec_eq(v___x_966_, v___x_956_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_mk_empty_array_with_capacity(v___x_968_);
v___x_970_ = lean_array_push(v___x_969_, v___x_964_);
v___x_971_ = l_Array_append___redArg(v___x_970_, v___x_965_);
lean_dec_ref(v___x_965_);
v___x_972_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 0);
lean_ctor_set(v___x_950_, 1, v___x_972_);
lean_ctor_set(v___x_950_, 0, v_s1_961_);
v___x_974_ = v___x_950_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_s1_961_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
else
{
lean_object* v___x_977_; 
lean_dec_ref(v___x_965_);
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 0);
lean_ctor_set(v___x_950_, 1, v___x_964_);
lean_ctor_set(v___x_950_, 0, v_s1_961_);
v___x_977_ = v___x_950_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_s1_961_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_964_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v___x_980_; lean_object* v_fst_981_; lean_object* v_snd_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_990_; 
lean_dec(v___x_959_);
lean_del_object(v___x_954_);
lean_del_object(v___x_950_);
v___x_980_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_tail_948_);
v_fst_981_ = lean_ctor_get(v___x_980_, 0);
v_snd_982_ = lean_ctor_get(v___x_980_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_990_ == 0)
{
v___x_984_ = v___x_980_;
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_snd_982_);
lean_inc(v_fst_981_);
lean_dec(v___x_980_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_string_append(v_string_952_, v_fst_981_);
lean_dec(v_fst_981_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_986_);
v___x_988_ = v___x_984_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_snd_982_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
case 9:
{
lean_object* v_tail_994_; lean_object* v_content_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_tail_994_ = lean_ctor_get(v_a_945_, 1);
lean_inc(v_tail_994_);
lean_dec_ref_known(v_a_945_, 2);
v_content_995_ = lean_ctor_get(v_head_947_, 0);
lean_inc_ref(v_content_995_);
lean_dec_ref_known(v_head_947_, 1);
v___x_996_ = lean_array_to_list(v_content_995_);
v___x_997_ = l_List_appendTR___redArg(v___x_996_, v_tail_994_);
v_a_945_ = v___x_997_;
goto _start;
}
default: 
{
lean_object* v_tail_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1037_; 
v_tail_999_ = lean_ctor_get(v_a_945_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_a_945_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v_a_945_, 0);
lean_dec(v_unused_1038_);
v___x_1001_ = v_a_945_;
v_isShared_1002_ = v_isSharedCheck_1037_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_tail_999_);
lean_dec(v_a_945_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1037_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1004_ = lean_array_mk(v_tail_999_);
if (lean_obj_tag(v_head_947_) == 9)
{
lean_object* v_content_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v_content_1005_ = lean_ctor_get(v_head_947_, 0);
v___x_1006_ = lean_array_get_size(v_content_1005_);
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = lean_nat_dec_eq(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1009_ = lean_array_get_size(v___x_1004_);
v___x_1010_ = lean_nat_dec_eq(v___x_1009_, v___x_1007_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
lean_inc_ref(v_content_1005_);
lean_dec_ref_known(v_head_947_, 1);
v___x_1011_ = l_Array_append___redArg(v_content_1005_, v___x_1004_);
lean_dec_ref(v___x_1004_);
v___x_1012_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 0);
lean_ctor_set(v___x_1001_, 1, v___x_1012_);
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1014_ = v___x_1001_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1003_);
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
lean_dec_ref(v___x_1004_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 0);
lean_ctor_set(v___x_1001_, 1, v_head_947_);
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1017_ = v___x_1001_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_head_947_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
lean_dec_ref_known(v_head_947_, 1);
v___x_1019_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1004_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 0);
lean_ctor_set(v___x_1001_, 1, v___x_1019_);
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1021_ = v___x_1001_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1023_ = lean_array_get_size(v___x_1004_);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_nat_dec_eq(v___x_1023_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_mk_empty_array_with_capacity(v___x_1026_);
v___x_1028_ = lean_array_push(v___x_1027_, v_head_947_);
v___x_1029_ = l_Array_append___redArg(v___x_1028_, v___x_1004_);
lean_dec_ref(v___x_1004_);
v___x_1030_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 0);
lean_ctor_set(v___x_1001_, 1, v___x_1030_);
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1032_ = v___x_1001_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
else
{
lean_object* v___x_1035_; 
lean_dec_ref(v___x_1004_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 0);
lean_ctor_set(v___x_1001_, 1, v_head_947_);
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1035_ = v___x_1001_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_head_947_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(lean_object* v_i_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(lean_object* v_inline_1042_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1044_, 0, v_inline_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(lean_object* v_i_1046_, lean_object* v_inline_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(lean_object* v_s_1049_, lean_object* v_pos_1050_){
_start:
{
lean_object* v_str_1051_; lean_object* v_startInclusive_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v_decide_1056_; 
v_str_1051_ = lean_ctor_get(v_s_1049_, 0);
v_startInclusive_1052_ = lean_ctor_get(v_s_1049_, 1);
v___x_1053_ = lean_nat_add(v_startInclusive_1052_, v_pos_1050_);
v___x_1054_ = lean_nat_sub(v___x_1053_, v_startInclusive_1052_);
v___x_1055_ = lean_unsigned_to_nat(0u);
v_decide_1056_ = lean_nat_dec_eq(v___x_1054_, v___x_1055_);
if (v_decide_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1065_; uint32_t v___x_1066_; uint32_t v___x_1067_; uint8_t v___x_1068_; 
lean_inc(v_startInclusive_1052_);
lean_inc_ref(v_str_1051_);
v___x_1057_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1057_, 0, v_str_1051_);
lean_ctor_set(v___x_1057_, 1, v_startInclusive_1052_);
lean_ctor_set(v___x_1057_, 2, v___x_1053_);
v___x_1058_ = lean_unsigned_to_nat(1u);
v___x_1059_ = lean_nat_sub(v___x_1054_, v___x_1058_);
lean_dec(v___x_1054_);
v___x_1060_ = l_String_Slice_posLE(v___x_1057_, v___x_1059_);
lean_dec_ref_known(v___x_1057_, 3);
v___x_1065_ = lean_nat_add(v_startInclusive_1052_, v___x_1060_);
v___x_1066_ = lean_string_utf8_get_fast(v_str_1051_, v___x_1065_);
lean_dec(v___x_1065_);
v___x_1067_ = 32;
v___x_1068_ = lean_uint32_dec_eq(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
uint32_t v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = 9;
v___x_1070_ = lean_uint32_dec_eq(v___x_1066_, v___x_1069_);
if (v___x_1070_ == 0)
{
uint32_t v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = 13;
v___x_1072_ = lean_uint32_dec_eq(v___x_1066_, v___x_1071_);
if (v___x_1072_ == 0)
{
uint32_t v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = 10;
v___x_1074_ = lean_uint32_dec_eq(v___x_1066_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_dec(v___x_1060_);
return v_pos_1050_;
}
else
{
goto v___jp_1061_;
}
}
else
{
goto v___jp_1061_;
}
}
else
{
goto v___jp_1061_;
}
}
else
{
goto v___jp_1061_;
}
v___jp_1061_:
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = lean_nat_add(v___x_1060_, v___x_1058_);
v___x_1063_ = lean_nat_dec_le(v___x_1062_, v_pos_1050_);
lean_dec(v___x_1062_);
if (v___x_1063_ == 0)
{
lean_dec(v___x_1060_);
return v_pos_1050_;
}
else
{
lean_dec(v_pos_1050_);
v_pos_1050_ = v___x_1060_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1054_);
lean_dec(v___x_1053_);
return v_pos_1050_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_1075_, lean_object* v_pos_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_1075_, v_pos_1076_);
lean_dec_ref(v_s_1075_);
return v_res_1077_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1079_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___x_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_xs_1081_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1082_ = lean_array_get_size(v_xs_1081_);
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_nat_dec_eq(v___x_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = lean_unsigned_to_nat(1u);
v___x_1086_ = lean_nat_sub(v___x_1082_, v___x_1085_);
v___x_1087_ = lean_array_fget(v_xs_1081_, v___x_1086_);
lean_dec(v___x_1086_);
switch(lean_obj_tag(v___x_1087_))
{
case 0:
{
lean_object* v_string_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1118_; 
v_string_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1118_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_string_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1118_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v_decide_1095_; 
v___x_1092_ = lean_string_utf8_byte_size(v_string_1088_);
lean_inc_ref(v_string_1088_);
v___x_1093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1093_, 0, v_string_1088_);
lean_ctor_set(v___x_1093_, 1, v___x_1083_);
lean_ctor_set(v___x_1093_, 2, v___x_1092_);
v___x_1094_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_1093_, v___x_1083_);
v_decide_1095_ = lean_nat_dec_eq(v___x_1094_, v___x_1092_);
lean_dec(v___x_1094_);
if (v_decide_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1096_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_1093_, v___x_1092_);
lean_dec_ref_known(v___x_1093_, 3);
v___x_1097_ = lean_array_pop(v_xs_1081_);
v___x_1098_ = lean_string_utf8_extract_fast(v_string_1088_, v___x_1083_, v___x_1096_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1098_);
v___x_1100_ = v___x_1090_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1101_ = lean_array_push(v___x_1097_, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
v___x_1103_ = lean_string_utf8_extract_fast(v_string_1088_, v___x_1096_, v___x_1092_);
lean_dec(v___x_1096_);
lean_dec_ref(v_string_1088_);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
return v___x_1104_;
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_fst_1108_; lean_object* v_snd_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1117_; 
lean_dec_ref_known(v___x_1093_, 3);
lean_del_object(v___x_1090_);
v___x_1106_ = lean_array_pop(v_xs_1081_);
v___x_1107_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1106_);
v_fst_1108_ = lean_ctor_get(v___x_1107_, 0);
v_snd_1109_ = lean_ctor_get(v___x_1107_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1111_ = v___x_1107_;
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_snd_1109_);
lean_inc(v_fst_1108_);
lean_dec(v___x_1107_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1113_ = lean_string_append(v_snd_1109_, v_string_1088_);
lean_dec_ref(v_string_1088_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v___x_1113_);
v___x_1115_ = v___x_1111_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_fst_1108_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
case 9:
{
lean_object* v_content_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_content_1119_ = lean_ctor_get(v___x_1087_, 0);
lean_inc_ref(v_content_1119_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1120_ = lean_array_pop(v_xs_1081_);
v___x_1121_ = l_Array_append___redArg(v___x_1120_, v_content_1119_);
lean_dec_ref(v_content_1119_);
v_xs_1081_ = v___x_1121_;
goto _start;
}
default: 
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_dec(v___x_1087_);
v___x_1123_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_xs_1081_);
v___x_1124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
return v___x_1125_;
}
}
}
else
{
lean_object* v___x_1126_; 
lean_dec_ref(v_xs_1081_);
v___x_1126_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_1127_, lean_object* v_xs_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_xs_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_1130_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_mk_empty_array_with_capacity(v___x_1131_);
v___x_1133_ = lean_array_push(v___x_1132_, v_inline_1130_);
v___x_1134_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_1135_, lean_object* v_inline_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v_fst_1140_; lean_object* v_snd_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1149_; 
v___x_1139_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1138_);
v_fst_1140_ = lean_ctor_get(v___x_1139_, 0);
v_snd_1141_ = lean_ctor_get(v___x_1139_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1143_ = v___x_1139_;
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1141_);
lean_inc(v_fst_1140_);
lean_dec(v___x_1139_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_1141_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1145_);
v___x_1147_ = v___x_1143_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_fst_1140_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_1150_, lean_object* v_inline_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_instMonadEIO___redArg();
return v___x_1153_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0);
v___x_1155_ = l_StateRefT_x27_instMonad___redArg(v___x_1154_);
return v___x_1155_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13));
v___x_1185_ = lean_unsigned_to_nat(3u);
v___x_1186_ = lean_mk_empty_array_with_capacity(v___x_1185_);
v___x_1187_ = lean_array_push(v___x_1186_, v___x_1184_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object* v_inst_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1190_, v_x_1191_, v_x_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
return v_res_1197_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_pieces_1206_; lean_object* v_pieces_1210_; lean_object* v___x_1213_; lean_object* v_toApplicative_1214_; lean_object* v_toFunctor_1215_; lean_object* v_toSeq_1216_; lean_object* v_toSeqLeft_1217_; lean_object* v_toSeqRight_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1213_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1214_ = lean_ctor_get(v___x_1213_, 0);
v_toFunctor_1215_ = lean_ctor_get(v_toApplicative_1214_, 0);
v_toSeq_1216_ = lean_ctor_get(v_toApplicative_1214_, 2);
v_toSeqLeft_1217_ = lean_ctor_get(v_toApplicative_1214_, 3);
v_toSeqRight_1218_ = lean_ctor_get(v_toApplicative_1214_, 4);
v___f_1219_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1220_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1215_, 2);
v___f_1221_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1221_, 0, v_toFunctor_1215_);
v___f_1222_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1222_, 0, v_toFunctor_1215_);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___f_1221_);
lean_ctor_set(v___x_1223_, 1, v___f_1222_);
lean_inc(v_toSeqRight_1218_);
v___f_1224_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1224_, 0, v_toSeqRight_1218_);
lean_inc(v_toSeqLeft_1217_);
v___f_1225_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1225_, 0, v_toSeqLeft_1217_);
lean_inc(v_toSeq_1216_);
v___f_1226_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1226_, 0, v_toSeq_1216_);
v___x_1227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1223_);
lean_ctor_set(v___x_1227_, 1, v___f_1219_);
lean_ctor_set(v___x_1227_, 2, v___f_1226_);
lean_ctor_set(v___x_1227_, 3, v___f_1225_);
lean_ctor_set(v___x_1227_, 4, v___f_1224_);
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set(v___x_1228_, 1, v___f_1220_);
v___x_1229_ = l_StateRefT_x27_instMonad___redArg(v___x_1228_);
switch(lean_obj_tag(v_x_1200_))
{
case 0:
{
lean_object* v_string_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec_ref(v___x_1229_);
lean_dec_ref(v_x_1199_);
lean_dec_ref(v_inst_1198_);
v_string_1230_ = lean_ctor_get(v_x_1200_, 0);
lean_inc_ref(v_string_1230_);
lean_dec_ref_known(v_x_1200_, 1);
v___x_1231_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1230_);
lean_dec_ref(v_string_1230_);
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_mk_empty_array_with_capacity(v___x_1232_);
v___x_1234_ = lean_array_push(v___x_1233_, v___x_1231_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
case 1:
{
lean_object* v_content_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v___x_1229_);
v_content_1236_ = lean_ctor_get(v_x_1200_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_x_1200_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1238_ = v_x_1200_;
v_isShared_1239_ = v_isSharedCheck_1287_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_content_1236_);
lean_dec(v_x_1200_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1287_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set_tag(v___x_1238_, 9);
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_content_1236_);
v___x_1241_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1242_; lean_object* v_snd_1243_; lean_object* v_fst_1244_; lean_object* v_fst_1245_; lean_object* v_snd_1246_; lean_object* v_pieces_1248_; uint8_t v_inEmph_1256_; uint8_t v_inBold_1257_; uint8_t v_inLink_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1285_; 
v___x_1242_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1241_);
v_snd_1243_ = lean_ctor_get(v___x_1242_, 1);
lean_inc(v_snd_1243_);
v_fst_1244_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_fst_1244_);
lean_dec_ref(v___x_1242_);
v_fst_1245_ = lean_ctor_get(v_snd_1243_, 0);
lean_inc(v_fst_1245_);
v_snd_1246_ = lean_ctor_get(v_snd_1243_, 1);
lean_inc(v_snd_1246_);
lean_dec(v_snd_1243_);
v_inEmph_1256_ = lean_ctor_get_uint8(v_x_1199_, 0);
v_inBold_1257_ = lean_ctor_get_uint8(v_x_1199_, 1);
v_inLink_1258_ = lean_ctor_get_uint8(v_x_1199_, 2);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1260_ = v_x_1199_;
v_isShared_1261_ = v_isSharedCheck_1285_;
goto v_resetjp_1259_;
}
else
{
lean_dec(v_x_1199_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1285_;
goto v_resetjp_1259_;
}
v___jp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1249_ = lean_string_utf8_byte_size(v_snd_1246_);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_nat_dec_eq(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_mk_empty_array_with_capacity(v___x_1252_);
v___x_1254_ = lean_array_push(v___x_1253_, v_snd_1246_);
v___x_1255_ = lean_array_push(v_pieces_1248_, v___x_1254_);
v_pieces_1210_ = v___x_1255_;
goto v___jp_1209_;
}
else
{
lean_dec(v_snd_1246_);
v_pieces_1210_ = v_pieces_1248_;
goto v___jp_1209_;
}
}
v_resetjp_1259_:
{
uint8_t v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = 1;
if (v_isShared_1261_ == 0)
{
v___x_1264_ = v___x_1260_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 1, v_inBold_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, 2, v_inLink_1258_);
v___x_1264_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; 
lean_ctor_set_uint8(v___x_1264_, 0, v___x_1262_);
v___x_1265_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1198_, v___x_1264_, v_fst_1245_, v_a_1201_, v_a_1202_, v_a_1203_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v_pieces_1268_; lean_object* v_pieces_1273_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1276_ = lean_unsigned_to_nat(0u);
v___x_1277_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1278_ = lean_string_utf8_byte_size(v_fst_1244_);
v___x_1279_ = lean_nat_dec_eq(v___x_1278_, v___x_1276_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = lean_mk_empty_array_with_capacity(v___x_1280_);
v___x_1282_ = lean_array_push(v___x_1281_, v_fst_1244_);
v___x_1283_ = lean_array_push(v___x_1277_, v___x_1282_);
v_pieces_1273_ = v___x_1283_;
goto v___jp_1272_;
}
else
{
lean_dec(v_fst_1244_);
v_pieces_1273_ = v___x_1277_;
goto v___jp_1272_;
}
v___jp_1267_:
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_array_push(v_pieces_1268_, v_a_1266_);
if (v_inEmph_1256_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1271_ = lean_array_push(v___x_1269_, v___x_1270_);
v_pieces_1248_ = v___x_1271_;
goto v___jp_1247_;
}
else
{
v_pieces_1248_ = v___x_1269_;
goto v___jp_1247_;
}
}
v___jp_1272_:
{
if (v_inEmph_1256_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1275_ = lean_array_push(v_pieces_1273_, v___x_1274_);
v_pieces_1268_ = v___x_1275_;
goto v___jp_1267_;
}
else
{
v_pieces_1268_ = v_pieces_1273_;
goto v___jp_1267_;
}
}
}
else
{
lean_dec(v_snd_1246_);
lean_dec(v_fst_1244_);
return v___x_1265_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v___x_1229_);
v_content_1288_ = lean_ctor_get(v_x_1200_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_x_1200_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1290_ = v_x_1200_;
v_isShared_1291_ = v_isSharedCheck_1339_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_content_1288_);
lean_dec(v_x_1200_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1339_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set_tag(v___x_1290_, 9);
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_content_1288_);
v___x_1293_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; lean_object* v_snd_1295_; lean_object* v_fst_1296_; lean_object* v_fst_1297_; lean_object* v_snd_1298_; lean_object* v_pieces_1300_; uint8_t v_inEmph_1308_; uint8_t v_inBold_1309_; uint8_t v_inLink_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1337_; 
v___x_1294_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1293_);
v_snd_1295_ = lean_ctor_get(v___x_1294_, 1);
lean_inc(v_snd_1295_);
v_fst_1296_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_fst_1296_);
lean_dec_ref(v___x_1294_);
v_fst_1297_ = lean_ctor_get(v_snd_1295_, 0);
lean_inc(v_fst_1297_);
v_snd_1298_ = lean_ctor_get(v_snd_1295_, 1);
lean_inc(v_snd_1298_);
lean_dec(v_snd_1295_);
v_inEmph_1308_ = lean_ctor_get_uint8(v_x_1199_, 0);
v_inBold_1309_ = lean_ctor_get_uint8(v_x_1199_, 1);
v_inLink_1310_ = lean_ctor_get_uint8(v_x_1199_, 2);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1312_ = v_x_1199_;
v_isShared_1313_ = v_isSharedCheck_1337_;
goto v_resetjp_1311_;
}
else
{
lean_dec(v_x_1199_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1337_;
goto v_resetjp_1311_;
}
v___jp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1301_ = lean_string_utf8_byte_size(v_snd_1298_);
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = lean_nat_dec_eq(v___x_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = lean_mk_empty_array_with_capacity(v___x_1304_);
v___x_1306_ = lean_array_push(v___x_1305_, v_snd_1298_);
v___x_1307_ = lean_array_push(v_pieces_1300_, v___x_1306_);
v_pieces_1206_ = v___x_1307_;
goto v___jp_1205_;
}
else
{
lean_dec(v_snd_1298_);
v_pieces_1206_ = v_pieces_1300_;
goto v___jp_1205_;
}
}
v_resetjp_1311_:
{
uint8_t v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = 1;
if (v_isShared_1313_ == 0)
{
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1336_, 0, v_inEmph_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1336_, 2, v_inLink_1310_);
v___x_1316_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; 
lean_ctor_set_uint8(v___x_1316_, 1, v___x_1314_);
v___x_1317_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1198_, v___x_1316_, v_fst_1297_, v_a_1201_, v_a_1202_, v_a_1203_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v_pieces_1320_; lean_object* v_pieces_1325_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1330_ = lean_string_utf8_byte_size(v_fst_1296_);
v___x_1331_ = lean_nat_dec_eq(v___x_1330_, v___x_1328_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1332_ = lean_unsigned_to_nat(1u);
v___x_1333_ = lean_mk_empty_array_with_capacity(v___x_1332_);
v___x_1334_ = lean_array_push(v___x_1333_, v_fst_1296_);
v___x_1335_ = lean_array_push(v___x_1329_, v___x_1334_);
v_pieces_1325_ = v___x_1335_;
goto v___jp_1324_;
}
else
{
lean_dec(v_fst_1296_);
v_pieces_1325_ = v___x_1329_;
goto v___jp_1324_;
}
v___jp_1319_:
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_array_push(v_pieces_1320_, v_a_1318_);
if (v_inBold_1309_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1323_ = lean_array_push(v___x_1321_, v___x_1322_);
v_pieces_1300_ = v___x_1323_;
goto v___jp_1299_;
}
else
{
v_pieces_1300_ = v___x_1321_;
goto v___jp_1299_;
}
}
v___jp_1324_:
{
if (v_inBold_1309_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1327_ = lean_array_push(v_pieces_1325_, v___x_1326_);
v_pieces_1320_ = v___x_1327_;
goto v___jp_1319_;
}
else
{
v_pieces_1320_ = v_pieces_1325_;
goto v___jp_1319_;
}
}
}
else
{
lean_dec(v_snd_1298_);
lean_dec(v_fst_1296_);
return v___x_1317_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec_ref(v___x_1229_);
lean_dec_ref(v_x_1199_);
lean_dec_ref(v_inst_1198_);
v_string_1340_ = lean_ctor_get(v_x_1200_, 0);
lean_inc_ref(v_string_1340_);
lean_dec_ref_known(v_x_1200_, 1);
v___x_1341_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1340_);
v___x_1342_ = lean_unsigned_to_nat(1u);
v___x_1343_ = lean_mk_empty_array_with_capacity(v___x_1342_);
v___x_1344_ = lean_array_push(v___x_1343_, v___x_1341_);
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
return v___x_1345_;
}
case 4:
{
uint8_t v_mode_1346_; 
lean_dec_ref(v___x_1229_);
lean_dec_ref(v_x_1199_);
lean_dec_ref(v_inst_1198_);
v_mode_1346_ = lean_ctor_get_uint8(v_x_1200_, sizeof(void*)*1);
if (v_mode_1346_ == 0)
{
lean_object* v_string_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_string_1347_ = lean_ctor_get(v_x_1200_, 0);
lean_inc_ref(v_string_1347_);
lean_dec_ref_known(v_x_1200_, 1);
v___x_1348_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_1349_ = lean_string_append(v___x_1348_, v_string_1347_);
lean_dec_ref(v_string_1347_);
v___x_1350_ = lean_string_append(v___x_1349_, v___x_1348_);
v___x_1351_ = lean_unsigned_to_nat(1u);
v___x_1352_ = lean_mk_empty_array_with_capacity(v___x_1351_);
v___x_1353_ = lean_array_push(v___x_1352_, v___x_1350_);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
else
{
lean_object* v_string_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_string_1355_ = lean_ctor_get(v_x_1200_, 0);
lean_inc_ref(v_string_1355_);
lean_dec_ref_known(v_x_1200_, 1);
v___x_1356_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_1357_ = lean_string_append(v___x_1356_, v_string_1355_);
lean_dec_ref(v_string_1355_);
v___x_1358_ = lean_string_append(v___x_1357_, v___x_1356_);
v___x_1359_ = lean_unsigned_to_nat(1u);
v___x_1360_ = lean_mk_empty_array_with_capacity(v___x_1359_);
v___x_1361_ = lean_array_push(v___x_1360_, v___x_1358_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
}
case 5:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec_ref_known(v_x_1200_, 1);
lean_dec_ref(v___x_1229_);
lean_dec_ref(v_x_1199_);
lean_dec_ref(v_inst_1198_);
v___x_1363_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
case 6:
{
uint8_t v_inLink_1365_; 
v_inLink_1365_ = lean_ctor_get_uint8(v_x_1199_, 2);
if (v_inLink_1365_ == 0)
{
lean_object* v_content_1366_; lean_object* v_url_1367_; uint8_t v_inEmph_1368_; uint8_t v_inBold_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1398_; 
lean_dec_ref(v___x_1229_);
v_content_1366_ = lean_ctor_get(v_x_1200_, 0);
lean_inc_ref(v_content_1366_);
v_url_1367_ = lean_ctor_get(v_x_1200_, 1);
lean_inc_ref(v_url_1367_);
lean_dec_ref_known(v_x_1200_, 2);
v_inEmph_1368_ = lean_ctor_get_uint8(v_x_1199_, 0);
v_inBold_1369_ = lean_ctor_get_uint8(v_x_1199_, 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1371_ = v_x_1199_;
v_isShared_1372_ = v_isSharedCheck_1398_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_x_1199_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1398_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
uint8_t v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = 1;
if (v_isShared_1372_ == 0)
{
v___x_1375_ = v___x_1371_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, 0, v_inEmph_1368_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, 1, v_inBold_1369_);
v___x_1375_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_ctor_set_uint8(v___x_1375_, 2, v___x_1373_);
v___x_1376_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_content_1366_);
v___x_1377_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1198_, v___x_1375_, v___x_1376_, v_a_1201_, v_a_1202_, v_a_1203_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1396_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1396_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1396_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1382_ = lean_unsigned_to_nat(1u);
v___x_1383_ = lean_mk_empty_array_with_capacity(v___x_1382_);
v___x_1384_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1385_ = lean_string_append(v___x_1384_, v_url_1367_);
lean_dec_ref(v_url_1367_);
v___x_1386_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1387_ = lean_string_append(v___x_1385_, v___x_1386_);
v___x_1388_ = lean_array_push(v___x_1383_, v___x_1387_);
v___x_1389_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_1390_ = lean_array_push(v___x_1389_, v_a_1378_);
v___x_1391_ = lean_array_push(v___x_1390_, v___x_1388_);
v___x_1392_ = l_Lean_Doc_joinInlines(v___x_1391_);
lean_dec_ref(v___x_1391_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1392_);
v___x_1394_ = v___x_1380_;
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
lean_dec_ref(v_url_1367_);
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_content_1399_; lean_object* v___x_1400_; size_t v_sz_1401_; size_t v___x_1402_; lean_object* v___x_4024__overap_1403_; lean_object* v___x_1404_; 
v_content_1399_ = lean_ctor_get(v_x_1200_, 0);
lean_inc_ref(v_content_1399_);
lean_dec_ref_known(v_x_1200_, 2);
v___x_1400_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1400_, 0, v_inst_1198_);
lean_closure_set(v___x_1400_, 1, v_x_1199_);
v_sz_1401_ = lean_array_size(v_content_1399_);
v___x_1402_ = ((size_t)0ULL);
v___x_4024__overap_1403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1229_, v___x_1400_, v_sz_1401_, v___x_1402_, v_content_1399_);
lean_inc(v_a_1203_);
lean_inc_ref(v_a_1202_);
lean_inc(v_a_1201_);
v___x_1404_ = lean_apply_4(v___x_4024__overap_1403_, v_a_1201_, v_a_1202_, v_a_1203_, lean_box(0));
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1413_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1409_ = l_Lean_Doc_joinInlines(v_a_1405_);
lean_dec(v_a_1405_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1409_);
v___x_1411_ = v___x_1407_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_a_1414_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1404_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1404_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
case 7:
{
lean_object* v_name_1422_; lean_object* v_content_1423_; lean_object* v___x_1424_; size_t v_sz_1425_; size_t v___x_1426_; lean_object* v___x_4027__overap_1427_; lean_object* v___x_1428_; 
v_name_1422_ = lean_ctor_get(v_x_1200_, 0);
lean_inc_ref(v_name_1422_);
v_content_1423_ = lean_ctor_get(v_x_1200_, 1);
lean_inc_ref(v_content_1423_);
lean_dec_ref_known(v_x_1200_, 2);
v___x_1424_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1424_, 0, v_inst_1198_);
lean_closure_set(v___x_1424_, 1, v_x_1199_);
v_sz_1425_ = lean_array_size(v_content_1423_);
v___x_1426_ = ((size_t)0ULL);
v___x_4027__overap_1427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1229_, v___x_1424_, v_sz_1425_, v___x_1426_, v_content_1423_);
lean_inc(v_a_1203_);
lean_inc_ref(v_a_1202_);
lean_inc(v_a_1201_);
v___x_1428_ = lean_apply_4(v___x_4027__overap_1427_, v_a_1201_, v_a_1202_, v_a_1203_, lean_box(0));
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_1431_ = l_Lean_Doc_joinInlines(v_a_1429_);
lean_dec(v_a_1429_);
v___x_1432_ = lean_array_to_list(v___x_1431_);
v___x_1433_ = l_String_intercalate(v___x_1430_, v___x_1432_);
lean_inc_ref(v_name_1422_);
v___x_1434_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_1422_, v___x_1433_, v_a_1201_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1448_; 
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v___x_1434_, 0);
lean_dec(v_unused_1449_);
v___x_1436_ = v___x_1434_;
v_isShared_1437_ = v_isSharedCheck_1448_;
goto v_resetjp_1435_;
}
else
{
lean_dec(v___x_1434_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1448_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1438_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_1439_ = lean_string_append(v___x_1438_, v_name_1422_);
lean_dec_ref(v_name_1422_);
v___x_1440_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_1441_ = lean_string_append(v___x_1439_, v___x_1440_);
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = lean_mk_empty_array_with_capacity(v___x_1442_);
v___x_1444_ = lean_array_push(v___x_1443_, v___x_1441_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1444_);
v___x_1446_ = v___x_1436_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v_name_1422_);
v_a_1450_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1434_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1434_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v_name_1422_);
v_a_1458_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1428_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1428_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
case 8:
{
lean_object* v_alt_1466_; lean_object* v_url_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec_ref(v___x_1229_);
lean_dec_ref(v_x_1199_);
lean_dec_ref(v_inst_1198_);
v_alt_1466_ = lean_ctor_get(v_x_1200_, 0);
lean_inc_ref(v_alt_1466_);
v_url_1467_ = lean_ctor_get(v_x_1200_, 1);
lean_inc_ref(v_url_1467_);
lean_dec_ref_known(v_x_1200_, 2);
v___x_1468_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_1469_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1466_);
lean_dec_ref(v_alt_1466_);
v___x_1470_ = lean_string_append(v___x_1468_, v___x_1469_);
lean_dec_ref(v___x_1469_);
v___x_1471_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1472_ = lean_string_append(v___x_1470_, v___x_1471_);
v___x_1473_ = lean_string_append(v___x_1472_, v_url_1467_);
lean_dec_ref(v_url_1467_);
v___x_1474_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1475_ = lean_string_append(v___x_1473_, v___x_1474_);
v___x_1476_ = lean_unsigned_to_nat(1u);
v___x_1477_ = lean_mk_empty_array_with_capacity(v___x_1476_);
v___x_1478_ = lean_array_push(v___x_1477_, v___x_1475_);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
case 9:
{
lean_object* v_content_1480_; lean_object* v___x_1481_; size_t v_sz_1482_; size_t v___x_1483_; lean_object* v___x_4030__overap_1484_; lean_object* v___x_1485_; 
v_content_1480_ = lean_ctor_get(v_x_1200_, 0);
lean_inc_ref(v_content_1480_);
lean_dec_ref_known(v_x_1200_, 1);
v___x_1481_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1481_, 0, v_inst_1198_);
lean_closure_set(v___x_1481_, 1, v_x_1199_);
v_sz_1482_ = lean_array_size(v_content_1480_);
v___x_1483_ = ((size_t)0ULL);
v___x_4030__overap_1484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1229_, v___x_1481_, v_sz_1482_, v___x_1483_, v_content_1480_);
lean_inc(v_a_1203_);
lean_inc_ref(v_a_1202_);
lean_inc(v_a_1201_);
v___x_1485_ = lean_apply_4(v___x_4030__overap_1484_, v_a_1201_, v_a_1202_, v_a_1203_, lean_box(0));
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1494_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = l_Lean_Doc_joinInlines(v_a_1486_);
lean_dec(v_a_1486_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_a_1495_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1485_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1485_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
default: 
{
lean_object* v_container_1503_; lean_object* v_content_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec_ref(v___x_1229_);
v_container_1503_ = lean_ctor_get(v_x_1200_, 0);
lean_inc(v_container_1503_);
v_content_1504_ = lean_ctor_get(v_x_1200_, 1);
lean_inc_ref(v_content_1504_);
lean_dec_ref_known(v_x_1200_, 2);
lean_inc_ref(v_inst_1198_);
v___x_1505_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1505_, 0, v_inst_1198_);
lean_closure_set(v___x_1505_, 1, v_x_1199_);
lean_inc(v_a_1203_);
lean_inc_ref(v_a_1202_);
lean_inc(v_a_1201_);
v___x_1506_ = lean_apply_7(v_inst_1198_, v___x_1505_, v_container_1503_, v_content_1504_, v_a_1201_, v_a_1202_, v_a_1203_, lean_box(0));
return v___x_1506_;
}
}
v___jp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = l_Lean_Doc_joinInlines(v_pieces_1206_);
lean_dec_ref(v_pieces_1206_);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
v___jp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = l_Lean_Doc_joinInlines(v_pieces_1210_);
lean_dec_ref(v_pieces_1210_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1198_ = stack[0].m_obj;
lean_object* v_x_1199_ = stack[1].m_obj;
lean_object* v_x_1200_ = stack[2].m_obj;
lean_object* v_a_1201_ = stack[3].m_obj;
lean_object* v_a_1202_ = stack[4].m_obj;
lean_object* v_a_1203_ = stack[5].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1198_, v_x_1199_, v_x_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
stack->m_obj
 = v_res_1507_;
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1508_, lean_object* v_inst_1509_, lean_object* v_x_1510_, lean_object* v_x_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1509_, v_x_1510_, v_x_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1509_ = stack[1].m_obj;
lean_object* v_x_1510_ = stack[2].m_obj;
lean_object* v_x_1511_ = stack[3].m_obj;
lean_object* v_a_1512_ = stack[4].m_obj;
lean_object* v_a_1513_ = stack[5].m_obj;
lean_object* v_a_1514_ = stack[6].m_obj;
lean_object* v_res_1517_;
v_res_1517_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_box(0), v_inst_1509_, v_x_1510_, v_x_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
stack->m_obj
 = v_res_1517_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object* v_i_1518_, lean_object* v_inst_1519_, lean_object* v_x_1520_, lean_object* v_x_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(v_i_1518_, v_inst_1519_, v_x_1520_, v_x_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec(v_a_1522_);
return v_res_1526_;
}
}
lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1534_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1527_, v___x_1533_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
return v___x_1534_;
}
}
LEAN_EXPORT void l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1527_ = stack[0].m_obj;
lean_object* v_a_1528_ = stack[1].m_obj;
lean_object* v_a_1529_ = stack[2].m_obj;
lean_object* v_a_1530_ = stack[3].m_obj;
lean_object* v_a_1531_ = stack[4].m_obj;
lean_object* v_res_1535_;
v_res_1535_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(v_inst_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
stack->m_obj
 = v_res_1535_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object* v_inst_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(v_inst_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
return v_res_1542_;
}
}
lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1543_, lean_object* v_inst_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1551_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1544_, v___x_1550_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
return v___x_1551_;
}
}
LEAN_EXPORT void l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1544_ = stack[1].m_obj;
lean_object* v_a_1545_ = stack[2].m_obj;
lean_object* v_a_1546_ = stack[3].m_obj;
lean_object* v_a_1547_ = stack[4].m_obj;
lean_object* v_a_1548_ = stack[5].m_obj;
lean_object* v_res_1552_;
v_res_1552_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_box(0), v_inst_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
stack->m_obj
 = v_res_1552_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object* v_i_1553_, lean_object* v_inst_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(v_i_1553_, v_inst_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1562_, 0, lean_box(0));
lean_closure_set(v___x_1562_, 1, v_inst_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1563_, lean_object* v_inst_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1565_, 0, lean_box(0));
lean_closure_set(v___x_1565_, 1, v_inst_1564_);
return v___x_1565_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(uint32_t v___x_1566_, lean_object* v_s_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_string_push(v_s_1567_, v___x_1566_);
return v___x_1568_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint32_t v___x_1566_ = stack[0].m_num;
lean_object* v_s_1567_ = stack[1].m_obj;
lean_object* v_res_1569_;
v_res_1569_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v___x_1566_, v_s_1567_);
stack->m_obj
 = v_res_1569_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object* v___x_1570_, lean_object* v_s_1571_){
_start:
{
uint32_t v___x_2520__boxed_1572_; lean_object* v_res_1573_; 
v___x_2520__boxed_1572_ = lean_unbox_uint32(v___x_1570_);
lean_dec(v___x_1570_);
v_res_1573_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v___x_2520__boxed_1572_, v_s_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed(lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v___x_1578_, lean_object* v_item_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(v_inst_1576_, v_inst_1577_, v___x_1578_, v_item_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
return v_res_1584_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___f_1587_; 
v___x_1586_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___f_1587_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1587_, 0, v___x_1586_);
return v___f_1587_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1588_, lean_object* v_inst_1589_, lean_object* v___x_1590_, lean_object* v___x_1591_, lean_object* v_a_1592_, lean_object* v_x_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_fst_1599_; lean_object* v_snd_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1640_; 
v_fst_1599_ = lean_ctor_get(v___y_1594_, 0);
v_snd_1600_ = lean_ctor_get(v___y_1594_, 1);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___y_1594_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1602_ = v___y_1594_;
v_isShared_1603_ = v_isSharedCheck_1640_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_snd_1600_);
lean_inc(v_fst_1599_);
lean_dec(v___y_1594_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1640_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___f_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; size_t v_sz_1612_; size_t v___x_1613_; lean_object* v___x_2461__overap_1614_; lean_object* v___x_1615_; 
lean_inc(v_snd_1600_);
v___x_1604_ = l_Nat_reprFast(v_snd_1600_);
v___x_1605_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_1606_ = lean_string_append(v___x_1604_, v___x_1605_);
v___x_1607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_1608_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1);
v___x_1609_ = lean_string_utf8_byte_size(v___x_1606_);
v___x_1610_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1608_, v___x_1609_, v___x_1607_);
v___x_1611_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1611_, 0, v_inst_1588_);
lean_closure_set(v___x_1611_, 1, v_inst_1589_);
v_sz_1612_ = lean_array_size(v_a_1592_);
v___x_1613_ = ((size_t)0ULL);
v___x_2461__overap_1614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1590_, v___x_1611_, v_sz_1612_, v___x_1613_, v_a_1592_);
lean_inc(v___y_1597_);
lean_inc_ref(v___y_1596_);
lean_inc(v___y_1595_);
v___x_1615_ = lean_apply_4(v___x_2461__overap_1614_, v___y_1595_, v___y_1596_, v___y_1597_, lean_box(0));
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1631_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1631_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1631_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1620_ = l_Lean_Doc_joinBlocks(v_a_1616_);
lean_dec(v_a_1616_);
v___x_1621_ = l_Lean_Doc_prefixListLines(v___x_1606_, v___x_1610_, v___x_1620_);
v___x_1622_ = lean_array_push(v_fst_1599_, v___x_1621_);
v___x_1623_ = lean_nat_add(v_snd_1600_, v___x_1591_);
lean_dec(v_snd_1600_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 1, v___x_1623_);
lean_ctor_set(v___x_1602_, 0, v___x_1622_);
v___x_1625_ = v___x_1602_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1626_);
v___x_1628_ = v___x_1618_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v___x_1610_);
lean_dec_ref(v___x_1606_);
lean_del_object(v___x_1602_);
lean_dec(v_snd_1600_);
lean_dec(v_fst_1599_);
v_a_1632_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1615_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1615_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1588_ = stack[0].m_obj;
lean_object* v_inst_1589_ = stack[1].m_obj;
lean_object* v___x_1590_ = stack[2].m_obj;
lean_object* v___x_1591_ = stack[3].m_obj;
lean_object* v_a_1592_ = stack[4].m_obj;
lean_object* v___y_1594_ = stack[6].m_obj;
lean_object* v___y_1595_ = stack[7].m_obj;
lean_object* v___y_1596_ = stack[8].m_obj;
lean_object* v___y_1597_ = stack[9].m_obj;
lean_object* v_res_1641_;
v_res_1641_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1588_, v_inst_1589_, v___x_1590_, v___x_1591_, v_a_1592_, lean_box(0), v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
stack->m_obj
 = v_res_1641_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v___x_1644_, lean_object* v___x_1645_, lean_object* v_a_1646_, lean_object* v_x_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1642_, v_inst_1643_, v___x_1644_, v___x_1645_, v_a_1646_, v_x_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec(v___x_1645_);
return v_res_1653_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v___x_1661_, lean_object* v_item_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v_term_1668_; lean_object* v_desc_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1667_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_1668_ = lean_ctor_get(v_item_1662_, 0);
lean_inc_ref(v_term_1668_);
v_desc_1669_ = lean_ctor_get(v_item_1662_, 1);
lean_inc_ref(v_desc_1669_);
lean_dec_ref(v_item_1662_);
v___x_1670_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_term_1668_);
lean_inc_ref(v_inst_1659_);
v___x_1671_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1659_, v___x_1667_, v___x_1670_, v___y_1663_, v___y_1664_, v___y_1665_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1673_; size_t v_sz_1674_; size_t v___x_1675_; lean_object* v___x_2489__overap_1676_; lean_object* v___x_1677_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1671_, 1);
v___x_1673_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1673_, 0, v_inst_1659_);
lean_closure_set(v___x_1673_, 1, v_inst_1660_);
v_sz_1674_ = lean_array_size(v_desc_1669_);
v___x_1675_ = ((size_t)0ULL);
lean_inc_ref(v_desc_1669_);
v___x_2489__overap_1676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1661_, v___x_1673_, v_sz_1674_, v___x_1675_, v_desc_1669_);
lean_inc(v___y_1665_);
lean_inc_ref(v___y_1664_);
lean_inc(v___y_1663_);
v___x_1677_ = lean_apply_4(v___x_2489__overap_1676_, v___y_1663_, v___y_1664_, v___y_1665_, lean_box(0));
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1705_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1705_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1705_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___y_1683_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1690_ = lean_unsigned_to_nat(1u);
v___x_1691_ = lean_mk_empty_array_with_capacity(v___x_1690_);
v___x_1692_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_1693_ = lean_unsigned_to_nat(2u);
v___x_1694_ = lean_mk_empty_array_with_capacity(v___x_1693_);
v___x_1695_ = lean_array_push(v___x_1694_, v_a_1672_);
v___x_1696_ = lean_array_push(v___x_1695_, v___x_1692_);
v___x_1697_ = l_Lean_Doc_joinInlines(v___x_1696_);
lean_dec_ref(v___x_1696_);
v___x_1698_ = lean_array_get_size(v_desc_1669_);
lean_dec_ref(v_desc_1669_);
v___x_1699_ = lean_nat_dec_le(v___x_1698_, v___x_1690_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1700_ = lean_array_push(v___x_1691_, v___x_1697_);
v___x_1701_ = l_Array_append___redArg(v___x_1700_, v_a_1678_);
lean_dec(v_a_1678_);
v___x_1702_ = l_Lean_Doc_joinBlocks(v___x_1701_);
lean_dec_ref(v___x_1701_);
v___y_1683_ = v___x_1702_;
goto v___jp_1682_;
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec_ref(v___x_1691_);
v___x_1703_ = l_Lean_Doc_joinBlocks(v_a_1678_);
lean_dec(v_a_1678_);
v___x_1704_ = l_Array_append___redArg(v___x_1697_, v___x_1703_);
lean_dec_ref(v___x_1703_);
v___y_1683_ = v___x_1704_;
goto v___jp_1682_;
}
v___jp_1682_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1684_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1685_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1686_ = l_Lean_Doc_prefixListLines(v___x_1684_, v___x_1685_, v___y_1683_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1686_);
v___x_1688_ = v___x_1680_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
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
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec(v_a_1672_);
lean_dec_ref(v_desc_1669_);
v_a_1706_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1677_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1677_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
else
{
lean_dec_ref(v_desc_1669_);
lean_dec_ref(v___x_1661_);
lean_dec_ref(v_inst_1660_);
lean_dec_ref(v_inst_1659_);
return v___x_1671_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1659_ = stack[0].m_obj;
lean_object* v_inst_1660_ = stack[1].m_obj;
lean_object* v___x_1661_ = stack[2].m_obj;
lean_object* v_item_1662_ = stack[3].m_obj;
lean_object* v___y_1663_ = stack[4].m_obj;
lean_object* v___y_1664_ = stack[5].m_obj;
lean_object* v___y_1665_ = stack[6].m_obj;
lean_object* v_res_1714_;
v_res_1714_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1659_, v_inst_1660_, v___x_1661_, v_item_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
stack->m_obj
 = v_res_1714_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v___x_1717_, lean_object* v_item_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1715_, v_inst_1716_, v___x_1717_, v_item_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
return v_res_1723_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_x_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v___x_1732_; lean_object* v_toApplicative_1733_; lean_object* v_toFunctor_1734_; lean_object* v_toSeq_1735_; lean_object* v_toSeqLeft_1736_; lean_object* v_toSeqRight_1737_; lean_object* v___f_1738_; lean_object* v___f_1739_; lean_object* v___f_1740_; lean_object* v___f_1741_; lean_object* v___x_1742_; lean_object* v___f_1743_; lean_object* v___f_1744_; lean_object* v___f_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1732_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1733_ = lean_ctor_get(v___x_1732_, 0);
v_toFunctor_1734_ = lean_ctor_get(v_toApplicative_1733_, 0);
v_toSeq_1735_ = lean_ctor_get(v_toApplicative_1733_, 2);
v_toSeqLeft_1736_ = lean_ctor_get(v_toApplicative_1733_, 3);
v_toSeqRight_1737_ = lean_ctor_get(v_toApplicative_1733_, 4);
v___f_1738_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1739_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1734_, 2);
v___f_1740_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1740_, 0, v_toFunctor_1734_);
v___f_1741_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1741_, 0, v_toFunctor_1734_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___f_1740_);
lean_ctor_set(v___x_1742_, 1, v___f_1741_);
lean_inc(v_toSeqRight_1737_);
v___f_1743_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1743_, 0, v_toSeqRight_1737_);
lean_inc(v_toSeqLeft_1736_);
v___f_1744_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1744_, 0, v_toSeqLeft_1736_);
lean_inc(v_toSeq_1735_);
v___f_1745_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1745_, 0, v_toSeq_1735_);
v___x_1746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1742_);
lean_ctor_set(v___x_1746_, 1, v___f_1738_);
lean_ctor_set(v___x_1746_, 2, v___f_1745_);
lean_ctor_set(v___x_1746_, 3, v___f_1744_);
lean_ctor_set(v___x_1746_, 4, v___f_1743_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v___f_1739_);
v___x_1748_ = l_StateRefT_x27_instMonad___redArg(v___x_1747_);
switch(lean_obj_tag(v_x_1727_))
{
case 0:
{
lean_object* v_contents_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1758_; 
lean_dec_ref(v___x_1748_);
lean_dec_ref(v_inst_1726_);
v_contents_1749_ = lean_ctor_get(v_x_1727_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_x_1727_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1751_ = v_x_1727_;
v_isShared_1752_ = v_isSharedCheck_1758_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_contents_1749_);
lean_dec(v_x_1727_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1758_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_1752_ == 0)
{
lean_ctor_set_tag(v___x_1751_, 9);
v___x_1755_ = v___x_1751_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_contents_1749_);
v___x_1755_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1756_; 
v___x_1756_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1725_, v___x_1753_, v___x_1755_, v_a_1728_, v_a_1729_, v_a_1730_);
return v___x_1756_;
}
}
}
case 1:
{
lean_object* v_content_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v___x_1748_);
lean_dec_ref(v_inst_1726_);
lean_dec_ref(v_inst_1725_);
v_content_1759_ = lean_ctor_get(v_x_1727_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_x_1727_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1761_ = v_x_1727_;
v_isShared_1762_ = v_isSharedCheck_1767_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_content_1759_);
lean_dec(v_x_1727_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1767_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1763_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_1759_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set_tag(v___x_1761_, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1763_);
v___x_1765_ = v___x_1761_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
case 2:
{
lean_object* v_items_1768_; lean_object* v___f_1769_; size_t v_sz_1770_; size_t v___x_1771_; lean_object* v___x_2384__overap_1772_; lean_object* v___x_1773_; 
v_items_1768_ = lean_ctor_get(v_x_1727_, 0);
lean_inc_ref(v_items_1768_);
lean_dec_ref_known(v_x_1727_, 1);
lean_inc_ref(v___x_1748_);
v___f_1769_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1769_, 0, v_inst_1725_);
lean_closure_set(v___f_1769_, 1, v_inst_1726_);
lean_closure_set(v___f_1769_, 2, v___x_1748_);
v_sz_1770_ = lean_array_size(v_items_1768_);
v___x_1771_ = ((size_t)0ULL);
v___x_2384__overap_1772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1748_, v___f_1769_, v_sz_1770_, v___x_1771_, v_items_1768_);
lean_inc(v_a_1730_);
lean_inc_ref(v_a_1729_);
lean_inc(v_a_1728_);
v___x_1773_ = lean_apply_4(v___x_2384__overap_1772_, v_a_1728_, v_a_1729_, v_a_1730_, lean_box(0));
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1782_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1782_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1782_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1778_ = l_Lean_Doc_joinBlocks(v_a_1774_);
lean_dec(v_a_1774_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1778_);
v___x_1780_ = v___x_1776_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_a_1783_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1773_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1773_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
case 3:
{
lean_object* v_start_1791_; lean_object* v_items_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1828_; 
v_start_1791_ = lean_ctor_get(v_x_1727_, 0);
v_items_1792_ = lean_ctor_get(v_x_1727_, 1);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_x_1727_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1794_ = v_x_1727_;
v_isShared_1795_ = v_isSharedCheck_1828_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_items_1792_);
lean_inc(v_start_1791_);
lean_dec(v_x_1727_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1828_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_out_1796_; lean_object* v___x_1797_; lean_object* v___f_1798_; lean_object* v___y_1800_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v_out_1796_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1797_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_1748_);
v___f_1798_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1798_, 0, v_inst_1725_);
lean_closure_set(v___f_1798_, 1, v_inst_1726_);
lean_closure_set(v___f_1798_, 2, v___x_1748_);
lean_closure_set(v___f_1798_, 3, v___x_1797_);
v___x_1826_ = l_Int_toNat(v_start_1791_);
lean_dec(v_start_1791_);
v___x_1827_ = lean_nat_dec_le(v___x_1797_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_dec(v___x_1826_);
v___y_1800_ = v___x_1797_;
goto v___jp_1799_;
}
else
{
v___y_1800_ = v___x_1826_;
goto v___jp_1799_;
}
v___jp_1799_:
{
lean_object* v___x_1802_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set_tag(v___x_1794_, 0);
lean_ctor_set(v___x_1794_, 1, v___y_1800_);
lean_ctor_set(v___x_1794_, 0, v_out_1796_);
v___x_1802_ = v___x_1794_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_out_1796_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v___y_1800_);
v___x_1802_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
size_t v_sz_1803_; size_t v___x_1804_; lean_object* v___x_2200__overap_1805_; lean_object* v___x_1806_; 
v_sz_1803_ = lean_array_size(v_items_1792_);
v___x_1804_ = ((size_t)0ULL);
v___x_2200__overap_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1748_, v_items_1792_, v___f_1798_, v_sz_1803_, v___x_1804_, v___x_1802_);
lean_inc(v_a_1730_);
lean_inc_ref(v_a_1729_);
lean_inc(v_a_1728_);
v___x_1806_ = lean_apply_4(v___x_2200__overap_1805_, v_a_1728_, v_a_1729_, v_a_1730_, lean_box(0));
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1816_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v_fst_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v_fst_1811_ = lean_ctor_get(v_a_1807_, 0);
lean_inc(v_fst_1811_);
lean_dec(v_a_1807_);
v___x_1812_ = l_Lean_Doc_joinBlocks(v_fst_1811_);
lean_dec(v_fst_1811_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1812_);
v___x_1814_ = v___x_1809_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_a_1817_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1806_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1806_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_1829_; lean_object* v___f_1830_; size_t v_sz_1831_; size_t v___x_1832_; lean_object* v___x_2390__overap_1833_; lean_object* v___x_1834_; 
v_items_1829_ = lean_ctor_get(v_x_1727_, 0);
lean_inc_ref(v_items_1829_);
lean_dec_ref_known(v_x_1727_, 1);
lean_inc_ref(v___x_1748_);
v___f_1830_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 8, 3);
lean_closure_set(v___f_1830_, 0, v_inst_1725_);
lean_closure_set(v___f_1830_, 1, v_inst_1726_);
lean_closure_set(v___f_1830_, 2, v___x_1748_);
v_sz_1831_ = lean_array_size(v_items_1829_);
v___x_1832_ = ((size_t)0ULL);
v___x_2390__overap_1833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1748_, v___f_1830_, v_sz_1831_, v___x_1832_, v_items_1829_);
lean_inc(v_a_1730_);
lean_inc_ref(v_a_1729_);
lean_inc(v_a_1728_);
v___x_1834_ = lean_apply_4(v___x_2390__overap_1833_, v_a_1728_, v_a_1729_, v_a_1730_, lean_box(0));
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1843_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = l_Lean_Doc_joinBlocks(v_a_1835_);
lean_dec(v_a_1835_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1839_);
v___x_1841_ = v___x_1837_;
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
v_a_1844_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1834_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1834_);
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
case 5:
{
lean_object* v_items_1852_; lean_object* v___x_1853_; size_t v_sz_1854_; size_t v___x_1855_; lean_object* v___x_2393__overap_1856_; lean_object* v___x_1857_; 
v_items_1852_ = lean_ctor_get(v_x_1727_, 0);
lean_inc_ref(v_items_1852_);
lean_dec_ref_known(v_x_1727_, 1);
v___x_1853_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1853_, 0, v_inst_1725_);
lean_closure_set(v___x_1853_, 1, v_inst_1726_);
v_sz_1854_ = lean_array_size(v_items_1852_);
v___x_1855_ = ((size_t)0ULL);
v___x_2393__overap_1856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1748_, v___x_1853_, v_sz_1854_, v___x_1855_, v_items_1852_);
lean_inc(v_a_1730_);
lean_inc_ref(v_a_1729_);
lean_inc(v_a_1728_);
v___x_1857_ = lean_apply_4(v___x_2393__overap_1856_, v_a_1728_, v_a_1729_, v_a_1730_, lean_box(0));
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1868_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1868_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1868_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1862_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_1863_ = l_Lean_Doc_joinBlocks(v_a_1858_);
lean_dec(v_a_1858_);
v___x_1864_ = l_Lean_Doc_prefixLines(v___x_1862_, v___x_1863_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1864_);
v___x_1866_ = v___x_1860_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
v_a_1869_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1857_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1857_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
case 6:
{
lean_object* v_content_1877_; lean_object* v___x_1878_; size_t v_sz_1879_; size_t v___x_1880_; lean_object* v___x_2396__overap_1881_; lean_object* v___x_1882_; 
v_content_1877_ = lean_ctor_get(v_x_1727_, 0);
lean_inc_ref(v_content_1877_);
lean_dec_ref_known(v_x_1727_, 1);
v___x_1878_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1878_, 0, v_inst_1725_);
lean_closure_set(v___x_1878_, 1, v_inst_1726_);
v_sz_1879_ = lean_array_size(v_content_1877_);
v___x_1880_ = ((size_t)0ULL);
v___x_2396__overap_1881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1748_, v___x_1878_, v_sz_1879_, v___x_1880_, v_content_1877_);
lean_inc(v_a_1730_);
lean_inc_ref(v_a_1729_);
lean_inc(v_a_1728_);
v___x_1882_ = lean_apply_4(v___x_2396__overap_1881_, v_a_1728_, v_a_1729_, v_a_1730_, lean_box(0));
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1891_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = l_Lean_Doc_joinBlocks(v_a_1883_);
lean_dec(v_a_1883_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
v_a_1892_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1882_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1882_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
default: 
{
lean_object* v_container_1900_; lean_object* v_content_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_dec_ref(v___x_1748_);
v_container_1900_ = lean_ctor_get(v_x_1727_, 0);
lean_inc(v_container_1900_);
v_content_1901_ = lean_ctor_get(v_x_1727_, 1);
lean_inc_ref(v_content_1901_);
lean_dec_ref_known(v_x_1727_, 2);
v___x_1902_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc_ref(v_inst_1725_);
v___x_1903_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed), 8, 3);
lean_closure_set(v___x_1903_, 0, lean_box(0));
lean_closure_set(v___x_1903_, 1, v_inst_1725_);
lean_closure_set(v___x_1903_, 2, v___x_1902_);
lean_inc_ref(v_inst_1726_);
v___x_1904_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1904_, 0, v_inst_1725_);
lean_closure_set(v___x_1904_, 1, v_inst_1726_);
lean_inc(v_a_1730_);
lean_inc_ref(v_a_1729_);
lean_inc(v_a_1728_);
v___x_1905_ = lean_apply_8(v_inst_1726_, v___x_1903_, v___x_1904_, v_container_1900_, v_content_1901_, v_a_1728_, v_a_1729_, v_a_1730_, lean_box(0));
return v___x_1905_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1725_ = stack[0].m_obj;
lean_object* v_inst_1726_ = stack[1].m_obj;
lean_object* v_x_1727_ = stack[2].m_obj;
lean_object* v_a_1728_ = stack[3].m_obj;
lean_object* v_a_1729_ = stack[4].m_obj;
lean_object* v_a_1730_ = stack[5].m_obj;
lean_object* v_res_1906_;
v_res_1906_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1725_, v_inst_1726_, v_x_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
stack->m_obj
 = v_res_1906_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed(lean_object* v_inst_1907_, lean_object* v_inst_1908_, lean_object* v_x_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1907_, v_inst_1908_, v_x_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
return v_res_1914_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v_inst_1915_, lean_object* v_inst_1916_, lean_object* v___x_1917_, lean_object* v_item_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; size_t v_sz_1924_; size_t v___x_1925_; lean_object* v___x_2428__overap_1926_; lean_object* v___x_1927_; 
v___x_1923_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1923_, 0, v_inst_1915_);
lean_closure_set(v___x_1923_, 1, v_inst_1916_);
v_sz_1924_ = lean_array_size(v_item_1918_);
v___x_1925_ = ((size_t)0ULL);
v___x_2428__overap_1926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1917_, v___x_1923_, v_sz_1924_, v___x_1925_, v_item_1918_);
lean_inc(v___y_1921_);
lean_inc_ref(v___y_1920_);
lean_inc(v___y_1919_);
v___x_1927_ = lean_apply_4(v___x_2428__overap_1926_, v___y_1919_, v___y_1920_, v___y_1921_, lean_box(0));
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1939_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1939_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1939_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1932_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1933_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1934_ = l_Lean_Doc_joinBlocks(v_a_1928_);
lean_dec(v_a_1928_);
v___x_1935_ = l_Lean_Doc_prefixListLines(v___x_1932_, v___x_1933_, v___x_1934_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1935_);
v___x_1937_ = v___x_1930_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
v_a_1940_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1927_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1927_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1915_ = stack[0].m_obj;
lean_object* v_inst_1916_ = stack[1].m_obj;
lean_object* v___x_1917_ = stack[2].m_obj;
lean_object* v_item_1918_ = stack[3].m_obj;
lean_object* v___y_1919_ = stack[4].m_obj;
lean_object* v___y_1920_ = stack[5].m_obj;
lean_object* v___y_1921_ = stack[6].m_obj;
lean_object* v_res_1948_;
v_res_1948_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(v_inst_1915_, v_inst_1916_, v___x_1917_, v_item_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
stack->m_obj
 = v_res_1948_;
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1949_, lean_object* v_b_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_x_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1951_, v_inst_1952_, v_x_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1951_ = stack[2].m_obj;
lean_object* v_inst_1952_ = stack[3].m_obj;
lean_object* v_x_1953_ = stack[4].m_obj;
lean_object* v_a_1954_ = stack[5].m_obj;
lean_object* v_a_1955_ = stack[6].m_obj;
lean_object* v_a_1956_ = stack[7].m_obj;
lean_object* v_res_1959_;
v_res_1959_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v_inst_1951_, v_inst_1952_, v_x_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
stack->m_obj
 = v_res_1959_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object* v_i_1960_, lean_object* v_b_1961_, lean_object* v_inst_1962_, lean_object* v_inst_1963_, lean_object* v_x_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(v_i_1960_, v_b_1961_, v_inst_1962_, v_inst_1963_, v_x_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
return v_res_1969_;
}
}
lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1970_, v_inst_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
return v___x_1977_;
}
}
LEAN_EXPORT void l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1970_ = stack[0].m_obj;
lean_object* v_inst_1971_ = stack[1].m_obj;
lean_object* v_a_1972_ = stack[2].m_obj;
lean_object* v_a_1973_ = stack[3].m_obj;
lean_object* v_a_1974_ = stack[4].m_obj;
lean_object* v_a_1975_ = stack[5].m_obj;
lean_object* v_res_1978_;
v_res_1978_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1970_, v_inst_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
stack->m_obj
 = v_res_1978_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1979_, v_inst_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec(v_a_1982_);
return v_res_1986_;
}
}
lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1987_, lean_object* v_b_1988_, lean_object* v_inst_1989_, lean_object* v_inst_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1989_, v_inst_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
return v___x_1996_;
}
}
LEAN_EXPORT void l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1989_ = stack[2].m_obj;
lean_object* v_inst_1990_ = stack[3].m_obj;
lean_object* v_a_1991_ = stack[4].m_obj;
lean_object* v_a_1992_ = stack[5].m_obj;
lean_object* v_a_1993_ = stack[6].m_obj;
lean_object* v_a_1994_ = stack[7].m_obj;
lean_object* v_res_1997_;
v_res_1997_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_box(0), lean_box(0), v_inst_1989_, v_inst_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
stack->m_obj
 = v_res_1997_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1998_, lean_object* v_b_1999_, lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1998_, v_b_1999_, v_inst_2000_, v_inst_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_2008_, lean_object* v_inst_2009_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_2010_, 0, lean_box(0));
lean_closure_set(v___x_2010_, 1, lean_box(0));
lean_closure_set(v___x_2010_, 2, v_inst_2008_);
lean_closure_set(v___x_2010_, 3, v_inst_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_2011_, lean_object* v_b_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_2015_, 0, lean_box(0));
lean_closure_set(v___x_2015_, 1, lean_box(0));
lean_closure_set(v___x_2015_, 2, v_inst_2013_);
lean_closure_set(v___x_2015_, 3, v_inst_2014_);
return v___x_2015_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = 35;
v___x_2017_ = lean_box_uint32(v___x_2016_);
return v___x_2017_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___f_2019_; 
v___x_2018_ = l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_2019_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2019_, 0, v___x_2018_);
return v___f_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_2020_, lean_object* v_inst_2021_, lean_object* v_level_2022_, lean_object* v_part_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2020_, v_inst_2021_, v_level_2022_, v_part_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec(v_a_2024_);
lean_dec(v_level_2022_);
return v_res_2028_;
}
}
lean_object* l_Lean_Doc_partMarkdown___redArg(lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_level_2031_, lean_object* v_part_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v___x_2037_; lean_object* v_toApplicative_2038_; lean_object* v_toFunctor_2039_; lean_object* v_toSeq_2040_; lean_object* v_toSeqLeft_2041_; lean_object* v_toSeqRight_2042_; lean_object* v___f_2043_; lean_object* v___f_2044_; lean_object* v___f_2045_; lean_object* v___f_2046_; lean_object* v___x_2047_; lean_object* v___f_2048_; lean_object* v___f_2049_; lean_object* v___f_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_title_2054_; lean_object* v_content_2055_; lean_object* v_subParts_2056_; lean_object* v___x_2057_; size_t v_sz_2058_; size_t v___x_2059_; lean_object* v___x_684__overap_2060_; lean_object* v___x_2061_; 
v___x_2037_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2038_ = lean_ctor_get(v___x_2037_, 0);
v_toFunctor_2039_ = lean_ctor_get(v_toApplicative_2038_, 0);
v_toSeq_2040_ = lean_ctor_get(v_toApplicative_2038_, 2);
v_toSeqLeft_2041_ = lean_ctor_get(v_toApplicative_2038_, 3);
v_toSeqRight_2042_ = lean_ctor_get(v_toApplicative_2038_, 4);
v___f_2043_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2044_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2039_, 2);
v___f_2045_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2045_, 0, v_toFunctor_2039_);
v___f_2046_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2046_, 0, v_toFunctor_2039_);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___f_2045_);
lean_ctor_set(v___x_2047_, 1, v___f_2046_);
lean_inc(v_toSeqRight_2042_);
v___f_2048_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2048_, 0, v_toSeqRight_2042_);
lean_inc(v_toSeqLeft_2041_);
v___f_2049_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2049_, 0, v_toSeqLeft_2041_);
lean_inc(v_toSeq_2040_);
v___f_2050_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2050_, 0, v_toSeq_2040_);
v___x_2051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2047_);
lean_ctor_set(v___x_2051_, 1, v___f_2043_);
lean_ctor_set(v___x_2051_, 2, v___f_2050_);
lean_ctor_set(v___x_2051_, 3, v___f_2049_);
lean_ctor_set(v___x_2051_, 4, v___f_2048_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v___f_2044_);
v___x_2053_ = l_StateRefT_x27_instMonad___redArg(v___x_2052_);
v_title_2054_ = lean_ctor_get(v_part_2032_, 0);
lean_inc_ref(v_title_2054_);
v_content_2055_ = lean_ctor_get(v_part_2032_, 3);
lean_inc_ref(v_content_2055_);
v_subParts_2056_ = lean_ctor_get(v_part_2032_, 4);
lean_inc_ref(v_subParts_2056_);
lean_dec_ref(v_part_2032_);
lean_inc_ref(v_inst_2029_);
v___x_2057_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_2057_, 0, lean_box(0));
lean_closure_set(v___x_2057_, 1, v_inst_2029_);
v_sz_2058_ = lean_array_size(v_title_2054_);
v___x_2059_ = ((size_t)0ULL);
lean_inc_ref(v___x_2053_);
v___x_684__overap_2060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2053_, v___x_2057_, v_sz_2058_, v___x_2059_, v_title_2054_);
lean_inc(v_a_2035_);
lean_inc_ref(v_a_2034_);
lean_inc(v_a_2033_);
v___x_2061_ = lean_apply_4(v___x_684__overap_2060_, v_a_2033_, v_a_2034_, v_a_2035_, lean_box(0));
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; lean_object* v___f_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; size_t v_sz_2076_; lean_object* v___x_687__overap_2077_; lean_object* v___x_2078_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_2064_ = lean_obj_once(&l_Lean_Doc_partMarkdown___redArg___closed__0, &l_Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_partMarkdown___redArg___closed__0);
v___x_2065_ = lean_unsigned_to_nat(1u);
v___x_2066_ = lean_nat_add(v_level_2031_, v___x_2065_);
lean_inc(v___x_2066_);
v___x_2067_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_2064_, v___x_2066_, v___x_2063_);
v___x_2068_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_2069_ = lean_string_append(v___x_2067_, v___x_2068_);
v___x_2070_ = lean_mk_empty_array_with_capacity(v___x_2065_);
lean_inc_ref_n(v___x_2070_, 2);
v___x_2071_ = lean_array_push(v___x_2070_, v___x_2069_);
v___x_2072_ = lean_array_push(v___x_2070_, v___x_2071_);
v___x_2073_ = l_Array_append___redArg(v___x_2072_, v_a_2062_);
lean_dec(v_a_2062_);
v___x_2074_ = l_Lean_Doc_joinInlines(v___x_2073_);
lean_dec_ref(v___x_2073_);
lean_inc_ref(v_inst_2030_);
lean_inc_ref(v_inst_2029_);
v___x_2075_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_2075_, 0, lean_box(0));
lean_closure_set(v___x_2075_, 1, lean_box(0));
lean_closure_set(v___x_2075_, 2, v_inst_2029_);
lean_closure_set(v___x_2075_, 3, v_inst_2030_);
v_sz_2076_ = lean_array_size(v_content_2055_);
lean_inc_ref(v___x_2053_);
v___x_687__overap_2077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2053_, v___x_2075_, v_sz_2076_, v___x_2059_, v_content_2055_);
lean_inc(v_a_2035_);
lean_inc_ref(v_a_2034_);
lean_inc(v_a_2033_);
v___x_2078_ = lean_apply_4(v___x_687__overap_2077_, v_a_2033_, v_a_2034_, v_a_2035_, lean_box(0));
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2080_; size_t v_sz_2081_; lean_object* v___x_690__overap_2082_; lean_object* v___x_2083_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
v___x_2080_ = lean_alloc_closure((void*)(l_Lean_Doc_partMarkdown___redArg___boxed), 8, 3);
lean_closure_set(v___x_2080_, 0, v_inst_2029_);
lean_closure_set(v___x_2080_, 1, v_inst_2030_);
lean_closure_set(v___x_2080_, 2, v___x_2066_);
v_sz_2081_ = lean_array_size(v_subParts_2056_);
v___x_690__overap_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2053_, v___x_2080_, v_sz_2081_, v___x_2059_, v_subParts_2056_);
lean_inc(v_a_2035_);
lean_inc_ref(v_a_2034_);
lean_inc(v_a_2033_);
v___x_2083_ = lean_apply_4(v___x_690__overap_2082_, v_a_2033_, v_a_2034_, v_a_2035_, lean_box(0));
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2095_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2086_ = v___x_2083_;
v_isShared_2087_ = v_isSharedCheck_2095_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2095_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2088_ = lean_array_push(v___x_2070_, v___x_2074_);
v___x_2089_ = l_Array_append___redArg(v___x_2088_, v_a_2079_);
lean_dec(v_a_2079_);
v___x_2090_ = l_Array_append___redArg(v___x_2089_, v_a_2084_);
lean_dec(v_a_2084_);
v___x_2091_ = l_Lean_Doc_joinBlocks(v___x_2090_);
lean_dec_ref(v___x_2090_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2091_);
v___x_2093_ = v___x_2086_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_a_2079_);
lean_dec_ref(v___x_2074_);
lean_dec_ref(v___x_2070_);
v_a_2096_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2083_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2083_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v___x_2074_);
lean_dec_ref(v___x_2070_);
lean_dec(v___x_2066_);
lean_dec_ref(v_subParts_2056_);
lean_dec_ref(v___x_2053_);
lean_dec_ref(v_inst_2030_);
lean_dec_ref(v_inst_2029_);
v_a_2104_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2078_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2078_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v_subParts_2056_);
lean_dec_ref(v_content_2055_);
lean_dec_ref(v___x_2053_);
lean_dec_ref(v_inst_2030_);
lean_dec_ref(v_inst_2029_);
v_a_2112_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2061_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2061_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_partMarkdown___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2029_ = stack[0].m_obj;
lean_object* v_inst_2030_ = stack[1].m_obj;
lean_object* v_level_2031_ = stack[2].m_obj;
lean_object* v_part_2032_ = stack[3].m_obj;
lean_object* v_a_2033_ = stack[4].m_obj;
lean_object* v_a_2034_ = stack[5].m_obj;
lean_object* v_a_2035_ = stack[6].m_obj;
lean_object* v_res_2120_;
v_res_2120_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2029_, v_inst_2030_, v_level_2031_, v_part_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
stack->m_obj
 = v_res_2120_;
}
lean_object* l_Lean_Doc_partMarkdown(lean_object* v_i_2121_, lean_object* v_b_2122_, lean_object* v_p_2123_, lean_object* v_inst_2124_, lean_object* v_inst_2125_, lean_object* v_level_2126_, lean_object* v_part_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2124_, v_inst_2125_, v_level_2126_, v_part_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT void l_Lean_Doc_partMarkdown_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2124_ = stack[3].m_obj;
lean_object* v_inst_2125_ = stack[4].m_obj;
lean_object* v_level_2126_ = stack[5].m_obj;
lean_object* v_part_2127_ = stack[6].m_obj;
lean_object* v_a_2128_ = stack[7].m_obj;
lean_object* v_a_2129_ = stack[8].m_obj;
lean_object* v_a_2130_ = stack[9].m_obj;
lean_object* v_res_2133_;
v_res_2133_ = l_Lean_Doc_partMarkdown(lean_box(0), lean_box(0), lean_box(0), v_inst_2124_, v_inst_2125_, v_level_2126_, v_part_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
stack->m_obj
 = v_res_2133_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___boxed(lean_object* v_i_2134_, lean_object* v_b_2135_, lean_object* v_p_2136_, lean_object* v_inst_2137_, lean_object* v_inst_2138_, lean_object* v_level_2139_, lean_object* v_part_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_Doc_partMarkdown(v_i_2134_, v_b_2135_, v_p_2136_, v_inst_2137_, v_inst_2138_, v_level_2139_, v_part_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec(v_level_2139_);
return v_res_2145_;
}
}
lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_2146_, lean_object* v_inst_2147_, lean_object* v_part_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_unsigned_to_nat(0u);
v___x_2154_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2146_, v_inst_2147_, v___x_2153_, v_part_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
return v___x_2154_;
}
}
LEAN_EXPORT void l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2146_ = stack[0].m_obj;
lean_object* v_inst_2147_ = stack[1].m_obj;
lean_object* v_part_2148_ = stack[2].m_obj;
lean_object* v___y_2149_ = stack[3].m_obj;
lean_object* v___y_2150_ = stack[4].m_obj;
lean_object* v___y_2151_ = stack[5].m_obj;
lean_object* v_res_2155_;
v_res_2155_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_2146_, v_inst_2147_, v_part_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
stack->m_obj
 = v_res_2155_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_2156_, lean_object* v_inst_2157_, lean_object* v_part_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_2156_, v_inst_2157_, v_part_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_2164_, lean_object* v_inst_2165_){
_start:
{
lean_object* v___f_2166_; 
v___f_2166_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2166_, 0, v_inst_2164_);
lean_closure_set(v___f_2166_, 1, v_inst_2165_);
return v___f_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_2167_, lean_object* v_b_2168_, lean_object* v_p_2169_, lean_object* v_inst_2170_, lean_object* v_inst_2171_){
_start:
{
lean_object* v___f_2172_; 
v___f_2172_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2172_, 0, v_inst_2170_);
lean_closure_set(v___f_2172_, 1, v_inst_2171_);
return v___f_2172_;
}
}
lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg(lean_object* v_inst_2173_, lean_object* v_f_2174_, lean_object* v_go_2175_, lean_object* v_val_2176_, lean_object* v_content_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2182_; lean_object* v_toApplicative_2183_; lean_object* v_toFunctor_2184_; lean_object* v_toSeq_2185_; lean_object* v_toSeqLeft_2186_; lean_object* v_toSeqRight_2187_; lean_object* v___f_2188_; lean_object* v___f_2189_; lean_object* v___f_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; lean_object* v___f_2193_; lean_object* v___f_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2182_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2183_ = lean_ctor_get(v___x_2182_, 0);
v_toFunctor_2184_ = lean_ctor_get(v_toApplicative_2183_, 0);
v_toSeq_2185_ = lean_ctor_get(v_toApplicative_2183_, 2);
v_toSeqLeft_2186_ = lean_ctor_get(v_toApplicative_2183_, 3);
v_toSeqRight_2187_ = lean_ctor_get(v_toApplicative_2183_, 4);
v___f_2188_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2189_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2184_, 2);
v___f_2190_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2190_, 0, v_toFunctor_2184_);
v___f_2191_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2191_, 0, v_toFunctor_2184_);
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___f_2190_);
lean_ctor_set(v___x_2192_, 1, v___f_2191_);
lean_inc(v_toSeqRight_2187_);
v___f_2193_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2193_, 0, v_toSeqRight_2187_);
lean_inc(v_toSeqLeft_2186_);
v___f_2194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2194_, 0, v_toSeqLeft_2186_);
lean_inc(v_toSeq_2185_);
v___f_2195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2195_, 0, v_toSeq_2185_);
v___x_2196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2192_);
lean_ctor_set(v___x_2196_, 1, v___f_2188_);
lean_ctor_set(v___x_2196_, 2, v___f_2195_);
lean_ctor_set(v___x_2196_, 3, v___f_2194_);
lean_ctor_set(v___x_2196_, 4, v___f_2193_);
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
lean_ctor_set(v___x_2197_, 1, v___f_2189_);
v___x_2198_ = l_StateRefT_x27_instMonad___redArg(v___x_2197_);
v___x_2199_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2176_, v_inst_2173_);
if (lean_obj_tag(v___x_2199_) == 0)
{
size_t v_sz_2200_; size_t v___x_2201_; lean_object* v___x_236__overap_2202_; lean_object* v___x_2203_; 
lean_dec_ref(v_f_2174_);
v_sz_2200_ = lean_array_size(v_content_2177_);
v___x_2201_ = ((size_t)0ULL);
v___x_236__overap_2202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2198_, v_go_2175_, v_sz_2200_, v___x_2201_, v_content_2177_);
lean_inc(v_a_2180_);
lean_inc_ref(v_a_2179_);
lean_inc(v_a_2178_);
v___x_2203_ = lean_apply_4(v___x_236__overap_2202_, v_a_2178_, v_a_2179_, v_a_2180_, lean_box(0));
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2212_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2212_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2212_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = l_Lean_Doc_joinInlines(v_a_2204_);
lean_dec(v_a_2204_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2208_);
v___x_2210_ = v___x_2206_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_a_2213_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2203_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2203_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v_val_2221_; lean_object* v___x_2222_; 
lean_dec_ref(v___x_2198_);
v_val_2221_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_val_2221_);
lean_dec_ref_known(v___x_2199_, 1);
lean_inc(v_a_2180_);
lean_inc_ref(v_a_2179_);
lean_inc(v_a_2178_);
v___x_2222_ = lean_apply_7(v_f_2174_, v_go_2175_, v_val_2221_, v_content_2177_, v_a_2178_, v_a_2179_, v_a_2180_, lean_box(0));
return v___x_2222_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_mkInlineMdRenderer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2173_ = stack[0].m_obj;
lean_object* v_f_2174_ = stack[1].m_obj;
lean_object* v_go_2175_ = stack[2].m_obj;
lean_object* v_val_2176_ = stack[3].m_obj;
lean_object* v_content_2177_ = stack[4].m_obj;
lean_object* v_a_2178_ = stack[5].m_obj;
lean_object* v_a_2179_ = stack[6].m_obj;
lean_object* v_a_2180_ = stack[7].m_obj;
lean_object* v_res_2223_;
v_res_2223_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2173_, v_f_2174_, v_go_2175_, v_val_2176_, v_content_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
stack->m_obj
 = v_res_2223_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg___boxed(lean_object* v_inst_2224_, lean_object* v_f_2225_, lean_object* v_go_2226_, lean_object* v_val_2227_, lean_object* v_content_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2224_, v_f_2225_, v_go_2226_, v_val_2227_, v_content_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec(v_val_2227_);
lean_dec(v_inst_2224_);
return v_res_2233_;
}
}
lean_object* l_Lean_Doc_mkInlineMdRenderer(lean_object* v_00_u03b1_2234_, lean_object* v_inst_2235_, lean_object* v_f_2236_, lean_object* v_go_2237_, lean_object* v_val_2238_, lean_object* v_content_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2235_, v_f_2236_, v_go_2237_, v_val_2238_, v_content_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkInlineMdRenderer_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2235_ = stack[1].m_obj;
lean_object* v_f_2236_ = stack[2].m_obj;
lean_object* v_go_2237_ = stack[3].m_obj;
lean_object* v_val_2238_ = stack[4].m_obj;
lean_object* v_content_2239_ = stack[5].m_obj;
lean_object* v_a_2240_ = stack[6].m_obj;
lean_object* v_a_2241_ = stack[7].m_obj;
lean_object* v_a_2242_ = stack[8].m_obj;
lean_object* v_res_2245_;
v_res_2245_ = l_Lean_Doc_mkInlineMdRenderer(lean_box(0), v_inst_2235_, v_f_2236_, v_go_2237_, v_val_2238_, v_content_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
stack->m_obj
 = v_res_2245_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___boxed(lean_object* v_00_u03b1_2246_, lean_object* v_inst_2247_, lean_object* v_f_2248_, lean_object* v_go_2249_, lean_object* v_val_2250_, lean_object* v_content_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Doc_mkInlineMdRenderer(v_00_u03b1_2246_, v_inst_2247_, v_f_2248_, v_go_2249_, v_val_2250_, v_content_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec(v_val_2250_);
lean_dec(v_inst_2247_);
return v_res_2256_;
}
}
lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg(lean_object* v_inst_2257_, lean_object* v_f_2258_, lean_object* v_goI_2259_, lean_object* v_goB_2260_, lean_object* v_val_2261_, lean_object* v_content_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v___x_2267_; lean_object* v_toApplicative_2268_; lean_object* v_toFunctor_2269_; lean_object* v_toSeq_2270_; lean_object* v_toSeqLeft_2271_; lean_object* v_toSeqRight_2272_; lean_object* v___f_2273_; lean_object* v___f_2274_; lean_object* v___f_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; lean_object* v___f_2278_; lean_object* v___f_2279_; lean_object* v___f_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2267_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2268_ = lean_ctor_get(v___x_2267_, 0);
v_toFunctor_2269_ = lean_ctor_get(v_toApplicative_2268_, 0);
v_toSeq_2270_ = lean_ctor_get(v_toApplicative_2268_, 2);
v_toSeqLeft_2271_ = lean_ctor_get(v_toApplicative_2268_, 3);
v_toSeqRight_2272_ = lean_ctor_get(v_toApplicative_2268_, 4);
v___f_2273_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2274_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2269_, 2);
v___f_2275_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2275_, 0, v_toFunctor_2269_);
v___f_2276_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2276_, 0, v_toFunctor_2269_);
v___x_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___f_2275_);
lean_ctor_set(v___x_2277_, 1, v___f_2276_);
lean_inc(v_toSeqRight_2272_);
v___f_2278_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2278_, 0, v_toSeqRight_2272_);
lean_inc(v_toSeqLeft_2271_);
v___f_2279_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2279_, 0, v_toSeqLeft_2271_);
lean_inc(v_toSeq_2270_);
v___f_2280_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2280_, 0, v_toSeq_2270_);
v___x_2281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2277_);
lean_ctor_set(v___x_2281_, 1, v___f_2273_);
lean_ctor_set(v___x_2281_, 2, v___f_2280_);
lean_ctor_set(v___x_2281_, 3, v___f_2279_);
lean_ctor_set(v___x_2281_, 4, v___f_2278_);
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v___f_2274_);
v___x_2283_ = l_StateRefT_x27_instMonad___redArg(v___x_2282_);
v___x_2284_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2261_, v_inst_2257_);
if (lean_obj_tag(v___x_2284_) == 0)
{
size_t v_sz_2285_; size_t v___x_2286_; lean_object* v___x_236__overap_2287_; lean_object* v___x_2288_; 
lean_dec_ref(v_goI_2259_);
lean_dec_ref(v_f_2258_);
v_sz_2285_ = lean_array_size(v_content_2262_);
v___x_2286_ = ((size_t)0ULL);
v___x_236__overap_2287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2283_, v_goB_2260_, v_sz_2285_, v___x_2286_, v_content_2262_);
lean_inc(v_a_2265_);
lean_inc_ref(v_a_2264_);
lean_inc(v_a_2263_);
v___x_2288_ = lean_apply_4(v___x_236__overap_2287_, v_a_2263_, v_a_2264_, v_a_2265_, lean_box(0));
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2297_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2297_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2297_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2293_ = l_Lean_Doc_joinBlocks(v_a_2289_);
lean_dec(v_a_2289_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2293_);
v___x_2295_ = v___x_2291_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
v_a_2298_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2288_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2288_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v_val_2306_; lean_object* v___x_2307_; 
lean_dec_ref(v___x_2283_);
v_val_2306_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_val_2306_);
lean_dec_ref_known(v___x_2284_, 1);
lean_inc(v_a_2265_);
lean_inc_ref(v_a_2264_);
lean_inc(v_a_2263_);
v___x_2307_ = lean_apply_8(v_f_2258_, v_goI_2259_, v_goB_2260_, v_val_2306_, v_content_2262_, v_a_2263_, v_a_2264_, v_a_2265_, lean_box(0));
return v___x_2307_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_mkBlockMdRenderer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2257_ = stack[0].m_obj;
lean_object* v_f_2258_ = stack[1].m_obj;
lean_object* v_goI_2259_ = stack[2].m_obj;
lean_object* v_goB_2260_ = stack[3].m_obj;
lean_object* v_val_2261_ = stack[4].m_obj;
lean_object* v_content_2262_ = stack[5].m_obj;
lean_object* v_a_2263_ = stack[6].m_obj;
lean_object* v_a_2264_ = stack[7].m_obj;
lean_object* v_a_2265_ = stack[8].m_obj;
lean_object* v_res_2308_;
v_res_2308_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2257_, v_f_2258_, v_goI_2259_, v_goB_2260_, v_val_2261_, v_content_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
stack->m_obj
 = v_res_2308_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg___boxed(lean_object* v_inst_2309_, lean_object* v_f_2310_, lean_object* v_goI_2311_, lean_object* v_goB_2312_, lean_object* v_val_2313_, lean_object* v_content_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2309_, v_f_2310_, v_goI_2311_, v_goB_2312_, v_val_2313_, v_content_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
lean_dec(v_a_2315_);
lean_dec(v_val_2313_);
lean_dec(v_inst_2309_);
return v_res_2319_;
}
}
lean_object* l_Lean_Doc_mkBlockMdRenderer(lean_object* v_00_u03b1_2320_, lean_object* v_inst_2321_, lean_object* v_f_2322_, lean_object* v_goI_2323_, lean_object* v_goB_2324_, lean_object* v_val_2325_, lean_object* v_content_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2321_, v_f_2322_, v_goI_2323_, v_goB_2324_, v_val_2325_, v_content_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
return v___x_2331_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkBlockMdRenderer_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2321_ = stack[1].m_obj;
lean_object* v_f_2322_ = stack[2].m_obj;
lean_object* v_goI_2323_ = stack[3].m_obj;
lean_object* v_goB_2324_ = stack[4].m_obj;
lean_object* v_val_2325_ = stack[5].m_obj;
lean_object* v_content_2326_ = stack[6].m_obj;
lean_object* v_a_2327_ = stack[7].m_obj;
lean_object* v_a_2328_ = stack[8].m_obj;
lean_object* v_a_2329_ = stack[9].m_obj;
lean_object* v_res_2332_;
v_res_2332_ = l_Lean_Doc_mkBlockMdRenderer(lean_box(0), v_inst_2321_, v_f_2322_, v_goI_2323_, v_goB_2324_, v_val_2325_, v_content_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
stack->m_obj
 = v_res_2332_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___boxed(lean_object* v_00_u03b1_2333_, lean_object* v_inst_2334_, lean_object* v_f_2335_, lean_object* v_goI_2336_, lean_object* v_goB_2337_, lean_object* v_val_2338_, lean_object* v_content_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_Doc_mkBlockMdRenderer(v_00_u03b1_2333_, v_inst_2334_, v_f_2335_, v_goI_2336_, v_goB_2337_, v_val_2338_, v_content_2339_, v_a_2340_, v_a_2341_, v_a_2342_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
lean_dec(v_a_2340_);
lean_dec(v_val_2338_);
lean_dec(v_inst_2334_);
return v_res_2344_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(lean_object* v_as_2349_, size_t v_i_2350_, size_t v_stop_2351_, lean_object* v_b_2352_){
_start:
{
uint8_t v___x_2353_; 
v___x_2353_ = lean_usize_dec_eq(v_i_2350_, v_stop_2351_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v_fst_2355_; lean_object* v_snd_2356_; lean_object* v___x_2357_; size_t v___x_2358_; size_t v___x_2359_; 
v___x_2354_ = lean_array_uget_borrowed(v_as_2349_, v_i_2350_);
v_fst_2355_ = lean_ctor_get(v___x_2354_, 0);
v_snd_2356_ = lean_ctor_get(v___x_2354_, 1);
lean_inc(v_snd_2356_);
lean_inc(v_fst_2355_);
v___x_2357_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2355_, v_snd_2356_, v_b_2352_);
v___x_2358_ = ((size_t)1ULL);
v___x_2359_ = lean_usize_add(v_i_2350_, v___x_2358_);
v_i_2350_ = v___x_2359_;
v_b_2352_ = v___x_2357_;
goto _start;
}
else
{
return v_b_2352_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2349_ = stack[0].m_obj;
size_t v_i_2350_ = stack[1].m_num;
size_t v_stop_2351_ = stack[2].m_num;
lean_object* v_b_2352_ = stack[3].m_obj;
lean_object* v_res_2361_;
v_res_2361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v_as_2349_, v_i_2350_, v_stop_2351_, v_b_2352_);
stack->m_obj
 = v_res_2361_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0___boxed(lean_object* v_as_2362_, lean_object* v_i_2363_, lean_object* v_stop_2364_, lean_object* v_b_2365_){
_start:
{
size_t v_i_boxed_2366_; size_t v_stop_boxed_2367_; lean_object* v_res_2368_; 
v_i_boxed_2366_ = lean_unbox_usize(v_i_2363_);
lean_dec(v_i_2363_);
v_stop_boxed_2367_ = lean_unbox_usize(v_stop_2364_);
lean_dec(v_stop_2364_);
v_res_2368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v_as_2362_, v_i_boxed_2366_, v_stop_boxed_2367_, v_b_2365_);
lean_dec_ref(v_as_2362_);
return v_res_2368_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(lean_object* v_as_2369_, size_t v_i_2370_, size_t v_stop_2371_, lean_object* v_b_2372_){
_start:
{
lean_object* v___y_2374_; uint8_t v___x_2378_; 
v___x_2378_ = lean_usize_dec_eq(v_i_2370_, v_stop_2371_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2379_ = lean_array_uget_borrowed(v_as_2369_, v_i_2370_);
v___x_2380_ = lean_unsigned_to_nat(0u);
v___x_2381_ = lean_array_get_size(v___x_2379_);
v___x_2382_ = lean_nat_dec_lt(v___x_2380_, v___x_2381_);
if (v___x_2382_ == 0)
{
v___y_2374_ = v_b_2372_;
goto v___jp_2373_;
}
else
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_nat_dec_le(v___x_2381_, v___x_2381_);
if (v___x_2383_ == 0)
{
if (v___x_2382_ == 0)
{
v___y_2374_ = v_b_2372_;
goto v___jp_2373_;
}
else
{
size_t v___x_2384_; size_t v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = ((size_t)0ULL);
v___x_2385_ = lean_usize_of_nat(v___x_2381_);
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2379_, v___x_2384_, v___x_2385_, v_b_2372_);
v___y_2374_ = v___x_2386_;
goto v___jp_2373_;
}
}
else
{
size_t v___x_2387_; size_t v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = ((size_t)0ULL);
v___x_2388_ = lean_usize_of_nat(v___x_2381_);
v___x_2389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2379_, v___x_2387_, v___x_2388_, v_b_2372_);
v___y_2374_ = v___x_2389_;
goto v___jp_2373_;
}
}
}
else
{
return v_b_2372_;
}
v___jp_2373_:
{
size_t v___x_2375_; size_t v___x_2376_; 
v___x_2375_ = ((size_t)1ULL);
v___x_2376_ = lean_usize_add(v_i_2370_, v___x_2375_);
v_i_2370_ = v___x_2376_;
v_b_2372_ = v___y_2374_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2369_ = stack[0].m_obj;
size_t v_i_2370_ = stack[1].m_num;
size_t v_stop_2371_ = stack[2].m_num;
lean_object* v_b_2372_ = stack[3].m_obj;
lean_object* v_res_2390_;
v_res_2390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_as_2369_, v_i_2370_, v_stop_2371_, v_b_2372_);
stack->m_obj
 = v_res_2390_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1___boxed(lean_object* v_as_2391_, lean_object* v_i_2392_, lean_object* v_stop_2393_, lean_object* v_b_2394_){
_start:
{
size_t v_i_boxed_2395_; size_t v_stop_boxed_2396_; lean_object* v_res_2397_; 
v_i_boxed_2395_ = lean_unbox_usize(v_i_2392_);
lean_dec(v_i_2392_);
v_stop_boxed_2396_ = lean_unbox_usize(v_stop_2393_);
lean_dec(v_stop_2393_);
v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_as_2391_, v_i_boxed_2395_, v_stop_boxed_2396_, v_b_2394_);
lean_dec_ref(v_as_2391_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(lean_object* v_init_2398_, lean_object* v_es_2399_){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2400_ = lean_unsigned_to_nat(0u);
v___x_2401_ = lean_array_get_size(v_es_2399_);
v___x_2402_ = lean_nat_dec_lt(v___x_2400_, v___x_2401_);
if (v___x_2402_ == 0)
{
return v_init_2398_;
}
else
{
uint8_t v___x_2403_; 
v___x_2403_ = lean_nat_dec_le(v___x_2401_, v___x_2401_);
if (v___x_2403_ == 0)
{
if (v___x_2402_ == 0)
{
return v_init_2398_;
}
else
{
size_t v___x_2404_; size_t v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = ((size_t)0ULL);
v___x_2405_ = lean_usize_of_nat(v___x_2401_);
v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2399_, v___x_2404_, v___x_2405_, v_init_2398_);
return v___x_2406_;
}
}
else
{
size_t v___x_2407_; size_t v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = ((size_t)0ULL);
v___x_2408_ = lean_usize_of_nat(v___x_2401_);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2399_, v___x_2407_, v___x_2408_, v_init_2398_);
return v___x_2409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries___boxed(lean_object* v_init_2410_, lean_object* v_es_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v_init_2410_, v_es_2411_);
lean_dec_ref(v_es_2411_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_2413_, lean_object* v_x_2414_){
_start:
{
if (lean_obj_tag(v_x_2414_) == 0)
{
lean_object* v_k_2415_; lean_object* v_v_2416_; lean_object* v_l_2417_; lean_object* v_r_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_k_2415_ = lean_ctor_get(v_x_2414_, 1);
v_v_2416_ = lean_ctor_get(v_x_2414_, 2);
v_l_2417_ = lean_ctor_get(v_x_2414_, 3);
v_r_2418_ = lean_ctor_get(v_x_2414_, 4);
v___x_2419_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2413_, v_l_2417_);
lean_inc(v_v_2416_);
lean_inc(v_k_2415_);
v___x_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2420_, 0, v_k_2415_);
lean_ctor_set(v___x_2420_, 1, v_v_2416_);
v___x_2421_ = lean_array_push(v___x_2419_, v___x_2420_);
v_init_2413_ = v___x_2421_;
v_x_2414_ = v_r_2418_;
goto _start;
}
else
{
return v_init_2413_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_2423_, lean_object* v_x_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2423_, v_x_2424_);
lean_dec(v_x_2424_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2428_){
_start:
{
lean_object* v_current_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_current_2429_ = lean_ctor_get(v_s_2428_, 1);
v___x_2430_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2431_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2430_, v_current_2429_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_s_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_s_2432_);
lean_dec_ref(v_s_2432_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_box(0);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2436_);
lean_dec_ref(v_x_2436_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2438_, lean_object* v_s_2439_){
_start:
{
lean_object* v_current_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_current_2440_ = lean_ctor_get(v_s_2439_, 1);
v___x_2441_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2442_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2441_, v_current_2440_);
lean_inc_ref_n(v___x_2442_, 2);
v___x_2443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
lean_ctor_set(v___x_2443_, 2, v___x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2444_, lean_object* v_s_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2444_, v_s_2445_);
lean_dec_ref(v_s_2445_);
lean_dec_ref(v_x_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2447_, lean_object* v_x_2448_){
_start:
{
lean_object* v_fst_2449_; lean_object* v_snd_2450_; lean_object* v_imported_2451_; lean_object* v_current_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2460_; 
v_fst_2449_ = lean_ctor_get(v_x_2448_, 0);
lean_inc(v_fst_2449_);
v_snd_2450_ = lean_ctor_get(v_x_2448_, 1);
lean_inc(v_snd_2450_);
lean_dec_ref(v_x_2448_);
v_imported_2451_ = lean_ctor_get(v_s_2447_, 0);
v_current_2452_ = lean_ctor_get(v_s_2447_, 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_s_2447_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2454_ = v_s_2447_;
v_isShared_2455_ = v_isSharedCheck_2460_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_current_2452_);
lean_inc(v_imported_2451_);
lean_dec(v_s_2447_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2460_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v___x_2458_; 
v___x_2456_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2449_, v_snd_2450_, v_current_2452_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 1, v___x_2456_);
v___x_2458_ = v___x_2454_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_imported_2451_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2461_, lean_object* v_es_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
lean_inc(v___x_2461_);
v___x_2465_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v___x_2461_, v_es_2462_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
lean_ctor_set(v___x_2466_, 1, v___x_2461_);
v___x_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2461_ = stack[0].m_obj;
lean_object* v_es_2462_ = stack[1].m_obj;
lean_object* v___y_2463_ = stack[2].m_obj;
lean_object* v_res_2468_;
v_res_2468_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2461_, v_es_2462_, v___y_2463_);
stack->m_obj
 = v_res_2468_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2469_, lean_object* v_es_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2469_, v_es_2470_, v___y_2471_);
lean_dec_ref(v___y_2471_);
lean_dec_ref(v_es_2470_);
return v_res_2473_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2474_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
return v___x_2476_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2474_ = stack[0].m_obj;
lean_object* v_res_2477_;
v_res_2477_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2474_);
stack->m_obj
 = v_res_2477_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2478_);
return v_res_2480_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2511_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2512_;
v_res_2512_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2512_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_();
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(lean_object* v_init_2515_, lean_object* v_t_2516_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2515_, v_t_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_2518_, lean_object* v_t_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(v_init_2518_, v_t_2519_);
lean_dec(v_t_2519_);
return v_res_2520_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_));
v___x_2541_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2542_;
v_res_2542_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2542_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2____boxed(lean_object* v_a_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_1277071390____hygCtx___hyg_2_();
return v_res_2544_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = lean_box(1);
v___x_2547_ = lean_st_mk_ref(v___x_2546_);
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2549_;
v_res_2549_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2549_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2____boxed(lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2917630591____hygCtx___hyg_2_();
return v_res_2551_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = lean_box(1);
v___x_2554_ = lean_st_mk_ref(v___x_2553_);
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2556_;
v_res_2556_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2556_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2____boxed(lean_object* v_a_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_2639420957____hygCtx___hyg_2_();
return v_res_2558_;
}
}
lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer(lean_object* v_type_2559_, lean_object* v_r_2560_){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2562_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2563_ = lean_st_ref_take(v___x_2562_);
v___x_2564_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2559_, v_r_2560_, v___x_2563_);
v___x_2565_ = lean_st_ref_put(v___x_2562_, v___x_2564_);
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT void l_Lean_Doc_addBuiltinInlineMdRenderer_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2559_ = stack[0].m_obj;
lean_object* v_r_2560_ = stack[1].m_obj;
lean_object* v_res_2567_;
v_res_2567_ = l_Lean_Doc_addBuiltinInlineMdRenderer(v_type_2559_, v_r_2560_);
stack->m_obj
 = v_res_2567_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinInlineMdRenderer___boxed(lean_object* v_type_2568_, lean_object* v_r_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Doc_addBuiltinInlineMdRenderer(v_type_2568_, v_r_2569_);
return v_res_2571_;
}
}
lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer(lean_object* v_type_2572_, lean_object* v_r_2573_){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2575_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2576_ = lean_st_ref_take(v___x_2575_);
v___x_2577_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_type_2572_, v_r_2573_, v___x_2576_);
v___x_2578_ = lean_st_ref_put(v___x_2575_, v___x_2577_);
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT void l_Lean_Doc_addBuiltinBlockMdRenderer_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2572_ = stack[0].m_obj;
lean_object* v_r_2573_ = stack[1].m_obj;
lean_object* v_res_2580_;
v_res_2580_ = l_Lean_Doc_addBuiltinBlockMdRenderer(v_type_2572_, v_r_2573_);
stack->m_obj
 = v_res_2580_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_addBuiltinBlockMdRenderer___boxed(lean_object* v_type_2581_, lean_object* v_r_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_Doc_addBuiltinBlockMdRenderer(v_type_2581_, v_r_2582_);
return v_res_2584_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2585_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
return v___x_2587_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2588_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2589_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
lean_ctor_set(v___x_2591_, 2, v___x_2590_);
lean_ctor_set(v___x_2591_, 3, v___x_2590_);
lean_ctor_set(v___x_2591_, 4, v___x_2589_);
lean_ctor_set(v___x_2591_, 5, v___x_2589_);
lean_ctor_set(v___x_2591_, 6, v___x_2589_);
lean_ctor_set(v___x_2591_, 7, v___x_2589_);
lean_ctor_set(v___x_2591_, 8, v___x_2589_);
lean_ctor_set(v___x_2591_, 9, v___x_2589_);
lean_ctor_set(v___x_2591_, 10, v___x_2589_);
lean_ctor_set(v___x_2591_, 11, v___x_2588_);
return v___x_2591_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = lean_unsigned_to_nat(32u);
v___x_2593_ = lean_mk_empty_array_with_capacity(v___x_2592_);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
return v___x_2594_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2595_ = ((size_t)5ULL);
v___x_2596_ = lean_unsigned_to_nat(0u);
v___x_2597_ = lean_unsigned_to_nat(32u);
v___x_2598_ = lean_mk_empty_array_with_capacity(v___x_2597_);
v___x_2599_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_2600_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v___x_2598_);
lean_ctor_set(v___x_2600_, 2, v___x_2596_);
lean_ctor_set(v___x_2600_, 3, v___x_2596_);
lean_ctor_set_usize(v___x_2600_, 4, v___x_2595_);
return v___x_2600_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2601_ = lean_box(1);
v___x_2602_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_2603_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
lean_ctor_set(v___x_2604_, 1, v___x_2602_);
lean_ctor_set(v___x_2604_, 2, v___x_2601_);
return v___x_2604_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; lean_object* v_toCold_2610_; lean_object* v_env_2611_; lean_object* v_options_2612_; uint8_t v___x_2613_; lean_object* v_env_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2609_ = lean_st_ref_get(v___y_2607_);
v_toCold_2610_ = lean_ctor_get(v___y_2606_, 0);
v_env_2611_ = lean_ctor_get(v___x_2609_, 0);
lean_inc_ref(v_env_2611_);
lean_dec(v___x_2609_);
v_options_2612_ = lean_ctor_get(v_toCold_2610_, 2);
v___x_2613_ = 0;
v_env_2614_ = l_Lean_Environment_setRecordingDeps(v_env_2611_, v___x_2613_);
v___x_2615_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_2616_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_2612_);
v___x_2617_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2617_, 0, v_env_2614_);
lean_ctor_set(v___x_2617_, 1, v___x_2615_);
lean_ctor_set(v___x_2617_, 2, v___x_2616_);
lean_ctor_set(v___x_2617_, 3, v_options_2612_);
v___x_2618_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
lean_ctor_set(v___x_2618_, 1, v_msgData_2605_);
v___x_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2605_ = stack[0].m_obj;
lean_object* v___y_2606_ = stack[1].m_obj;
lean_object* v___y_2607_ = stack[2].m_obj;
lean_object* v_res_2620_;
v_res_2620_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_2605_, v___y_2606_, v___y_2607_);
stack->m_obj
 = v_res_2620_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
return v_res_2625_;
}
}
lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_ref_2630_; lean_object* v___x_2631_; lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2640_; 
v_ref_2630_ = lean_ctor_get(v___y_2627_, 2);
v___x_2631_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_2626_, v___y_2627_, v___y_2628_);
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2640_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2640_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; lean_object* v___x_2638_; 
lean_inc(v_ref_2630_);
v___x_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2636_, 0, v_ref_2630_);
lean_ctor_set(v___x_2636_, 1, v_a_2632_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set_tag(v___x_2634_, 1);
lean_ctor_set(v___x_2634_, 0, v___x_2636_);
v___x_2638_ = v___x_2634_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2626_ = stack[0].m_obj;
lean_object* v___y_2627_ = stack[1].m_obj;
lean_object* v___y_2628_ = stack[2].m_obj;
lean_object* v_res_2641_;
v_res_2641_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2626_, v___y_2627_, v___y_2628_);
stack->m_obj
 = v_res_2641_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
return v_res_2646_;
}
}
lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(lean_object* v_x_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
if (lean_obj_tag(v_x_2647_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_a_2651_ = lean_ctor_get(v_x_2647_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v_x_2647_, 1);
v___x_2652_ = l_Lean_stringToMessageData(v_a_2651_);
v___x_2653_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v___x_2652_, v___y_2648_, v___y_2649_);
return v___x_2653_;
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
v_a_2654_ = lean_ctor_get(v_x_2647_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_x_2647_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v_x_2647_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v_x_2647_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
lean_ctor_set_tag(v___x_2656_, 0);
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2647_ = stack[0].m_obj;
lean_object* v___y_2648_ = stack[1].m_obj;
lean_object* v___y_2649_ = stack[2].m_obj;
lean_object* v_res_2662_;
v_res_2662_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2647_, v___y_2648_, v___y_2649_);
stack->m_obj
 = v_res_2662_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
return v_res_2667_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2668_ = lean_box(0);
v___x_2669_ = l_Lean_Elab_abortCommandExceptionId;
v___x_2670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v___x_2668_);
return v___x_2670_;
}
}
lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2672_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2674_;
v_res_2674_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
stack->m_obj
 = v_res_2674_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v_res_2676_;
}
}
lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(lean_object* v_constName_2677_, uint8_t v_checkMeta_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v_env_2683_; uint8_t v___x_2684_; 
v___x_2682_ = lean_st_ref_get(v___y_2680_);
v_env_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc_ref(v_env_2683_);
lean_dec(v___x_2682_);
lean_inc(v_constName_2677_);
v___x_2684_ = lean_has_compile_error(v_env_2683_, v_constName_2677_);
if (v___x_2684_ == 0)
{
lean_object* v___x_2685_; lean_object* v_env_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2685_ = lean_st_ref_get(v___y_2680_);
v_env_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc_ref(v_env_2686_);
lean_dec(v___x_2685_);
v___x_2687_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2679_);
v___x_2688_ = l_Lean_Environment_evalConst___redArg(v_env_2686_, v___x_2687_, v_constName_2677_, v_checkMeta_2678_);
lean_dec(v_constName_2677_);
lean_dec_ref(v___x_2687_);
lean_dec_ref(v_env_2686_);
v___x_2689_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2688_, v___y_2679_, v___y_2680_);
return v___x_2689_;
}
else
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v___x_2691_; lean_object* v_env_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_dec_ref_known(v___x_2690_, 1);
v___x_2691_ = lean_st_ref_get(v___y_2680_);
v_env_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc_ref(v_env_2692_);
lean_dec(v___x_2691_);
v___x_2693_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2679_);
v___x_2694_ = l_Lean_Environment_evalConst___redArg(v_env_2692_, v___x_2693_, v_constName_2677_, v_checkMeta_2678_);
lean_dec(v_constName_2677_);
lean_dec_ref(v___x_2693_);
lean_dec_ref(v_env_2692_);
v___x_2695_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v___x_2694_, v___y_2679_, v___y_2680_);
return v___x_2695_;
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v_constName_2677_);
v_a_2696_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2690_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2690_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2677_ = stack[0].m_obj;
uint8_t v_checkMeta_2678_ = stack[1].m_num;
lean_object* v___y_2679_ = stack[2].m_obj;
lean_object* v___y_2680_ = stack[3].m_obj;
lean_object* v_res_2704_;
v_res_2704_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2677_, v_checkMeta_2678_, v___y_2679_, v___y_2680_);
stack->m_obj
 = v_res_2704_;
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg___boxed(lean_object* v_constName_2705_, lean_object* v_checkMeta_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
uint8_t v_checkMeta_boxed_2710_; lean_object* v_res_2711_; 
v_checkMeta_boxed_2710_ = lean_unbox(v_checkMeta_2706_);
v_res_2711_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2705_, v_checkMeta_boxed_2710_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
return v_res_2711_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(lean_object* v_type_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___y_2719_; lean_object* v_env_2750_; lean_object* v___x_2751_; lean_object* v_toEnvExtension_2752_; lean_object* v_asyncMode_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; lean_object* v_imported_2757_; lean_object* v_current_2758_; lean_object* v___x_2759_; 
v___x_2716_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2717_ = lean_st_ref_get(v_a_2714_);
v_env_2750_ = lean_ctor_get(v___x_2717_, 0);
lean_inc_ref(v_env_2750_);
lean_dec(v___x_2717_);
v___x_2751_ = l_Lean_Doc_docInlineMdExt;
v_toEnvExtension_2752_ = lean_ctor_get(v___x_2751_, 0);
v_asyncMode_2753_ = lean_ctor_get(v_toEnvExtension_2752_, 2);
v___x_2754_ = lean_box(0);
v___x_2755_ = 0;
v___x_2756_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2716_, v___x_2751_, v_env_2750_, v_asyncMode_2753_, v___x_2754_, v___x_2755_);
v_imported_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_imported_2757_);
v_current_2758_ = lean_ctor_get(v___x_2756_, 1);
lean_inc(v_current_2758_);
lean_dec(v___x_2756_);
v___x_2759_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2758_, v_type_2712_);
lean_dec(v_current_2758_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2757_, v_type_2712_);
lean_dec(v_imported_2757_);
v___y_2719_ = v___x_2760_;
goto v___jp_2718_;
}
else
{
lean_dec(v_imported_2757_);
v___y_2719_ = v___x_2759_;
goto v___jp_2718_;
}
v___jp_2718_:
{
if (lean_obj_tag(v___y_2719_) == 0)
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2720_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinInlineMdRenderers;
v___x_2721_ = lean_st_ref_get(v___x_2720_);
v___x_2722_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2721_, v_type_2712_);
lean_dec(v___x_2721_);
v___x_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
return v___x_2723_;
}
else
{
lean_object* v_val_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2749_; 
v_val_2724_ = lean_ctor_get(v___y_2719_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___y_2719_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2726_ = v___y_2719_;
v_isShared_2727_ = v_isSharedCheck_2749_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_val_2724_);
lean_dec(v___y_2719_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2749_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
uint8_t v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = 1;
v___x_2729_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2724_, v___x_2728_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2740_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2740_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2740_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 0, v_a_2730_);
v___x_2735_ = v___x_2726_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2737_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2735_);
v___x_2737_ = v___x_2732_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_del_object(v___x_2726_);
v_a_2741_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2729_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2729_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2712_ = stack[0].m_obj;
lean_object* v_a_2713_ = stack[1].m_obj;
lean_object* v_a_2714_ = stack[2].m_obj;
lean_object* v_res_2761_;
v_res_2761_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v_type_2712_, v_a_2713_, v_a_2714_);
stack->m_obj
 = v_res_2761_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe___boxed(lean_object* v_type_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v_type_2762_, v_a_2763_, v_a_2764_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_type_2762_);
return v_res_2766_;
}
}
lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___redArg();
return v___x_2771_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2768_ = stack[1].m_obj;
lean_object* v___y_2769_ = stack[2].m_obj;
lean_object* v_res_2772_;
v_res_2772_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(lean_box(0), v___y_2768_, v___y_2769_);
stack->m_obj
 = v_res_2772_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__1(v_00_u03b1_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
return v_res_2777_;
}
}
lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(lean_object* v_00_u03b1_2778_, lean_object* v_constName_2779_, uint8_t v_checkMeta_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_constName_2779_, v_checkMeta_2780_, v___y_2781_, v___y_2782_);
return v___x_2784_;
}
}
LEAN_EXPORT void l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2779_ = stack[1].m_obj;
uint8_t v_checkMeta_2780_ = stack[2].m_num;
lean_object* v___y_2781_ = stack[3].m_obj;
lean_object* v___y_2782_ = stack[4].m_obj;
lean_object* v_res_2785_;
v_res_2785_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(lean_box(0), v_constName_2779_, v_checkMeta_2780_, v___y_2781_, v___y_2782_);
stack->m_obj
 = v_res_2785_;
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___boxed(lean_object* v_00_u03b1_2786_, lean_object* v_constName_2787_, lean_object* v_checkMeta_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
uint8_t v_checkMeta_boxed_2792_; lean_object* v_res_2793_; 
v_checkMeta_boxed_2792_ = lean_unbox(v_checkMeta_2788_);
v_res_2793_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0(v_00_u03b1_2786_, v_constName_2787_, v_checkMeta_boxed_2792_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
return v_res_2793_;
}
}
lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_2794_, lean_object* v_x_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___redArg(v_x_2795_, v___y_2796_, v___y_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2795_ = stack[1].m_obj;
lean_object* v___y_2796_ = stack[2].m_obj;
lean_object* v___y_2797_ = stack[3].m_obj;
lean_object* v_res_2800_;
v_res_2800_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(lean_box(0), v_x_2795_, v___y_2796_, v___y_2797_);
stack->m_obj
 = v_res_2800_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2801_, lean_object* v_x_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0(v_00_u03b1_2801_, v_x_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
return v_res_2806_;
}
}
lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2807_, lean_object* v_msg_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_2808_, v___y_2809_, v___y_2810_);
return v___x_2812_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2808_ = stack[1].m_obj;
lean_object* v___y_2809_ = stack[2].m_obj;
lean_object* v___y_2810_ = stack[3].m_obj;
lean_object* v_res_2813_;
v_res_2813_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(lean_box(0), v_msg_2808_, v___y_2809_, v___y_2810_);
stack->m_obj
 = v_res_2813_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2814_, lean_object* v_msg_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_2814_, v_msg_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
return v_res_2819_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(lean_object* v_typeName_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___y_2827_; lean_object* v_env_2858_; lean_object* v___x_2859_; lean_object* v_toEnvExtension_2860_; lean_object* v_asyncMode_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v_imported_2865_; lean_object* v_current_2866_; lean_object* v___x_2867_; 
v___x_2824_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2825_ = lean_st_ref_get(v_a_2822_);
v_env_2858_ = lean_ctor_get(v___x_2825_, 0);
lean_inc_ref(v_env_2858_);
lean_dec(v___x_2825_);
v___x_2859_ = l_Lean_Doc_docBlockMdExt;
v_toEnvExtension_2860_ = lean_ctor_get(v___x_2859_, 0);
v_asyncMode_2861_ = lean_ctor_get(v_toEnvExtension_2860_, 2);
v___x_2862_ = lean_box(0);
v___x_2863_ = 0;
v___x_2864_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2824_, v___x_2859_, v_env_2858_, v_asyncMode_2861_, v___x_2862_, v___x_2863_);
v_imported_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_imported_2865_);
v_current_2866_ = lean_ctor_get(v___x_2864_, 1);
lean_inc(v_current_2866_);
lean_dec(v___x_2864_);
v___x_2867_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2866_, v_typeName_2820_);
lean_dec(v_current_2866_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2865_, v_typeName_2820_);
lean_dec(v_imported_2865_);
v___y_2827_ = v___x_2868_;
goto v___jp_2826_;
}
else
{
lean_dec(v_imported_2865_);
v___y_2827_ = v___x_2867_;
goto v___jp_2826_;
}
v___jp_2826_:
{
if (lean_obj_tag(v___y_2827_) == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2828_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2829_ = lean_st_ref_get(v___x_2828_);
v___x_2830_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2829_, v_typeName_2820_);
lean_dec(v___x_2829_);
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
return v___x_2831_;
}
else
{
lean_object* v_val_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2857_; 
v_val_2832_ = lean_ctor_get(v___y_2827_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___y_2827_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2834_ = v___y_2827_;
v_isShared_2835_ = v_isSharedCheck_2857_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_val_2832_);
lean_dec(v___y_2827_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2857_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
uint8_t v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = 1;
v___x_2837_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2832_, v___x_2836_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2848_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2848_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2848_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v_a_2838_);
v___x_2843_ = v___x_2834_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2845_; 
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2843_);
v___x_2845_ = v___x_2840_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_del_object(v___x_2834_);
v_a_2849_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2837_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2837_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_2820_ = stack[0].m_obj;
lean_object* v_a_2821_ = stack[1].m_obj;
lean_object* v_a_2822_ = stack[2].m_obj;
lean_object* v_res_2869_;
v_res_2869_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v_typeName_2820_, v_a_2821_, v_a_2822_);
stack->m_obj
 = v_res_2869_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe___boxed(lean_object* v_typeName_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v_typeName_2870_, v_a_2871_, v_a_2872_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_typeName_2870_);
return v_res_2874_;
}
}
static lean_object* _init_l_Lean_Doc_mdRendererHeartbeats(void){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = lean_unsigned_to_nat(200000u);
return v___x_2875_;
}
}
lean_object* l_Lean_Doc_withMdRendererBudget___redArg(lean_object* v_x_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v___x_2881_; lean_object* v_toCold_2882_; lean_object* v_currRecDepth_2883_; lean_object* v_ref_2884_; uint16_t v_optionFlags_2885_; uint8_t v_suppressElabErrors_2886_; uint8_t v_isRecordingDeps_2887_; lean_object* v_fileName_2888_; lean_object* v_fileMap_2889_; lean_object* v_options_2890_; lean_object* v_maxRecDepth_2891_; lean_object* v_currNamespace_2892_; lean_object* v_openDecls_2893_; lean_object* v_quotContext_2894_; lean_object* v_currMacroScope_2895_; lean_object* v_cancelTk_x3f_2896_; lean_object* v_inheritedTraceOptions_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2881_ = lean_io_get_num_heartbeats();
v_toCold_2882_ = lean_ctor_get(v_a_2878_, 0);
v_currRecDepth_2883_ = lean_ctor_get(v_a_2878_, 1);
v_ref_2884_ = lean_ctor_get(v_a_2878_, 2);
v_optionFlags_2885_ = lean_ctor_get_uint16(v_a_2878_, sizeof(void*)*3);
v_suppressElabErrors_2886_ = lean_ctor_get_uint8(v_a_2878_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2887_ = lean_ctor_get_uint8(v_a_2878_, sizeof(void*)*3 + 3);
v_fileName_2888_ = lean_ctor_get(v_toCold_2882_, 0);
v_fileMap_2889_ = lean_ctor_get(v_toCold_2882_, 1);
v_options_2890_ = lean_ctor_get(v_toCold_2882_, 2);
v_maxRecDepth_2891_ = lean_ctor_get(v_toCold_2882_, 3);
v_currNamespace_2892_ = lean_ctor_get(v_toCold_2882_, 4);
v_openDecls_2893_ = lean_ctor_get(v_toCold_2882_, 5);
v_quotContext_2894_ = lean_ctor_get(v_toCold_2882_, 8);
v_currMacroScope_2895_ = lean_ctor_get(v_toCold_2882_, 9);
v_cancelTk_x3f_2896_ = lean_ctor_get(v_toCold_2882_, 10);
v_inheritedTraceOptions_2897_ = lean_ctor_get(v_toCold_2882_, 11);
v___x_2898_ = lean_unsigned_to_nat(200000u);
lean_inc_ref(v_inheritedTraceOptions_2897_);
lean_inc(v_cancelTk_x3f_2896_);
lean_inc(v_currMacroScope_2895_);
lean_inc(v_quotContext_2894_);
lean_inc(v_openDecls_2893_);
lean_inc(v_currNamespace_2892_);
lean_inc(v_maxRecDepth_2891_);
lean_inc_ref(v_options_2890_);
lean_inc_ref(v_fileMap_2889_);
lean_inc_ref(v_fileName_2888_);
v___x_2899_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2899_, 0, v_fileName_2888_);
lean_ctor_set(v___x_2899_, 1, v_fileMap_2889_);
lean_ctor_set(v___x_2899_, 2, v_options_2890_);
lean_ctor_set(v___x_2899_, 3, v_maxRecDepth_2891_);
lean_ctor_set(v___x_2899_, 4, v_currNamespace_2892_);
lean_ctor_set(v___x_2899_, 5, v_openDecls_2893_);
lean_ctor_set(v___x_2899_, 6, v___x_2881_);
lean_ctor_set(v___x_2899_, 7, v___x_2898_);
lean_ctor_set(v___x_2899_, 8, v_quotContext_2894_);
lean_ctor_set(v___x_2899_, 9, v_currMacroScope_2895_);
lean_ctor_set(v___x_2899_, 10, v_cancelTk_x3f_2896_);
lean_ctor_set(v___x_2899_, 11, v_inheritedTraceOptions_2897_);
lean_inc(v_ref_2884_);
lean_inc(v_currRecDepth_2883_);
v___x_2900_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
lean_ctor_set(v___x_2900_, 1, v_currRecDepth_2883_);
lean_ctor_set(v___x_2900_, 2, v_ref_2884_);
lean_ctor_set_uint16(v___x_2900_, sizeof(void*)*3, v_optionFlags_2885_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*3 + 2, v_suppressElabErrors_2886_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*3 + 3, v_isRecordingDeps_2887_);
lean_inc(v_a_2879_);
lean_inc(v_a_2877_);
v___x_2901_ = lean_apply_4(v_x_2876_, v_a_2877_, v___x_2900_, v_a_2879_, lean_box(0));
return v___x_2901_;
}
}
LEAN_EXPORT void l_Lean_Doc_withMdRendererBudget___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2876_ = stack[0].m_obj;
lean_object* v_a_2877_ = stack[1].m_obj;
lean_object* v_a_2878_ = stack[2].m_obj;
lean_object* v_a_2879_ = stack[3].m_obj;
lean_object* v_res_2902_;
v_res_2902_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
stack->m_obj
 = v_res_2902_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg___boxed(lean_object* v_x_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
return v_res_2908_;
}
}
lean_object* l_Lean_Doc_withMdRendererBudget(lean_object* v_00_u03b1_2909_, lean_object* v_x_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_Doc_withMdRendererBudget___redArg(v_x_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT void l_Lean_Doc_withMdRendererBudget_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2910_ = stack[1].m_obj;
lean_object* v_a_2911_ = stack[2].m_obj;
lean_object* v_a_2912_ = stack[3].m_obj;
lean_object* v_a_2913_ = stack[4].m_obj;
lean_object* v_res_2916_;
v_res_2916_ = l_Lean_Doc_withMdRendererBudget(lean_box(0), v_x_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
stack->m_obj
 = v_res_2916_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___boxed(lean_object* v_00_u03b1_2917_, lean_object* v_x_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Doc_withMdRendererBudget(v_00_u03b1_2917_, v_x_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
return v_res_2923_;
}
}
lean_object* l_Lean_Doc_withRendererFallback(lean_object* v_fallback_2924_, lean_object* v_act_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = lean_st_ref_get(v_a_2926_);
v___x_2931_ = l_Lean_Doc_withMdRendererBudget___redArg(v_act_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_dec(v___x_2930_);
lean_dec_ref(v_fallback_2924_);
return v___x_2931_;
}
else
{
lean_object* v_a_2932_; uint8_t v___x_2933_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
v___x_2933_ = l_Lean_Exception_isInterrupt(v_a_2932_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
lean_dec_ref_known(v___x_2931_, 1);
v___x_2934_ = lean_st_ref_swap(v_a_2926_, v___x_2930_);
lean_dec(v___x_2934_);
lean_inc(v_a_2928_);
lean_inc_ref(v_a_2927_);
lean_inc(v_a_2926_);
v___x_2935_ = lean_apply_4(v_fallback_2924_, v_a_2926_, v_a_2927_, v_a_2928_, lean_box(0));
return v___x_2935_;
}
else
{
lean_dec(v___x_2930_);
lean_dec_ref(v_fallback_2924_);
return v___x_2931_;
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_withRendererFallback_0interp(lean_interpreter_value* stack)
{
lean_object* v_fallback_2924_ = stack[0].m_obj;
lean_object* v_act_2925_ = stack[1].m_obj;
lean_object* v_a_2926_ = stack[2].m_obj;
lean_object* v_a_2927_ = stack[3].m_obj;
lean_object* v_a_2928_ = stack[4].m_obj;
lean_object* v_res_2936_;
v_res_2936_ = l_Lean_Doc_withRendererFallback(v_fallback_2924_, v_act_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
stack->m_obj
 = v_res_2936_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_withRendererFallback___boxed(lean_object* v_fallback_2937_, lean_object* v_act_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Doc_withRendererFallback(v_fallback_2937_, v_act_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
return v_res_2943_;
}
}
lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0(lean_object* v_____do__lift_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = l_Lean_Doc_joinInlines(v_____do__lift_2944_);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT void l_Lean_Doc_instMarkdownInlineElabInline___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_2944_ = stack[0].m_obj;
lean_object* v___y_2945_ = stack[1].m_obj;
lean_object* v___y_2946_ = stack[2].m_obj;
lean_object* v___y_2947_ = stack[3].m_obj;
lean_object* v_res_2951_;
v_res_2951_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__0(v_____do__lift_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
stack->m_obj
 = v_res_2951_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__0___boxed(lean_object* v_____do__lift_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__0(v_____do__lift_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v_____do__lift_2952_);
return v_res_2957_;
}
}
lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1(lean_object* v___x_2958_, lean_object* v___x_2959_, lean_object* v___f_2960_, lean_object* v_go_2961_, lean_object* v_container_2962_, lean_object* v_content_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
if (lean_obj_tag(v_container_2962_) == 0)
{
lean_object* v_val_2968_; size_t v_sz_2969_; size_t v___x_2970_; lean_object* v___x_2971_; lean_object* v_fallback_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v_val_2968_ = lean_ctor_get(v_container_2962_, 0);
lean_inc(v_val_2968_);
lean_dec_ref_known(v_container_2962_, 1);
v_sz_2969_ = lean_array_size(v_content_2963_);
v___x_2970_ = ((size_t)0ULL);
lean_inc_ref(v_content_2963_);
lean_inc_ref(v_go_2961_);
lean_inc_ref(v___x_2958_);
v___x_2971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2958_, v_go_2961_, v_sz_2969_, v___x_2970_, v_content_2963_);
lean_inc_ref(v___f_2960_);
v_fallback_2972_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_2972_, 0, lean_box(0));
lean_closure_set(v_fallback_2972_, 1, lean_box(0));
lean_closure_set(v_fallback_2972_, 2, v___x_2959_);
lean_closure_set(v_fallback_2972_, 3, lean_box(0));
lean_closure_set(v_fallback_2972_, 4, lean_box(0));
lean_closure_set(v_fallback_2972_, 5, v___x_2971_);
lean_closure_set(v_fallback_2972_, 6, v___f_2960_);
v___x_2973_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2968_);
v___x_2974_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_2973_, v___y_2965_, v___y_2966_);
lean_dec(v___x_2973_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
if (lean_obj_tag(v_a_2975_) == 0)
{
lean_object* v___x_543__overap_2976_; lean_object* v___x_2977_; 
lean_dec_ref(v_fallback_2972_);
lean_dec(v_val_2968_);
v___x_543__overap_2976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2958_, v_go_2961_, v_sz_2969_, v___x_2970_, v_content_2963_);
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2965_);
lean_inc(v___y_2964_);
v___x_2977_ = lean_apply_4(v___x_543__overap_2976_, v___y_2964_, v___y_2965_, v___y_2966_, lean_box(0));
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2965_);
lean_inc(v___y_2964_);
v___x_2979_ = lean_apply_5(v___f_2960_, v_a_2978_, v___y_2964_, v___y_2965_, v___y_2966_, lean_box(0));
return v___x_2979_;
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec_ref(v___f_2960_);
v_a_2980_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2977_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2977_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
else
{
lean_object* v_val_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_dec_ref(v___f_2960_);
lean_dec_ref(v___x_2958_);
v_val_2988_ = lean_ctor_get(v_a_2975_, 0);
lean_inc(v_val_2988_);
lean_dec_ref_known(v_a_2975_, 1);
v___x_2989_ = lean_apply_3(v_val_2988_, v_go_2961_, v_val_2968_, v_content_2963_);
v___x_2990_ = l_Lean_Doc_withRendererFallback(v_fallback_2972_, v___x_2989_, v___y_2964_, v___y_2965_, v___y_2966_);
return v___x_2990_;
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v_fallback_2972_);
lean_dec(v_val_2968_);
lean_dec_ref(v_content_2963_);
lean_dec_ref(v_go_2961_);
lean_dec_ref(v___f_2960_);
lean_dec_ref(v___x_2958_);
v_a_2991_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2974_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2974_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
else
{
size_t v_sz_2999_; size_t v___x_3000_; lean_object* v___x_558__overap_3001_; lean_object* v___x_3002_; 
lean_dec_ref_known(v_container_2962_, 1);
lean_dec_ref(v___f_2960_);
lean_dec_ref(v___x_2959_);
v_sz_2999_ = lean_array_size(v_content_2963_);
v___x_3000_ = ((size_t)0ULL);
v___x_558__overap_3001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2958_, v_go_2961_, v_sz_2999_, v___x_3000_, v_content_2963_);
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2965_);
lean_inc(v___y_2964_);
v___x_3002_ = lean_apply_4(v___x_558__overap_3001_, v___y_2964_, v___y_2965_, v___y_2966_, lean_box(0));
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3011_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3011_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3011_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3007_ = l_Lean_Doc_joinInlines(v_a_3003_);
lean_dec(v_a_3003_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3007_);
v___x_3009_ = v___x_3005_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
else
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
v_a_3012_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_3002_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3002_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_instMarkdownInlineElabInline___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2958_ = stack[0].m_obj;
lean_object* v___x_2959_ = stack[1].m_obj;
lean_object* v___f_2960_ = stack[2].m_obj;
lean_object* v_go_2961_ = stack[3].m_obj;
lean_object* v_container_2962_ = stack[4].m_obj;
lean_object* v_content_2963_ = stack[5].m_obj;
lean_object* v___y_2964_ = stack[6].m_obj;
lean_object* v___y_2965_ = stack[7].m_obj;
lean_object* v___y_2966_ = stack[8].m_obj;
lean_object* v_res_3020_;
v_res_3020_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__1(v___x_2958_, v___x_2959_, v___f_2960_, v_go_2961_, v_container_2962_, v_content_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
stack->m_obj
 = v_res_3020_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed(lean_object* v___x_3021_, lean_object* v___x_3022_, lean_object* v___f_3023_, lean_object* v_go_3024_, lean_object* v_container_3025_, lean_object* v_content_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__1(v___x_3021_, v___x_3022_, v___f_3023_, v_go_3024_, v_container_3025_, v_content_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
return v_res_3031_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownInlineElabInline(void){
_start:
{
lean_object* v___x_3033_; lean_object* v_toApplicative_3034_; lean_object* v_toFunctor_3035_; lean_object* v_toSeq_3036_; lean_object* v_toSeqLeft_3037_; lean_object* v_toSeqRight_3038_; lean_object* v___f_3039_; lean_object* v___f_3040_; lean_object* v___f_3041_; lean_object* v___f_3042_; lean_object* v___f_3043_; lean_object* v___x_3044_; lean_object* v___f_3045_; lean_object* v___f_3046_; lean_object* v___f_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___f_3051_; 
v___x_3033_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3034_ = lean_ctor_get(v___x_3033_, 0);
v_toFunctor_3035_ = lean_ctor_get(v_toApplicative_3034_, 0);
v_toSeq_3036_ = lean_ctor_get(v_toApplicative_3034_, 2);
v_toSeqLeft_3037_ = lean_ctor_get(v_toApplicative_3034_, 3);
v_toSeqRight_3038_ = lean_ctor_get(v_toApplicative_3034_, 4);
v___f_3039_ = ((lean_object*)(l_Lean_Doc_instMarkdownInlineElabInline___closed__0));
v___f_3040_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3041_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3035_, 2);
v___f_3042_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3042_, 0, v_toFunctor_3035_);
v___f_3043_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3043_, 0, v_toFunctor_3035_);
v___x_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___f_3042_);
lean_ctor_set(v___x_3044_, 1, v___f_3043_);
lean_inc(v_toSeqRight_3038_);
v___f_3045_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3045_, 0, v_toSeqRight_3038_);
lean_inc(v_toSeqLeft_3037_);
v___f_3046_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3046_, 0, v_toSeqLeft_3037_);
lean_inc(v_toSeq_3036_);
v___f_3047_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3047_, 0, v_toSeq_3036_);
v___x_3048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3044_);
lean_ctor_set(v___x_3048_, 1, v___f_3040_);
lean_ctor_set(v___x_3048_, 2, v___f_3047_);
lean_ctor_set(v___x_3048_, 3, v___f_3046_);
lean_ctor_set(v___x_3048_, 4, v___f_3045_);
v___x_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
lean_ctor_set(v___x_3049_, 1, v___f_3041_);
lean_inc_ref(v___x_3049_);
v___x_3050_ = l_StateRefT_x27_instMonad___redArg(v___x_3049_);
v___f_3051_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3051_, 0, v___x_3050_);
lean_closure_set(v___f_3051_, 1, v___x_3049_);
lean_closure_set(v___f_3051_, 2, v___f_3039_);
return v___f_3051_;
}
}
lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v_____do__lift_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = l_Lean_Doc_joinBlocks(v_____do__lift_3052_);
v___x_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT void l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_3052_ = stack[0].m_obj;
lean_object* v___y_3053_ = stack[1].m_obj;
lean_object* v___y_3054_ = stack[2].m_obj;
lean_object* v___y_3055_ = stack[3].m_obj;
lean_object* v_res_3059_;
v_res_3059_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(v_____do__lift_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
stack->m_obj
 = v_res_3059_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object* v_____do__lift_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(v_____do__lift_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v_____do__lift_3060_);
return v_res_3065_;
}
}
lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object* v___x_3066_, lean_object* v___x_3067_, lean_object* v___f_3068_, lean_object* v_goI_3069_, lean_object* v_goB_3070_, lean_object* v_container_3071_, lean_object* v_content_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
if (lean_obj_tag(v_container_3071_) == 0)
{
lean_object* v_val_3077_; size_t v_sz_3078_; size_t v___x_3079_; lean_object* v___x_3080_; lean_object* v_fallback_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_val_3077_ = lean_ctor_get(v_container_3071_, 0);
lean_inc(v_val_3077_);
lean_dec_ref_known(v_container_3071_, 1);
v_sz_3078_ = lean_array_size(v_content_3072_);
v___x_3079_ = ((size_t)0ULL);
lean_inc_ref(v_content_3072_);
lean_inc_ref(v_goB_3070_);
lean_inc_ref(v___x_3066_);
v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3066_, v_goB_3070_, v_sz_3078_, v___x_3079_, v_content_3072_);
lean_inc_ref(v___f_3068_);
v_fallback_3081_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_3081_, 0, lean_box(0));
lean_closure_set(v_fallback_3081_, 1, lean_box(0));
lean_closure_set(v_fallback_3081_, 2, v___x_3067_);
lean_closure_set(v_fallback_3081_, 3, lean_box(0));
lean_closure_set(v_fallback_3081_, 4, lean_box(0));
lean_closure_set(v_fallback_3081_, 5, v___x_3080_);
lean_closure_set(v_fallback_3081_, 6, v___f_3068_);
v___x_3082_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3077_);
v___x_3083_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_3082_, v___y_3074_, v___y_3075_);
lean_dec(v___x_3082_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
if (lean_obj_tag(v_a_3084_) == 0)
{
lean_object* v___x_543__overap_3085_; lean_object* v___x_3086_; 
lean_dec_ref(v_fallback_3081_);
lean_dec(v_val_3077_);
lean_dec_ref(v_goI_3069_);
v___x_543__overap_3085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3066_, v_goB_3070_, v_sz_3078_, v___x_3079_, v_content_3072_);
lean_inc(v___y_3075_);
lean_inc_ref(v___y_3074_);
lean_inc(v___y_3073_);
v___x_3086_ = lean_apply_4(v___x_543__overap_3085_, v___y_3073_, v___y_3074_, v___y_3075_, lean_box(0));
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3088_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3086_, 1);
lean_inc(v___y_3075_);
lean_inc_ref(v___y_3074_);
lean_inc(v___y_3073_);
v___x_3088_ = lean_apply_5(v___f_3068_, v_a_3087_, v___y_3073_, v___y_3074_, v___y_3075_, lean_box(0));
return v___x_3088_;
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec_ref(v___f_3068_);
v_a_3089_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3086_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3086_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_object* v_val_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec_ref(v___f_3068_);
lean_dec_ref(v___x_3066_);
v_val_3097_ = lean_ctor_get(v_a_3084_, 0);
lean_inc(v_val_3097_);
lean_dec_ref_known(v_a_3084_, 1);
v___x_3098_ = lean_apply_4(v_val_3097_, v_goI_3069_, v_goB_3070_, v_val_3077_, v_content_3072_);
v___x_3099_ = l_Lean_Doc_withRendererFallback(v_fallback_3081_, v___x_3098_, v___y_3073_, v___y_3074_, v___y_3075_);
return v___x_3099_;
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec_ref(v_fallback_3081_);
lean_dec(v_val_3077_);
lean_dec_ref(v_content_3072_);
lean_dec_ref(v_goB_3070_);
lean_dec_ref(v_goI_3069_);
lean_dec_ref(v___f_3068_);
lean_dec_ref(v___x_3066_);
v_a_3100_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3083_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3083_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
else
{
size_t v_sz_3108_; size_t v___x_3109_; lean_object* v___x_558__overap_3110_; lean_object* v___x_3111_; 
lean_dec_ref_known(v_container_3071_, 1);
lean_dec_ref(v_goI_3069_);
lean_dec_ref(v___f_3068_);
lean_dec_ref(v___x_3067_);
v_sz_3108_ = lean_array_size(v_content_3072_);
v___x_3109_ = ((size_t)0ULL);
v___x_558__overap_3110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3066_, v_goB_3070_, v_sz_3108_, v___x_3109_, v_content_3072_);
lean_inc(v___y_3075_);
lean_inc_ref(v___y_3074_);
lean_inc(v___y_3073_);
v___x_3111_ = lean_apply_4(v___x_558__overap_3110_, v___y_3073_, v___y_3074_, v___y_3075_, lean_box(0));
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3120_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3114_ = v___x_3111_;
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = l_Lean_Doc_joinBlocks(v_a_3112_);
lean_dec(v_a_3112_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3116_);
v___x_3118_ = v___x_3114_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
v_a_3121_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3111_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3111_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3066_ = stack[0].m_obj;
lean_object* v___x_3067_ = stack[1].m_obj;
lean_object* v___f_3068_ = stack[2].m_obj;
lean_object* v_goI_3069_ = stack[3].m_obj;
lean_object* v_goB_3070_ = stack[4].m_obj;
lean_object* v_container_3071_ = stack[5].m_obj;
lean_object* v_content_3072_ = stack[6].m_obj;
lean_object* v___y_3073_ = stack[7].m_obj;
lean_object* v___y_3074_ = stack[8].m_obj;
lean_object* v___y_3075_ = stack[9].m_obj;
lean_object* v_res_3129_;
v_res_3129_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_3066_, v___x_3067_, v___f_3068_, v_goI_3069_, v_goB_3070_, v_container_3071_, v_content_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
stack->m_obj
 = v_res_3129_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object* v___x_3130_, lean_object* v___x_3131_, lean_object* v___f_3132_, lean_object* v_goI_3133_, lean_object* v_goB_3134_, lean_object* v_container_3135_, lean_object* v_content_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_3130_, v___x_3131_, v___f_3132_, v_goI_3133_, v_goB_3134_, v_container_3135_, v_content_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3137_);
return v_res_3141_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownBlockElabInlineElabBlock(void){
_start:
{
lean_object* v___x_3143_; lean_object* v_toApplicative_3144_; lean_object* v_toFunctor_3145_; lean_object* v_toSeq_3146_; lean_object* v_toSeqLeft_3147_; lean_object* v_toSeqRight_3148_; lean_object* v___f_3149_; lean_object* v___f_3150_; lean_object* v___f_3151_; lean_object* v___f_3152_; lean_object* v___f_3153_; lean_object* v___x_3154_; lean_object* v___f_3155_; lean_object* v___f_3156_; lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___f_3161_; 
v___x_3143_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3144_ = lean_ctor_get(v___x_3143_, 0);
v_toFunctor_3145_ = lean_ctor_get(v_toApplicative_3144_, 0);
v_toSeq_3146_ = lean_ctor_get(v_toApplicative_3144_, 2);
v_toSeqLeft_3147_ = lean_ctor_get(v_toApplicative_3144_, 3);
v_toSeqRight_3148_ = lean_ctor_get(v_toApplicative_3144_, 4);
v___f_3149_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___closed__0));
v___f_3150_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3151_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3145_, 2);
v___f_3152_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3152_, 0, v_toFunctor_3145_);
v___f_3153_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3153_, 0, v_toFunctor_3145_);
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___f_3152_);
lean_ctor_set(v___x_3154_, 1, v___f_3153_);
lean_inc(v_toSeqRight_3148_);
v___f_3155_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3155_, 0, v_toSeqRight_3148_);
lean_inc(v_toSeqLeft_3147_);
v___f_3156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3156_, 0, v_toSeqLeft_3147_);
lean_inc(v_toSeq_3146_);
v___f_3157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3157_, 0, v_toSeq_3146_);
v___x_3158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3154_);
lean_ctor_set(v___x_3158_, 1, v___f_3150_);
lean_ctor_set(v___x_3158_, 2, v___f_3157_);
lean_ctor_set(v___x_3158_, 3, v___f_3156_);
lean_ctor_set(v___x_3158_, 4, v___f_3155_);
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
lean_ctor_set(v___x_3159_, 1, v___f_3151_);
lean_inc_ref(v___x_3159_);
v___x_3160_ = l_StateRefT_x27_instMonad___redArg(v___x_3159_);
v___f_3161_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3161_, 0, v___x_3160_);
lean_closure_set(v___f_3161_, 1, v___x_3159_);
lean_closure_set(v___f_3161_, 2, v___f_3149_);
return v___f_3161_;
}
}
lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0(lean_object* v___x_3162_, lean_object* v___x_3163_, lean_object* v_part_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = lean_unsigned_to_nat(0u);
v___x_3170_ = l_Lean_Doc_partMarkdown___redArg(v___x_3162_, v___x_3163_, v___x_3169_, v_part_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3170_;
}
}
LEAN_EXPORT void l_Lean_Doc_instToMarkdownVersoDocString___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3162_ = stack[0].m_obj;
lean_object* v___x_3163_ = stack[1].m_obj;
lean_object* v_part_3164_ = stack[2].m_obj;
lean_object* v___y_3165_ = stack[3].m_obj;
lean_object* v___y_3166_ = stack[4].m_obj;
lean_object* v___y_3167_ = stack[5].m_obj;
lean_object* v_res_3171_;
v_res_3171_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__0(v___x_3162_, v___x_3163_, v_part_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
stack->m_obj
 = v_res_3171_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed(lean_object* v___x_3172_, lean_object* v___x_3173_, lean_object* v_part_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__0(v___x_3172_, v___x_3173_, v_part_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
return v_res_3179_;
}
}
lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1(lean_object* v___x_3180_, lean_object* v___x_3181_, lean_object* v___x_3182_, lean_object* v___f_3183_, lean_object* v_x_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_text_3189_; lean_object* v_subsections_3190_; lean_object* v___x_3191_; size_t v_sz_3192_; size_t v___x_3193_; lean_object* v___x_443__overap_3194_; lean_object* v___x_3195_; 
v_text_3189_ = lean_ctor_get(v_x_3184_, 0);
lean_inc_ref(v_text_3189_);
v_subsections_3190_ = lean_ctor_get(v_x_3184_, 1);
lean_inc_ref(v_subsections_3190_);
lean_dec_ref(v_x_3184_);
v___x_3191_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3191_, 0, lean_box(0));
lean_closure_set(v___x_3191_, 1, lean_box(0));
lean_closure_set(v___x_3191_, 2, v___x_3180_);
lean_closure_set(v___x_3191_, 3, v___x_3181_);
v_sz_3192_ = lean_array_size(v_text_3189_);
v___x_3193_ = ((size_t)0ULL);
lean_inc_ref(v___x_3182_);
v___x_443__overap_3194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3182_, v___x_3191_, v_sz_3192_, v___x_3193_, v_text_3189_);
lean_inc(v___y_3187_);
lean_inc_ref(v___y_3186_);
lean_inc(v___y_3185_);
v___x_3195_ = lean_apply_4(v___x_443__overap_3194_, v___y_3185_, v___y_3186_, v___y_3187_, lean_box(0));
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; size_t v_sz_3197_; lean_object* v___x_446__overap_3198_; lean_object* v___x_3199_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3195_, 1);
v_sz_3197_ = lean_array_size(v_subsections_3190_);
v___x_446__overap_3198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3182_, v___f_3183_, v_sz_3197_, v___x_3193_, v_subsections_3190_);
lean_inc(v___y_3187_);
lean_inc_ref(v___y_3186_);
lean_inc(v___y_3185_);
v___x_3199_ = lean_apply_4(v___x_446__overap_3198_, v___y_3185_, v___y_3186_, v___y_3187_, lean_box(0));
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3209_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3209_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3209_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3204_ = l_Array_append___redArg(v_a_3196_, v_a_3200_);
lean_dec(v_a_3200_);
v___x_3205_ = l_Lean_Doc_joinBlocks(v___x_3204_);
lean_dec_ref(v___x_3204_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v___x_3205_);
v___x_3207_ = v___x_3202_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v_a_3196_);
v_a_3210_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3199_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3199_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec_ref(v_subsections_3190_);
lean_dec_ref(v___f_3183_);
lean_dec_ref(v___x_3182_);
v_a_3218_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3195_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3195_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_instToMarkdownVersoDocString___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3180_ = stack[0].m_obj;
lean_object* v___x_3181_ = stack[1].m_obj;
lean_object* v___x_3182_ = stack[2].m_obj;
lean_object* v___f_3183_ = stack[3].m_obj;
lean_object* v_x_3184_ = stack[4].m_obj;
lean_object* v___y_3185_ = stack[5].m_obj;
lean_object* v___y_3186_ = stack[6].m_obj;
lean_object* v___y_3187_ = stack[7].m_obj;
lean_object* v_res_3226_;
v_res_3226_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__1(v___x_3180_, v___x_3181_, v___x_3182_, v___f_3183_, v_x_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
stack->m_obj
 = v_res_3226_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed(lean_object* v___x_3227_, lean_object* v___x_3228_, lean_object* v___x_3229_, lean_object* v___f_3230_, lean_object* v_x_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__1(v___x_3227_, v___x_3228_, v___x_3229_, v___f_3230_, v_x_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
return v_res_3236_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___f_3239_; 
v___x_3237_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3238_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3239_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3239_, 0, v___x_3238_);
lean_closure_set(v___f_3239_, 1, v___x_3237_);
return v___f_3239_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString(void){
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
v___f_3259_ = lean_obj_once(&l_Lean_Doc_instToMarkdownVersoDocString___closed__0, &l_Lean_Doc_instToMarkdownVersoDocString___closed__0_once, _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0);
v___f_3260_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3260_, 0, v___x_3257_);
lean_closure_set(v___f_3260_, 1, v___x_3258_);
lean_closure_set(v___f_3260_, 2, v___x_3256_);
lean_closure_set(v___f_3260_, 3, v___f_3259_);
return v___f_3260_;
}
}
lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0(lean_object* v___x_3261_, lean_object* v___x_3262_, lean_object* v_x_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v_snd_3268_; lean_object* v_fst_3269_; lean_object* v_snd_3270_; lean_object* v___x_3271_; 
v_snd_3268_ = lean_ctor_get(v_x_3263_, 1);
lean_inc(v_snd_3268_);
v_fst_3269_ = lean_ctor_get(v_x_3263_, 0);
lean_inc(v_fst_3269_);
lean_dec_ref(v_x_3263_);
v_snd_3270_ = lean_ctor_get(v_snd_3268_, 1);
lean_inc(v_snd_3270_);
lean_dec(v_snd_3268_);
v___x_3271_ = l_Lean_Doc_partMarkdown___redArg(v___x_3261_, v___x_3262_, v_fst_3269_, v_snd_3270_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec(v_fst_3269_);
return v___x_3271_;
}
}
LEAN_EXPORT void l_Lean_Doc_instToMarkdownSnippet___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3261_ = stack[0].m_obj;
lean_object* v___x_3262_ = stack[1].m_obj;
lean_object* v_x_3263_ = stack[2].m_obj;
lean_object* v___y_3264_ = stack[3].m_obj;
lean_object* v___y_3265_ = stack[4].m_obj;
lean_object* v___y_3266_ = stack[5].m_obj;
lean_object* v_res_3272_;
v_res_3272_ = l_Lean_Doc_instToMarkdownSnippet___lam__0(v___x_3261_, v___x_3262_, v_x_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
stack->m_obj
 = v_res_3272_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_3273_, lean_object* v___x_3274_, lean_object* v_x_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_Doc_instToMarkdownSnippet___lam__0(v___x_3273_, v___x_3274_, v_x_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
return v_res_3280_;
}
}
lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1(lean_object* v___x_3281_, lean_object* v___x_3282_, lean_object* v___x_3283_, lean_object* v___f_3284_, lean_object* v_x_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_text_3290_; lean_object* v_sections_3291_; lean_object* v___x_3292_; size_t v_sz_3293_; size_t v___x_3294_; lean_object* v___x_490__overap_3295_; lean_object* v___x_3296_; 
v_text_3290_ = lean_ctor_get(v_x_3285_, 0);
lean_inc_ref(v_text_3290_);
v_sections_3291_ = lean_ctor_get(v_x_3285_, 1);
lean_inc_ref(v_sections_3291_);
lean_dec_ref(v_x_3285_);
v___x_3292_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3292_, 0, lean_box(0));
lean_closure_set(v___x_3292_, 1, lean_box(0));
lean_closure_set(v___x_3292_, 2, v___x_3281_);
lean_closure_set(v___x_3292_, 3, v___x_3282_);
v_sz_3293_ = lean_array_size(v_text_3290_);
v___x_3294_ = ((size_t)0ULL);
lean_inc_ref(v___x_3283_);
v___x_490__overap_3295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3283_, v___x_3292_, v_sz_3293_, v___x_3294_, v_text_3290_);
lean_inc(v___y_3288_);
lean_inc_ref(v___y_3287_);
lean_inc(v___y_3286_);
v___x_3296_ = lean_apply_4(v___x_490__overap_3295_, v___y_3286_, v___y_3287_, v___y_3288_, lean_box(0));
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; size_t v_sz_3298_; lean_object* v___x_493__overap_3299_; lean_object* v___x_3300_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v_sz_3298_ = lean_array_size(v_sections_3291_);
v___x_493__overap_3299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3283_, v___f_3284_, v_sz_3298_, v___x_3294_, v_sections_3291_);
lean_inc(v___y_3288_);
lean_inc_ref(v___y_3287_);
lean_inc(v___y_3286_);
v___x_3300_ = lean_apply_4(v___x_493__overap_3299_, v___y_3286_, v___y_3287_, v___y_3288_, lean_box(0));
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3310_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3310_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3310_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3305_ = l_Array_append___redArg(v_a_3297_, v_a_3301_);
lean_dec(v_a_3301_);
v___x_3306_ = l_Lean_Doc_joinBlocks(v___x_3305_);
lean_dec_ref(v___x_3305_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3306_);
v___x_3308_ = v___x_3303_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec(v_a_3297_);
v_a_3311_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3300_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3300_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec_ref(v_sections_3291_);
lean_dec_ref(v___f_3284_);
lean_dec_ref(v___x_3283_);
v_a_3319_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3296_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3296_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_instToMarkdownSnippet___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3281_ = stack[0].m_obj;
lean_object* v___x_3282_ = stack[1].m_obj;
lean_object* v___x_3283_ = stack[2].m_obj;
lean_object* v___f_3284_ = stack[3].m_obj;
lean_object* v_x_3285_ = stack[4].m_obj;
lean_object* v___y_3286_ = stack[5].m_obj;
lean_object* v___y_3287_ = stack[6].m_obj;
lean_object* v___y_3288_ = stack[7].m_obj;
lean_object* v_res_3327_;
v_res_3327_ = l_Lean_Doc_instToMarkdownSnippet___lam__1(v___x_3281_, v___x_3282_, v___x_3283_, v___f_3284_, v_x_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
stack->m_obj
 = v_res_3327_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_3328_, lean_object* v___x_3329_, lean_object* v___x_3330_, lean_object* v___f_3331_, lean_object* v_x_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Lean_Doc_instToMarkdownSnippet___lam__1(v___x_3328_, v___x_3329_, v___x_3330_, v___f_3331_, v_x_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
return v_res_3337_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___f_3340_; 
v___x_3338_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3339_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3340_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3340_, 0, v___x_3339_);
lean_closure_set(v___f_3340_, 1, v___x_3338_);
return v___f_3340_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet(void){
_start:
{
lean_object* v___x_3341_; lean_object* v_toApplicative_3342_; lean_object* v_toFunctor_3343_; lean_object* v_toSeq_3344_; lean_object* v_toSeqLeft_3345_; lean_object* v_toSeqRight_3346_; lean_object* v___f_3347_; lean_object* v___f_3348_; lean_object* v___f_3349_; lean_object* v___f_3350_; lean_object* v___x_3351_; lean_object* v___f_3352_; lean_object* v___f_3353_; lean_object* v___f_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___f_3360_; lean_object* v___f_3361_; 
v___x_3341_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3342_ = lean_ctor_get(v___x_3341_, 0);
v_toFunctor_3343_ = lean_ctor_get(v_toApplicative_3342_, 0);
v_toSeq_3344_ = lean_ctor_get(v_toApplicative_3342_, 2);
v_toSeqLeft_3345_ = lean_ctor_get(v_toApplicative_3342_, 3);
v_toSeqRight_3346_ = lean_ctor_get(v_toApplicative_3342_, 4);
v___f_3347_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3348_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3343_, 2);
v___f_3349_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3349_, 0, v_toFunctor_3343_);
v___f_3350_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3350_, 0, v_toFunctor_3343_);
v___x_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___f_3349_);
lean_ctor_set(v___x_3351_, 1, v___f_3350_);
lean_inc(v_toSeqRight_3346_);
v___f_3352_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3352_, 0, v_toSeqRight_3346_);
lean_inc(v_toSeqLeft_3345_);
v___f_3353_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3353_, 0, v_toSeqLeft_3345_);
lean_inc(v_toSeq_3344_);
v___f_3354_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3354_, 0, v_toSeq_3344_);
v___x_3355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3351_);
lean_ctor_set(v___x_3355_, 1, v___f_3347_);
lean_ctor_set(v___x_3355_, 2, v___f_3354_);
lean_ctor_set(v___x_3355_, 3, v___f_3353_);
lean_ctor_set(v___x_3355_, 4, v___f_3352_);
v___x_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
lean_ctor_set(v___x_3356_, 1, v___f_3348_);
v___x_3357_ = l_StateRefT_x27_instMonad___redArg(v___x_3356_);
v___x_3358_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3359_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3360_ = lean_obj_once(&l_Lean_Doc_instToMarkdownSnippet___closed__0, &l_Lean_Doc_instToMarkdownSnippet___closed__0_once, _init_l_Lean_Doc_instToMarkdownSnippet___closed__0);
v___f_3361_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3361_, 0, v___x_3358_);
lean_closure_set(v___f_3361_, 1, v___x_3359_);
lean_closure_set(v___f_3361_, 2, v___x_3357_);
lean_closure_set(v___f_3361_, 3, v___f_3360_);
return v___f_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(lean_object* v_opts_3362_, lean_object* v_opt_3363_){
_start:
{
lean_object* v_name_3364_; lean_object* v_defValue_3365_; lean_object* v_map_3366_; lean_object* v___x_3367_; 
v_name_3364_ = lean_ctor_get(v_opt_3363_, 0);
v_defValue_3365_ = lean_ctor_get(v_opt_3363_, 1);
v_map_3366_ = lean_ctor_get(v_opts_3362_, 0);
v___x_3367_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3366_, v_name_3364_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_inc(v_defValue_3365_);
return v_defValue_3365_;
}
else
{
lean_object* v_val_3368_; 
v_val_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_val_3368_);
lean_dec_ref_known(v___x_3367_, 1);
if (lean_obj_tag(v_val_3368_) == 3)
{
lean_object* v_v_3369_; 
v_v_3369_ = lean_ctor_get(v_val_3368_, 0);
lean_inc(v_v_3369_);
lean_dec_ref_known(v_val_3368_, 1);
return v_v_3369_;
}
else
{
lean_dec(v_val_3368_);
lean_inc(v_defValue_3365_);
return v_defValue_3365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0___boxed(lean_object* v_opts_3370_, lean_object* v_opt_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_opts_3370_, v_opt_3371_);
lean_dec_ref(v_opt_3371_);
lean_dec_ref(v_opts_3370_);
return v_res_3372_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = lean_unsigned_to_nat(1u);
v___x_3375_ = l_Lean_firstFrontendMacroScope;
v___x_3376_ = lean_nat_add(v___x_3375_, v___x_3374_);
return v___x_3376_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__6(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = lean_unsigned_to_nat(32u);
v___x_3388_ = lean_mk_empty_array_with_capacity(v___x_3387_);
v___x_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
return v___x_3389_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__7(void){
_start:
{
size_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3390_ = ((size_t)5ULL);
v___x_3391_ = lean_unsigned_to_nat(0u);
v___x_3392_ = lean_unsigned_to_nat(32u);
v___x_3393_ = lean_mk_empty_array_with_capacity(v___x_3392_);
v___x_3394_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__6, &l_Lean_Doc_runMarkdown___redArg___closed__6_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__6);
v___x_3395_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v___x_3393_);
lean_ctor_set(v___x_3395_, 2, v___x_3391_);
lean_ctor_set(v___x_3395_, 3, v___x_3391_);
lean_ctor_set_usize(v___x_3395_, 4, v___x_3390_);
return v___x_3395_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__8(void){
_start:
{
lean_object* v___x_3396_; uint64_t v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3397_ = 0ULL;
v___x_3398_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3398_, 0, v___x_3396_);
lean_ctor_set_uint64(v___x_3398_, sizeof(void*)*1, v___x_3397_);
return v___x_3398_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__9(void){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
return v___x_3400_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__10(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__9, &l_Lean_Doc_runMarkdown___redArg___closed__9_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__9);
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
return v___x_3402_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__12(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3405_ = lean_unsigned_to_nat(0u);
v___x_3406_ = l_Lean_Options_empty;
v___x_3407_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__11));
v___x_3408_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_ctor_set(v___x_3408_, 1, v___x_3406_);
lean_ctor_set(v___x_3408_, 2, v___x_3407_);
lean_ctor_set(v___x_3408_, 3, v___x_3405_);
lean_ctor_set(v___x_3408_, 4, v___x_3405_);
lean_ctor_set(v___x_3408_, 5, v___x_3405_);
return v___x_3408_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__13(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3409_ = l_Lean_NameSet_empty;
v___x_3410_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
lean_ctor_set(v___x_3411_, 2, v___x_3409_);
return v___x_3411_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__14(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; lean_object* v___x_3415_; 
v___x_3412_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3413_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__9, &l_Lean_Doc_runMarkdown___redArg___closed__9_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__9);
v___x_3414_ = 1;
v___x_3415_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3415_, 0, v___x_3413_);
lean_ctor_set(v___x_3415_, 1, v___x_3413_);
lean_ctor_set(v___x_3415_, 2, v___x_3412_);
lean_ctor_set_uint8(v___x_3415_, sizeof(void*)*3, v___x_3414_);
return v___x_3415_;
}
}
lean_object* l_Lean_Doc_runMarkdown___redArg(lean_object* v_env_3419_, lean_object* v_act_3420_, lean_object* v_options_3421_, lean_object* v_currNamespace_3422_, lean_object* v_openDecls_3423_, lean_object* v_cancelTk_x3f_3424_){
_start:
{
lean_object* v_a_3427_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint16_t v___x_3437_; uint8_t v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v_fileName_3453_; lean_object* v_fileMap_3454_; lean_object* v_currNamespace_3455_; lean_object* v_openDecls_3456_; lean_object* v_initHeartbeats_3457_; lean_object* v_maxHeartbeats_3458_; lean_object* v_quotContext_3459_; lean_object* v_currMacroScope_3460_; lean_object* v_cancelTk_x3f_3461_; lean_object* v_inheritedTraceOptions_3462_; lean_object* v_currRecDepth_3463_; lean_object* v_ref_3464_; uint8_t v_suppressElabErrors_3465_; uint8_t v_isRecordingDeps_3466_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___y_3507_; lean_object* v_env_3528_; uint8_t v___x_3529_; uint16_t v___x_3530_; uint16_t v___x_3531_; uint16_t v___x_3532_; uint8_t v___x_3533_; 
v___x_3430_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__0));
v___x_3431_ = l_Lean_instInhabitedFileMap_default;
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = l_Lean_Core_getMaxHeartbeats(v_options_3421_);
v___x_3434_ = lean_box(0);
v___x_3435_ = l_Lean_firstFrontendMacroScope;
v___x_3436_ = lean_box(0);
v___x_3437_ = l_Lean_OptionFlags_ofOptions(v_options_3421_);
v___x_3438_ = 0;
v___x_3439_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__1, &l_Lean_Doc_runMarkdown___redArg___closed__1_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__1);
v___x_3440_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__4));
v___x_3441_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__5));
v___x_3442_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__8, &l_Lean_Doc_runMarkdown___redArg___closed__8_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__8);
v___x_3443_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__10, &l_Lean_Doc_runMarkdown___redArg___closed__10_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__10);
v___x_3444_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__11));
v___x_3445_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__12, &l_Lean_Doc_runMarkdown___redArg___closed__12_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__12);
v___x_3446_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__13, &l_Lean_Doc_runMarkdown___redArg___closed__13_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__13);
v___x_3447_ = 1;
v___x_3448_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__14, &l_Lean_Doc_runMarkdown___redArg___closed__14_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__14);
v___x_3449_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3449_, 0, v_env_3419_);
lean_ctor_set(v___x_3449_, 1, v___x_3439_);
lean_ctor_set(v___x_3449_, 2, v___x_3440_);
lean_ctor_set(v___x_3449_, 3, v___x_3441_);
lean_ctor_set(v___x_3449_, 4, v___x_3442_);
lean_ctor_set(v___x_3449_, 5, v___x_3443_);
lean_ctor_set(v___x_3449_, 6, v___x_3445_);
lean_ctor_set(v___x_3449_, 7, v___x_3446_);
lean_ctor_set(v___x_3449_, 8, v___x_3448_);
lean_ctor_set(v___x_3449_, 9, v___x_3444_);
v___x_3450_ = lean_io_get_num_heartbeats();
v___x_3451_ = lean_st_mk_ref(v___x_3449_);
v___x_3503_ = l_Lean_inheritedTraceOptions;
v___x_3504_ = lean_st_ref_get(v___x_3503_);
v___x_3505_ = lean_st_ref_get(v___x_3451_);
v_env_3528_ = lean_ctor_get(v___x_3505_, 0);
lean_inc_ref(v_env_3528_);
lean_dec(v___x_3505_);
v___x_3529_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3528_);
lean_dec_ref(v_env_3528_);
v___x_3530_ = 512;
v___x_3531_ = lean_uint16_land(v___x_3437_, v___x_3530_);
v___x_3532_ = 0;
v___x_3533_ = lean_uint16_dec_eq(v___x_3531_, v___x_3532_);
if (v___x_3533_ == 0)
{
if (v___x_3529_ == 0)
{
v___y_3507_ = v___x_3447_;
goto v___jp_3506_;
}
else
{
v_fileName_3453_ = v___x_3430_;
v_fileMap_3454_ = v___x_3431_;
v_currNamespace_3455_ = v_currNamespace_3422_;
v_openDecls_3456_ = v_openDecls_3423_;
v_initHeartbeats_3457_ = v___x_3450_;
v_maxHeartbeats_3458_ = v___x_3433_;
v_quotContext_3459_ = v___x_3434_;
v_currMacroScope_3460_ = v___x_3435_;
v_cancelTk_x3f_3461_ = v_cancelTk_x3f_3424_;
v_inheritedTraceOptions_3462_ = v___x_3504_;
v_currRecDepth_3463_ = v___x_3432_;
v_ref_3464_ = v___x_3436_;
v_suppressElabErrors_3465_ = v___x_3438_;
v_isRecordingDeps_3466_ = v___x_3438_;
goto v___jp_3452_;
}
}
else
{
if (v___x_3529_ == 0)
{
v_fileName_3453_ = v___x_3430_;
v_fileMap_3454_ = v___x_3431_;
v_currNamespace_3455_ = v_currNamespace_3422_;
v_openDecls_3456_ = v_openDecls_3423_;
v_initHeartbeats_3457_ = v___x_3450_;
v_maxHeartbeats_3458_ = v___x_3433_;
v_quotContext_3459_ = v___x_3434_;
v_currMacroScope_3460_ = v___x_3435_;
v_cancelTk_x3f_3461_ = v_cancelTk_x3f_3424_;
v_inheritedTraceOptions_3462_ = v___x_3504_;
v_currRecDepth_3463_ = v___x_3432_;
v_ref_3464_ = v___x_3436_;
v_suppressElabErrors_3465_ = v___x_3438_;
v_isRecordingDeps_3466_ = v___x_3438_;
goto v___jp_3452_;
}
else
{
v___y_3507_ = v___x_3438_;
goto v___jp_3506_;
}
}
v___jp_3426_:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = lean_mk_io_user_error(v_a_3427_);
v___x_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
v___jp_3452_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3467_ = l_Lean_maxRecDepth;
v___x_3468_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_options_3421_, v___x_3467_);
lean_inc(v_currMacroScope_3460_);
lean_inc(v_quotContext_3459_);
lean_inc_ref(v_fileMap_3454_);
lean_inc_ref(v_fileName_3453_);
v___x_3469_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3469_, 0, v_fileName_3453_);
lean_ctor_set(v___x_3469_, 1, v_fileMap_3454_);
lean_ctor_set(v___x_3469_, 2, v_options_3421_);
lean_ctor_set(v___x_3469_, 3, v___x_3468_);
lean_ctor_set(v___x_3469_, 4, v_currNamespace_3455_);
lean_ctor_set(v___x_3469_, 5, v_openDecls_3456_);
lean_ctor_set(v___x_3469_, 6, v_initHeartbeats_3457_);
lean_ctor_set(v___x_3469_, 7, v_maxHeartbeats_3458_);
lean_ctor_set(v___x_3469_, 8, v_quotContext_3459_);
lean_ctor_set(v___x_3469_, 9, v_currMacroScope_3460_);
lean_ctor_set(v___x_3469_, 10, v_cancelTk_x3f_3461_);
lean_ctor_set(v___x_3469_, 11, v_inheritedTraceOptions_3462_);
lean_inc(v_ref_3464_);
v___x_3470_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v_currRecDepth_3463_);
lean_ctor_set(v___x_3470_, 2, v_ref_3464_);
lean_ctor_set_uint16(v___x_3470_, sizeof(void*)*3, v___x_3437_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*3 + 2, v_suppressElabErrors_3465_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*3 + 3, v_isRecordingDeps_3466_);
lean_inc(v___x_3451_);
v___x_3471_ = lean_apply_3(v_act_3420_, v___x_3470_, v___x_3451_, lean_box(0));
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3480_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3474_ = v___x_3471_;
v_isShared_3475_ = v_isSharedCheck_3480_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3480_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3476_ = lean_st_ref_get(v___x_3451_);
lean_dec(v___x_3451_);
lean_dec(v___x_3476_);
if (v_isShared_3475_ == 0)
{
v___x_3478_ = v___x_3474_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3472_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3502_; 
lean_dec(v___x_3451_);
v_a_3481_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3483_ = v___x_3471_;
v_isShared_3484_ = v_isSharedCheck_3502_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3471_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3502_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
if (lean_obj_tag(v_a_3481_) == 0)
{
lean_object* v_msg_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3489_; 
v_msg_3485_ = lean_ctor_get(v_a_3481_, 1);
lean_inc_ref(v_msg_3485_);
lean_dec_ref_known(v_a_3481_, 2);
v___x_3486_ = l_Lean_MessageData_toString(v_msg_3485_);
v___x_3487_ = lean_mk_io_user_error(v___x_3486_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3487_);
v___x_3489_ = v___x_3483_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
else
{
lean_object* v_id_3491_; lean_object* v___x_3492_; 
lean_del_object(v___x_3483_);
v_id_3491_ = lean_ctor_get(v_a_3481_, 0);
lean_inc(v_id_3491_);
lean_dec_ref_known(v_a_3481_, 2);
v___x_3492_ = l_Lean_InternalExceptionId_getName(v_id_3491_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
lean_dec(v_id_3491_);
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v___x_3494_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__15));
v___x_3495_ = l_Lean_Name_toString(v_a_3493_, v___x_3447_);
v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
lean_dec_ref(v___x_3495_);
v_a_3427_ = v___x_3496_;
goto v___jp_3426_;
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
lean_dec_ref_known(v___x_3492_, 1);
v___x_3497_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__16));
v___x_3498_ = l_Nat_reprFast(v_id_3491_);
v___x_3499_ = lean_string_append(v___x_3497_, v___x_3498_);
lean_dec_ref(v___x_3498_);
v___x_3500_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__17));
v___x_3501_ = lean_string_append(v___x_3499_, v___x_3500_);
v_a_3427_ = v___x_3501_;
goto v___jp_3426_;
}
}
}
}
}
v___jp_3506_:
{
lean_object* v___x_3508_; lean_object* v_env_3509_; lean_object* v_nextMacroScope_3510_; lean_object* v_ngen_3511_; lean_object* v_auxDeclNGen_3512_; lean_object* v_traceState_3513_; lean_object* v_recordedDeps_3514_; lean_object* v_messages_3515_; lean_object* v_infoState_3516_; lean_object* v_snapshotTasks_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3526_; 
v___x_3508_ = lean_st_ref_take(v___x_3451_);
v_env_3509_ = lean_ctor_get(v___x_3508_, 0);
v_nextMacroScope_3510_ = lean_ctor_get(v___x_3508_, 1);
v_ngen_3511_ = lean_ctor_get(v___x_3508_, 2);
v_auxDeclNGen_3512_ = lean_ctor_get(v___x_3508_, 3);
v_traceState_3513_ = lean_ctor_get(v___x_3508_, 4);
v_recordedDeps_3514_ = lean_ctor_get(v___x_3508_, 6);
v_messages_3515_ = lean_ctor_get(v___x_3508_, 7);
v_infoState_3516_ = lean_ctor_get(v___x_3508_, 8);
v_snapshotTasks_3517_ = lean_ctor_get(v___x_3508_, 9);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3526_ == 0)
{
lean_object* v_unused_3527_; 
v_unused_3527_ = lean_ctor_get(v___x_3508_, 5);
lean_dec(v_unused_3527_);
v___x_3519_ = v___x_3508_;
v_isShared_3520_ = v_isSharedCheck_3526_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_snapshotTasks_3517_);
lean_inc(v_infoState_3516_);
lean_inc(v_messages_3515_);
lean_inc(v_recordedDeps_3514_);
lean_inc(v_traceState_3513_);
lean_inc(v_auxDeclNGen_3512_);
lean_inc(v_ngen_3511_);
lean_inc(v_nextMacroScope_3510_);
lean_inc(v_env_3509_);
lean_dec(v___x_3508_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3526_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3521_ = l_Lean_Kernel_enableDiag(v_env_3509_, v___y_3507_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 5, v___x_3443_);
lean_ctor_set(v___x_3519_, 0, v___x_3521_);
v___x_3523_ = v___x_3519_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_nextMacroScope_3510_);
lean_ctor_set(v_reuseFailAlloc_3525_, 2, v_ngen_3511_);
lean_ctor_set(v_reuseFailAlloc_3525_, 3, v_auxDeclNGen_3512_);
lean_ctor_set(v_reuseFailAlloc_3525_, 4, v_traceState_3513_);
lean_ctor_set(v_reuseFailAlloc_3525_, 5, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3525_, 6, v_recordedDeps_3514_);
lean_ctor_set(v_reuseFailAlloc_3525_, 7, v_messages_3515_);
lean_ctor_set(v_reuseFailAlloc_3525_, 8, v_infoState_3516_);
lean_ctor_set(v_reuseFailAlloc_3525_, 9, v_snapshotTasks_3517_);
v___x_3523_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3524_; 
v___x_3524_ = lean_st_ref_put(v___x_3451_, v___x_3523_);
v_fileName_3453_ = v___x_3430_;
v_fileMap_3454_ = v___x_3431_;
v_currNamespace_3455_ = v_currNamespace_3422_;
v_openDecls_3456_ = v_openDecls_3423_;
v_initHeartbeats_3457_ = v___x_3450_;
v_maxHeartbeats_3458_ = v___x_3433_;
v_quotContext_3459_ = v___x_3434_;
v_currMacroScope_3460_ = v___x_3435_;
v_cancelTk_x3f_3461_ = v_cancelTk_x3f_3424_;
v_inheritedTraceOptions_3462_ = v___x_3504_;
v_currRecDepth_3463_ = v___x_3432_;
v_ref_3464_ = v___x_3436_;
v_suppressElabErrors_3465_ = v___x_3438_;
v_isRecordingDeps_3466_ = v___x_3438_;
goto v___jp_3452_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_runMarkdown___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3419_ = stack[0].m_obj;
lean_object* v_act_3420_ = stack[1].m_obj;
lean_object* v_options_3421_ = stack[2].m_obj;
lean_object* v_currNamespace_3422_ = stack[3].m_obj;
lean_object* v_openDecls_3423_ = stack[4].m_obj;
lean_object* v_cancelTk_x3f_3424_ = stack[5].m_obj;
lean_object* v_res_3534_;
v_res_3534_ = l_Lean_Doc_runMarkdown___redArg(v_env_3419_, v_act_3420_, v_options_3421_, v_currNamespace_3422_, v_openDecls_3423_, v_cancelTk_x3f_3424_);
stack->m_obj
 = v_res_3534_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___redArg___boxed(lean_object* v_env_3535_, lean_object* v_act_3536_, lean_object* v_options_3537_, lean_object* v_currNamespace_3538_, lean_object* v_openDecls_3539_, lean_object* v_cancelTk_x3f_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lean_Doc_runMarkdown___redArg(v_env_3535_, v_act_3536_, v_options_3537_, v_currNamespace_3538_, v_openDecls_3539_, v_cancelTk_x3f_3540_);
return v_res_3542_;
}
}
lean_object* l_Lean_Doc_runMarkdown(lean_object* v_00_u03b1_3543_, lean_object* v_env_3544_, lean_object* v_act_3545_, lean_object* v_options_3546_, lean_object* v_currNamespace_3547_, lean_object* v_openDecls_3548_, lean_object* v_cancelTk_x3f_3549_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Lean_Doc_runMarkdown___redArg(v_env_3544_, v_act_3545_, v_options_3546_, v_currNamespace_3547_, v_openDecls_3548_, v_cancelTk_x3f_3549_);
return v___x_3551_;
}
}
LEAN_EXPORT void l_Lean_Doc_runMarkdown_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3544_ = stack[1].m_obj;
lean_object* v_act_3545_ = stack[2].m_obj;
lean_object* v_options_3546_ = stack[3].m_obj;
lean_object* v_currNamespace_3547_ = stack[4].m_obj;
lean_object* v_openDecls_3548_ = stack[5].m_obj;
lean_object* v_cancelTk_x3f_3549_ = stack[6].m_obj;
lean_object* v_res_3552_;
v_res_3552_ = l_Lean_Doc_runMarkdown(lean_box(0), v_env_3544_, v_act_3545_, v_options_3546_, v_currNamespace_3547_, v_openDecls_3548_, v_cancelTk_x3f_3549_);
stack->m_obj
 = v_res_3552_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_runMarkdown___boxed(lean_object* v_00_u03b1_3553_, lean_object* v_env_3554_, lean_object* v_act_3555_, lean_object* v_options_3556_, lean_object* v_currNamespace_3557_, lean_object* v_openDecls_3558_, lean_object* v_cancelTk_x3f_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_Doc_runMarkdown(v_00_u03b1_3553_, v_env_3554_, v_act_3555_, v_options_3556_, v_currNamespace_3557_, v_openDecls_3558_, v_cancelTk_x3f_3559_);
return v_res_3561_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(lean_object* v_x_3562_, size_t v_sz_3563_, size_t v_i_3564_, lean_object* v_bs_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
uint8_t v___x_3570_; 
v___x_3570_ = lean_usize_dec_lt(v_i_3564_, v_sz_3563_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
lean_dec_ref(v_x_3562_);
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v_bs_3565_);
return v___x_3571_;
}
else
{
lean_object* v_v_3572_; lean_object* v___x_3573_; lean_object* v_bs_x27_3574_; lean_object* v___x_3575_; 
v_v_3572_ = lean_array_uget(v_bs_3565_, v_i_3564_);
v___x_3573_ = lean_unsigned_to_nat(0u);
v_bs_x27_3574_ = lean_array_uset(v_bs_3565_, v_i_3564_, v___x_3573_);
lean_inc_ref(v_x_3562_);
v___x_3575_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3562_, v_v_3572_, v___y_3566_, v___y_3567_, v___y_3568_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; size_t v___x_3577_; size_t v___x_3578_; lean_object* v___x_3579_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3576_);
lean_dec_ref_known(v___x_3575_, 1);
v___x_3577_ = ((size_t)1ULL);
v___x_3578_ = lean_usize_add(v_i_3564_, v___x_3577_);
v___x_3579_ = lean_array_uset(v_bs_x27_3574_, v_i_3564_, v_a_3576_);
v_i_3564_ = v___x_3578_;
v_bs_3565_ = v___x_3579_;
goto _start;
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec_ref(v_bs_x27_3574_);
lean_dec_ref(v_x_3562_);
v_a_3581_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3575_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3575_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3562_ = stack[0].m_obj;
size_t v_sz_3563_ = stack[1].m_num;
size_t v_i_3564_ = stack[2].m_num;
lean_object* v_bs_3565_ = stack[3].m_obj;
lean_object* v___y_3566_ = stack[4].m_obj;
lean_object* v___y_3567_ = stack[5].m_obj;
lean_object* v___y_3568_ = stack[6].m_obj;
lean_object* v_res_3589_;
v_res_3589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3562_, v_sz_3563_, v_i_3564_, v_bs_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
stack->m_obj
 = v_res_3589_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed(lean_object* v_x_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(v_x_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
return v_res_3596_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(lean_object* v_x_3599_, size_t v_sz_3600_, size_t v___x_3601_, lean_object* v_content_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3599_, v_sz_3600_, v___x_3601_, v_content_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3616_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3610_ = v___x_3607_;
v_isShared_3611_ = v_isSharedCheck_3616_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3607_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3616_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; lean_object* v___x_3614_; 
v___x_3612_ = l_Lean_Doc_joinInlines(v_a_3608_);
lean_dec(v_a_3608_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3612_);
v___x_3614_ = v___x_3610_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
v_a_3617_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3607_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3607_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3599_ = stack[0].m_obj;
size_t v_sz_3600_ = stack[1].m_num;
size_t v___x_3601_ = stack[2].m_num;
lean_object* v_content_3602_ = stack[3].m_obj;
lean_object* v___y_3603_ = stack[4].m_obj;
lean_object* v___y_3604_ = stack[5].m_obj;
lean_object* v___y_3605_ = stack[6].m_obj;
lean_object* v_res_3625_;
v_res_3625_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(v_x_3599_, v_sz_3600_, v___x_3601_, v_content_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
stack->m_obj
 = v_res_3625_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed(lean_object* v_x_3626_, lean_object* v_sz_3627_, lean_object* v___x_3628_, lean_object* v_content_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
size_t v_sz_boxed_3634_; size_t v___x_3984__boxed_3635_; lean_object* v_res_3636_; 
v_sz_boxed_3634_ = lean_unbox_usize(v_sz_3627_);
lean_dec(v_sz_3627_);
v___x_3984__boxed_3635_ = lean_unbox_usize(v___x_3628_);
lean_dec(v___x_3628_);
v_res_3636_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(v_x_3626_, v_sz_boxed_3634_, v___x_3984__boxed_3635_, v_content_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
return v_res_3636_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(lean_object* v_x_3637_, lean_object* v_x_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v_pieces_3644_; lean_object* v_pieces_3648_; 
switch(lean_obj_tag(v_x_3638_))
{
case 0:
{
lean_object* v_string_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
lean_dec_ref(v_x_3637_);
v_string_3651_ = lean_ctor_get(v_x_3638_, 0);
lean_inc_ref(v_string_3651_);
lean_dec_ref_known(v_x_3638_, 1);
v___x_3652_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_3651_);
lean_dec_ref(v_string_3651_);
v___x_3653_ = lean_unsigned_to_nat(1u);
v___x_3654_ = lean_mk_empty_array_with_capacity(v___x_3653_);
v___x_3655_ = lean_array_push(v___x_3654_, v___x_3652_);
v___x_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
return v___x_3656_;
}
case 1:
{
lean_object* v_content_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3712_; 
v_content_3657_ = lean_ctor_get(v_x_3638_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_x_3638_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3659_ = v_x_3638_;
v_isShared_3660_ = v_isSharedCheck_3712_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_content_3657_);
lean_dec(v_x_3638_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3712_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
lean_ctor_set_tag(v___x_3659_, 9);
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_content_3657_);
v___x_3662_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3663_; lean_object* v_snd_3664_; lean_object* v_fst_3665_; lean_object* v_fst_3666_; lean_object* v_snd_3667_; lean_object* v_pieces_3669_; uint8_t v_inEmph_3677_; uint8_t v_inBold_3678_; uint8_t v_inLink_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3710_; 
v___x_3663_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3662_);
v_snd_3664_ = lean_ctor_get(v___x_3663_, 1);
lean_inc(v_snd_3664_);
v_fst_3665_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_fst_3665_);
lean_dec_ref(v___x_3663_);
v_fst_3666_ = lean_ctor_get(v_snd_3664_, 0);
lean_inc(v_fst_3666_);
v_snd_3667_ = lean_ctor_get(v_snd_3664_, 1);
lean_inc(v_snd_3667_);
lean_dec(v_snd_3664_);
v_inEmph_3677_ = lean_ctor_get_uint8(v_x_3637_, 0);
v_inBold_3678_ = lean_ctor_get_uint8(v_x_3637_, 1);
v_inLink_3679_ = lean_ctor_get_uint8(v_x_3637_, 2);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_x_3637_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3681_ = v_x_3637_;
v_isShared_3682_ = v_isSharedCheck_3710_;
goto v_resetjp_3680_;
}
else
{
lean_dec(v_x_3637_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3710_;
goto v_resetjp_3680_;
}
v___jp_3668_:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; uint8_t v___x_3672_; 
v___x_3670_ = lean_string_utf8_byte_size(v_snd_3667_);
v___x_3671_ = lean_unsigned_to_nat(0u);
v___x_3672_ = lean_nat_dec_eq(v___x_3670_, v___x_3671_);
if (v___x_3672_ == 0)
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3673_ = lean_unsigned_to_nat(1u);
v___x_3674_ = lean_mk_empty_array_with_capacity(v___x_3673_);
v___x_3675_ = lean_array_push(v___x_3674_, v_snd_3667_);
v___x_3676_ = lean_array_push(v_pieces_3669_, v___x_3675_);
v_pieces_3648_ = v___x_3676_;
goto v___jp_3647_;
}
else
{
lean_dec(v_snd_3667_);
v_pieces_3648_ = v_pieces_3669_;
goto v___jp_3647_;
}
}
v_resetjp_3680_:
{
uint8_t v___x_3683_; lean_object* v___x_3685_; 
v___x_3683_ = 1;
if (v_isShared_3682_ == 0)
{
v___x_3685_ = v___x_3681_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3709_, 1, v_inBold_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3709_, 2, v_inLink_3679_);
v___x_3685_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
lean_object* v___x_3686_; 
lean_ctor_set_uint8(v___x_3685_, 0, v___x_3683_);
v___x_3686_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3685_, v_fst_3666_, v_a_3639_, v_a_3640_, v_a_3641_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v_pieces_3689_; lean_object* v_pieces_3696_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v___x_3701_ = lean_unsigned_to_nat(0u);
v___x_3702_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3703_ = lean_string_utf8_byte_size(v_fst_3665_);
v___x_3704_ = lean_nat_dec_eq(v___x_3703_, v___x_3701_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3705_ = lean_unsigned_to_nat(1u);
v___x_3706_ = lean_mk_empty_array_with_capacity(v___x_3705_);
v___x_3707_ = lean_array_push(v___x_3706_, v_fst_3665_);
v___x_3708_ = lean_array_push(v___x_3702_, v___x_3707_);
v_pieces_3696_ = v___x_3708_;
goto v___jp_3695_;
}
else
{
lean_dec(v_fst_3665_);
v_pieces_3696_ = v___x_3702_;
goto v___jp_3695_;
}
v___jp_3688_:
{
lean_object* v___x_3690_; 
v___x_3690_ = lean_array_push(v_pieces_3689_, v_a_3687_);
if (v_inEmph_3677_ == 0)
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3691_ = lean_unsigned_to_nat(1u);
v___x_3692_ = lean_mk_empty_array_with_capacity(v___x_3691_);
lean_dec_ref(v___x_3692_);
v___x_3693_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3694_ = lean_array_push(v___x_3690_, v___x_3693_);
v_pieces_3669_ = v___x_3694_;
goto v___jp_3668_;
}
else
{
v_pieces_3669_ = v___x_3690_;
goto v___jp_3668_;
}
}
v___jp_3695_:
{
if (v_inEmph_3677_ == 0)
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3697_ = lean_unsigned_to_nat(1u);
v___x_3698_ = lean_mk_empty_array_with_capacity(v___x_3697_);
lean_dec_ref(v___x_3698_);
v___x_3699_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_3700_ = lean_array_push(v_pieces_3696_, v___x_3699_);
v_pieces_3689_ = v___x_3700_;
goto v___jp_3688_;
}
else
{
v_pieces_3689_ = v_pieces_3696_;
goto v___jp_3688_;
}
}
}
else
{
lean_dec(v_snd_3667_);
lean_dec(v_fst_3665_);
return v___x_3686_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3768_; 
v_content_3713_ = lean_ctor_get(v_x_3638_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v_x_3638_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3715_ = v_x_3638_;
v_isShared_3716_ = v_isSharedCheck_3768_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_content_3713_);
lean_dec(v_x_3638_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3768_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
lean_ctor_set_tag(v___x_3715_, 9);
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_content_3713_);
v___x_3718_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
lean_object* v___x_3719_; lean_object* v_snd_3720_; lean_object* v_fst_3721_; lean_object* v_fst_3722_; lean_object* v_snd_3723_; lean_object* v_pieces_3725_; uint8_t v_inEmph_3733_; uint8_t v_inBold_3734_; uint8_t v_inLink_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3766_; 
v___x_3719_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3718_);
v_snd_3720_ = lean_ctor_get(v___x_3719_, 1);
lean_inc(v_snd_3720_);
v_fst_3721_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_fst_3721_);
lean_dec_ref(v___x_3719_);
v_fst_3722_ = lean_ctor_get(v_snd_3720_, 0);
lean_inc(v_fst_3722_);
v_snd_3723_ = lean_ctor_get(v_snd_3720_, 1);
lean_inc(v_snd_3723_);
lean_dec(v_snd_3720_);
v_inEmph_3733_ = lean_ctor_get_uint8(v_x_3637_, 0);
v_inBold_3734_ = lean_ctor_get_uint8(v_x_3637_, 1);
v_inLink_3735_ = lean_ctor_get_uint8(v_x_3637_, 2);
v_isSharedCheck_3766_ = !lean_is_exclusive(v_x_3637_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3737_ = v_x_3637_;
v_isShared_3738_ = v_isSharedCheck_3766_;
goto v_resetjp_3736_;
}
else
{
lean_dec(v_x_3637_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3766_;
goto v_resetjp_3736_;
}
v___jp_3724_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; 
v___x_3726_ = lean_string_utf8_byte_size(v_snd_3723_);
v___x_3727_ = lean_unsigned_to_nat(0u);
v___x_3728_ = lean_nat_dec_eq(v___x_3726_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3729_ = lean_unsigned_to_nat(1u);
v___x_3730_ = lean_mk_empty_array_with_capacity(v___x_3729_);
v___x_3731_ = lean_array_push(v___x_3730_, v_snd_3723_);
v___x_3732_ = lean_array_push(v_pieces_3725_, v___x_3731_);
v_pieces_3644_ = v___x_3732_;
goto v___jp_3643_;
}
else
{
lean_dec(v_snd_3723_);
v_pieces_3644_ = v_pieces_3725_;
goto v___jp_3643_;
}
}
v_resetjp_3736_:
{
uint8_t v___x_3739_; lean_object* v___x_3741_; 
v___x_3739_ = 1;
if (v_isShared_3738_ == 0)
{
v___x_3741_ = v___x_3737_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3765_, 0, v_inEmph_3733_);
lean_ctor_set_uint8(v_reuseFailAlloc_3765_, 2, v_inLink_3735_);
v___x_3741_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
lean_object* v___x_3742_; 
lean_ctor_set_uint8(v___x_3741_, 1, v___x_3739_);
v___x_3742_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3741_, v_fst_3722_, v_a_3639_, v_a_3640_, v_a_3641_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v_pieces_3745_; lean_object* v_pieces_3752_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; uint8_t v___x_3760_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v___x_3757_ = lean_unsigned_to_nat(0u);
v___x_3758_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_3759_ = lean_string_utf8_byte_size(v_fst_3721_);
v___x_3760_ = lean_nat_dec_eq(v___x_3759_, v___x_3757_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3761_ = lean_unsigned_to_nat(1u);
v___x_3762_ = lean_mk_empty_array_with_capacity(v___x_3761_);
v___x_3763_ = lean_array_push(v___x_3762_, v_fst_3721_);
v___x_3764_ = lean_array_push(v___x_3758_, v___x_3763_);
v_pieces_3752_ = v___x_3764_;
goto v___jp_3751_;
}
else
{
lean_dec(v_fst_3721_);
v_pieces_3752_ = v___x_3758_;
goto v___jp_3751_;
}
v___jp_3744_:
{
lean_object* v___x_3746_; 
v___x_3746_ = lean_array_push(v_pieces_3745_, v_a_3743_);
if (v_inBold_3734_ == 0)
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3747_ = lean_unsigned_to_nat(1u);
v___x_3748_ = lean_mk_empty_array_with_capacity(v___x_3747_);
lean_dec_ref(v___x_3748_);
v___x_3749_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3750_ = lean_array_push(v___x_3746_, v___x_3749_);
v_pieces_3725_ = v___x_3750_;
goto v___jp_3724_;
}
else
{
v_pieces_3725_ = v___x_3746_;
goto v___jp_3724_;
}
}
v___jp_3751_:
{
if (v_inBold_3734_ == 0)
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3753_ = lean_unsigned_to_nat(1u);
v___x_3754_ = lean_mk_empty_array_with_capacity(v___x_3753_);
lean_dec_ref(v___x_3754_);
v___x_3755_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_3756_ = lean_array_push(v_pieces_3752_, v___x_3755_);
v_pieces_3745_ = v___x_3756_;
goto v___jp_3744_;
}
else
{
v_pieces_3745_ = v_pieces_3752_;
goto v___jp_3744_;
}
}
}
else
{
lean_dec(v_snd_3723_);
lean_dec(v_fst_3721_);
return v___x_3742_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
lean_dec_ref(v_x_3637_);
v_string_3769_ = lean_ctor_get(v_x_3638_, 0);
lean_inc_ref(v_string_3769_);
lean_dec_ref_known(v_x_3638_, 1);
v___x_3770_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_3769_);
v___x_3771_ = lean_unsigned_to_nat(1u);
v___x_3772_ = lean_mk_empty_array_with_capacity(v___x_3771_);
v___x_3773_ = lean_array_push(v___x_3772_, v___x_3770_);
v___x_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
return v___x_3774_;
}
case 4:
{
uint8_t v_mode_3775_; 
lean_dec_ref(v_x_3637_);
v_mode_3775_ = lean_ctor_get_uint8(v_x_3638_, sizeof(void*)*1);
if (v_mode_3775_ == 0)
{
lean_object* v_string_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v_string_3776_ = lean_ctor_get(v_x_3638_, 0);
lean_inc_ref(v_string_3776_);
lean_dec_ref_known(v_x_3638_, 1);
v___x_3777_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_3778_ = lean_string_append(v___x_3777_, v_string_3776_);
lean_dec_ref(v_string_3776_);
v___x_3779_ = lean_string_append(v___x_3778_, v___x_3777_);
v___x_3780_ = lean_unsigned_to_nat(1u);
v___x_3781_ = lean_mk_empty_array_with_capacity(v___x_3780_);
v___x_3782_ = lean_array_push(v___x_3781_, v___x_3779_);
v___x_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
return v___x_3783_;
}
else
{
lean_object* v_string_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v_string_3784_ = lean_ctor_get(v_x_3638_, 0);
lean_inc_ref(v_string_3784_);
lean_dec_ref_known(v_x_3638_, 1);
v___x_3785_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_3786_ = lean_string_append(v___x_3785_, v_string_3784_);
lean_dec_ref(v_string_3784_);
v___x_3787_ = lean_string_append(v___x_3786_, v___x_3785_);
v___x_3788_ = lean_unsigned_to_nat(1u);
v___x_3789_ = lean_mk_empty_array_with_capacity(v___x_3788_);
v___x_3790_ = lean_array_push(v___x_3789_, v___x_3787_);
v___x_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3790_);
return v___x_3791_;
}
}
case 5:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
lean_dec_ref_known(v_x_3638_, 1);
lean_dec_ref(v_x_3637_);
v___x_3792_ = lean_unsigned_to_nat(2u);
v___x_3793_ = lean_mk_empty_array_with_capacity(v___x_3792_);
lean_dec_ref(v___x_3793_);
v___x_3794_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3794_);
return v___x_3795_;
}
case 6:
{
uint8_t v_inLink_3796_; 
v_inLink_3796_ = lean_ctor_get_uint8(v_x_3637_, 2);
if (v_inLink_3796_ == 0)
{
lean_object* v_content_3797_; lean_object* v_url_3798_; uint8_t v_inEmph_3799_; uint8_t v_inBold_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3831_; 
v_content_3797_ = lean_ctor_get(v_x_3638_, 0);
lean_inc_ref(v_content_3797_);
v_url_3798_ = lean_ctor_get(v_x_3638_, 1);
lean_inc_ref(v_url_3798_);
lean_dec_ref_known(v_x_3638_, 2);
v_inEmph_3799_ = lean_ctor_get_uint8(v_x_3637_, 0);
v_inBold_3800_ = lean_ctor_get_uint8(v_x_3637_, 1);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_x_3637_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3802_ = v_x_3637_;
v_isShared_3803_ = v_isSharedCheck_3831_;
goto v_resetjp_3801_;
}
else
{
lean_dec(v_x_3637_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3831_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
uint8_t v___x_3804_; lean_object* v___x_3806_; 
v___x_3804_ = 1;
if (v_isShared_3803_ == 0)
{
v___x_3806_ = v___x_3802_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_3830_, 0, v_inEmph_3799_);
lean_ctor_set_uint8(v_reuseFailAlloc_3830_, 1, v_inBold_3800_);
v___x_3806_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
lean_ctor_set_uint8(v___x_3806_, 2, v___x_3804_);
v___x_3807_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3807_, 0, v_content_3797_);
v___x_3808_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3806_, v___x_3807_, v_a_3639_, v_a_3640_, v_a_3641_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3829_; 
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3811_ = v___x_3808_;
v_isShared_3812_ = v_isSharedCheck_3829_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3808_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3829_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3827_; 
v___x_3813_ = lean_unsigned_to_nat(1u);
v___x_3814_ = lean_mk_empty_array_with_capacity(v___x_3813_);
v___x_3815_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3816_ = lean_string_append(v___x_3815_, v_url_3798_);
lean_dec_ref(v_url_3798_);
v___x_3817_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3818_ = lean_string_append(v___x_3816_, v___x_3817_);
v___x_3819_ = lean_array_push(v___x_3814_, v___x_3818_);
v___x_3820_ = lean_unsigned_to_nat(3u);
v___x_3821_ = lean_mk_empty_array_with_capacity(v___x_3820_);
lean_dec_ref(v___x_3821_);
v___x_3822_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_3823_ = lean_array_push(v___x_3822_, v_a_3809_);
v___x_3824_ = lean_array_push(v___x_3823_, v___x_3819_);
v___x_3825_ = l_Lean_Doc_joinInlines(v___x_3824_);
lean_dec_ref(v___x_3824_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 0, v___x_3825_);
v___x_3827_ = v___x_3811_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3825_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
else
{
lean_dec_ref(v_url_3798_);
return v___x_3808_;
}
}
}
}
else
{
lean_object* v_content_3832_; size_t v_sz_3833_; size_t v___x_3834_; lean_object* v___x_3835_; 
v_content_3832_ = lean_ctor_get(v_x_3638_, 0);
lean_inc_ref(v_content_3832_);
lean_dec_ref_known(v_x_3638_, 2);
v_sz_3833_ = lean_array_size(v_content_3832_);
v___x_3834_ = ((size_t)0ULL);
v___x_3835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3637_, v_sz_3833_, v___x_3834_, v_content_3832_, v_a_3639_, v_a_3640_, v_a_3641_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3844_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3838_ = v___x_3835_;
v_isShared_3839_ = v_isSharedCheck_3844_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3835_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3844_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; lean_object* v___x_3842_; 
v___x_3840_ = l_Lean_Doc_joinInlines(v_a_3836_);
lean_dec(v_a_3836_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v___x_3840_);
v___x_3842_ = v___x_3838_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3840_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
v_a_3845_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3835_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3835_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
case 7:
{
lean_object* v_name_3853_; lean_object* v_content_3854_; size_t v_sz_3855_; size_t v___x_3856_; lean_object* v___x_3857_; 
v_name_3853_ = lean_ctor_get(v_x_3638_, 0);
lean_inc_ref(v_name_3853_);
v_content_3854_ = lean_ctor_get(v_x_3638_, 1);
lean_inc_ref(v_content_3854_);
lean_dec_ref_known(v_x_3638_, 2);
v_sz_3855_ = lean_array_size(v_content_3854_);
v___x_3856_ = ((size_t)0ULL);
v___x_3857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3637_, v_sz_3855_, v___x_3856_, v_content_3854_, v_a_3639_, v_a_3640_, v_a_3641_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___x_3857_, 1);
v___x_3859_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_3860_ = l_Lean_Doc_joinInlines(v_a_3858_);
lean_dec(v_a_3858_);
v___x_3861_ = lean_array_to_list(v___x_3860_);
v___x_3862_ = l_String_intercalate(v___x_3859_, v___x_3861_);
lean_inc_ref(v_name_3853_);
v___x_3863_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_3853_, v___x_3862_, v_a_3639_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3877_; 
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3877_ == 0)
{
lean_object* v_unused_3878_; 
v_unused_3878_ = lean_ctor_get(v___x_3863_, 0);
lean_dec(v_unused_3878_);
v___x_3865_ = v___x_3863_;
v_isShared_3866_ = v_isSharedCheck_3877_;
goto v_resetjp_3864_;
}
else
{
lean_dec(v___x_3863_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3877_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3875_; 
v___x_3867_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_3868_ = lean_string_append(v___x_3867_, v_name_3853_);
lean_dec_ref(v_name_3853_);
v___x_3869_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_3870_ = lean_string_append(v___x_3868_, v___x_3869_);
v___x_3871_ = lean_unsigned_to_nat(1u);
v___x_3872_ = lean_mk_empty_array_with_capacity(v___x_3871_);
v___x_3873_ = lean_array_push(v___x_3872_, v___x_3870_);
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 0, v___x_3873_);
v___x_3875_ = v___x_3865_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3873_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec_ref(v_name_3853_);
v_a_3879_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3863_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3863_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec_ref(v_name_3853_);
v_a_3887_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3857_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3857_);
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
case 8:
{
lean_object* v_alt_3895_; lean_object* v_url_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
lean_dec_ref(v_x_3637_);
v_alt_3895_ = lean_ctor_get(v_x_3638_, 0);
lean_inc_ref(v_alt_3895_);
v_url_3896_ = lean_ctor_get(v_x_3638_, 1);
lean_inc_ref(v_url_3896_);
lean_dec_ref_known(v_x_3638_, 2);
v___x_3897_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_3898_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_3895_);
lean_dec_ref(v_alt_3895_);
v___x_3899_ = lean_string_append(v___x_3897_, v___x_3898_);
lean_dec_ref(v___x_3898_);
v___x_3900_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_3901_ = lean_string_append(v___x_3899_, v___x_3900_);
v___x_3902_ = lean_string_append(v___x_3901_, v_url_3896_);
lean_dec_ref(v_url_3896_);
v___x_3903_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_3904_ = lean_string_append(v___x_3902_, v___x_3903_);
v___x_3905_ = lean_unsigned_to_nat(1u);
v___x_3906_ = lean_mk_empty_array_with_capacity(v___x_3905_);
v___x_3907_ = lean_array_push(v___x_3906_, v___x_3904_);
v___x_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
return v___x_3908_;
}
case 9:
{
lean_object* v_content_3909_; size_t v_sz_3910_; size_t v___x_3911_; lean_object* v___x_3912_; 
v_content_3909_ = lean_ctor_get(v_x_3638_, 0);
lean_inc_ref(v_content_3909_);
lean_dec_ref_known(v_x_3638_, 1);
v_sz_3910_ = lean_array_size(v_content_3909_);
v___x_3911_ = ((size_t)0ULL);
v___x_3912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3637_, v_sz_3910_, v___x_3911_, v_content_3909_, v_a_3639_, v_a_3640_, v_a_3641_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3921_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3915_ = v___x_3912_;
v_isShared_3916_ = v_isSharedCheck_3921_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3912_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3921_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3917_; lean_object* v___x_3919_; 
v___x_3917_ = l_Lean_Doc_joinInlines(v_a_3913_);
lean_dec(v_a_3913_);
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 0, v___x_3917_);
v___x_3919_ = v___x_3915_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
v_a_3922_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3912_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3912_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
default: 
{
lean_object* v_container_3930_; 
v_container_3930_ = lean_ctor_get(v_x_3638_, 0);
if (lean_obj_tag(v_container_3930_) == 0)
{
lean_object* v_content_3931_; lean_object* v_val_3932_; lean_object* v___f_3933_; size_t v_sz_3934_; size_t v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v_fallback_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
lean_inc_ref(v_container_3930_);
v_content_3931_ = lean_ctor_get(v_x_3638_, 1);
lean_inc_ref_n(v_content_3931_, 2);
lean_dec_ref_known(v_x_3638_, 2);
v_val_3932_ = lean_ctor_get(v_container_3930_, 0);
lean_inc(v_val_3932_);
lean_dec_ref_known(v_container_3930_, 1);
lean_inc_ref_n(v_x_3637_, 2);
v___f_3933_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3933_, 0, v_x_3637_);
v_sz_3934_ = lean_array_size(v_content_3931_);
v___x_3935_ = ((size_t)0ULL);
v___x_3936_ = lean_box_usize(v_sz_3934_);
v___x_3937_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
v_fallback_3938_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v_fallback_3938_, 0, v_x_3637_);
lean_closure_set(v_fallback_3938_, 1, v___x_3936_);
lean_closure_set(v_fallback_3938_, 2, v___x_3937_);
lean_closure_set(v_fallback_3938_, 3, v_content_3931_);
v___x_3939_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3932_);
v___x_3940_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_3939_, v_a_3640_, v_a_3641_);
lean_dec(v___x_3939_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3941_);
lean_dec_ref_known(v___x_3940_, 1);
if (lean_obj_tag(v_a_3941_) == 0)
{
lean_object* v___x_3942_; 
lean_dec_ref(v_fallback_3938_);
lean_dec_ref(v___f_3933_);
lean_dec(v_val_3932_);
v___x_3942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3637_, v_sz_3934_, v___x_3935_, v_content_3931_, v_a_3639_, v_a_3640_, v_a_3641_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3951_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_3951_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3951_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3947_; lean_object* v___x_3949_; 
v___x_3947_ = l_Lean_Doc_joinInlines(v_a_3943_);
lean_dec(v_a_3943_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v___x_3947_);
v___x_3949_ = v___x_3945_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3947_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
else
{
lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3959_; 
v_a_3952_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3954_ = v___x_3942_;
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___x_3942_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3957_; 
if (v_isShared_3955_ == 0)
{
v___x_3957_ = v___x_3954_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_a_3952_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
}
}
else
{
lean_object* v_val_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
lean_dec_ref(v_x_3637_);
v_val_3960_ = lean_ctor_get(v_a_3941_, 0);
lean_inc(v_val_3960_);
lean_dec_ref_known(v_a_3941_, 1);
v___x_3961_ = lean_apply_3(v_val_3960_, v___f_3933_, v_val_3932_, v_content_3931_);
v___x_3962_ = l_Lean_Doc_withRendererFallback(v_fallback_3938_, v___x_3961_, v_a_3639_, v_a_3640_, v_a_3641_);
return v___x_3962_;
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec_ref(v_fallback_3938_);
lean_dec_ref(v___f_3933_);
lean_dec(v_val_3932_);
lean_dec_ref(v_content_3931_);
lean_dec_ref(v_x_3637_);
v_a_3963_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3940_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3940_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
else
{
lean_object* v_content_3971_; size_t v_sz_3972_; size_t v___x_3973_; lean_object* v___x_3974_; 
v_content_3971_ = lean_ctor_get(v_x_3638_, 1);
lean_inc_ref(v_content_3971_);
lean_dec_ref_known(v_x_3638_, 2);
v_sz_3972_ = lean_array_size(v_content_3971_);
v___x_3973_ = ((size_t)0ULL);
v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3637_, v_sz_3972_, v___x_3973_, v_content_3971_, v_a_3639_, v_a_3640_, v_a_3641_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3983_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3977_ = v___x_3974_;
v_isShared_3978_ = v_isSharedCheck_3983_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3974_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3983_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v___x_3981_; 
v___x_3979_ = l_Lean_Doc_joinInlines(v_a_3975_);
lean_dec(v_a_3975_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v___x_3979_);
v___x_3981_ = v___x_3977_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3979_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
v_a_3984_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3974_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3974_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
}
v___jp_3643_:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = l_Lean_Doc_joinInlines(v_pieces_3644_);
lean_dec_ref(v_pieces_3644_);
v___x_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
return v___x_3646_;
}
v___jp_3647_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = l_Lean_Doc_joinInlines(v_pieces_3648_);
lean_dec_ref(v_pieces_3648_);
v___x_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
return v___x_3650_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3637_ = stack[0].m_obj;
lean_object* v_x_3638_ = stack[1].m_obj;
lean_object* v_a_3639_ = stack[2].m_obj;
lean_object* v_a_3640_ = stack[3].m_obj;
lean_object* v_a_3641_ = stack[4].m_obj;
lean_object* v_res_3992_;
v_res_3992_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3637_, v_x_3638_, v_a_3639_, v_a_3640_, v_a_3641_);
stack->m_obj
 = v_res_3992_;
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(lean_object* v_x_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
return v___x_3999_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3993_ = stack[0].m_obj;
lean_object* v___y_3994_ = stack[1].m_obj;
lean_object* v___y_3995_ = stack[2].m_obj;
lean_object* v___y_3996_ = stack[3].m_obj;
lean_object* v___y_3997_ = stack[4].m_obj;
lean_object* v_res_4000_;
v_res_4000_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(v_x_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
stack->m_obj
 = v_res_4000_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_x_4001_, lean_object* v_sz_4002_, lean_object* v_i_4003_, lean_object* v_bs_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
size_t v_sz_boxed_4009_; size_t v_i_boxed_4010_; lean_object* v_res_4011_; 
v_sz_boxed_4009_ = lean_unbox_usize(v_sz_4002_);
lean_dec(v_sz_4002_);
v_i_boxed_4010_ = lean_unbox_usize(v_i_4003_);
lean_dec(v_i_4003_);
v_res_4011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_4001_, v_sz_boxed_4009_, v_i_boxed_4010_, v_bs_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed(lean_object* v_x_4012_, lean_object* v_x_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_4012_, v_x_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
return v_res_4018_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(lean_object* v___x_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
return v___x_4025_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4019_ = stack[0].m_obj;
lean_object* v___y_4020_ = stack[1].m_obj;
lean_object* v___y_4021_ = stack[2].m_obj;
lean_object* v___y_4022_ = stack[3].m_obj;
lean_object* v___y_4023_ = stack[4].m_obj;
lean_object* v_res_4026_;
v_res_4026_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(v___x_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
stack->m_obj
 = v_res_4026_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0___boxed(lean_object* v___x_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(v___x_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(lean_object* v_x_4034_, lean_object* v_x_4035_){
_start:
{
lean_object* v_zero_4036_; uint8_t v_isZero_4037_; 
v_zero_4036_ = lean_unsigned_to_nat(0u);
v_isZero_4037_ = lean_nat_dec_eq(v_x_4034_, v_zero_4036_);
if (v_isZero_4037_ == 1)
{
lean_dec(v_x_4034_);
return v_x_4035_;
}
else
{
uint32_t v___x_4038_; lean_object* v_one_4039_; lean_object* v_n_4040_; lean_object* v___x_4041_; 
v___x_4038_ = 32;
v_one_4039_ = lean_unsigned_to_nat(1u);
v_n_4040_ = lean_nat_sub(v_x_4034_, v_one_4039_);
lean_dec(v_x_4034_);
v___x_4041_ = lean_string_push(v_x_4035_, v___x_4038_);
v_x_4034_ = v_n_4040_;
v_x_4035_ = v___x_4041_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(size_t v_sz_4043_, size_t v_i_4044_, lean_object* v_bs_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
uint8_t v___x_4050_; 
v___x_4050_ = lean_usize_dec_lt(v_i_4044_, v_sz_4043_);
if (v___x_4050_ == 0)
{
lean_object* v___x_4051_; 
v___x_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4051_, 0, v_bs_4045_);
return v___x_4051_;
}
else
{
lean_object* v_v_4052_; lean_object* v___x_4053_; lean_object* v_bs_x27_4054_; size_t v_sz_4055_; size_t v___x_4056_; lean_object* v___x_4057_; 
v_v_4052_ = lean_array_uget(v_bs_4045_, v_i_4044_);
v___x_4053_ = lean_unsigned_to_nat(0u);
v_bs_x27_4054_ = lean_array_uset(v_bs_4045_, v_i_4044_, v___x_4053_);
v_sz_4055_ = lean_array_size(v_v_4052_);
v___x_4056_ = ((size_t)0ULL);
v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4055_, v___x_4056_, v_v_4052_, v___y_4046_, v___y_4047_, v___y_4048_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_a_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; size_t v___x_4063_; size_t v___x_4064_; lean_object* v___x_4065_; 
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_a_4058_);
lean_dec_ref_known(v___x_4057_, 1);
v___x_4059_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_4060_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_4061_ = l_Lean_Doc_joinBlocks(v_a_4058_);
lean_dec(v_a_4058_);
v___x_4062_ = l_Lean_Doc_prefixListLines(v___x_4059_, v___x_4060_, v___x_4061_);
v___x_4063_ = ((size_t)1ULL);
v___x_4064_ = lean_usize_add(v_i_4044_, v___x_4063_);
v___x_4065_ = lean_array_uset(v_bs_x27_4054_, v_i_4044_, v___x_4062_);
v_i_4044_ = v___x_4064_;
v_bs_4045_ = v___x_4065_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_4054_);
return v___x_4057_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4043_ = stack[0].m_num;
size_t v_i_4044_ = stack[1].m_num;
lean_object* v_bs_4045_ = stack[2].m_obj;
lean_object* v___y_4046_ = stack[3].m_obj;
lean_object* v___y_4047_ = stack[4].m_obj;
lean_object* v___y_4048_ = stack[5].m_obj;
lean_object* v_res_4067_;
v_res_4067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_4043_, v_i_4044_, v_bs_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
stack->m_obj
 = v_res_4067_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(lean_object* v_as_4068_, size_t v_sz_4069_, size_t v_i_4070_, lean_object* v_b_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
uint8_t v___x_4076_; 
v___x_4076_ = lean_usize_dec_lt(v_i_4070_, v_sz_4069_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; 
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v_b_4071_);
return v___x_4077_;
}
else
{
lean_object* v_fst_4078_; lean_object* v_snd_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4113_; 
v_fst_4078_ = lean_ctor_get(v_b_4071_, 0);
v_snd_4079_ = lean_ctor_get(v_b_4071_, 1);
v_isSharedCheck_4113_ = !lean_is_exclusive(v_b_4071_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4081_ = v_b_4071_;
v_isShared_4082_ = v_isSharedCheck_4113_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_snd_4079_);
lean_inc(v_fst_4078_);
lean_dec(v_b_4071_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4113_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; lean_object* v_a_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; size_t v_sz_4091_; size_t v___x_4092_; lean_object* v___x_4093_; 
v___x_4083_ = lean_unsigned_to_nat(1u);
v_a_4084_ = lean_array_uget_borrowed(v_as_4068_, v_i_4070_);
lean_inc(v_snd_4079_);
v___x_4085_ = l_Nat_reprFast(v_snd_4079_);
v___x_4086_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_4087_ = lean_string_append(v___x_4085_, v___x_4086_);
v___x_4088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4089_ = lean_string_utf8_byte_size(v___x_4087_);
v___x_4090_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(v___x_4089_, v___x_4088_);
v_sz_4091_ = lean_array_size(v_a_4084_);
v___x_4092_ = ((size_t)0ULL);
lean_inc(v_a_4084_);
v___x_4093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4091_, v___x_4092_, v_a_4084_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4100_; 
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_a_4094_);
lean_dec_ref_known(v___x_4093_, 1);
v___x_4095_ = l_Lean_Doc_joinBlocks(v_a_4094_);
lean_dec(v_a_4094_);
v___x_4096_ = l_Lean_Doc_prefixListLines(v___x_4087_, v___x_4090_, v___x_4095_);
v___x_4097_ = lean_array_push(v_fst_4078_, v___x_4096_);
v___x_4098_ = lean_nat_add(v_snd_4079_, v___x_4083_);
lean_dec(v_snd_4079_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 1, v___x_4098_);
lean_ctor_set(v___x_4081_, 0, v___x_4097_);
v___x_4100_ = v___x_4081_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v___x_4097_);
lean_ctor_set(v_reuseFailAlloc_4104_, 1, v___x_4098_);
v___x_4100_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
size_t v___x_4101_; size_t v___x_4102_; 
v___x_4101_ = ((size_t)1ULL);
v___x_4102_ = lean_usize_add(v_i_4070_, v___x_4101_);
v_i_4070_ = v___x_4102_;
v_b_4071_ = v___x_4100_;
goto _start;
}
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_dec_ref(v___x_4090_);
lean_dec_ref(v___x_4087_);
lean_del_object(v___x_4081_);
lean_dec(v_snd_4079_);
lean_dec(v_fst_4078_);
v_a_4105_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4093_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4093_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4068_ = stack[0].m_obj;
size_t v_sz_4069_ = stack[1].m_num;
size_t v_i_4070_ = stack[2].m_num;
lean_object* v_b_4071_ = stack[3].m_obj;
lean_object* v___y_4072_ = stack[4].m_obj;
lean_object* v___y_4073_ = stack[5].m_obj;
lean_object* v___y_4074_ = stack[6].m_obj;
lean_object* v_res_4114_;
v_res_4114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_as_4068_, v_sz_4069_, v_i_4070_, v_b_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
stack->m_obj
 = v_res_4114_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(size_t v_sz_4115_, size_t v_i_4116_, lean_object* v_bs_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
uint8_t v___x_4122_; 
v___x_4122_ = lean_usize_dec_lt(v_i_4116_, v_sz_4115_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; 
v___x_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4123_, 0, v_bs_4117_);
return v___x_4123_;
}
else
{
lean_object* v_v_4124_; lean_object* v___x_4125_; lean_object* v_term_4126_; lean_object* v_desc_4127_; lean_object* v___x_4128_; lean_object* v_bs_x27_4129_; lean_object* v_a_4131_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
v_v_4124_ = lean_array_uget_borrowed(v_bs_4117_, v_i_4116_);
v___x_4125_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_4126_ = lean_ctor_get(v_v_4124_, 0);
lean_inc_ref(v_term_4126_);
v_desc_4127_ = lean_ctor_get(v_v_4124_, 1);
lean_inc_ref(v_desc_4127_);
v___x_4128_ = lean_unsigned_to_nat(0u);
v_bs_x27_4129_ = lean_array_uset(v_bs_4117_, v_i_4116_, v___x_4128_);
v___x_4136_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4136_, 0, v_term_4126_);
v___x_4137_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4125_, v___x_4136_, v___y_4118_, v___y_4119_, v___y_4120_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; size_t v_sz_4139_; size_t v___x_4140_; lean_object* v___x_4141_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_a_4138_);
lean_dec_ref_known(v___x_4137_, 1);
v_sz_4139_ = lean_array_size(v_desc_4127_);
v___x_4140_ = ((size_t)0ULL);
lean_inc_ref(v_desc_4127_);
v___x_4141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4139_, v___x_4140_, v_desc_4127_, v___y_4118_, v___y_4119_, v___y_4120_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___y_4144_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4141_, 1);
v___x_4148_ = lean_unsigned_to_nat(1u);
v___x_4149_ = lean_mk_empty_array_with_capacity(v___x_4148_);
v___x_4150_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_4151_ = lean_unsigned_to_nat(2u);
v___x_4152_ = lean_mk_empty_array_with_capacity(v___x_4151_);
v___x_4153_ = lean_array_push(v___x_4152_, v_a_4138_);
v___x_4154_ = lean_array_push(v___x_4153_, v___x_4150_);
v___x_4155_ = l_Lean_Doc_joinInlines(v___x_4154_);
lean_dec_ref(v___x_4154_);
v___x_4156_ = lean_array_get_size(v_desc_4127_);
lean_dec_ref(v_desc_4127_);
v___x_4157_ = lean_nat_dec_le(v___x_4156_, v___x_4148_);
if (v___x_4157_ == 0)
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4158_ = lean_array_push(v___x_4149_, v___x_4155_);
v___x_4159_ = l_Array_append___redArg(v___x_4158_, v_a_4142_);
lean_dec(v_a_4142_);
v___x_4160_ = l_Lean_Doc_joinBlocks(v___x_4159_);
lean_dec_ref(v___x_4159_);
v___y_4144_ = v___x_4160_;
goto v___jp_4143_;
}
else
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
lean_dec_ref(v___x_4149_);
v___x_4161_ = l_Lean_Doc_joinBlocks(v_a_4142_);
lean_dec(v_a_4142_);
v___x_4162_ = l_Array_append___redArg(v___x_4155_, v___x_4161_);
lean_dec_ref(v___x_4161_);
v___y_4144_ = v___x_4162_;
goto v___jp_4143_;
}
v___jp_4143_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4145_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_4146_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_4147_ = l_Lean_Doc_prefixListLines(v___x_4145_, v___x_4146_, v___y_4144_);
v_a_4131_ = v___x_4147_;
goto v___jp_4130_;
}
}
else
{
lean_dec(v_a_4138_);
lean_dec_ref(v_bs_x27_4129_);
lean_dec_ref(v_desc_4127_);
return v___x_4141_;
}
}
else
{
lean_dec_ref(v_desc_4127_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4163_; 
v_a_4163_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4137_, 1);
v_a_4131_ = v_a_4163_;
goto v___jp_4130_;
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec_ref(v_bs_x27_4129_);
v_a_4164_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4137_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4137_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
v___jp_4130_:
{
size_t v___x_4132_; size_t v___x_4133_; lean_object* v___x_4134_; 
v___x_4132_ = ((size_t)1ULL);
v___x_4133_ = lean_usize_add(v_i_4116_, v___x_4132_);
v___x_4134_ = lean_array_uset(v_bs_x27_4129_, v_i_4116_, v_a_4131_);
v_i_4116_ = v___x_4133_;
v_bs_4117_ = v___x_4134_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4115_ = stack[0].m_num;
size_t v_i_4116_ = stack[1].m_num;
lean_object* v_bs_4117_ = stack[2].m_obj;
lean_object* v___y_4118_ = stack[3].m_obj;
lean_object* v___y_4119_ = stack[4].m_obj;
lean_object* v___y_4120_ = stack[5].m_obj;
lean_object* v_res_4172_;
v_res_4172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_4115_, v_i_4116_, v_bs_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
stack->m_obj
 = v_res_4172_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed(lean_object* v_x_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_x_4173_, v_a_4174_, v_a_4175_, v_a_4176_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec(v_a_4174_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed(lean_object* v_sz_4181_, lean_object* v___x_4182_, lean_object* v_content_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
size_t v_sz_boxed_4188_; size_t v___x_5264__boxed_4189_; lean_object* v_res_4190_; 
v_sz_boxed_4188_ = lean_unbox_usize(v_sz_4181_);
lean_dec(v_sz_4181_);
v___x_5264__boxed_4189_ = lean_unbox_usize(v___x_4182_);
lean_dec(v___x_4182_);
v_res_4190_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(v_sz_boxed_4188_, v___x_5264__boxed_4189_, v_content_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
return v_res_4190_;
}
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(lean_object* v_x_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
switch(lean_obj_tag(v_x_4191_))
{
case 0:
{
lean_object* v_contents_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4205_; 
v_contents_4196_ = lean_ctor_get(v_x_4191_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v_x_4191_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4198_ = v_x_4191_;
v_isShared_4199_ = v_isSharedCheck_4205_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_contents_4196_);
lean_dec(v_x_4191_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4205_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4200_; lean_object* v___x_4202_; 
v___x_4200_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_4199_ == 0)
{
lean_ctor_set_tag(v___x_4198_, 9);
v___x_4202_ = v___x_4198_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_contents_4196_);
v___x_4202_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
lean_object* v___x_4203_; 
v___x_4203_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4200_, v___x_4202_, v_a_4192_, v_a_4193_, v_a_4194_);
return v___x_4203_;
}
}
}
case 1:
{
lean_object* v_content_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4214_; 
v_content_4206_ = lean_ctor_get(v_x_4191_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v_x_4191_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4208_ = v_x_4191_;
v_isShared_4209_ = v_isSharedCheck_4214_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_content_4206_);
lean_dec(v_x_4191_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4214_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4210_; lean_object* v___x_4212_; 
v___x_4210_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_4206_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set_tag(v___x_4208_, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4210_);
v___x_4212_ = v___x_4208_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
case 2:
{
lean_object* v_items_4215_; size_t v_sz_4216_; size_t v___x_4217_; lean_object* v___x_4218_; 
v_items_4215_ = lean_ctor_get(v_x_4191_, 0);
lean_inc_ref(v_items_4215_);
lean_dec_ref_known(v_x_4191_, 1);
v_sz_4216_ = lean_array_size(v_items_4215_);
v___x_4217_ = ((size_t)0ULL);
v___x_4218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_4216_, v___x_4217_, v_items_4215_, v_a_4192_, v_a_4193_, v_a_4194_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4227_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4221_ = v___x_4218_;
v_isShared_4222_ = v_isSharedCheck_4227_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4218_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4227_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4223_; lean_object* v___x_4225_; 
v___x_4223_ = l_Lean_Doc_joinBlocks(v_a_4219_);
lean_dec(v_a_4219_);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v___x_4223_);
v___x_4225_ = v___x_4221_;
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
v_a_4228_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4218_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4218_);
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
case 3:
{
lean_object* v_start_4236_; lean_object* v_items_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4271_; 
v_start_4236_ = lean_ctor_get(v_x_4191_, 0);
v_items_4237_ = lean_ctor_get(v_x_4191_, 1);
v_isSharedCheck_4271_ = !lean_is_exclusive(v_x_4191_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4239_ = v_x_4191_;
v_isShared_4240_ = v_isSharedCheck_4271_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_items_4237_);
lean_inc(v_start_4236_);
lean_dec(v_x_4191_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4271_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v_out_4241_; lean_object* v___y_4243_; lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v_out_4241_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_4268_ = lean_unsigned_to_nat(1u);
v___x_4269_ = l_Int_toNat(v_start_4236_);
lean_dec(v_start_4236_);
v___x_4270_ = lean_nat_dec_le(v___x_4268_, v___x_4269_);
if (v___x_4270_ == 0)
{
lean_dec(v___x_4269_);
v___y_4243_ = v___x_4268_;
goto v___jp_4242_;
}
else
{
v___y_4243_ = v___x_4269_;
goto v___jp_4242_;
}
v___jp_4242_:
{
lean_object* v___x_4245_; 
if (v_isShared_4240_ == 0)
{
lean_ctor_set_tag(v___x_4239_, 0);
lean_ctor_set(v___x_4239_, 1, v___y_4243_);
lean_ctor_set(v___x_4239_, 0, v_out_4241_);
v___x_4245_ = v___x_4239_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_out_4241_);
lean_ctor_set(v_reuseFailAlloc_4267_, 1, v___y_4243_);
v___x_4245_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
size_t v_sz_4246_; size_t v___x_4247_; lean_object* v___x_4248_; 
v_sz_4246_ = lean_array_size(v_items_4237_);
v___x_4247_ = ((size_t)0ULL);
v___x_4248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_items_4237_, v_sz_4246_, v___x_4247_, v___x_4245_, v_a_4192_, v_a_4193_, v_a_4194_);
lean_dec_ref(v_items_4237_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4258_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4251_ = v___x_4248_;
v_isShared_4252_ = v_isSharedCheck_4258_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4248_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4258_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v_fst_4253_; lean_object* v___x_4254_; lean_object* v___x_4256_; 
v_fst_4253_ = lean_ctor_get(v_a_4249_, 0);
lean_inc(v_fst_4253_);
lean_dec(v_a_4249_);
v___x_4254_ = l_Lean_Doc_joinBlocks(v_fst_4253_);
lean_dec(v_fst_4253_);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 0, v___x_4254_);
v___x_4256_ = v___x_4251_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v___x_4254_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
v_a_4259_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4248_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4248_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_4272_; size_t v_sz_4273_; size_t v___x_4274_; lean_object* v___x_4275_; 
v_items_4272_ = lean_ctor_get(v_x_4191_, 0);
lean_inc_ref(v_items_4272_);
lean_dec_ref_known(v_x_4191_, 1);
v_sz_4273_ = lean_array_size(v_items_4272_);
v___x_4274_ = ((size_t)0ULL);
v___x_4275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_4273_, v___x_4274_, v_items_4272_, v_a_4192_, v_a_4193_, v_a_4194_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4284_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4278_ = v___x_4275_;
v_isShared_4279_ = v_isSharedCheck_4284_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4275_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4284_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4280_; lean_object* v___x_4282_; 
v___x_4280_ = l_Lean_Doc_joinBlocks(v_a_4276_);
lean_dec(v_a_4276_);
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 0, v___x_4280_);
v___x_4282_ = v___x_4278_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4280_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
v_a_4285_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4275_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4275_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
case 5:
{
lean_object* v_items_4293_; size_t v_sz_4294_; size_t v___x_4295_; lean_object* v___x_4296_; 
v_items_4293_ = lean_ctor_get(v_x_4191_, 0);
lean_inc_ref(v_items_4293_);
lean_dec_ref_known(v_x_4191_, 1);
v_sz_4294_ = lean_array_size(v_items_4293_);
v___x_4295_ = ((size_t)0ULL);
v___x_4296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4294_, v___x_4295_, v_items_4293_, v_a_4192_, v_a_4193_, v_a_4194_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4307_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4299_ = v___x_4296_;
v_isShared_4300_ = v_isSharedCheck_4307_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4296_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4307_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4305_; 
v___x_4301_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_4302_ = l_Lean_Doc_joinBlocks(v_a_4297_);
lean_dec(v_a_4297_);
v___x_4303_ = l_Lean_Doc_prefixLines(v___x_4301_, v___x_4302_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 0, v___x_4303_);
v___x_4305_ = v___x_4299_;
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
v_a_4308_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4296_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4296_);
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
case 6:
{
lean_object* v_content_4316_; size_t v_sz_4317_; size_t v___x_4318_; lean_object* v___x_4319_; 
v_content_4316_ = lean_ctor_get(v_x_4191_, 0);
lean_inc_ref(v_content_4316_);
lean_dec_ref_known(v_x_4191_, 1);
v_sz_4317_ = lean_array_size(v_content_4316_);
v___x_4318_ = ((size_t)0ULL);
v___x_4319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4317_, v___x_4318_, v_content_4316_, v_a_4192_, v_a_4193_, v_a_4194_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4328_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4322_ = v___x_4319_;
v_isShared_4323_ = v_isSharedCheck_4328_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4319_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4328_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4324_; lean_object* v___x_4326_; 
v___x_4324_ = l_Lean_Doc_joinBlocks(v_a_4320_);
lean_dec(v_a_4320_);
if (v_isShared_4323_ == 0)
{
lean_ctor_set(v___x_4322_, 0, v___x_4324_);
v___x_4326_ = v___x_4322_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
v_a_4329_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4319_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4319_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
default: 
{
lean_object* v_container_4337_; 
v_container_4337_ = lean_ctor_get(v_x_4191_, 0);
if (lean_obj_tag(v_container_4337_) == 0)
{
lean_object* v_content_4338_; lean_object* v_val_4339_; lean_object* v___f_4340_; lean_object* v___f_4341_; size_t v_sz_4342_; size_t v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v_fallback_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
lean_inc_ref(v_container_4337_);
v_content_4338_ = lean_ctor_get(v_x_4191_, 1);
lean_inc_ref_n(v_content_4338_, 2);
lean_dec_ref_known(v_x_4191_, 2);
v_val_4339_ = lean_ctor_get(v_container_4337_, 0);
lean_inc(v_val_4339_);
lean_dec_ref_known(v_container_4337_, 1);
v___f_4340_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed), 5, 0);
v___f_4341_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___closed__0));
v_sz_4342_ = lean_array_size(v_content_4338_);
v___x_4343_ = ((size_t)0ULL);
v___x_4344_ = lean_box_usize(v_sz_4342_);
v___x_4345_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
v_fallback_4346_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_fallback_4346_, 0, v___x_4344_);
lean_closure_set(v_fallback_4346_, 1, v___x_4345_);
lean_closure_set(v_fallback_4346_, 2, v_content_4338_);
v___x_4347_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_4339_);
v___x_4348_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_4347_, v_a_4193_, v_a_4194_);
lean_dec(v___x_4347_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v_a_4349_; 
v_a_4349_ = lean_ctor_get(v___x_4348_, 0);
lean_inc(v_a_4349_);
lean_dec_ref_known(v___x_4348_, 1);
if (lean_obj_tag(v_a_4349_) == 0)
{
lean_object* v___x_4350_; 
lean_dec_ref(v_fallback_4346_);
lean_dec_ref(v___f_4340_);
lean_dec(v_val_4339_);
v___x_4350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4342_, v___x_4343_, v_content_4338_, v_a_4192_, v_a_4193_, v_a_4194_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4359_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4353_ = v___x_4350_;
v_isShared_4354_ = v_isSharedCheck_4359_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4359_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4355_ = l_Lean_Doc_joinBlocks(v_a_4351_);
lean_dec(v_a_4351_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 0, v___x_4355_);
v___x_4357_ = v___x_4353_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4355_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
v_a_4360_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4350_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4350_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
else
{
lean_object* v_val_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v_val_4368_ = lean_ctor_get(v_a_4349_, 0);
lean_inc(v_val_4368_);
lean_dec_ref_known(v_a_4349_, 1);
v___x_4369_ = lean_apply_4(v_val_4368_, v___f_4341_, v___f_4340_, v_val_4339_, v_content_4338_);
v___x_4370_ = l_Lean_Doc_withRendererFallback(v_fallback_4346_, v___x_4369_, v_a_4192_, v_a_4193_, v_a_4194_);
return v___x_4370_;
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_dec_ref(v_fallback_4346_);
lean_dec_ref(v___f_4340_);
lean_dec(v_val_4339_);
lean_dec_ref(v_content_4338_);
v_a_4371_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4348_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4348_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
else
{
lean_object* v_content_4379_; size_t v_sz_4380_; size_t v___x_4381_; lean_object* v___x_4382_; 
v_content_4379_ = lean_ctor_get(v_x_4191_, 1);
lean_inc_ref(v_content_4379_);
lean_dec_ref_known(v_x_4191_, 2);
v_sz_4380_ = lean_array_size(v_content_4379_);
v___x_4381_ = ((size_t)0ULL);
v___x_4382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4380_, v___x_4381_, v_content_4379_, v_a_4192_, v_a_4193_, v_a_4194_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4391_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4385_ = v___x_4382_;
v_isShared_4386_ = v_isSharedCheck_4391_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4382_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4391_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4387_; lean_object* v___x_4389_; 
v___x_4387_ = l_Lean_Doc_joinBlocks(v_a_4383_);
lean_dec(v_a_4383_);
if (v_isShared_4386_ == 0)
{
lean_ctor_set(v___x_4385_, 0, v___x_4387_);
v___x_4389_ = v___x_4385_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4387_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
v_a_4392_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4382_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4382_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4392_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4191_ = stack[0].m_obj;
lean_object* v_a_4192_ = stack[1].m_obj;
lean_object* v_a_4193_ = stack[2].m_obj;
lean_object* v_a_4194_ = stack[3].m_obj;
lean_object* v_res_4400_;
v_res_4400_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_x_4191_, v_a_4192_, v_a_4193_, v_a_4194_);
stack->m_obj
 = v_res_4400_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(size_t v_sz_4401_, size_t v_i_4402_, lean_object* v_bs_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
uint8_t v___x_4408_; 
v___x_4408_ = lean_usize_dec_lt(v_i_4402_, v_sz_4401_);
if (v___x_4408_ == 0)
{
lean_object* v___x_4409_; 
v___x_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4409_, 0, v_bs_4403_);
return v___x_4409_;
}
else
{
lean_object* v_v_4410_; lean_object* v___x_4411_; lean_object* v_bs_x27_4412_; lean_object* v___x_4413_; 
v_v_4410_ = lean_array_uget(v_bs_4403_, v_i_4402_);
v___x_4411_ = lean_unsigned_to_nat(0u);
v_bs_x27_4412_ = lean_array_uset(v_bs_4403_, v_i_4402_, v___x_4411_);
v___x_4413_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_v_4410_, v___y_4404_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; size_t v___x_4415_; size_t v___x_4416_; lean_object* v___x_4417_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref_known(v___x_4413_, 1);
v___x_4415_ = ((size_t)1ULL);
v___x_4416_ = lean_usize_add(v_i_4402_, v___x_4415_);
v___x_4417_ = lean_array_uset(v_bs_x27_4412_, v_i_4402_, v_a_4414_);
v_i_4402_ = v___x_4416_;
v_bs_4403_ = v___x_4417_;
goto _start;
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_dec_ref(v_bs_x27_4412_);
v_a_4419_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4413_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4413_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4401_ = stack[0].m_num;
size_t v_i_4402_ = stack[1].m_num;
lean_object* v_bs_4403_ = stack[2].m_obj;
lean_object* v___y_4404_ = stack[3].m_obj;
lean_object* v___y_4405_ = stack[4].m_obj;
lean_object* v___y_4406_ = stack[5].m_obj;
lean_object* v_res_4427_;
v_res_4427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4401_, v_i_4402_, v_bs_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
stack->m_obj
 = v_res_4427_;
}
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(size_t v_sz_4428_, size_t v___x_4429_, lean_object* v_content_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4428_, v___x_4429_, v_content_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4444_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4438_ = v___x_4435_;
v_isShared_4439_ = v_isSharedCheck_4444_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4435_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4444_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4440_; lean_object* v___x_4442_; 
v___x_4440_ = l_Lean_Doc_joinBlocks(v_a_4436_);
lean_dec(v_a_4436_);
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4440_);
v___x_4442_ = v___x_4438_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
v_a_4445_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4435_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4435_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4428_ = stack[0].m_num;
size_t v___x_4429_ = stack[1].m_num;
lean_object* v_content_4430_ = stack[2].m_obj;
lean_object* v___y_4431_ = stack[3].m_obj;
lean_object* v___y_4432_ = stack[4].m_obj;
lean_object* v___y_4433_ = stack[5].m_obj;
lean_object* v_res_4453_;
v_res_4453_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(v_sz_4428_, v___x_4429_, v_content_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
stack->m_obj
 = v_res_4453_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2___boxed(lean_object* v_sz_4454_, lean_object* v_i_4455_, lean_object* v_bs_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
size_t v_sz_boxed_4461_; size_t v_i_boxed_4462_; lean_object* v_res_4463_; 
v_sz_boxed_4461_ = lean_unbox_usize(v_sz_4454_);
lean_dec(v_sz_4454_);
v_i_boxed_4462_ = lean_unbox_usize(v_i_4455_);
lean_dec(v_i_4455_);
v_res_4463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_boxed_4461_, v_i_boxed_4462_, v_bs_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v___y_4457_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5___boxed(lean_object* v_sz_4464_, lean_object* v_i_4465_, lean_object* v_bs_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
size_t v_sz_boxed_4471_; size_t v_i_boxed_4472_; lean_object* v_res_4473_; 
v_sz_boxed_4471_ = lean_unbox_usize(v_sz_4464_);
lean_dec(v_sz_4464_);
v_i_boxed_4472_ = lean_unbox_usize(v_i_4465_);
lean_dec(v_i_4465_);
v_res_4473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_boxed_4471_, v_i_boxed_4472_, v_bs_4466_, v___y_4467_, v___y_4468_, v___y_4469_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7___boxed(lean_object* v_as_4474_, lean_object* v_sz_4475_, lean_object* v_i_4476_, lean_object* v_b_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
size_t v_sz_boxed_4482_; size_t v_i_boxed_4483_; lean_object* v_res_4484_; 
v_sz_boxed_4482_ = lean_unbox_usize(v_sz_4475_);
lean_dec(v_sz_4475_);
v_i_boxed_4483_ = lean_unbox_usize(v_i_4476_);
lean_dec(v_i_4476_);
v_res_4484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_as_4474_, v_sz_boxed_4482_, v_i_boxed_4483_, v_b_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v_as_4474_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8___boxed(lean_object* v_sz_4485_, lean_object* v_i_4486_, lean_object* v_bs_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
size_t v_sz_boxed_4492_; size_t v_i_boxed_4493_; lean_object* v_res_4494_; 
v_sz_boxed_4492_ = lean_unbox_usize(v_sz_4485_);
lean_dec(v_sz_4485_);
v_i_boxed_4493_ = lean_unbox_usize(v_i_4486_);
lean_dec(v_i_4486_);
v_res_4494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_boxed_4492_, v_i_boxed_4493_, v_bs_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
return v_res_4494_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(size_t v_sz_4495_, size_t v_i_4496_, lean_object* v_bs_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
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
lean_object* v_v_4504_; lean_object* v___x_4505_; lean_object* v_bs_x27_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v_v_4504_ = lean_array_uget(v_bs_4497_, v_i_4496_);
v___x_4505_ = lean_unsigned_to_nat(0u);
v_bs_x27_4506_ = lean_array_uset(v_bs_4497_, v_i_4496_, v___x_4505_);
v___x_4507_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_4508_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4507_, v_v_4504_, v___y_4498_, v___y_4499_, v___y_4500_);
if (lean_obj_tag(v___x_4508_) == 0)
{
lean_object* v_a_4509_; size_t v___x_4510_; size_t v___x_4511_; lean_object* v___x_4512_; 
v_a_4509_ = lean_ctor_get(v___x_4508_, 0);
lean_inc(v_a_4509_);
lean_dec_ref_known(v___x_4508_, 1);
v___x_4510_ = ((size_t)1ULL);
v___x_4511_ = lean_usize_add(v_i_4496_, v___x_4510_);
v___x_4512_ = lean_array_uset(v_bs_x27_4506_, v_i_4496_, v_a_4509_);
v_i_4496_ = v___x_4511_;
v_bs_4497_ = v___x_4512_;
goto _start;
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
lean_dec_ref(v_bs_x27_4506_);
v_a_4514_ = lean_ctor_get(v___x_4508_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4508_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4508_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4495_ = stack[0].m_num;
size_t v_i_4496_ = stack[1].m_num;
lean_object* v_bs_4497_ = stack[2].m_obj;
lean_object* v___y_4498_ = stack[3].m_obj;
lean_object* v___y_4499_ = stack[4].m_obj;
lean_object* v___y_4500_ = stack[5].m_obj;
lean_object* v_res_4522_;
v_res_4522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_4495_, v_i_4496_, v_bs_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
stack->m_obj
 = v_res_4522_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1___boxed(lean_object* v_sz_4523_, lean_object* v_i_4524_, lean_object* v_bs_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
size_t v_sz_boxed_4530_; size_t v_i_boxed_4531_; lean_object* v_res_4532_; 
v_sz_boxed_4530_ = lean_unbox_usize(v_sz_4523_);
lean_dec(v_sz_4523_);
v_i_boxed_4531_ = lean_unbox_usize(v_i_4524_);
lean_dec(v_i_4524_);
v_res_4532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_boxed_4530_, v_i_boxed_4531_, v_bs_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(lean_object* v_x_4533_, lean_object* v_x_4534_){
_start:
{
lean_object* v_zero_4535_; uint8_t v_isZero_4536_; 
v_zero_4535_ = lean_unsigned_to_nat(0u);
v_isZero_4536_ = lean_nat_dec_eq(v_x_4533_, v_zero_4535_);
if (v_isZero_4536_ == 1)
{
lean_dec(v_x_4533_);
return v_x_4534_;
}
else
{
uint32_t v___x_4537_; lean_object* v_one_4538_; lean_object* v_n_4539_; lean_object* v___x_4540_; 
v___x_4537_ = 35;
v_one_4538_ = lean_unsigned_to_nat(1u);
v_n_4539_ = lean_nat_sub(v_x_4533_, v_one_4538_);
lean_dec(v_x_4533_);
v___x_4540_ = lean_string_push(v_x_4534_, v___x_4537_);
v_x_4533_ = v_n_4539_;
v_x_4534_ = v___x_4540_;
goto _start;
}
}
}
lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(lean_object* v_level_4542_, lean_object* v_part_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v_title_4548_; lean_object* v_content_4549_; lean_object* v_subParts_4550_; size_t v_sz_4551_; size_t v___x_4552_; lean_object* v___x_4553_; 
v_title_4548_ = lean_ctor_get(v_part_4543_, 0);
lean_inc_ref(v_title_4548_);
v_content_4549_ = lean_ctor_get(v_part_4543_, 3);
lean_inc_ref(v_content_4549_);
v_subParts_4550_ = lean_ctor_get(v_part_4543_, 4);
lean_inc_ref(v_subParts_4550_);
lean_dec_ref(v_part_4543_);
v_sz_4551_ = lean_array_size(v_title_4548_);
v___x_4552_ = ((size_t)0ULL);
v___x_4553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_4551_, v___x_4552_, v_title_4548_, v_a_4544_, v_a_4545_, v_a_4546_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; size_t v_sz_4566_; lean_object* v___x_4567_; 
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_a_4554_);
lean_dec_ref_known(v___x_4553_, 1);
v___x_4555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4556_ = lean_unsigned_to_nat(1u);
v___x_4557_ = lean_nat_add(v_level_4542_, v___x_4556_);
lean_inc(v___x_4557_);
v___x_4558_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(v___x_4557_, v___x_4555_);
v___x_4559_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_4560_ = lean_string_append(v___x_4558_, v___x_4559_);
v___x_4561_ = lean_mk_empty_array_with_capacity(v___x_4556_);
lean_inc_ref_n(v___x_4561_, 2);
v___x_4562_ = lean_array_push(v___x_4561_, v___x_4560_);
v___x_4563_ = lean_array_push(v___x_4561_, v___x_4562_);
v___x_4564_ = l_Array_append___redArg(v___x_4563_, v_a_4554_);
lean_dec(v_a_4554_);
v___x_4565_ = l_Lean_Doc_joinInlines(v___x_4564_);
lean_dec_ref(v___x_4564_);
v_sz_4566_ = lean_array_size(v_content_4549_);
v___x_4567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4566_, v___x_4552_, v_content_4549_, v_a_4544_, v_a_4545_, v_a_4546_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_object* v_a_4568_; size_t v_sz_4569_; lean_object* v___x_4570_; 
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc(v_a_4568_);
lean_dec_ref_known(v___x_4567_, 1);
v_sz_4569_ = lean_array_size(v_subParts_4550_);
v___x_4570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4557_, v_sz_4569_, v___x_4552_, v_subParts_4550_, v_a_4544_, v_a_4545_, v_a_4546_);
lean_dec(v___x_4557_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4582_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4573_ = v___x_4570_;
v_isShared_4574_ = v_isSharedCheck_4582_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4570_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4582_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4580_; 
v___x_4575_ = lean_array_push(v___x_4561_, v___x_4565_);
v___x_4576_ = l_Array_append___redArg(v___x_4575_, v_a_4568_);
lean_dec(v_a_4568_);
v___x_4577_ = l_Array_append___redArg(v___x_4576_, v_a_4571_);
lean_dec(v_a_4571_);
v___x_4578_ = l_Lean_Doc_joinBlocks(v___x_4577_);
lean_dec_ref(v___x_4577_);
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 0, v___x_4578_);
v___x_4580_ = v___x_4573_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4578_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
else
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
lean_dec(v_a_4568_);
lean_dec_ref(v___x_4565_);
lean_dec_ref(v___x_4561_);
v_a_4583_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___x_4570_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4570_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
else
{
lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4598_; 
lean_dec_ref(v___x_4565_);
lean_dec_ref(v___x_4561_);
lean_dec(v___x_4557_);
lean_dec_ref(v_subParts_4550_);
v_a_4591_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4598_ == 0)
{
v___x_4593_ = v___x_4567_;
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_dec(v___x_4567_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4596_; 
if (v_isShared_4594_ == 0)
{
v___x_4596_ = v___x_4593_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4591_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
}
}
else
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4606_; 
lean_dec_ref(v_subParts_4550_);
lean_dec_ref(v_content_4549_);
v_a_4599_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4601_ = v___x_4553_;
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4553_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4604_; 
if (v_isShared_4602_ == 0)
{
v___x_4604_ = v___x_4601_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_level_4542_ = stack[0].m_obj;
lean_object* v_part_4543_ = stack[1].m_obj;
lean_object* v_a_4544_ = stack[2].m_obj;
lean_object* v_a_4545_ = stack[3].m_obj;
lean_object* v_a_4546_ = stack[4].m_obj;
lean_object* v_res_4607_;
v_res_4607_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4542_, v_part_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
stack->m_obj
 = v_res_4607_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(lean_object* v___x_4608_, size_t v_sz_4609_, size_t v_i_4610_, lean_object* v_bs_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
uint8_t v___x_4616_; 
v___x_4616_ = lean_usize_dec_lt(v_i_4610_, v_sz_4609_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; 
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v_bs_4611_);
return v___x_4617_;
}
else
{
lean_object* v_v_4618_; lean_object* v___x_4619_; lean_object* v_bs_x27_4620_; lean_object* v___x_4621_; 
v_v_4618_ = lean_array_uget(v_bs_4611_, v_i_4610_);
v___x_4619_ = lean_unsigned_to_nat(0u);
v_bs_x27_4620_ = lean_array_uset(v_bs_4611_, v_i_4610_, v___x_4619_);
v___x_4621_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4608_, v_v_4618_, v___y_4612_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v_a_4622_; size_t v___x_4623_; size_t v___x_4624_; lean_object* v___x_4625_; 
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
lean_inc(v_a_4622_);
lean_dec_ref_known(v___x_4621_, 1);
v___x_4623_ = ((size_t)1ULL);
v___x_4624_ = lean_usize_add(v_i_4610_, v___x_4623_);
v___x_4625_ = lean_array_uset(v_bs_x27_4620_, v_i_4610_, v_a_4622_);
v_i_4610_ = v___x_4624_;
v_bs_4611_ = v___x_4625_;
goto _start;
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
lean_dec_ref(v_bs_x27_4620_);
v_a_4627_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4621_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4621_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4630_ == 0)
{
v___x_4632_ = v___x_4629_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4627_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4608_ = stack[0].m_obj;
size_t v_sz_4609_ = stack[1].m_num;
size_t v_i_4610_ = stack[2].m_num;
lean_object* v_bs_4611_ = stack[3].m_obj;
lean_object* v___y_4612_ = stack[4].m_obj;
lean_object* v___y_4613_ = stack[5].m_obj;
lean_object* v___y_4614_ = stack[6].m_obj;
lean_object* v_res_4635_;
v_res_4635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4608_, v_sz_4609_, v_i_4610_, v_bs_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
stack->m_obj
 = v_res_4635_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg___boxed(lean_object* v___x_4636_, lean_object* v_sz_4637_, lean_object* v_i_4638_, lean_object* v_bs_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
size_t v_sz_boxed_4644_; size_t v_i_boxed_4645_; lean_object* v_res_4646_; 
v_sz_boxed_4644_ = lean_unbox_usize(v_sz_4637_);
lean_dec(v_sz_4637_);
v_i_boxed_4645_ = lean_unbox_usize(v_i_4638_);
lean_dec(v_i_4638_);
v_res_4646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4636_, v_sz_boxed_4644_, v_i_boxed_4645_, v_bs_4639_, v___y_4640_, v___y_4641_, v___y_4642_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
lean_dec(v___y_4640_);
lean_dec(v___x_4636_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg___boxed(lean_object* v_level_4647_, lean_object* v_part_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4647_, v_part_4648_, v_a_4649_, v_a_4650_, v_a_4651_);
lean_dec(v_a_4651_);
lean_dec_ref(v_a_4650_);
lean_dec(v_a_4649_);
lean_dec(v_level_4647_);
return v_res_4653_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(size_t v_sz_4654_, size_t v_i_4655_, lean_object* v_bs_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_){
_start:
{
uint8_t v___x_4661_; 
v___x_4661_ = lean_usize_dec_lt(v_i_4655_, v_sz_4654_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; 
v___x_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4662_, 0, v_bs_4656_);
return v___x_4662_;
}
else
{
lean_object* v_v_4663_; lean_object* v___x_4664_; lean_object* v_bs_x27_4665_; lean_object* v___x_4666_; 
v_v_4663_ = lean_array_uget(v_bs_4656_, v_i_4655_);
v___x_4664_ = lean_unsigned_to_nat(0u);
v_bs_x27_4665_ = lean_array_uset(v_bs_4656_, v_i_4655_, v___x_4664_);
v___x_4666_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4664_, v_v_4663_, v___y_4657_, v___y_4658_, v___y_4659_);
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_object* v_a_4667_; size_t v___x_4668_; size_t v___x_4669_; lean_object* v___x_4670_; 
v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
lean_inc(v_a_4667_);
lean_dec_ref_known(v___x_4666_, 1);
v___x_4668_ = ((size_t)1ULL);
v___x_4669_ = lean_usize_add(v_i_4655_, v___x_4668_);
v___x_4670_ = lean_array_uset(v_bs_x27_4665_, v_i_4655_, v_a_4667_);
v_i_4655_ = v___x_4669_;
v_bs_4656_ = v___x_4670_;
goto _start;
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
lean_dec_ref(v_bs_x27_4665_);
v_a_4672_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4666_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4666_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4654_ = stack[0].m_num;
size_t v_i_4655_ = stack[1].m_num;
lean_object* v_bs_4656_ = stack[2].m_obj;
lean_object* v___y_4657_ = stack[3].m_obj;
lean_object* v___y_4658_ = stack[4].m_obj;
lean_object* v___y_4659_ = stack[5].m_obj;
lean_object* v_res_4680_;
v_res_4680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_4654_, v_i_4655_, v_bs_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
stack->m_obj
 = v_res_4680_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3___boxed(lean_object* v_sz_4681_, lean_object* v_i_4682_, lean_object* v_bs_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_){
_start:
{
size_t v_sz_boxed_4688_; size_t v_i_boxed_4689_; lean_object* v_res_4690_; 
v_sz_boxed_4688_ = lean_unbox_usize(v_sz_4681_);
lean_dec(v_sz_4681_);
v_i_boxed_4689_ = lean_unbox_usize(v_i_4682_);
lean_dec(v_i_4682_);
v_res_4690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_boxed_4688_, v_i_boxed_4689_, v_bs_4683_, v___y_4684_, v___y_4685_, v___y_4686_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v___y_4684_);
return v_res_4690_;
}
}
lean_object* l_Lean_findSimpleDocString_x3f___lam__0(lean_object* v_val_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
lean_object* v_text_4696_; lean_object* v_subsections_4697_; size_t v_sz_4698_; size_t v___x_4699_; lean_object* v___x_4700_; 
v_text_4696_ = lean_ctor_get(v_val_4691_, 0);
lean_inc_ref(v_text_4696_);
v_subsections_4697_ = lean_ctor_get(v_val_4691_, 1);
lean_inc_ref(v_subsections_4697_);
lean_dec_ref(v_val_4691_);
v_sz_4698_ = lean_array_size(v_text_4696_);
v___x_4699_ = ((size_t)0ULL);
v___x_4700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4698_, v___x_4699_, v_text_4696_, v___y_4692_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v_a_4701_; size_t v_sz_4702_; lean_object* v___x_4703_; 
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v___x_4700_, 1);
v_sz_4702_ = lean_array_size(v_subsections_4697_);
v___x_4703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_4702_, v___x_4699_, v_subsections_4697_, v___y_4692_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4713_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4706_ = v___x_4703_;
v_isShared_4707_ = v_isSharedCheck_4713_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4703_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4713_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4711_; 
v___x_4708_ = l_Array_append___redArg(v_a_4701_, v_a_4704_);
lean_dec(v_a_4704_);
v___x_4709_ = l_Lean_Doc_joinBlocks(v___x_4708_);
lean_dec_ref(v___x_4708_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 0, v___x_4709_);
v___x_4711_ = v___x_4706_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4709_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
else
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4721_; 
lean_dec(v_a_4701_);
v_a_4714_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4716_ = v___x_4703_;
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4703_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4719_; 
if (v_isShared_4717_ == 0)
{
v___x_4719_ = v___x_4716_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4714_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
}
else
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
lean_dec_ref(v_subsections_4697_);
v_a_4722_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4724_ = v___x_4700_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4700_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4727_; 
if (v_isShared_4725_ == 0)
{
v___x_4727_ = v___x_4724_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_findSimpleDocString_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_4691_ = stack[0].m_obj;
lean_object* v___y_4692_ = stack[1].m_obj;
lean_object* v___y_4693_ = stack[2].m_obj;
lean_object* v___y_4694_ = stack[3].m_obj;
lean_object* v_res_4730_;
v_res_4730_ = l_Lean_findSimpleDocString_x3f___lam__0(v_val_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
stack->m_obj
 = v_res_4730_;
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0___boxed(lean_object* v_val_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Lean_findSimpleDocString_x3f___lam__0(v_val_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
return v_res_4736_;
}
}
lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_4737_, lean_object* v_declName_4738_, uint8_t v_includeBuiltin_4739_, lean_object* v_options_4740_, lean_object* v_currNamespace_4741_, lean_object* v_openDecls_4742_, lean_object* v_cancelTk_x3f_4743_){
_start:
{
lean_object* v___x_4745_; 
lean_inc_ref(v_env_4737_);
v___x_4745_ = l_Lean_findInternalDocString_x3f(v_env_4737_, v_declName_4738_, v_includeBuiltin_4739_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4789_; 
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4748_ = v___x_4745_;
v_isShared_4749_ = v_isSharedCheck_4789_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4745_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4789_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
if (lean_obj_tag(v_a_4746_) == 0)
{
lean_object* v___x_4750_; lean_object* v___x_4752_; 
lean_dec(v_cancelTk_x3f_4743_);
lean_dec(v_openDecls_4742_);
lean_dec(v_currNamespace_4741_);
lean_dec_ref(v_options_4740_);
lean_dec_ref(v_env_4737_);
v___x_4750_ = lean_box(0);
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 0, v___x_4750_);
v___x_4752_ = v___x_4748_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4750_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
else
{
lean_object* v_val_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4788_; 
v_val_4754_ = lean_ctor_get(v_a_4746_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v_a_4746_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4756_ = v_a_4746_;
v_isShared_4757_ = v_isSharedCheck_4788_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_val_4754_);
lean_dec(v_a_4746_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4788_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
if (lean_obj_tag(v_val_4754_) == 0)
{
lean_object* v_val_4758_; lean_object* v___x_4760_; 
lean_dec(v_cancelTk_x3f_4743_);
lean_dec(v_openDecls_4742_);
lean_dec(v_currNamespace_4741_);
lean_dec_ref(v_options_4740_);
lean_dec_ref(v_env_4737_);
v_val_4758_ = lean_ctor_get(v_val_4754_, 0);
lean_inc(v_val_4758_);
lean_dec_ref_known(v_val_4754_, 1);
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 0, v_val_4758_);
v___x_4760_ = v___x_4756_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_val_4758_);
v___x_4760_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
lean_object* v___x_4762_; 
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 0, v___x_4760_);
v___x_4762_ = v___x_4748_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v___x_4760_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
else
{
lean_object* v_val_4765_; lean_object* v___f_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
lean_del_object(v___x_4748_);
v_val_4765_ = lean_ctor_get(v_val_4754_, 0);
lean_inc(v_val_4765_);
lean_dec_ref_known(v_val_4754_, 1);
v___f_4766_ = lean_alloc_closure((void*)(l_Lean_findSimpleDocString_x3f___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4766_, 0, v_val_4765_);
v___x_4767_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_4767_, 0, v___f_4766_);
v___x_4768_ = l_Lean_Doc_runMarkdown___redArg(v_env_4737_, v___x_4767_, v_options_4740_, v_currNamespace_4741_, v_openDecls_4742_, v_cancelTk_x3f_4743_);
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4779_; 
v_a_4769_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4771_ = v___x_4768_;
v_isShared_4772_ = v_isSharedCheck_4779_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4768_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4779_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4774_; 
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 0, v_a_4769_);
v___x_4774_ = v___x_4756_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_a_4769_);
v___x_4774_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
lean_object* v___x_4776_; 
if (v_isShared_4772_ == 0)
{
lean_ctor_set(v___x_4771_, 0, v___x_4774_);
v___x_4776_ = v___x_4771_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4774_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
else
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4787_; 
lean_del_object(v___x_4756_);
v_a_4780_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4782_ = v___x_4768_;
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4768_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4785_; 
if (v_isShared_4783_ == 0)
{
v___x_4785_ = v___x_4782_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
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
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
lean_dec(v_cancelTk_x3f_4743_);
lean_dec(v_openDecls_4742_);
lean_dec(v_currNamespace_4741_);
lean_dec_ref(v_options_4740_);
lean_dec_ref(v_env_4737_);
v_a_4790_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4792_ = v___x_4745_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4745_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_findSimpleDocString_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_4737_ = stack[0].m_obj;
lean_object* v_declName_4738_ = stack[1].m_obj;
uint8_t v_includeBuiltin_4739_ = stack[2].m_num;
lean_object* v_options_4740_ = stack[3].m_obj;
lean_object* v_currNamespace_4741_ = stack[4].m_obj;
lean_object* v_openDecls_4742_ = stack[5].m_obj;
lean_object* v_cancelTk_x3f_4743_ = stack[6].m_obj;
lean_object* v_res_4798_;
v_res_4798_ = l_Lean_findSimpleDocString_x3f(v_env_4737_, v_declName_4738_, v_includeBuiltin_4739_, v_options_4740_, v_currNamespace_4741_, v_openDecls_4742_, v_cancelTk_x3f_4743_);
stack->m_obj
 = v_res_4798_;
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_4799_, lean_object* v_declName_4800_, lean_object* v_includeBuiltin_4801_, lean_object* v_options_4802_, lean_object* v_currNamespace_4803_, lean_object* v_openDecls_4804_, lean_object* v_cancelTk_x3f_4805_, lean_object* v_a_4806_){
_start:
{
uint8_t v_includeBuiltin_boxed_4807_; lean_object* v_res_4808_; 
v_includeBuiltin_boxed_4807_ = lean_unbox(v_includeBuiltin_4801_);
v_res_4808_ = l_Lean_findSimpleDocString_x3f(v_env_4799_, v_declName_4800_, v_includeBuiltin_boxed_4807_, v_options_4802_, v_currNamespace_4803_, v_openDecls_4804_, v_cancelTk_x3f_4805_);
return v_res_4808_;
}
}
lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(lean_object* v_p_4809_, lean_object* v_level_4810_, lean_object* v_part_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_){
_start:
{
lean_object* v___x_4816_; 
v___x_4816_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4810_, v_part_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
return v___x_4816_;
}
}
LEAN_EXPORT void l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_level_4810_ = stack[1].m_obj;
lean_object* v_part_4811_ = stack[2].m_obj;
lean_object* v_a_4812_ = stack[3].m_obj;
lean_object* v_a_4813_ = stack[4].m_obj;
lean_object* v_a_4814_ = stack[5].m_obj;
lean_object* v_res_4817_;
v_res_4817_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(lean_box(0), v_level_4810_, v_part_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
stack->m_obj
 = v_res_4817_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___boxed(lean_object* v_p_4818_, lean_object* v_level_4819_, lean_object* v_part_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(v_p_4818_, v_level_4819_, v_part_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
lean_dec(v_a_4823_);
lean_dec_ref(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec(v_level_4819_);
return v_res_4825_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(lean_object* v_p_4826_, lean_object* v___x_4827_, size_t v_sz_4828_, size_t v_i_4829_, lean_object* v_bs_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_){
_start:
{
lean_object* v___x_4835_; 
v___x_4835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4827_, v_sz_4828_, v_i_4829_, v_bs_4830_, v___y_4831_, v___y_4832_, v___y_4833_);
return v___x_4835_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4827_ = stack[1].m_obj;
size_t v_sz_4828_ = stack[2].m_num;
size_t v_i_4829_ = stack[3].m_num;
lean_object* v_bs_4830_ = stack[4].m_obj;
lean_object* v___y_4831_ = stack[5].m_obj;
lean_object* v___y_4832_ = stack[6].m_obj;
lean_object* v___y_4833_ = stack[7].m_obj;
lean_object* v_res_4836_;
v_res_4836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(lean_box(0), v___x_4827_, v_sz_4828_, v_i_4829_, v_bs_4830_, v___y_4831_, v___y_4832_, v___y_4833_);
stack->m_obj
 = v_res_4836_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___boxed(lean_object* v_p_4837_, lean_object* v___x_4838_, lean_object* v_sz_4839_, lean_object* v_i_4840_, lean_object* v_bs_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
size_t v_sz_boxed_4846_; size_t v_i_boxed_4847_; lean_object* v_res_4848_; 
v_sz_boxed_4846_ = lean_unbox_usize(v_sz_4839_);
lean_dec(v_sz_4839_);
v_i_boxed_4847_ = lean_unbox_usize(v_i_4840_);
lean_dec(v_i_4840_);
v_res_4848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(v_p_4837_, v___x_4838_, v_sz_boxed_4846_, v_i_boxed_4847_, v_bs_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
lean_dec(v___y_4844_);
lean_dec_ref(v___y_4843_);
lean_dec(v___y_4842_);
lean_dec(v___x_4838_);
return v_res_4848_;
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
