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
lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_275_ = lean_string_utf8_byte_size(v_l_273_);
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_nat_dec_le(v___x_276_, v___x_275_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = lean_string_append(v_l_273_, v_r_274_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_279_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_nat_sub(v___x_275_, v___x_276_);
v___x_282_ = lean_string_memcmp(v_l_273_, v___x_279_, v___x_281_, v___x_280_, v___x_276_);
lean_dec(v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_string_append(v_l_273_, v_r_274_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_string_utf8_byte_size(v_r_274_);
v___x_285_ = lean_nat_dec_le(v___x_276_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
v___x_286_ = lean_string_append(v_l_273_, v_r_274_);
return v___x_286_;
}
else
{
uint8_t v___x_287_; 
v___x_287_ = lean_string_memcmp(v_r_274_, v___x_279_, v___x_280_, v___x_280_, v___x_276_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; 
v___x_288_ = lean_string_append(v_l_273_, v_r_274_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1));
v___x_290_ = lean_string_append(v_l_273_, v___x_289_);
v___x_291_ = lean_string_append(v___x_290_, v_r_274_);
return v___x_291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___boxed(lean_object* v_l_292_, lean_object* v_r_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v_l_292_, v_r_293_);
lean_dec_ref(v_r_293_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(lean_object* v_as_295_, size_t v_i_296_, size_t v_stop_297_, lean_object* v_b_298_){
_start:
{
lean_object* v___y_300_; uint8_t v___x_304_; 
v___x_304_ = lean_usize_dec_eq(v_i_296_, v_stop_297_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_305_ = lean_array_uget_borrowed(v_as_295_, v_i_296_);
v___x_306_ = lean_array_get_size(v___x_305_);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_nat_dec_eq(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_array_get_size(v_b_298_);
v___x_310_ = lean_nat_dec_eq(v___x_309_, v___x_307_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v_lastIdx_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v_glued_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v_lastIdx_312_ = lean_nat_sub(v___x_309_, v___x_311_);
v___x_313_ = lean_array_fget_borrowed(v_b_298_, v_lastIdx_312_);
v___x_314_ = lean_array_fget_borrowed(v___x_305_, v___x_307_);
lean_inc(v___x_313_);
v_glued_315_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v___x_313_, v___x_314_);
v___x_316_ = lean_array_fset(v_b_298_, v_lastIdx_312_, v_glued_315_);
lean_dec(v_lastIdx_312_);
v___x_317_ = l_Array_extract___redArg(v___x_305_, v___x_311_, v___x_306_);
v___x_318_ = l_Array_append___redArg(v___x_316_, v___x_317_);
lean_dec_ref(v___x_317_);
v___y_300_ = v___x_318_;
goto v___jp_299_;
}
else
{
lean_dec_ref(v_b_298_);
lean_inc(v___x_305_);
v___y_300_ = v___x_305_;
goto v___jp_299_;
}
}
else
{
v___y_300_ = v_b_298_;
goto v___jp_299_;
}
}
else
{
return v_b_298_;
}
v___jp_299_:
{
size_t v___x_301_; size_t v___x_302_; 
v___x_301_ = ((size_t)1ULL);
v___x_302_ = lean_usize_add(v_i_296_, v___x_301_);
v_i_296_ = v___x_302_;
v_b_298_ = v___y_300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0___boxed(lean_object* v_as_319_, lean_object* v_i_320_, lean_object* v_stop_321_, lean_object* v_b_322_){
_start:
{
size_t v_i_boxed_323_; size_t v_stop_boxed_324_; lean_object* v_res_325_; 
v_i_boxed_323_ = lean_unbox_usize(v_i_320_);
lean_dec(v_i_320_);
v_stop_boxed_324_ = lean_unbox_usize(v_stop_321_);
lean_dec(v_stop_321_);
v_res_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_as_319_, v_i_boxed_323_, v_stop_boxed_324_, v_b_322_);
lean_dec_ref(v_as_319_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines(lean_object* v_parts_326_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = ((lean_object*)(l_Lean_Doc_joinBlocks___closed__0));
v___x_329_ = lean_array_get_size(v_parts_326_);
v___x_330_ = lean_nat_dec_lt(v___x_327_, v___x_329_);
if (v___x_330_ == 0)
{
return v___x_328_;
}
else
{
uint8_t v___x_331_; 
v___x_331_ = lean_nat_dec_le(v___x_329_, v___x_329_);
if (v___x_331_ == 0)
{
if (v___x_330_ == 0)
{
return v___x_328_;
}
else
{
size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v___x_332_ = ((size_t)0ULL);
v___x_333_ = lean_usize_of_nat(v___x_329_);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_326_, v___x_332_, v___x_333_, v___x_328_);
return v___x_334_;
}
}
else
{
size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; 
v___x_335_ = ((size_t)0ULL);
v___x_336_ = lean_usize_of_nat(v___x_329_);
v___x_337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_326_, v___x_335_, v___x_336_, v___x_328_);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_joinInlines___boxed(lean_object* v_parts_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Doc_joinInlines(v_parts_338_);
lean_dec_ref(v_parts_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0(lean_object* v_a_340_, uint8_t v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
uint8_t v_a_19__boxed_354_; lean_object* v_res_355_; 
v_a_19__boxed_354_ = lean_unbox(v_a_348_);
v_res_355_ = l_Lean_Doc_instMarkdownInlineEmpty___lam__0(v_a_347_, v_a_19__boxed_354_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec_ref(v_a_347_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0(lean_object* v_a_358_, lean_object* v_a_359_, uint8_t v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0___boxed(lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
uint8_t v_a_41__boxed_374_; lean_object* v_res_375_; 
v_a_41__boxed_374_ = lean_unbox(v_a_368_);
v_res_375_ = l_Lean_Doc_instMarkdownBlockEmpty___redArg___lam__0(v_a_366_, v_a_367_, v_a_41__boxed_374_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec_ref(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg(){
_start:
{
lean_object* v___f_378_; 
v___f_378_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0));
return v___f_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty___redArg___boxed(lean_object* v___dummy_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Doc_instMarkdownBlockEmpty___redArg();
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockEmpty(lean_object* v_i_381_){
_start:
{
lean_object* v___f_382_; 
v___f_382_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockEmpty___redArg___closed__0));
return v___f_382_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(lean_object* v_x_383_, lean_object* v_x_384_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
if (lean_obj_tag(v_x_384_) == 0)
{
uint8_t v___x_385_; 
v___x_385_ = 1;
return v___x_385_;
}
else
{
uint8_t v___x_386_; 
v___x_386_ = 0;
return v___x_386_;
}
}
else
{
if (lean_obj_tag(v_x_384_) == 0)
{
uint8_t v___x_387_; 
v___x_387_ = 0;
return v___x_387_;
}
else
{
lean_object* v_val_388_; lean_object* v_val_389_; uint32_t v___x_390_; uint32_t v___x_391_; uint8_t v___x_392_; 
v_val_388_ = lean_ctor_get(v_x_383_, 0);
v_val_389_ = lean_ctor_get(v_x_384_, 0);
v___x_390_ = lean_unbox_uint32(v_val_388_);
v___x_391_ = lean_unbox_uint32(v_val_389_);
v___x_392_ = lean_uint32_dec_eq(v___x_390_, v___x_391_);
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1___boxed(lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_x_393_, v_x_394_);
lean_dec(v_x_394_);
lean_dec(v_x_393_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(lean_object* v_s_397_, uint32_t v_c_398_, lean_object* v_a_399_, uint8_t v_b_400_){
_start:
{
lean_object* v_str_401_; lean_object* v_startInclusive_402_; lean_object* v_endExclusive_403_; lean_object* v___x_404_; uint8_t v_decide_405_; 
v_str_401_ = lean_ctor_get(v_s_397_, 0);
v_startInclusive_402_ = lean_ctor_get(v_s_397_, 1);
v_endExclusive_403_ = lean_ctor_get(v_s_397_, 2);
v___x_404_ = lean_nat_sub(v_endExclusive_403_, v_startInclusive_402_);
v_decide_405_ = lean_nat_dec_eq(v_a_399_, v___x_404_);
lean_dec(v___x_404_);
if (v_decide_405_ == 0)
{
lean_object* v___x_406_; uint32_t v___x_407_; uint8_t v___x_408_; 
v___x_406_ = lean_nat_add(v_startInclusive_402_, v_a_399_);
lean_dec(v_a_399_);
v___x_407_ = lean_string_utf8_get_fast(v_str_401_, v___x_406_);
v___x_408_ = lean_uint32_dec_eq(v___x_407_, v_c_398_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_string_utf8_next_fast(v_str_401_, v___x_406_);
lean_dec(v___x_406_);
v___x_410_ = lean_nat_sub(v___x_409_, v_startInclusive_402_);
v_a_399_ = v___x_410_;
v_b_400_ = v___x_408_;
goto _start;
}
else
{
lean_dec(v___x_406_);
return v___x_408_;
}
}
else
{
lean_dec(v_a_399_);
return v_b_400_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg___boxed(lean_object* v_s_412_, lean_object* v_c_413_, lean_object* v_a_414_, lean_object* v_b_415_){
_start:
{
uint32_t v_c_boxed_416_; uint8_t v_b_boxed_417_; uint8_t v_res_418_; lean_object* v_r_419_; 
v_c_boxed_416_ = lean_unbox_uint32(v_c_413_);
lean_dec(v_c_413_);
v_b_boxed_417_ = lean_unbox(v_b_415_);
v_res_418_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_412_, v_c_boxed_416_, v_a_414_, v_b_boxed_417_);
lean_dec_ref(v_s_412_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(uint32_t v_c_420_, lean_object* v_s_421_){
_start:
{
lean_object* v_searcher_422_; uint8_t v___x_423_; uint8_t v___x_424_; 
v_searcher_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = 0;
v___x_424_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_421_, v_c_420_, v_searcher_422_, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0___boxed(lean_object* v_c_425_, lean_object* v_s_426_){
_start:
{
uint32_t v_c_boxed_427_; uint8_t v_res_428_; lean_object* v_r_429_; 
v_c_boxed_427_ = lean_unbox_uint32(v_c_425_);
lean_dec(v_c_425_);
v_res_428_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_boxed_427_, v_s_426_);
lean_dec_ref(v_s_426_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_435_; lean_object* v___x_436_; 
v___x_435_ = 91;
v___x_436_ = lean_box_uint32(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2___boxed__const__1;
v___x_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(uint32_t v_c_439_, lean_object* v_next_x3f_440_){
_start:
{
uint32_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 33;
v___x_442_ = lean_uint32_dec_eq(v_c_439_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1));
v___x_444_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_439_, v___x_443_);
return v___x_444_;
}
else
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2, &l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2);
v___x_446_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_440_, v___x_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___boxed(lean_object* v_c_447_, lean_object* v_next_x3f_448_){
_start:
{
uint32_t v_c_boxed_449_; uint8_t v_res_450_; lean_object* v_r_451_; 
v_c_boxed_449_ = lean_unbox_uint32(v_c_447_);
lean_dec(v_c_447_);
v_res_450_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_boxed_449_, v_next_x3f_448_);
lean_dec(v_next_x3f_448_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(lean_object* v_s_452_, uint32_t v_c_453_, lean_object* v_inst_454_, lean_object* v_R_455_, lean_object* v_a_456_, uint8_t v_b_457_, lean_object* v_c_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_452_, v_c_453_, v_a_456_, v_b_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___boxed(lean_object* v_s_460_, lean_object* v_c_461_, lean_object* v_inst_462_, lean_object* v_R_463_, lean_object* v_a_464_, lean_object* v_b_465_, lean_object* v_c_466_){
_start:
{
uint32_t v_c_boxed_467_; uint8_t v_b_boxed_468_; uint8_t v_res_469_; lean_object* v_r_470_; 
v_c_boxed_467_ = lean_unbox_uint32(v_c_461_);
lean_dec(v_c_461_);
v_b_boxed_468_ = lean_unbox(v_b_465_);
v_res_469_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(v_s_460_, v_c_boxed_467_, v_inst_462_, v_R_463_, v_a_464_, v_b_boxed_468_, v_c_466_);
lean_dec_ref(v_s_460_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_471_; lean_object* v___x_472_; 
v___x_471_ = 32;
v___x_472_ = lean_box_uint32(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(lean_object* v_prev_x3f_475_, uint32_t v_c_476_, lean_object* v_next_x3f_477_){
_start:
{
uint8_t v___y_479_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0);
v___x_497_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_477_, v___x_496_);
if (v___x_497_ == 0)
{
if (lean_obj_tag(v_next_x3f_477_) == 0)
{
uint8_t v___x_498_; 
v___x_498_ = 1;
v___y_479_ = v___x_498_;
goto v___jp_478_;
}
else
{
v___y_479_ = v___x_497_;
goto v___jp_478_;
}
}
else
{
v___y_479_ = v___x_497_;
goto v___jp_478_;
}
v___jp_478_:
{
uint32_t v___x_480_; uint8_t v___x_481_; 
v___x_480_ = 62;
v___x_481_ = lean_uint32_dec_eq(v_c_476_, v___x_480_);
if (v___x_481_ == 0)
{
uint32_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = 45;
v___x_483_ = lean_uint32_dec_eq(v_c_476_, v___x_482_);
if (v___x_483_ == 0)
{
uint32_t v___x_484_; uint8_t v___x_485_; 
v___x_484_ = 43;
v___x_485_ = lean_uint32_dec_eq(v_c_476_, v___x_484_);
if (v___x_485_ == 0)
{
uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = 46;
v___x_487_ = lean_uint32_dec_eq(v_c_476_, v___x_486_);
if (v___x_487_ == 0)
{
uint8_t v___x_488_; 
v___x_488_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v_c_476_, v_next_x3f_477_);
return v___x_488_;
}
else
{
if (lean_obj_tag(v_prev_x3f_475_) == 0)
{
return v___x_485_;
}
else
{
lean_object* v_val_489_; uint32_t v___x_490_; uint32_t v___x_491_; uint8_t v___x_492_; 
v_val_489_ = lean_ctor_get(v_prev_x3f_475_, 0);
v___x_490_ = 48;
v___x_491_ = lean_unbox_uint32(v_val_489_);
v___x_492_ = lean_uint32_dec_le(v___x_490_, v___x_491_);
if (v___x_492_ == 0)
{
return v___x_492_;
}
else
{
uint32_t v___x_493_; uint32_t v___x_494_; uint8_t v___x_495_; 
v___x_493_ = 57;
v___x_494_ = lean_unbox_uint32(v_val_489_);
v___x_495_ = lean_uint32_dec_le(v___x_494_, v___x_493_);
if (v___x_495_ == 0)
{
return v___x_495_;
}
else
{
return v___y_479_;
}
}
}
}
}
else
{
return v___y_479_;
}
}
else
{
return v___y_479_;
}
}
else
{
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___boxed(lean_object* v_prev_x3f_499_, lean_object* v_c_500_, lean_object* v_next_x3f_501_){
_start:
{
uint32_t v_c_boxed_502_; uint8_t v_res_503_; lean_object* v_r_504_; 
v_c_boxed_502_ = lean_unbox_uint32(v_c_500_);
lean_dec(v_c_500_);
v_res_503_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_prev_x3f_499_, v_c_boxed_502_, v_next_x3f_501_);
lean_dec(v_next_x3f_501_);
lean_dec(v_prev_x3f_499_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(uint32_t v___x_510_, lean_object* v___x_511_, lean_object* v_____r_512_, lean_object* v_s_x27_513_){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint32_t v___x_527_; uint8_t v___x_528_; 
v___x_514_ = lean_string_push(v_s_x27_513_, v___x_510_);
v___x_515_ = lean_box_uint32(v___x_510_);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
v___x_527_ = 48;
v___x_528_ = lean_uint32_dec_le(v___x_527_, v___x_510_);
if (v___x_528_ == 0)
{
goto v___jp_521_;
}
else
{
uint32_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 57;
v___x_530_ = lean_uint32_dec_le(v___x_510_, v___x_529_);
if (v___x_530_ == 0)
{
goto v___jp_521_;
}
else
{
goto v___jp_517_;
}
}
v___jp_517_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_511_);
lean_ctor_set(v___x_518_, 1, v___x_516_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_514_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
v___jp_521_:
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1));
v___x_523_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v___x_510_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_511_);
lean_ctor_set(v___x_524_, 1, v___x_516_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_514_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
else
{
goto v___jp_517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed(lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v_____r_533_, lean_object* v_s_x27_534_){
_start:
{
uint32_t v___x_2069__boxed_535_; lean_object* v_res_536_; 
v___x_2069__boxed_535_ = lean_unbox_uint32(v___x_531_);
lean_dec(v___x_531_);
v_res_536_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_2069__boxed_535_, v___x_532_, v_____r_533_, v_s_x27_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(lean_object* v_s_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___y_540_; lean_object* v_snd_544_; lean_object* v_fst_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_583_; 
v_snd_544_ = lean_ctor_get(v_a_538_, 1);
v_fst_545_ = lean_ctor_get(v_a_538_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_a_538_);
if (v_isSharedCheck_583_ == 0)
{
v___x_547_ = v_a_538_;
v_isShared_548_ = v_isSharedCheck_583_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_snd_544_);
lean_inc(v_fst_545_);
lean_dec(v_a_538_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_583_;
goto v_resetjp_546_;
}
v___jp_539_:
{
if (lean_obj_tag(v___y_540_) == 0)
{
lean_object* v_a_541_; 
v_a_541_ = lean_ctor_get(v___y_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___y_540_, 1);
return v_a_541_;
}
else
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v___y_540_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___y_540_, 1);
v_a_538_ = v_a_542_;
goto _start;
}
}
v_resetjp_546_:
{
lean_object* v_fst_549_; lean_object* v_snd_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_582_; 
v_fst_549_ = lean_ctor_get(v_snd_544_, 0);
v_snd_550_ = lean_ctor_get(v_snd_544_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v_snd_544_);
if (v_isSharedCheck_582_ == 0)
{
v___x_552_ = v_snd_544_;
v_isShared_553_ = v_isSharedCheck_582_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snd_550_);
lean_inc(v_fst_549_);
lean_dec(v_snd_544_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_582_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; uint8_t v_decide_555_; 
v___x_554_ = lean_string_utf8_byte_size(v_s_537_);
v_decide_555_ = lean_nat_dec_eq(v_fst_549_, v___x_554_);
if (v_decide_555_ == 0)
{
uint32_t v___x_556_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___f_569_; uint8_t v_decide_574_; 
lean_del_object(v___x_552_);
lean_del_object(v___x_547_);
v___x_556_ = lean_string_utf8_get_fast(v_s_537_, v_fst_549_);
v___x_567_ = lean_string_utf8_next_fast(v_s_537_, v_fst_549_);
lean_dec(v_fst_549_);
v___x_568_ = lean_box_uint32(v___x_556_);
v___f_569_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_569_, 0, v___x_568_);
lean_closure_set(v___f_569_, 1, v___x_567_);
v_decide_574_ = lean_nat_dec_eq(v___x_567_, v___x_554_);
if (v_decide_574_ == 0)
{
goto v___jp_570_;
}
else
{
if (v_decide_555_ == 0)
{
lean_object* v_prev_x3f_575_; 
v_prev_x3f_575_ = lean_box(0);
v___y_558_ = v___f_569_;
v___y_559_ = v_prev_x3f_575_;
goto v___jp_557_;
}
else
{
goto v___jp_570_;
}
}
v___jp_557_:
{
uint8_t v___x_560_; 
v___x_560_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(v_snd_550_, v___x_556_, v___y_559_);
lean_dec(v___y_559_);
lean_dec(v_snd_550_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_box(0);
v___x_562_ = lean_apply_2(v___y_558_, v___x_561_, v_fst_545_);
v___y_540_ = v___x_562_;
goto v___jp_539_;
}
else
{
uint32_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_563_ = 92;
v___x_564_ = lean_string_push(v_fst_545_, v___x_563_);
v___x_565_ = lean_box(0);
v___x_566_ = lean_apply_2(v___y_558_, v___x_565_, v___x_564_);
v___y_540_ = v___x_566_;
goto v___jp_539_;
}
}
v___jp_570_:
{
uint32_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_string_utf8_get_fast(v_s_537_, v___x_567_);
v___x_572_ = lean_box_uint32(v___x_571_);
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
v___y_558_ = v___f_569_;
v___y_559_ = v___x_573_;
goto v___jp_557_;
}
}
else
{
lean_object* v___x_577_; 
if (v_isShared_553_ == 0)
{
v___x_577_ = v___x_552_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_fst_549_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_snd_550_);
v___x_577_ = v_reuseFailAlloc_581_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 1, v___x_577_);
v___x_579_ = v___x_547_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_fst_545_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___boxed(lean_object* v_s_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_584_, v_a_585_);
lean_dec_ref(v_s_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(uint32_t v___x_587_, lean_object* v___x_588_, lean_object* v_____r_589_, lean_object* v_s_x27_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_string_push(v_s_x27_590_, v___x_587_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_588_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0___boxed(lean_object* v___x_594_, lean_object* v___x_595_, lean_object* v_____r_596_, lean_object* v_s_x27_597_){
_start:
{
uint32_t v___x_2197__boxed_598_; lean_object* v_res_599_; 
v___x_2197__boxed_598_ = lean_unbox_uint32(v___x_594_);
lean_dec(v___x_594_);
v_res_599_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_2197__boxed_598_, v___x_595_, v_____r_596_, v_s_x27_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(lean_object* v_s_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___y_603_; lean_object* v_fst_607_; lean_object* v_snd_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_633_; 
v_fst_607_ = lean_ctor_get(v_a_601_, 0);
v_snd_608_ = lean_ctor_get(v_a_601_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_a_601_);
if (v_isSharedCheck_633_ == 0)
{
v___x_610_ = v_a_601_;
v_isShared_611_ = v_isSharedCheck_633_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snd_608_);
lean_inc(v_fst_607_);
lean_dec(v_a_601_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_633_;
goto v_resetjp_609_;
}
v___jp_602_:
{
if (lean_obj_tag(v___y_603_) == 0)
{
lean_object* v_a_604_; 
v_a_604_ = lean_ctor_get(v___y_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___y_603_, 1);
return v_a_604_;
}
else
{
lean_object* v_a_605_; 
v_a_605_ = lean_ctor_get(v___y_603_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___y_603_, 1);
v_a_601_ = v_a_605_;
goto _start;
}
}
v_resetjp_609_:
{
lean_object* v___x_612_; uint8_t v_decide_613_; 
v___x_612_ = lean_string_utf8_byte_size(v_s_600_);
v_decide_613_ = lean_nat_dec_eq(v_snd_608_, v___x_612_);
if (v_decide_613_ == 0)
{
uint32_t v___x_614_; lean_object* v___x_615_; lean_object* v___y_617_; uint8_t v_decide_625_; 
lean_del_object(v___x_610_);
v___x_614_ = lean_string_utf8_get_fast(v_s_600_, v_snd_608_);
v___x_615_ = lean_string_utf8_next_fast(v_s_600_, v_snd_608_);
lean_dec(v_snd_608_);
v_decide_625_ = lean_nat_dec_eq(v___x_615_, v___x_612_);
if (v_decide_625_ == 0)
{
uint32_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_string_utf8_get_fast(v_s_600_, v___x_615_);
v___x_627_ = lean_box_uint32(v___x_626_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
v___y_617_ = v___x_628_;
goto v___jp_616_;
}
else
{
lean_object* v_prev_x3f_629_; 
v_prev_x3f_629_ = lean_box(0);
v___y_617_ = v_prev_x3f_629_;
goto v___jp_616_;
}
v___jp_616_:
{
uint8_t v___x_618_; 
v___x_618_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(v___x_614_, v___y_617_);
lean_dec(v___y_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_box(0);
v___x_620_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_614_, v___x_615_, v___x_619_, v_fst_607_);
v___y_603_ = v___x_620_;
goto v___jp_602_;
}
else
{
uint32_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_621_ = 92;
v___x_622_ = lean_string_push(v_fst_607_, v___x_621_);
v___x_623_ = lean_box(0);
v___x_624_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_614_, v___x_615_, v___x_623_, v___x_622_);
v___y_603_ = v___x_624_;
goto v___jp_602_;
}
}
}
else
{
lean_object* v___x_631_; 
if (v_isShared_611_ == 0)
{
v___x_631_ = v___x_610_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_fst_607_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_snd_608_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___boxed(lean_object* v_s_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_634_, v_a_635_);
lean_dec_ref(v_s_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object* v_s_643_){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v_snd_646_; lean_object* v_fst_647_; lean_object* v_fst_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_657_; 
v___x_644_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1));
v___x_645_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_643_, v___x_644_);
v_snd_646_ = lean_ctor_get(v___x_645_, 1);
lean_inc(v_snd_646_);
v_fst_647_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_fst_647_);
lean_dec_ref(v___x_645_);
v_fst_648_ = lean_ctor_get(v_snd_646_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_snd_646_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v_snd_646_, 1);
lean_dec(v_unused_658_);
v___x_650_ = v_snd_646_;
v_isShared_651_ = v_isSharedCheck_657_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_fst_648_);
lean_dec(v_snd_646_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_657_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v_fst_648_);
lean_ctor_set(v___x_650_, 0, v_fst_647_);
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_fst_647_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_fst_648_);
v___x_653_ = v_reuseFailAlloc_656_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; lean_object* v_fst_655_; 
v___x_654_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_643_, v___x_653_);
v_fst_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_fst_655_);
lean_dec_ref(v___x_654_);
return v_fst_655_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(lean_object* v_s_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_659_);
lean_dec_ref(v_s_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(lean_object* v_s_661_, lean_object* v_inst_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_661_, v_a_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(lean_object* v_s_665_, lean_object* v_inst_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_665_, v_inst_666_, v_a_667_);
lean_dec_ref(v_s_665_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(lean_object* v_s_669_, lean_object* v_inst_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_669_, v_a_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___boxed(lean_object* v_s_673_, lean_object* v_inst_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(v_s_673_, v_inst_674_, v_a_675_);
lean_dec_ref(v_s_673_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v_str_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_snd_679_; lean_object* v_fst_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_722_; 
v_snd_679_ = lean_ctor_get(v_a_678_, 1);
v_fst_680_ = lean_ctor_get(v_a_678_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_722_ == 0)
{
v___x_682_ = v_a_678_;
v_isShared_683_ = v_isSharedCheck_722_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_snd_679_);
lean_inc(v_fst_680_);
lean_dec(v_a_678_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_722_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_fst_684_; lean_object* v_snd_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_721_; 
v_fst_684_ = lean_ctor_get(v_snd_679_, 0);
v_snd_685_ = lean_ctor_get(v_snd_679_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_snd_679_);
if (v_isSharedCheck_721_ == 0)
{
v___x_687_ = v_snd_679_;
v_isShared_688_ = v_isSharedCheck_721_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_snd_685_);
lean_inc(v_fst_684_);
lean_dec(v_snd_679_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_721_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; uint8_t v_decide_690_; 
v___x_689_ = lean_string_utf8_byte_size(v_str_677_);
v_decide_690_ = lean_nat_dec_eq(v_snd_685_, v___x_689_);
if (v_decide_690_ == 0)
{
uint32_t v___x_691_; lean_object* v___x_692_; uint32_t v___x_693_; uint8_t v___x_694_; 
v___x_691_ = lean_string_utf8_get_fast(v_str_677_, v_snd_685_);
v___x_692_ = lean_string_utf8_next_fast(v_str_677_, v_snd_685_);
lean_dec(v_snd_685_);
v___x_693_ = 96;
v___x_694_ = lean_uint32_dec_eq(v___x_691_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v_longest_695_; lean_object* v___y_697_; uint8_t v___x_705_; 
v_longest_695_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_nat_dec_le(v_fst_680_, v_fst_684_);
if (v___x_705_ == 0)
{
lean_dec(v_fst_684_);
v___y_697_ = v_fst_680_;
goto v___jp_696_;
}
else
{
lean_dec(v_fst_680_);
v___y_697_ = v_fst_684_;
goto v___jp_696_;
}
v___jp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_692_);
lean_ctor_set(v___x_687_, 0, v_longest_695_);
v___x_699_ = v___x_687_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_longest_695_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_692_);
v___x_699_ = v_reuseFailAlloc_704_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_699_);
lean_ctor_set(v___x_682_, 0, v___y_697_);
v___x_701_ = v___x_682_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___y_697_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_699_);
v___x_701_ = v_reuseFailAlloc_703_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v_a_678_ = v___x_701_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = lean_nat_add(v_fst_684_, v___x_706_);
lean_dec(v_fst_684_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_692_);
lean_ctor_set(v___x_687_, 0, v___x_707_);
v___x_709_ = v___x_687_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_692_);
v___x_709_ = v_reuseFailAlloc_714_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_709_);
v___x_711_ = v___x_682_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_fst_680_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_709_);
v___x_711_ = v_reuseFailAlloc_713_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
v_a_678_ = v___x_711_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_716_; 
if (v_isShared_688_ == 0)
{
v___x_716_ = v___x_687_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_fst_684_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_snd_685_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_716_);
v___x_718_ = v___x_682_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_fst_680_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v_str_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_723_, v_a_724_);
lean_dec_ref(v_str_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(lean_object* v_str_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_snd_734_; lean_object* v_fst_735_; lean_object* v_fst_736_; uint8_t v___x_737_; 
v___x_732_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1));
v___x_733_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_731_, v___x_732_);
v_snd_734_ = lean_ctor_get(v___x_733_, 1);
lean_inc(v_snd_734_);
v_fst_735_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_fst_735_);
lean_dec_ref(v___x_733_);
v_fst_736_ = lean_ctor_get(v_snd_734_, 0);
lean_inc(v_fst_736_);
lean_dec(v_snd_734_);
v___x_737_ = lean_nat_dec_le(v_fst_735_, v_fst_736_);
if (v___x_737_ == 0)
{
lean_dec(v_fst_736_);
return v_fst_735_;
}
else
{
lean_dec(v_fst_735_);
return v_fst_736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___boxed(lean_object* v_str_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_738_);
lean_dec_ref(v_str_738_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(lean_object* v_str_740_, lean_object* v_inst_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_740_, v_a_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v_str_744_, lean_object* v_inst_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(v_str_744_, v_inst_745_, v_a_746_);
lean_dec_ref(v_str_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
lean_object* v_zero_750_; uint8_t v_isZero_751_; 
v_zero_750_ = lean_unsigned_to_nat(0u);
v_isZero_751_ = lean_nat_dec_eq(v_x_748_, v_zero_750_);
if (v_isZero_751_ == 1)
{
lean_dec(v_x_748_);
return v_x_749_;
}
else
{
uint32_t v___x_752_; lean_object* v_one_753_; lean_object* v_n_754_; lean_object* v___x_755_; 
v___x_752_ = 96;
v_one_753_ = lean_unsigned_to_nat(1u);
v_n_754_ = lean_nat_sub(v_x_748_, v_one_753_);
lean_dec(v_x_748_);
v___x_755_ = lean_string_push(v_x_749_, v___x_752_);
v_x_748_ = v_n_754_;
v_x_749_ = v___x_755_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(lean_object* v_atLeast_757_, lean_object* v_str_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___y_761_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_765_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_758_);
v___x_766_ = lean_nat_dec_le(v_atLeast_757_, v___x_765_);
if (v___x_766_ == 0)
{
lean_dec(v___x_765_);
v___y_761_ = v_atLeast_757_;
goto v___jp_760_;
}
else
{
lean_dec(v_atLeast_757_);
v___y_761_ = v___x_765_;
goto v___jp_760_;
}
v___jp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v___y_761_, v___x_762_);
lean_dec(v___y_761_);
v___x_764_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(v___x_763_, v___x_759_);
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor___boxed(lean_object* v_atLeast_767_, lean_object* v_str_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v_atLeast_767_, v_str_768_);
lean_dec_ref(v_str_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object* v_str_771_){
_start:
{
lean_object* v___x_772_; lean_object* v_backticks_773_; lean_object* v___y_775_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_772_ = lean_unsigned_to_nat(0u);
v_backticks_773_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_772_, v_str_771_);
v___x_789_ = lean_string_utf8_byte_size(v_str_771_);
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_nat_dec_le(v___x_790_, v___x_789_);
if (v___x_791_ == 0)
{
goto v___jp_782_;
}
else
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_793_ = lean_string_memcmp(v_str_771_, v___x_792_, v___x_772_, v___x_772_, v___x_790_);
if (v___x_793_ == 0)
{
goto v___jp_782_;
}
else
{
goto v___jp_778_;
}
}
v___jp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
lean_inc_ref(v_backticks_773_);
v___x_776_ = lean_string_append(v_backticks_773_, v___y_775_);
lean_dec_ref(v___y_775_);
v___x_777_ = lean_string_append(v___x_776_, v_backticks_773_);
lean_dec_ref(v_backticks_773_);
return v___x_777_;
}
v___jp_778_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_780_ = lean_string_append(v___x_779_, v_str_771_);
lean_dec_ref(v_str_771_);
v___x_781_ = lean_string_append(v___x_780_, v___x_779_);
v___y_775_ = v___x_781_;
goto v___jp_774_;
}
v___jp_782_:
{
lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_783_ = lean_string_utf8_byte_size(v_str_771_);
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = lean_nat_dec_le(v___x_784_, v___x_783_);
if (v___x_785_ == 0)
{
v___y_775_ = v_str_771_;
goto v___jp_774_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_786_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0));
v___x_787_ = lean_nat_sub(v___x_783_, v___x_784_);
v___x_788_ = lean_string_memcmp(v_str_771_, v___x_786_, v___x_787_, v___x_772_, v___x_784_);
lean_dec(v___x_787_);
if (v___x_788_ == 0)
{
v___y_775_ = v_str_771_;
goto v___jp_774_;
}
else
{
goto v___jp_778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg(){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___closed__0));
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg___boxed(lean_object* v___dummy_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg();
return v_res_799_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___redArg();
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(lean_object* v_s_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___boxed(lean_object* v_s_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v_s_803_);
lean_dec_ref(v_s_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(lean_object* v_str_805_, lean_object* v___x_806_, lean_object* v___x_807_, lean_object* v_a_808_, lean_object* v_b_809_){
_start:
{
lean_object* v_it_811_; lean_object* v_startInclusive_812_; lean_object* v_endExclusive_813_; 
if (lean_obj_tag(v_a_808_) == 0)
{
lean_object* v_currPos_817_; lean_object* v_searcher_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_841_; 
v_currPos_817_ = lean_ctor_get(v_a_808_, 0);
v_searcher_818_ = lean_ctor_get(v_a_808_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_841_ == 0)
{
v___x_820_ = v_a_808_;
v_isShared_821_ = v_isSharedCheck_841_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_searcher_818_);
lean_inc(v_currPos_817_);
lean_dec(v_a_808_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_841_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v_decide_822_; 
v_decide_822_ = lean_nat_dec_eq(v_searcher_818_, v___x_807_);
if (v_decide_822_ == 0)
{
uint32_t v___x_823_; uint32_t v___x_824_; uint8_t v___x_825_; 
v___x_823_ = 10;
v___x_824_ = lean_string_utf8_get_fast(v_str_805_, v_searcher_818_);
v___x_825_ = lean_uint32_dec_eq(v___x_824_, v___x_823_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = lean_string_utf8_next_fast(v_str_805_, v_searcher_818_);
lean_dec(v_searcher_818_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___x_826_);
v___x_828_ = v___x_820_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_currPos_817_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_826_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v_a_808_ = v___x_828_;
goto _start;
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_slice_834_; lean_object* v_nextIt_836_; 
v___x_831_ = lean_string_utf8_next_fast(v_str_805_, v_searcher_818_);
v___x_832_ = lean_nat_sub(v___x_831_, v_searcher_818_);
v___x_833_ = lean_nat_add(v_searcher_818_, v___x_832_);
lean_dec(v___x_832_);
v_slice_834_ = l_String_Slice_subslice_x21(v___x_806_, v_currPos_817_, v_searcher_818_);
lean_inc(v___x_833_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___x_833_);
lean_ctor_set(v___x_820_, 0, v___x_833_);
v_nextIt_836_ = v___x_820_;
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
v_it_811_ = v_nextIt_836_;
v_startInclusive_812_ = v_startInclusive_837_;
v_endExclusive_813_ = v_endExclusive_838_;
goto v___jp_810_;
}
}
}
else
{
lean_object* v___x_840_; 
lean_del_object(v___x_820_);
lean_dec(v_searcher_818_);
v___x_840_ = lean_box(1);
lean_inc(v___x_807_);
v_it_811_ = v___x_840_;
v_startInclusive_812_ = v_currPos_817_;
v_endExclusive_813_ = v___x_807_;
goto v___jp_810_;
}
}
}
else
{
lean_dec(v___x_807_);
return v_b_809_;
}
v___jp_810_:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_string_utf8_extract_fast(v_str_805_, v_startInclusive_812_, v_endExclusive_813_);
lean_dec(v_endExclusive_813_);
lean_dec(v_startInclusive_812_);
v___x_815_ = lean_array_push(v_b_809_, v___x_814_);
v_a_808_ = v_it_811_;
v_b_809_ = v___x_815_;
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
v___x_852_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0);
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
lean_object* v___x_872_; lean_object* v_fence_873_; lean_object* v___y_875_; lean_object* v_body_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_872_ = lean_unsigned_to_nat(2u);
v_fence_873_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v___x_872_, v_str_871_);
v_body_881_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(v_str_871_);
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_array_get_size(v_body_881_);
v___x_884_ = lean_nat_dec_lt(v___x_882_, v___x_883_);
if (v___x_884_ == 0)
{
v___y_875_ = v_body_881_;
goto v___jp_874_;
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = lean_nat_sub(v___x_883_, v___x_886_);
v___x_888_ = lean_array_get_borrowed(v___x_885_, v_body_881_, v___x_887_);
lean_dec(v___x_887_);
v___x_889_ = lean_string_utf8_byte_size(v___x_888_);
v___x_890_ = lean_nat_dec_eq(v___x_889_, v___x_882_);
if (v___x_890_ == 0)
{
v___y_875_ = v_body_881_;
goto v___jp_874_;
}
else
{
lean_object* v___x_891_; 
v___x_891_ = lean_array_pop(v_body_881_);
v___y_875_ = v___x_891_;
goto v___jp_874_;
}
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
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(lean_object* v_s_892_, lean_object* v_pos_893_){
_start:
{
lean_object* v_str_894_; lean_object* v_startInclusive_895_; lean_object* v_endExclusive_896_; lean_object* v___x_897_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v_decide_908_; 
v_str_894_ = lean_ctor_get(v_s_892_, 0);
v_startInclusive_895_ = lean_ctor_get(v_s_892_, 1);
v_endExclusive_896_ = lean_ctor_get(v_s_892_, 2);
v___x_897_ = lean_nat_add(v_startInclusive_895_, v_pos_893_);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_nat_sub(v_endExclusive_896_, v___x_897_);
v_decide_908_ = lean_nat_dec_eq(v___x_906_, v___x_907_);
lean_dec(v___x_907_);
if (v_decide_908_ == 0)
{
uint32_t v___x_909_; uint32_t v___x_910_; uint8_t v___x_911_; 
v___x_909_ = lean_string_utf8_get_fast(v_str_894_, v___x_897_);
v___x_910_ = 32;
v___x_911_ = lean_uint32_dec_eq(v___x_909_, v___x_910_);
if (v___x_911_ == 0)
{
uint32_t v___x_912_; uint8_t v___x_913_; 
v___x_912_ = 9;
v___x_913_ = lean_uint32_dec_eq(v___x_909_, v___x_912_);
if (v___x_913_ == 0)
{
uint32_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = 13;
v___x_915_ = lean_uint32_dec_eq(v___x_909_, v___x_914_);
if (v___x_915_ == 0)
{
uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 10;
v___x_917_ = lean_uint32_dec_eq(v___x_909_, v___x_916_);
if (v___x_917_ == 0)
{
lean_dec(v___x_897_);
return v_pos_893_;
}
else
{
goto v___jp_898_;
}
}
else
{
goto v___jp_898_;
}
}
else
{
goto v___jp_898_;
}
}
else
{
goto v___jp_898_;
}
}
else
{
lean_dec(v___x_897_);
return v_pos_893_;
}
v___jp_898_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_899_ = lean_string_utf8_next_fast(v_str_894_, v___x_897_);
v___x_900_ = lean_nat_sub(v___x_899_, v___x_897_);
lean_dec(v___x_897_);
v___x_901_ = lean_nat_add(v_pos_893_, v___x_900_);
lean_dec(v___x_900_);
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_nat_add(v_pos_893_, v___x_902_);
v___x_904_ = lean_nat_dec_le(v___x_903_, v___x_901_);
lean_dec(v___x_903_);
if (v___x_904_ == 0)
{
lean_dec(v___x_901_);
return v_pos_893_;
}
else
{
lean_dec(v_pos_893_);
v_pos_893_ = v___x_901_;
goto _start;
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
v___x_921_ = l_Lean_Doc_Inline_empty___redArg();
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
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v_decide_940_; 
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_string_utf8_byte_size(v_string_932_);
lean_inc_ref(v_string_932_);
v___x_938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_938_, 0, v_string_932_);
lean_ctor_set(v___x_938_, 1, v___x_936_);
lean_ctor_set(v___x_938_, 2, v___x_937_);
v___x_939_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_938_, v___x_936_);
lean_dec_ref_known(v___x_938_, 3);
v_decide_940_ = lean_nat_dec_eq(v___x_939_, v___x_937_);
if (v_decide_940_ == 0)
{
lean_object* v_s1_941_; lean_object* v_s2_942_; lean_object* v___x_944_; 
v_s1_941_ = lean_string_utf8_extract_fast(v_string_932_, v___x_936_, v___x_939_);
v_s2_942_ = lean_string_utf8_extract_fast(v_string_932_, v___x_939_, v___x_937_);
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
lean_object* v_str_1031_; lean_object* v_startInclusive_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v_decide_1036_; 
v_str_1031_ = lean_ctor_get(v_s_1029_, 0);
v_startInclusive_1032_ = lean_ctor_get(v_s_1029_, 1);
v___x_1033_ = lean_nat_add(v_startInclusive_1032_, v_pos_1030_);
v___x_1034_ = lean_nat_sub(v___x_1033_, v_startInclusive_1032_);
v___x_1035_ = lean_unsigned_to_nat(0u);
v_decide_1036_ = lean_nat_dec_eq(v___x_1034_, v___x_1035_);
if (v_decide_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1045_; uint32_t v___x_1046_; uint32_t v___x_1047_; uint8_t v___x_1048_; 
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
v___x_1045_ = lean_nat_add(v_startInclusive_1032_, v___x_1040_);
v___x_1046_ = lean_string_utf8_get_fast(v_str_1031_, v___x_1045_);
lean_dec(v___x_1045_);
v___x_1047_ = 32;
v___x_1048_ = lean_uint32_dec_eq(v___x_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
uint32_t v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = 9;
v___x_1050_ = lean_uint32_dec_eq(v___x_1046_, v___x_1049_);
if (v___x_1050_ == 0)
{
uint32_t v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = 13;
v___x_1052_ = lean_uint32_dec_eq(v___x_1046_, v___x_1051_);
if (v___x_1052_ == 0)
{
uint32_t v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = 10;
v___x_1054_ = lean_uint32_dec_eq(v___x_1046_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_dec(v___x_1040_);
return v_pos_1030_;
}
else
{
goto v___jp_1041_;
}
}
else
{
goto v___jp_1041_;
}
}
else
{
goto v___jp_1041_;
}
}
else
{
goto v___jp_1041_;
}
v___jp_1041_:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_nat_add(v___x_1040_, v___x_1038_);
v___x_1043_ = lean_nat_dec_le(v___x_1042_, v_pos_1030_);
lean_dec(v___x_1042_);
if (v___x_1043_ == 0)
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
}
else
{
lean_dec(v___x_1034_);
lean_dec(v___x_1033_);
return v_pos_1030_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(lean_object* v_s_1055_, lean_object* v_pos_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_1055_, v_pos_1056_);
lean_dec_ref(v_s_1055_);
return v_res_1057_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1059_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v___x_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(lean_object* v_xs_1061_){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = lean_array_get_size(v_xs_1061_);
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = lean_nat_dec_eq(v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = lean_unsigned_to_nat(1u);
v___x_1066_ = lean_nat_sub(v___x_1062_, v___x_1065_);
v___x_1067_ = lean_array_fget(v_xs_1061_, v___x_1066_);
lean_dec(v___x_1066_);
switch(lean_obj_tag(v___x_1067_))
{
case 0:
{
lean_object* v_string_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1098_; 
v_string_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1098_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_string_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1098_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v_decide_1075_; 
v___x_1072_ = lean_string_utf8_byte_size(v_string_1068_);
lean_inc_ref(v_string_1068_);
v___x_1073_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1073_, 0, v_string_1068_);
lean_ctor_set(v___x_1073_, 1, v___x_1063_);
lean_ctor_set(v___x_1073_, 2, v___x_1072_);
v___x_1074_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_1073_, v___x_1063_);
v_decide_1075_ = lean_nat_dec_eq(v___x_1074_, v___x_1072_);
lean_dec(v___x_1074_);
if (v_decide_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1076_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_1073_, v___x_1072_);
lean_dec_ref_known(v___x_1073_, 3);
v___x_1077_ = lean_array_pop(v_xs_1061_);
v___x_1078_ = lean_string_utf8_extract_fast(v_string_1068_, v___x_1063_, v___x_1076_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1078_);
v___x_1080_ = v___x_1070_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1081_ = lean_array_push(v___x_1077_, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
v___x_1083_ = lean_string_utf8_extract_fast(v_string_1068_, v___x_1076_, v___x_1072_);
lean_dec(v___x_1076_);
lean_dec_ref(v_string_1068_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
return v___x_1084_;
}
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v_fst_1088_; lean_object* v_snd_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref_known(v___x_1073_, 3);
lean_del_object(v___x_1070_);
v___x_1086_ = lean_array_pop(v_xs_1061_);
v___x_1087_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1086_);
v_fst_1088_ = lean_ctor_get(v___x_1087_, 0);
v_snd_1089_ = lean_ctor_get(v___x_1087_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1091_ = v___x_1087_;
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_snd_1089_);
lean_inc(v_fst_1088_);
lean_dec(v___x_1087_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = lean_string_append(v_snd_1089_, v_string_1068_);
lean_dec_ref(v_string_1068_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v___x_1093_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_fst_1088_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
case 9:
{
lean_object* v_content_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_content_1099_ = lean_ctor_get(v___x_1067_, 0);
lean_inc_ref(v_content_1099_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1100_ = lean_array_pop(v_xs_1061_);
v___x_1101_ = l_Array_append___redArg(v___x_1100_, v_content_1099_);
lean_dec_ref(v_content_1099_);
v_xs_1061_ = v___x_1101_;
goto _start;
}
default: 
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v___x_1067_);
v___x_1103_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_xs_1061_);
v___x_1104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
return v___x_1105_;
}
}
}
else
{
lean_object* v___x_1106_; 
lean_dec_ref(v_xs_1061_);
v___x_1106_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(lean_object* v_i_1107_, lean_object* v_xs_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_xs_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(lean_object* v_inline_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_mk_empty_array_with_capacity(v___x_1111_);
v___x_1113_ = lean_array_push(v___x_1112_, v_inline_1110_);
v___x_1114_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(lean_object* v_i_1115_, lean_object* v_inline_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(lean_object* v_inline_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v_fst_1120_; lean_object* v_snd_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1129_; 
v___x_1119_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_1118_);
v_fst_1120_ = lean_ctor_get(v___x_1119_, 0);
v_snd_1121_ = lean_ctor_get(v___x_1119_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1123_ = v___x_1119_;
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_snd_1121_);
lean_inc(v_fst_1120_);
lean_dec(v___x_1119_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v___x_1125_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_fst_1120_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object* v_i_1130_, lean_object* v_inline_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_instMonadEIO___redArg();
return v___x_1133_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0);
v___x_1135_ = l_StateRefT_x27_instMonad___redArg(v___x_1134_);
return v___x_1135_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1164_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13));
v___x_1165_ = lean_unsigned_to_nat(3u);
v___x_1166_ = lean_mk_empty_array_with_capacity(v___x_1165_);
v___x_1167_ = lean_array_push(v___x_1166_, v___x_1164_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed(lean_object* v_inst_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1170_, v_x_1171_, v_x_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(lean_object* v_inst_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_pieces_1186_; lean_object* v_pieces_1190_; lean_object* v___x_1193_; lean_object* v_toApplicative_1194_; lean_object* v_toFunctor_1195_; lean_object* v_toSeq_1196_; lean_object* v_toSeqLeft_1197_; lean_object* v_toSeqRight_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1193_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1194_ = lean_ctor_get(v___x_1193_, 0);
v_toFunctor_1195_ = lean_ctor_get(v_toApplicative_1194_, 0);
v_toSeq_1196_ = lean_ctor_get(v_toApplicative_1194_, 2);
v_toSeqLeft_1197_ = lean_ctor_get(v_toApplicative_1194_, 3);
v_toSeqRight_1198_ = lean_ctor_get(v_toApplicative_1194_, 4);
v___f_1199_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1200_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1195_, 2);
v___f_1201_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1201_, 0, v_toFunctor_1195_);
v___f_1202_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1202_, 0, v_toFunctor_1195_);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___f_1201_);
lean_ctor_set(v___x_1203_, 1, v___f_1202_);
lean_inc(v_toSeqRight_1198_);
v___f_1204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1204_, 0, v_toSeqRight_1198_);
lean_inc(v_toSeqLeft_1197_);
v___f_1205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1205_, 0, v_toSeqLeft_1197_);
lean_inc(v_toSeq_1196_);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toSeq_1196_);
v___x_1207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1203_);
lean_ctor_set(v___x_1207_, 1, v___f_1199_);
lean_ctor_set(v___x_1207_, 2, v___f_1206_);
lean_ctor_set(v___x_1207_, 3, v___f_1205_);
lean_ctor_set(v___x_1207_, 4, v___f_1204_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___f_1200_);
v___x_1209_ = l_StateRefT_x27_instMonad___redArg(v___x_1208_);
switch(lean_obj_tag(v_x_1180_))
{
case 0:
{
lean_object* v_string_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec_ref(v___x_1209_);
lean_dec_ref(v_x_1179_);
lean_dec_ref(v_inst_1178_);
v_string_1210_ = lean_ctor_get(v_x_1180_, 0);
lean_inc_ref(v_string_1210_);
lean_dec_ref_known(v_x_1180_, 1);
v___x_1211_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1210_);
lean_dec_ref(v_string_1210_);
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_mk_empty_array_with_capacity(v___x_1212_);
v___x_1214_ = lean_array_push(v___x_1213_, v___x_1211_);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
case 1:
{
lean_object* v_content_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v___x_1209_);
v_content_1216_ = lean_ctor_get(v_x_1180_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_x_1180_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1218_ = v_x_1180_;
v_isShared_1219_ = v_isSharedCheck_1267_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_content_1216_);
lean_dec(v_x_1180_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1267_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set_tag(v___x_1218_, 9);
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_content_1216_);
v___x_1221_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v_snd_1223_; lean_object* v_fst_1224_; lean_object* v_fst_1225_; lean_object* v_snd_1226_; lean_object* v_pieces_1228_; uint8_t v_inEmph_1236_; uint8_t v_inBold_1237_; uint8_t v_inLink_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1265_; 
v___x_1222_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1221_);
v_snd_1223_ = lean_ctor_get(v___x_1222_, 1);
lean_inc(v_snd_1223_);
v_fst_1224_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_fst_1224_);
lean_dec_ref(v___x_1222_);
v_fst_1225_ = lean_ctor_get(v_snd_1223_, 0);
lean_inc(v_fst_1225_);
v_snd_1226_ = lean_ctor_get(v_snd_1223_, 1);
lean_inc(v_snd_1226_);
lean_dec(v_snd_1223_);
v_inEmph_1236_ = lean_ctor_get_uint8(v_x_1179_, 0);
v_inBold_1237_ = lean_ctor_get_uint8(v_x_1179_, 1);
v_inLink_1238_ = lean_ctor_get_uint8(v_x_1179_, 2);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_x_1179_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1240_ = v_x_1179_;
v_isShared_1241_ = v_isSharedCheck_1265_;
goto v_resetjp_1239_;
}
else
{
lean_dec(v_x_1179_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1265_;
goto v_resetjp_1239_;
}
v___jp_1227_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1229_ = lean_string_utf8_byte_size(v_snd_1226_);
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = lean_nat_dec_eq(v___x_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_mk_empty_array_with_capacity(v___x_1232_);
v___x_1234_ = lean_array_push(v___x_1233_, v_snd_1226_);
v___x_1235_ = lean_array_push(v_pieces_1228_, v___x_1234_);
v_pieces_1190_ = v___x_1235_;
goto v___jp_1189_;
}
else
{
lean_dec(v_snd_1226_);
v_pieces_1190_ = v_pieces_1228_;
goto v___jp_1189_;
}
}
v_resetjp_1239_:
{
uint8_t v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = 1;
if (v_isShared_1241_ == 0)
{
v___x_1244_ = v___x_1240_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1264_, 1, v_inBold_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1264_, 2, v_inLink_1238_);
v___x_1244_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; 
lean_ctor_set_uint8(v___x_1244_, 0, v___x_1242_);
v___x_1245_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1178_, v___x_1244_, v_fst_1225_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v_pieces_1248_; lean_object* v_pieces_1253_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1258_ = lean_string_utf8_byte_size(v_fst_1224_);
v___x_1259_ = lean_nat_dec_eq(v___x_1258_, v___x_1256_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_mk_empty_array_with_capacity(v___x_1260_);
v___x_1262_ = lean_array_push(v___x_1261_, v_fst_1224_);
v___x_1263_ = lean_array_push(v___x_1257_, v___x_1262_);
v_pieces_1253_ = v___x_1263_;
goto v___jp_1252_;
}
else
{
lean_dec(v_fst_1224_);
v_pieces_1253_ = v___x_1257_;
goto v___jp_1252_;
}
v___jp_1247_:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_array_push(v_pieces_1248_, v_a_1246_);
if (v_inEmph_1236_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1251_ = lean_array_push(v___x_1249_, v___x_1250_);
v_pieces_1228_ = v___x_1251_;
goto v___jp_1227_;
}
else
{
v_pieces_1228_ = v___x_1249_;
goto v___jp_1227_;
}
}
v___jp_1252_:
{
if (v_inEmph_1236_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5));
v___x_1255_ = lean_array_push(v_pieces_1253_, v___x_1254_);
v_pieces_1248_ = v___x_1255_;
goto v___jp_1247_;
}
else
{
v_pieces_1248_ = v_pieces_1253_;
goto v___jp_1247_;
}
}
}
else
{
lean_dec(v_snd_1226_);
lean_dec(v_fst_1224_);
return v___x_1245_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref(v___x_1209_);
v_content_1268_ = lean_ctor_get(v_x_1180_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_x_1180_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1270_ = v_x_1180_;
v_isShared_1271_ = v_isSharedCheck_1319_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_content_1268_);
lean_dec(v_x_1180_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1319_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 9);
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_content_1268_);
v___x_1273_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; lean_object* v_snd_1275_; lean_object* v_fst_1276_; lean_object* v_fst_1277_; lean_object* v_snd_1278_; lean_object* v_pieces_1280_; uint8_t v_inEmph_1288_; uint8_t v_inBold_1289_; uint8_t v_inLink_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1317_; 
v___x_1274_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_1273_);
v_snd_1275_ = lean_ctor_get(v___x_1274_, 1);
lean_inc(v_snd_1275_);
v_fst_1276_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_fst_1276_);
lean_dec_ref(v___x_1274_);
v_fst_1277_ = lean_ctor_get(v_snd_1275_, 0);
lean_inc(v_fst_1277_);
v_snd_1278_ = lean_ctor_get(v_snd_1275_, 1);
lean_inc(v_snd_1278_);
lean_dec(v_snd_1275_);
v_inEmph_1288_ = lean_ctor_get_uint8(v_x_1179_, 0);
v_inBold_1289_ = lean_ctor_get_uint8(v_x_1179_, 1);
v_inLink_1290_ = lean_ctor_get_uint8(v_x_1179_, 2);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_x_1179_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1292_ = v_x_1179_;
v_isShared_1293_ = v_isSharedCheck_1317_;
goto v_resetjp_1291_;
}
else
{
lean_dec(v_x_1179_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1317_;
goto v_resetjp_1291_;
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1281_ = lean_string_utf8_byte_size(v_snd_1278_);
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = lean_nat_dec_eq(v___x_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = lean_unsigned_to_nat(1u);
v___x_1285_ = lean_mk_empty_array_with_capacity(v___x_1284_);
v___x_1286_ = lean_array_push(v___x_1285_, v_snd_1278_);
v___x_1287_ = lean_array_push(v_pieces_1280_, v___x_1286_);
v_pieces_1186_ = v___x_1287_;
goto v___jp_1185_;
}
else
{
lean_dec(v_snd_1278_);
v_pieces_1186_ = v_pieces_1280_;
goto v___jp_1185_;
}
}
v_resetjp_1291_:
{
uint8_t v___x_1294_; lean_object* v___x_1296_; 
v___x_1294_ = 1;
if (v_isShared_1293_ == 0)
{
v___x_1296_ = v___x_1292_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1316_, 0, v_inEmph_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1316_, 2, v_inLink_1290_);
v___x_1296_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; 
lean_ctor_set_uint8(v___x_1296_, 1, v___x_1294_);
v___x_1297_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1178_, v___x_1296_, v_fst_1277_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v_pieces_1300_; lean_object* v_pieces_1305_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1310_ = lean_string_utf8_byte_size(v_fst_1276_);
v___x_1311_ = lean_nat_dec_eq(v___x_1310_, v___x_1308_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = lean_unsigned_to_nat(1u);
v___x_1313_ = lean_mk_empty_array_with_capacity(v___x_1312_);
v___x_1314_ = lean_array_push(v___x_1313_, v_fst_1276_);
v___x_1315_ = lean_array_push(v___x_1309_, v___x_1314_);
v_pieces_1305_ = v___x_1315_;
goto v___jp_1304_;
}
else
{
lean_dec(v_fst_1276_);
v_pieces_1305_ = v___x_1309_;
goto v___jp_1304_;
}
v___jp_1299_:
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_array_push(v_pieces_1300_, v_a_1298_);
if (v_inBold_1289_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1303_ = lean_array_push(v___x_1301_, v___x_1302_);
v_pieces_1280_ = v___x_1303_;
goto v___jp_1279_;
}
else
{
v_pieces_1280_ = v___x_1301_;
goto v___jp_1279_;
}
}
v___jp_1304_:
{
if (v_inBold_1289_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8));
v___x_1307_ = lean_array_push(v_pieces_1305_, v___x_1306_);
v_pieces_1300_ = v___x_1307_;
goto v___jp_1299_;
}
else
{
v_pieces_1300_ = v_pieces_1305_;
goto v___jp_1299_;
}
}
}
else
{
lean_dec(v_snd_1278_);
lean_dec(v_fst_1276_);
return v___x_1297_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec_ref(v___x_1209_);
lean_dec_ref(v_x_1179_);
lean_dec_ref(v_inst_1178_);
v_string_1320_ = lean_ctor_get(v_x_1180_, 0);
lean_inc_ref(v_string_1320_);
lean_dec_ref_known(v_x_1180_, 1);
v___x_1321_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1320_);
v___x_1322_ = lean_unsigned_to_nat(1u);
v___x_1323_ = lean_mk_empty_array_with_capacity(v___x_1322_);
v___x_1324_ = lean_array_push(v___x_1323_, v___x_1321_);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
case 4:
{
uint8_t v_mode_1326_; 
lean_dec_ref(v___x_1209_);
lean_dec_ref(v_x_1179_);
lean_dec_ref(v_inst_1178_);
v_mode_1326_ = lean_ctor_get_uint8(v_x_1180_, sizeof(void*)*1);
if (v_mode_1326_ == 0)
{
lean_object* v_string_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_string_1327_ = lean_ctor_get(v_x_1180_, 0);
lean_inc_ref(v_string_1327_);
lean_dec_ref_known(v_x_1180_, 1);
v___x_1328_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9));
v___x_1329_ = lean_string_append(v___x_1328_, v_string_1327_);
lean_dec_ref(v_string_1327_);
v___x_1330_ = lean_string_append(v___x_1329_, v___x_1328_);
v___x_1331_ = lean_unsigned_to_nat(1u);
v___x_1332_ = lean_mk_empty_array_with_capacity(v___x_1331_);
v___x_1333_ = lean_array_push(v___x_1332_, v___x_1330_);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
else
{
lean_object* v_string_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_string_1335_ = lean_ctor_get(v_x_1180_, 0);
lean_inc_ref(v_string_1335_);
lean_dec_ref_known(v_x_1180_, 1);
v___x_1336_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10));
v___x_1337_ = lean_string_append(v___x_1336_, v_string_1335_);
lean_dec_ref(v_string_1335_);
v___x_1338_ = lean_string_append(v___x_1337_, v___x_1336_);
v___x_1339_ = lean_unsigned_to_nat(1u);
v___x_1340_ = lean_mk_empty_array_with_capacity(v___x_1339_);
v___x_1341_ = lean_array_push(v___x_1340_, v___x_1338_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
}
case 5:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec_ref_known(v_x_1180_, 1);
lean_dec_ref(v___x_1209_);
lean_dec_ref(v_x_1179_);
lean_dec_ref(v_inst_1178_);
v___x_1343_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11));
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
case 6:
{
uint8_t v_inLink_1345_; 
v_inLink_1345_ = lean_ctor_get_uint8(v_x_1179_, 2);
if (v_inLink_1345_ == 0)
{
lean_object* v_content_1346_; lean_object* v_url_1347_; uint8_t v_inEmph_1348_; uint8_t v_inBold_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v___x_1209_);
v_content_1346_ = lean_ctor_get(v_x_1180_, 0);
lean_inc_ref(v_content_1346_);
v_url_1347_ = lean_ctor_get(v_x_1180_, 1);
lean_inc_ref(v_url_1347_);
lean_dec_ref_known(v_x_1180_, 2);
v_inEmph_1348_ = lean_ctor_get_uint8(v_x_1179_, 0);
v_inBold_1349_ = lean_ctor_get_uint8(v_x_1179_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1179_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1351_ = v_x_1179_;
v_isShared_1352_ = v_isSharedCheck_1378_;
goto v_resetjp_1350_;
}
else
{
lean_dec(v_x_1179_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1378_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
uint8_t v___x_1353_; lean_object* v___x_1355_; 
v___x_1353_ = 1;
if (v_isShared_1352_ == 0)
{
v___x_1355_ = v___x_1351_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1377_, 0, v_inEmph_1348_);
lean_ctor_set_uint8(v_reuseFailAlloc_1377_, 1, v_inBold_1349_);
v___x_1355_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_ctor_set_uint8(v___x_1355_, 2, v___x_1353_);
v___x_1356_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_content_1346_);
v___x_1357_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1178_, v___x_1355_, v___x_1356_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1376_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1376_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1376_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_mk_empty_array_with_capacity(v___x_1362_);
v___x_1364_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1365_ = lean_string_append(v___x_1364_, v_url_1347_);
lean_dec_ref(v_url_1347_);
v___x_1366_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1367_ = lean_string_append(v___x_1365_, v___x_1366_);
v___x_1368_ = lean_array_push(v___x_1363_, v___x_1367_);
v___x_1369_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16);
v___x_1370_ = lean_array_push(v___x_1369_, v_a_1358_);
v___x_1371_ = lean_array_push(v___x_1370_, v___x_1368_);
v___x_1372_ = l_Lean_Doc_joinInlines(v___x_1371_);
lean_dec_ref(v___x_1371_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1372_);
v___x_1374_ = v___x_1360_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
lean_dec_ref(v_url_1347_);
return v___x_1357_;
}
}
}
}
else
{
lean_object* v_content_1379_; lean_object* v___x_1380_; size_t v_sz_1381_; size_t v___x_1382_; lean_object* v___x_4024__overap_1383_; lean_object* v___x_1384_; 
v_content_1379_ = lean_ctor_get(v_x_1180_, 0);
lean_inc_ref(v_content_1379_);
lean_dec_ref_known(v_x_1180_, 2);
v___x_1380_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1380_, 0, v_inst_1178_);
lean_closure_set(v___x_1380_, 1, v_x_1179_);
v_sz_1381_ = lean_array_size(v_content_1379_);
v___x_1382_ = ((size_t)0ULL);
v___x_4024__overap_1383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1209_, v___x_1380_, v_sz_1381_, v___x_1382_, v_content_1379_);
lean_inc(v_a_1183_);
lean_inc_ref(v_a_1182_);
lean_inc(v_a_1181_);
v___x_1384_ = lean_apply_4(v___x_4024__overap_1383_, v_a_1181_, v_a_1182_, v_a_1183_, lean_box(0));
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1393_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1393_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1393_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1389_ = l_Lean_Doc_joinInlines(v_a_1385_);
lean_dec(v_a_1385_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1389_);
v___x_1391_ = v___x_1387_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
v_a_1394_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1384_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1384_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
case 7:
{
lean_object* v_name_1402_; lean_object* v_content_1403_; lean_object* v___x_1404_; size_t v_sz_1405_; size_t v___x_1406_; lean_object* v___x_4027__overap_1407_; lean_object* v___x_1408_; 
v_name_1402_ = lean_ctor_get(v_x_1180_, 0);
lean_inc_ref(v_name_1402_);
v_content_1403_ = lean_ctor_get(v_x_1180_, 1);
lean_inc_ref(v_content_1403_);
lean_dec_ref_known(v_x_1180_, 2);
v___x_1404_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1404_, 0, v_inst_1178_);
lean_closure_set(v___x_1404_, 1, v_x_1179_);
v_sz_1405_ = lean_array_size(v_content_1403_);
v___x_1406_ = ((size_t)0ULL);
v___x_4027__overap_1407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1209_, v___x_1404_, v_sz_1405_, v___x_1406_, v_content_1403_);
lean_inc(v_a_1183_);
lean_inc_ref(v_a_1182_);
lean_inc(v_a_1181_);
v___x_1408_ = lean_apply_4(v___x_4027__overap_1407_, v_a_1181_, v_a_1182_, v_a_1183_, lean_box(0));
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1408_, 1);
v___x_1410_ = ((lean_object*)(l_Lean_Doc_MarkdownM_run_x27___closed__1));
v___x_1411_ = l_Lean_Doc_joinInlines(v_a_1409_);
lean_dec(v_a_1409_);
v___x_1412_ = lean_array_to_list(v___x_1411_);
v___x_1413_ = l_String_intercalate(v___x_1410_, v___x_1412_);
lean_inc_ref(v_name_1402_);
v___x_1414_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote___redArg(v_name_1402_, v___x_1413_, v_a_1181_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1428_; 
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v___x_1414_, 0);
lean_dec(v_unused_1429_);
v___x_1416_ = v___x_1414_;
v_isShared_1417_ = v_isSharedCheck_1428_;
goto v_resetjp_1415_;
}
else
{
lean_dec(v___x_1414_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1428_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1418_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0));
v___x_1419_ = lean_string_append(v___x_1418_, v_name_1402_);
lean_dec_ref(v_name_1402_);
v___x_1420_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17));
v___x_1421_ = lean_string_append(v___x_1419_, v___x_1420_);
v___x_1422_ = lean_unsigned_to_nat(1u);
v___x_1423_ = lean_mk_empty_array_with_capacity(v___x_1422_);
v___x_1424_ = lean_array_push(v___x_1423_, v___x_1421_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1424_);
v___x_1426_ = v___x_1416_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v_name_1402_);
v_a_1430_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1414_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1414_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v_name_1402_);
v_a_1438_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1408_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1408_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
case 8:
{
lean_object* v_alt_1446_; lean_object* v_url_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v___x_1209_);
lean_dec_ref(v_x_1179_);
lean_dec_ref(v_inst_1178_);
v_alt_1446_ = lean_ctor_get(v_x_1180_, 0);
lean_inc_ref(v_alt_1446_);
v_url_1447_ = lean_ctor_get(v_x_1180_, 1);
lean_inc_ref(v_url_1447_);
lean_dec_ref_known(v_x_1180_, 2);
v___x_1448_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18));
v___x_1449_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1446_);
lean_dec_ref(v_alt_1446_);
v___x_1450_ = lean_string_append(v___x_1448_, v___x_1449_);
lean_dec_ref(v___x_1449_);
v___x_1451_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14));
v___x_1452_ = lean_string_append(v___x_1450_, v___x_1451_);
v___x_1453_ = lean_string_append(v___x_1452_, v_url_1447_);
lean_dec_ref(v_url_1447_);
v___x_1454_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15));
v___x_1455_ = lean_string_append(v___x_1453_, v___x_1454_);
v___x_1456_ = lean_unsigned_to_nat(1u);
v___x_1457_ = lean_mk_empty_array_with_capacity(v___x_1456_);
v___x_1458_ = lean_array_push(v___x_1457_, v___x_1455_);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
case 9:
{
lean_object* v_content_1460_; lean_object* v___x_1461_; size_t v_sz_1462_; size_t v___x_1463_; lean_object* v___x_4030__overap_1464_; lean_object* v___x_1465_; 
v_content_1460_ = lean_ctor_get(v_x_1180_, 0);
lean_inc_ref(v_content_1460_);
lean_dec_ref_known(v_x_1180_, 1);
v___x_1461_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1461_, 0, v_inst_1178_);
lean_closure_set(v___x_1461_, 1, v_x_1179_);
v_sz_1462_ = lean_array_size(v_content_1460_);
v___x_1463_ = ((size_t)0ULL);
v___x_4030__overap_1464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1209_, v___x_1461_, v_sz_1462_, v___x_1463_, v_content_1460_);
lean_inc(v_a_1183_);
lean_inc_ref(v_a_1182_);
lean_inc(v_a_1181_);
v___x_1465_ = lean_apply_4(v___x_4030__overap_1464_, v_a_1181_, v_a_1182_, v_a_1183_, lean_box(0));
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1474_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = l_Lean_Doc_joinInlines(v_a_1466_);
lean_dec(v_a_1466_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
v_a_1475_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1465_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1465_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
default: 
{
lean_object* v_container_1483_; lean_object* v_content_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_dec_ref(v___x_1209_);
v_container_1483_ = lean_ctor_get(v_x_1180_, 0);
lean_inc(v_container_1483_);
v_content_1484_ = lean_ctor_get(v_x_1180_, 1);
lean_inc_ref(v_content_1484_);
lean_dec_ref_known(v_x_1180_, 2);
lean_inc_ref(v_inst_1178_);
v___x_1485_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1485_, 0, v_inst_1178_);
lean_closure_set(v___x_1485_, 1, v_x_1179_);
lean_inc(v_a_1183_);
lean_inc_ref(v_a_1182_);
lean_inc(v_a_1181_);
v___x_1486_ = lean_apply_7(v_inst_1178_, v___x_1485_, v_container_1483_, v_content_1484_, v_a_1181_, v_a_1182_, v_a_1183_, lean_box(0));
return v___x_1486_;
}
}
v___jp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = l_Lean_Doc_joinInlines(v_pieces_1186_);
lean_dec_ref(v_pieces_1186_);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
v___jp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = l_Lean_Doc_joinInlines(v_pieces_1190_);
lean_dec_ref(v_pieces_1190_);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object* v_i_1487_, lean_object* v_inst_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1488_, v_x_1489_, v_x_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed(lean_object* v_i_1496_, lean_object* v_inst_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(v_i_1496_, v_inst_1497_, v_x_1498_, v_x_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(lean_object* v_inst_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1512_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1505_, v___x_1511_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg___boxed(lean_object* v_inst_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(v_inst_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(lean_object* v_i_1520_, lean_object* v_inst_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_1528_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1521_, v___x_1527_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed(lean_object* v_i_1529_, lean_object* v_inst_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(v_i_1529_, v_inst_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(lean_object* v_inst_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1538_, 0, lean_box(0));
lean_closure_set(v___x_1538_, 1, v_inst_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(lean_object* v_i_1539_, lean_object* v_inst_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_1541_, 0, lean_box(0));
lean_closure_set(v___x_1541_, 1, v_inst_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(uint32_t v___x_1542_, lean_object* v_s_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_string_push(v_s_1543_, v___x_1542_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(lean_object* v___x_1545_, lean_object* v_s_1546_){
_start:
{
uint32_t v___x_2520__boxed_1547_; lean_object* v_res_1548_; 
v___x_2520__boxed_1547_ = lean_unbox_uint32(v___x_1545_);
lean_dec(v___x_1545_);
v_res_1548_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(v___x_2520__boxed_1547_, v_s_1546_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed(lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v___x_1553_, lean_object* v_item_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(v_inst_1551_, v_inst_1552_, v___x_1553_, v_item_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
return v_res_1559_;
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___f_1562_; 
v___x_1561_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
v___f_1562_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1562_, 0, v___x_1561_);
return v___f_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(lean_object* v_inst_1563_, lean_object* v_inst_1564_, lean_object* v___x_1565_, lean_object* v___x_1566_, lean_object* v_a_1567_, lean_object* v_x_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_fst_1574_; lean_object* v_snd_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1615_; 
v_fst_1574_ = lean_ctor_get(v___y_1569_, 0);
v_snd_1575_ = lean_ctor_get(v___y_1569_, 1);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___y_1569_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1577_ = v___y_1569_;
v_isShared_1578_ = v_isSharedCheck_1615_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_snd_1575_);
lean_inc(v_fst_1574_);
lean_dec(v___y_1569_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1615_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___f_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; size_t v_sz_1587_; size_t v___x_1588_; lean_object* v___x_2461__overap_1589_; lean_object* v___x_1590_; 
lean_inc(v_snd_1575_);
v___x_1579_ = l_Nat_reprFast(v_snd_1575_);
v___x_1580_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_1581_ = lean_string_append(v___x_1579_, v___x_1580_);
v___x_1582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_1583_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1);
v___x_1584_ = lean_string_utf8_byte_size(v___x_1581_);
v___x_1585_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_1583_, v___x_1584_, v___x_1582_);
v___x_1586_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1586_, 0, v_inst_1563_);
lean_closure_set(v___x_1586_, 1, v_inst_1564_);
v_sz_1587_ = lean_array_size(v_a_1567_);
v___x_1588_ = ((size_t)0ULL);
v___x_2461__overap_1589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1565_, v___x_1586_, v_sz_1587_, v___x_1588_, v_a_1567_);
lean_inc(v___y_1572_);
lean_inc_ref(v___y_1571_);
lean_inc(v___y_1570_);
v___x_1590_ = lean_apply_4(v___x_2461__overap_1589_, v___y_1570_, v___y_1571_, v___y_1572_, lean_box(0));
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1606_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1606_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1606_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1595_ = l_Lean_Doc_joinBlocks(v_a_1591_);
lean_dec(v_a_1591_);
v___x_1596_ = l_Lean_Doc_prefixListLines(v___x_1581_, v___x_1585_, v___x_1595_);
v___x_1597_ = lean_array_push(v_fst_1574_, v___x_1596_);
v___x_1598_ = lean_nat_add(v_snd_1575_, v___x_1566_);
lean_dec(v_snd_1575_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 1, v___x_1598_);
lean_ctor_set(v___x_1577_, 0, v___x_1597_);
v___x_1600_ = v___x_1577_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1601_);
v___x_1603_ = v___x_1593_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
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
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v___x_1585_);
lean_dec_ref(v___x_1581_);
lean_del_object(v___x_1577_);
lean_dec(v_snd_1575_);
lean_dec(v_fst_1574_);
v_a_1607_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1590_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1590_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(lean_object* v_inst_1616_, lean_object* v_inst_1617_, lean_object* v___x_1618_, lean_object* v___x_1619_, lean_object* v_a_1620_, lean_object* v_x_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(v_inst_1616_, v_inst_1617_, v___x_1618_, v___x_1619_, v_a_1620_, v_x_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec(v___x_1619_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v___x_1635_, lean_object* v_item_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; lean_object* v_term_1642_; lean_object* v_desc_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1641_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_1642_ = lean_ctor_get(v_item_1636_, 0);
lean_inc_ref(v_term_1642_);
v_desc_1643_ = lean_ctor_get(v_item_1636_, 1);
lean_inc_ref(v_desc_1643_);
lean_dec_ref(v_item_1636_);
v___x_1644_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1644_, 0, v_term_1642_);
lean_inc_ref(v_inst_1633_);
v___x_1645_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1633_, v___x_1641_, v___x_1644_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; size_t v_sz_1648_; size_t v___x_1649_; lean_object* v___x_2489__overap_1650_; lean_object* v___x_1651_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1647_, 0, v_inst_1633_);
lean_closure_set(v___x_1647_, 1, v_inst_1634_);
v_sz_1648_ = lean_array_size(v_desc_1643_);
v___x_1649_ = ((size_t)0ULL);
lean_inc_ref(v_desc_1643_);
v___x_2489__overap_1650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1635_, v___x_1647_, v_sz_1648_, v___x_1649_, v_desc_1643_);
lean_inc(v___y_1639_);
lean_inc_ref(v___y_1638_);
lean_inc(v___y_1637_);
v___x_1651_ = lean_apply_4(v___x_2489__overap_1650_, v___y_1637_, v___y_1638_, v___y_1639_, lean_box(0));
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1679_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1679_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1679_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___y_1657_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1664_ = lean_unsigned_to_nat(1u);
v___x_1665_ = lean_mk_empty_array_with_capacity(v___x_1664_);
v___x_1666_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_1667_ = lean_unsigned_to_nat(2u);
v___x_1668_ = lean_mk_empty_array_with_capacity(v___x_1667_);
v___x_1669_ = lean_array_push(v___x_1668_, v_a_1646_);
v___x_1670_ = lean_array_push(v___x_1669_, v___x_1666_);
v___x_1671_ = l_Lean_Doc_joinInlines(v___x_1670_);
lean_dec_ref(v___x_1670_);
v___x_1672_ = lean_array_get_size(v_desc_1643_);
lean_dec_ref(v_desc_1643_);
v___x_1673_ = lean_nat_dec_le(v___x_1672_, v___x_1664_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_array_push(v___x_1665_, v___x_1671_);
v___x_1675_ = l_Array_append___redArg(v___x_1674_, v_a_1652_);
lean_dec(v_a_1652_);
v___x_1676_ = l_Lean_Doc_joinBlocks(v___x_1675_);
lean_dec_ref(v___x_1675_);
v___y_1657_ = v___x_1676_;
goto v___jp_1656_;
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec_ref(v___x_1665_);
v___x_1677_ = l_Lean_Doc_joinBlocks(v_a_1652_);
lean_dec(v_a_1652_);
v___x_1678_ = l_Array_append___redArg(v___x_1671_, v___x_1677_);
lean_dec_ref(v___x_1677_);
v___y_1657_ = v___x_1678_;
goto v___jp_1656_;
}
v___jp_1656_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1658_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1659_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1660_ = l_Lean_Doc_prefixListLines(v___x_1658_, v___x_1659_, v___y_1657_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1660_);
v___x_1662_ = v___x_1654_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v_a_1646_);
lean_dec_ref(v_desc_1643_);
v_a_1680_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1651_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1651_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_dec_ref(v_desc_1643_);
lean_dec_ref(v___x_1635_);
lean_dec_ref(v_inst_1634_);
lean_dec_ref(v_inst_1633_);
return v___x_1645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed(lean_object* v_inst_1688_, lean_object* v_inst_1689_, lean_object* v___x_1690_, lean_object* v_item_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(v_inst_1688_, v_inst_1689_, v___x_1690_, v_item_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_x_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1705_; lean_object* v_toApplicative_1706_; lean_object* v_toFunctor_1707_; lean_object* v_toSeq_1708_; lean_object* v_toSeqLeft_1709_; lean_object* v_toSeqRight_1710_; lean_object* v___f_1711_; lean_object* v___f_1712_; lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___x_1715_; lean_object* v___f_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1705_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_1706_ = lean_ctor_get(v___x_1705_, 0);
v_toFunctor_1707_ = lean_ctor_get(v_toApplicative_1706_, 0);
v_toSeq_1708_ = lean_ctor_get(v_toApplicative_1706_, 2);
v_toSeqLeft_1709_ = lean_ctor_get(v_toApplicative_1706_, 3);
v_toSeqRight_1710_ = lean_ctor_get(v_toApplicative_1706_, 4);
v___f_1711_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_1712_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1707_, 2);
v___f_1713_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1713_, 0, v_toFunctor_1707_);
v___f_1714_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1714_, 0, v_toFunctor_1707_);
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___f_1713_);
lean_ctor_set(v___x_1715_, 1, v___f_1714_);
lean_inc(v_toSeqRight_1710_);
v___f_1716_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1716_, 0, v_toSeqRight_1710_);
lean_inc(v_toSeqLeft_1709_);
v___f_1717_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1717_, 0, v_toSeqLeft_1709_);
lean_inc(v_toSeq_1708_);
v___f_1718_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1718_, 0, v_toSeq_1708_);
v___x_1719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1715_);
lean_ctor_set(v___x_1719_, 1, v___f_1711_);
lean_ctor_set(v___x_1719_, 2, v___f_1718_);
lean_ctor_set(v___x_1719_, 3, v___f_1717_);
lean_ctor_set(v___x_1719_, 4, v___f_1716_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
lean_ctor_set(v___x_1720_, 1, v___f_1712_);
v___x_1721_ = l_StateRefT_x27_instMonad___redArg(v___x_1720_);
switch(lean_obj_tag(v_x_1700_))
{
case 0:
{
lean_object* v_contents_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v___x_1721_);
lean_dec_ref(v_inst_1699_);
v_contents_1722_ = lean_ctor_get(v_x_1700_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_x_1700_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1724_ = v_x_1700_;
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_contents_1722_);
lean_dec(v_x_1700_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 9);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_contents_1722_);
v___x_1728_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; 
v___x_1729_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(v_inst_1698_, v___x_1726_, v___x_1728_, v_a_1701_, v_a_1702_, v_a_1703_);
return v___x_1729_;
}
}
}
case 1:
{
lean_object* v_content_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1740_; 
lean_dec_ref(v___x_1721_);
lean_dec_ref(v_inst_1699_);
lean_dec_ref(v_inst_1698_);
v_content_1732_ = lean_ctor_get(v_x_1700_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_x_1700_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1734_ = v_x_1700_;
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_content_1732_);
lean_dec(v_x_1700_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_1732_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set_tag(v___x_1734_, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
case 2:
{
lean_object* v_items_1741_; lean_object* v___f_1742_; size_t v_sz_1743_; size_t v___x_1744_; lean_object* v___x_2384__overap_1745_; lean_object* v___x_1746_; 
v_items_1741_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_items_1741_);
lean_dec_ref_known(v_x_1700_, 1);
lean_inc_ref(v___x_1721_);
v___f_1742_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1742_, 0, v_inst_1698_);
lean_closure_set(v___f_1742_, 1, v_inst_1699_);
lean_closure_set(v___f_1742_, 2, v___x_1721_);
v_sz_1743_ = lean_array_size(v_items_1741_);
v___x_1744_ = ((size_t)0ULL);
v___x_2384__overap_1745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1721_, v___f_1742_, v_sz_1743_, v___x_1744_, v_items_1741_);
lean_inc(v_a_1703_);
lean_inc_ref(v_a_1702_);
lean_inc(v_a_1701_);
v___x_1746_ = lean_apply_4(v___x_2384__overap_1745_, v_a_1701_, v_a_1702_, v_a_1703_, lean_box(0));
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1755_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1751_ = l_Lean_Doc_joinBlocks(v_a_1747_);
lean_dec(v_a_1747_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1751_);
v___x_1753_ = v___x_1749_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
v_a_1756_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1746_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1746_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
case 3:
{
lean_object* v_start_1764_; lean_object* v_items_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1801_; 
v_start_1764_ = lean_ctor_get(v_x_1700_, 0);
v_items_1765_ = lean_ctor_get(v_x_1700_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_x_1700_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1767_ = v_x_1700_;
v_isShared_1768_ = v_isSharedCheck_1801_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_items_1765_);
lean_inc(v_start_1764_);
lean_dec(v_x_1700_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1801_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_out_1769_; lean_object* v___x_1770_; lean_object* v___f_1771_; lean_object* v___y_1773_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v_out_1769_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_1770_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_1721_);
v___f_1771_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1771_, 0, v_inst_1698_);
lean_closure_set(v___f_1771_, 1, v_inst_1699_);
lean_closure_set(v___f_1771_, 2, v___x_1721_);
lean_closure_set(v___f_1771_, 3, v___x_1770_);
v___x_1799_ = l_Int_toNat(v_start_1764_);
lean_dec(v_start_1764_);
v___x_1800_ = lean_nat_dec_le(v___x_1770_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_dec(v___x_1799_);
v___y_1773_ = v___x_1770_;
goto v___jp_1772_;
}
else
{
v___y_1773_ = v___x_1799_;
goto v___jp_1772_;
}
v___jp_1772_:
{
lean_object* v___x_1775_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 0);
lean_ctor_set(v___x_1767_, 1, v___y_1773_);
lean_ctor_set(v___x_1767_, 0, v_out_1769_);
v___x_1775_ = v___x_1767_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_out_1769_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v___y_1773_);
v___x_1775_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
size_t v_sz_1776_; size_t v___x_1777_; lean_object* v___x_2200__overap_1778_; lean_object* v___x_1779_; 
v_sz_1776_ = lean_array_size(v_items_1765_);
v___x_1777_ = ((size_t)0ULL);
v___x_2200__overap_1778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1721_, v_items_1765_, v___f_1771_, v_sz_1776_, v___x_1777_, v___x_1775_);
lean_inc(v_a_1703_);
lean_inc_ref(v_a_1702_);
lean_inc(v_a_1701_);
v___x_1779_ = lean_apply_4(v___x_2200__overap_1778_, v_a_1701_, v_a_1702_, v_a_1703_, lean_box(0));
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1789_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1789_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1789_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v_fst_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v_fst_1784_ = lean_ctor_get(v_a_1780_, 0);
lean_inc(v_fst_1784_);
lean_dec(v_a_1780_);
v___x_1785_ = l_Lean_Doc_joinBlocks(v_fst_1784_);
lean_dec(v_fst_1784_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1785_);
v___x_1787_ = v___x_1782_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v_a_1790_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1779_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1779_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_1802_; lean_object* v___f_1803_; size_t v_sz_1804_; size_t v___x_1805_; lean_object* v___x_2390__overap_1806_; lean_object* v___x_1807_; 
v_items_1802_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_items_1802_);
lean_dec_ref_known(v_x_1700_, 1);
lean_inc_ref(v___x_1721_);
v___f_1803_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___boxed), 8, 3);
lean_closure_set(v___f_1803_, 0, v_inst_1698_);
lean_closure_set(v___f_1803_, 1, v_inst_1699_);
lean_closure_set(v___f_1803_, 2, v___x_1721_);
v_sz_1804_ = lean_array_size(v_items_1802_);
v___x_1805_ = ((size_t)0ULL);
v___x_2390__overap_1806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1721_, v___f_1803_, v_sz_1804_, v___x_1805_, v_items_1802_);
lean_inc(v_a_1703_);
lean_inc_ref(v_a_1702_);
lean_inc(v_a_1701_);
v___x_1807_ = lean_apply_4(v___x_2390__overap_1806_, v_a_1701_, v_a_1702_, v_a_1703_, lean_box(0));
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1816_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1816_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1816_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = l_Lean_Doc_joinBlocks(v_a_1808_);
lean_dec(v_a_1808_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1812_);
v___x_1814_ = v___x_1810_;
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
v_a_1817_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1807_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1807_);
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
case 5:
{
lean_object* v_items_1825_; lean_object* v___x_1826_; size_t v_sz_1827_; size_t v___x_1828_; lean_object* v___x_2393__overap_1829_; lean_object* v___x_1830_; 
v_items_1825_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_items_1825_);
lean_dec_ref_known(v_x_1700_, 1);
v___x_1826_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1826_, 0, v_inst_1698_);
lean_closure_set(v___x_1826_, 1, v_inst_1699_);
v_sz_1827_ = lean_array_size(v_items_1825_);
v___x_1828_ = ((size_t)0ULL);
v___x_2393__overap_1829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1721_, v___x_1826_, v_sz_1827_, v___x_1828_, v_items_1825_);
lean_inc(v_a_1703_);
lean_inc_ref(v_a_1702_);
lean_inc(v_a_1701_);
v___x_1830_ = lean_apply_4(v___x_2393__overap_1829_, v_a_1701_, v_a_1702_, v_a_1703_, lean_box(0));
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1841_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1841_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1841_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1835_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_1836_ = l_Lean_Doc_joinBlocks(v_a_1831_);
lean_dec(v_a_1831_);
v___x_1837_ = l_Lean_Doc_prefixLines(v___x_1835_, v___x_1836_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1837_);
v___x_1839_ = v___x_1833_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_a_1842_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1830_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1830_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
case 6:
{
lean_object* v_content_1850_; lean_object* v___x_1851_; size_t v_sz_1852_; size_t v___x_1853_; lean_object* v___x_2396__overap_1854_; lean_object* v___x_1855_; 
v_content_1850_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_content_1850_);
lean_dec_ref_known(v_x_1700_, 1);
v___x_1851_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1851_, 0, v_inst_1698_);
lean_closure_set(v___x_1851_, 1, v_inst_1699_);
v_sz_1852_ = lean_array_size(v_content_1850_);
v___x_1853_ = ((size_t)0ULL);
v___x_2396__overap_1854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1721_, v___x_1851_, v_sz_1852_, v___x_1853_, v_content_1850_);
lean_inc(v_a_1703_);
lean_inc_ref(v_a_1702_);
lean_inc(v_a_1701_);
v___x_1855_ = lean_apply_4(v___x_2396__overap_1854_, v_a_1701_, v_a_1702_, v_a_1703_, lean_box(0));
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1864_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1860_ = l_Lean_Doc_joinBlocks(v_a_1856_);
lean_dec(v_a_1856_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1860_);
v___x_1862_ = v___x_1858_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
v_a_1865_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1855_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1855_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
default: 
{
lean_object* v_container_1873_; lean_object* v_content_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec_ref(v___x_1721_);
v_container_1873_ = lean_ctor_get(v_x_1700_, 0);
lean_inc(v_container_1873_);
v_content_1874_ = lean_ctor_get(v_x_1700_, 1);
lean_inc_ref(v_content_1874_);
lean_dec_ref_known(v_x_1700_, 2);
v___x_1875_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
lean_inc_ref(v_inst_1698_);
v___x_1876_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___boxed), 8, 3);
lean_closure_set(v___x_1876_, 0, lean_box(0));
lean_closure_set(v___x_1876_, 1, v_inst_1698_);
lean_closure_set(v___x_1876_, 2, v___x_1875_);
lean_inc_ref(v_inst_1699_);
v___x_1877_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1877_, 0, v_inst_1698_);
lean_closure_set(v___x_1877_, 1, v_inst_1699_);
lean_inc(v_a_1703_);
lean_inc_ref(v_a_1702_);
lean_inc(v_a_1701_);
v___x_1878_ = lean_apply_8(v_inst_1699_, v___x_1876_, v___x_1877_, v_container_1873_, v_content_1874_, v_a_1701_, v_a_1702_, v_a_1703_, lean_box(0));
return v___x_1878_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed(lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_x_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1879_, v_inst_1880_, v_x_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v_a_1882_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v___x_1889_, lean_object* v_item_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; size_t v_sz_1896_; size_t v___x_1897_; lean_object* v___x_2428__overap_1898_; lean_object* v___x_1899_; 
v___x_1895_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___boxed), 7, 2);
lean_closure_set(v___x_1895_, 0, v_inst_1887_);
lean_closure_set(v___x_1895_, 1, v_inst_1888_);
v_sz_1896_ = lean_array_size(v_item_1890_);
v___x_1897_ = ((size_t)0ULL);
v___x_2428__overap_1898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1889_, v___x_1895_, v_sz_1896_, v___x_1897_, v_item_1890_);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1891_);
v___x_1899_ = lean_apply_4(v___x_2428__overap_1898_, v___y_1891_, v___y_1892_, v___y_1893_, lean_box(0));
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1911_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1911_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1911_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1904_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_1905_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_1906_ = l_Lean_Doc_joinBlocks(v_a_1900_);
lean_dec(v_a_1900_);
v___x_1907_ = l_Lean_Doc_prefixListLines(v___x_1904_, v___x_1905_, v___x_1906_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1907_);
v___x_1909_ = v___x_1902_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
v_a_1912_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1899_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1899_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object* v_i_1920_, lean_object* v_b_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_x_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1922_, v_inst_1923_, v_x_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___boxed(lean_object* v_i_1930_, lean_object* v_b_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_x_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(v_i_1930_, v_b_1931_, v_inst_1932_, v_inst_1933_, v_x_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1940_, v_inst_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg___boxed(lean_object* v_inst_1948_, lean_object* v_inst_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(v_inst_1948_, v_inst_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object* v_i_1956_, lean_object* v_b_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(v_inst_1958_, v_inst_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed(lean_object* v_i_1966_, lean_object* v_b_1967_, lean_object* v_inst_1968_, lean_object* v_inst_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(v_i_1966_, v_b_1967_, v_inst_1968_, v_inst_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_1976_, lean_object* v_inst_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_1978_, 0, lean_box(0));
lean_closure_set(v___x_1978_, 1, lean_box(0));
lean_closure_set(v___x_1978_, 2, v_inst_1976_);
lean_closure_set(v___x_1978_, 3, v_inst_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_1979_, lean_object* v_b_1980_, lean_object* v_inst_1981_, lean_object* v_inst_1982_){
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
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = 35;
v___x_1985_ = lean_box_uint32(v___x_1984_);
return v___x_1985_;
}
}
static lean_object* _init_l_Lean_Doc_partMarkdown___redArg___closed__0(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___f_1987_; 
v___x_1986_ = l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
v___f_1987_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1987_, 0, v___x_1986_);
return v___f_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg___boxed(lean_object* v_inst_1988_, lean_object* v_inst_1989_, lean_object* v_level_1990_, lean_object* v_part_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Doc_partMarkdown___redArg(v_inst_1988_, v_inst_1989_, v_level_1990_, v_part_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec(v_level_1990_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___redArg(lean_object* v_inst_1997_, lean_object* v_inst_1998_, lean_object* v_level_1999_, lean_object* v_part_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v___x_2005_; lean_object* v_toApplicative_2006_; lean_object* v_toFunctor_2007_; lean_object* v_toSeq_2008_; lean_object* v_toSeqLeft_2009_; lean_object* v_toSeqRight_2010_; lean_object* v___f_2011_; lean_object* v___f_2012_; lean_object* v___f_2013_; lean_object* v___f_2014_; lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___f_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v_title_2022_; lean_object* v_content_2023_; lean_object* v_subParts_2024_; lean_object* v___x_2025_; size_t v_sz_2026_; size_t v___x_2027_; lean_object* v___x_684__overap_2028_; lean_object* v___x_2029_; 
v___x_2005_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2006_ = lean_ctor_get(v___x_2005_, 0);
v_toFunctor_2007_ = lean_ctor_get(v_toApplicative_2006_, 0);
v_toSeq_2008_ = lean_ctor_get(v_toApplicative_2006_, 2);
v_toSeqLeft_2009_ = lean_ctor_get(v_toApplicative_2006_, 3);
v_toSeqRight_2010_ = lean_ctor_get(v_toApplicative_2006_, 4);
v___f_2011_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2012_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2007_, 2);
v___f_2013_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2013_, 0, v_toFunctor_2007_);
v___f_2014_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2014_, 0, v_toFunctor_2007_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___f_2013_);
lean_ctor_set(v___x_2015_, 1, v___f_2014_);
lean_inc(v_toSeqRight_2010_);
v___f_2016_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2016_, 0, v_toSeqRight_2010_);
lean_inc(v_toSeqLeft_2009_);
v___f_2017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2017_, 0, v_toSeqLeft_2009_);
lean_inc(v_toSeq_2008_);
v___f_2018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2018_, 0, v_toSeq_2008_);
v___x_2019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2015_);
lean_ctor_set(v___x_2019_, 1, v___f_2011_);
lean_ctor_set(v___x_2019_, 2, v___f_2018_);
lean_ctor_set(v___x_2019_, 3, v___f_2017_);
lean_ctor_set(v___x_2019_, 4, v___f_2016_);
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v___f_2012_);
v___x_2021_ = l_StateRefT_x27_instMonad___redArg(v___x_2020_);
v_title_2022_ = lean_ctor_get(v_part_2000_, 0);
lean_inc_ref(v_title_2022_);
v_content_2023_ = lean_ctor_get(v_part_2000_, 3);
lean_inc_ref(v_content_2023_);
v_subParts_2024_ = lean_ctor_get(v_part_2000_, 4);
lean_inc_ref(v_subParts_2024_);
lean_dec_ref(v_part_2000_);
lean_inc_ref(v_inst_1997_);
v___x_2025_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___boxed), 7, 2);
lean_closure_set(v___x_2025_, 0, lean_box(0));
lean_closure_set(v___x_2025_, 1, v_inst_1997_);
v_sz_2026_ = lean_array_size(v_title_2022_);
v___x_2027_ = ((size_t)0ULL);
lean_inc_ref(v___x_2021_);
v___x_684__overap_2028_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2021_, v___x_2025_, v_sz_2026_, v___x_2027_, v_title_2022_);
lean_inc(v_a_2003_);
lean_inc_ref(v_a_2002_);
lean_inc(v_a_2001_);
v___x_2029_ = lean_apply_4(v___x_684__overap_2028_, v_a_2001_, v_a_2002_, v_a_2003_, lean_box(0));
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; lean_object* v___f_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; size_t v_sz_2044_; lean_object* v___x_687__overap_2045_; lean_object* v___x_2046_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
v___x_2031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___f_2032_ = lean_obj_once(&l_Lean_Doc_partMarkdown___redArg___closed__0, &l_Lean_Doc_partMarkdown___redArg___closed__0_once, _init_l_Lean_Doc_partMarkdown___redArg___closed__0);
v___x_2033_ = lean_unsigned_to_nat(1u);
v___x_2034_ = lean_nat_add(v_level_1999_, v___x_2033_);
lean_inc(v___x_2034_);
v___x_2035_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_2032_, v___x_2034_, v___x_2031_);
v___x_2036_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_2037_ = lean_string_append(v___x_2035_, v___x_2036_);
v___x_2038_ = lean_mk_empty_array_with_capacity(v___x_2033_);
lean_inc_ref_n(v___x_2038_, 2);
v___x_2039_ = lean_array_push(v___x_2038_, v___x_2037_);
v___x_2040_ = lean_array_push(v___x_2038_, v___x_2039_);
v___x_2041_ = l_Array_append___redArg(v___x_2040_, v_a_2030_);
lean_dec(v_a_2030_);
v___x_2042_ = l_Lean_Doc_joinInlines(v___x_2041_);
lean_dec_ref(v___x_2041_);
lean_inc_ref(v_inst_1998_);
lean_inc_ref(v_inst_1997_);
v___x_2043_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_2043_, 0, lean_box(0));
lean_closure_set(v___x_2043_, 1, lean_box(0));
lean_closure_set(v___x_2043_, 2, v_inst_1997_);
lean_closure_set(v___x_2043_, 3, v_inst_1998_);
v_sz_2044_ = lean_array_size(v_content_2023_);
lean_inc_ref(v___x_2021_);
v___x_687__overap_2045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2021_, v___x_2043_, v_sz_2044_, v___x_2027_, v_content_2023_);
lean_inc(v_a_2003_);
lean_inc_ref(v_a_2002_);
lean_inc(v_a_2001_);
v___x_2046_ = lean_apply_4(v___x_687__overap_2045_, v_a_2001_, v_a_2002_, v_a_2003_, lean_box(0));
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; size_t v_sz_2049_; lean_object* v___x_690__overap_2050_; lean_object* v___x_2051_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = lean_alloc_closure((void*)(l_Lean_Doc_partMarkdown___redArg___boxed), 8, 3);
lean_closure_set(v___x_2048_, 0, v_inst_1997_);
lean_closure_set(v___x_2048_, 1, v_inst_1998_);
lean_closure_set(v___x_2048_, 2, v___x_2034_);
v_sz_2049_ = lean_array_size(v_subParts_2024_);
v___x_690__overap_2050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2021_, v___x_2048_, v_sz_2049_, v___x_2027_, v_subParts_2024_);
lean_inc(v_a_2003_);
lean_inc_ref(v_a_2002_);
lean_inc(v_a_2001_);
v___x_2051_ = lean_apply_4(v___x_690__overap_2050_, v_a_2001_, v_a_2002_, v_a_2003_, lean_box(0));
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2063_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2063_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2063_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2056_ = lean_array_push(v___x_2038_, v___x_2042_);
v___x_2057_ = l_Array_append___redArg(v___x_2056_, v_a_2047_);
lean_dec(v_a_2047_);
v___x_2058_ = l_Array_append___redArg(v___x_2057_, v_a_2052_);
lean_dec(v_a_2052_);
v___x_2059_ = l_Lean_Doc_joinBlocks(v___x_2058_);
lean_dec_ref(v___x_2058_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2059_);
v___x_2061_ = v___x_2054_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_a_2047_);
lean_dec_ref(v___x_2042_);
lean_dec_ref(v___x_2038_);
v_a_2064_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2051_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2051_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v___x_2042_);
lean_dec_ref(v___x_2038_);
lean_dec(v___x_2034_);
lean_dec_ref(v_subParts_2024_);
lean_dec_ref(v___x_2021_);
lean_dec_ref(v_inst_1998_);
lean_dec_ref(v_inst_1997_);
v_a_2072_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2046_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2046_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec_ref(v_subParts_2024_);
lean_dec_ref(v_content_2023_);
lean_dec_ref(v___x_2021_);
lean_dec_ref(v_inst_1998_);
lean_dec_ref(v_inst_1997_);
v_a_2080_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2029_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2029_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown(lean_object* v_i_2088_, lean_object* v_b_2089_, lean_object* v_p_2090_, lean_object* v_inst_2091_, lean_object* v_inst_2092_, lean_object* v_level_2093_, lean_object* v_part_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2091_, v_inst_2092_, v_level_2093_, v_part_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___boxed(lean_object* v_i_2100_, lean_object* v_b_2101_, lean_object* v_p_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_level_2105_, lean_object* v_part_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_Doc_partMarkdown(v_i_2100_, v_b_2101_, v_p_2102_, v_inst_2103_, v_inst_2104_, v_level_2105_, v_part_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec(v_level_2105_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_part_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = l_Lean_Doc_partMarkdown___redArg(v_inst_2112_, v_inst_2113_, v___x_2119_, v_part_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed(lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_part_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(v_inst_2121_, v_inst_2122_, v_part_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(lean_object* v_inst_2129_, lean_object* v_inst_2130_){
_start:
{
lean_object* v___f_2131_; 
v___f_2131_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2131_, 0, v_inst_2129_);
lean_closure_set(v___f_2131_, 1, v_inst_2130_);
return v___f_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(lean_object* v_i_2132_, lean_object* v_b_2133_, lean_object* v_p_2134_, lean_object* v_inst_2135_, lean_object* v_inst_2136_){
_start:
{
lean_object* v___f_2137_; 
v___f_2137_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2137_, 0, v_inst_2135_);
lean_closure_set(v___f_2137_, 1, v_inst_2136_);
return v___f_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg(lean_object* v_inst_2138_, lean_object* v_f_2139_, lean_object* v_go_2140_, lean_object* v_val_2141_, lean_object* v_content_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v___x_2147_; lean_object* v_toApplicative_2148_; lean_object* v_toFunctor_2149_; lean_object* v_toSeq_2150_; lean_object* v_toSeqLeft_2151_; lean_object* v_toSeqRight_2152_; lean_object* v___f_2153_; lean_object* v___f_2154_; lean_object* v___f_2155_; lean_object* v___f_2156_; lean_object* v___x_2157_; lean_object* v___f_2158_; lean_object* v___f_2159_; lean_object* v___f_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2147_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2148_ = lean_ctor_get(v___x_2147_, 0);
v_toFunctor_2149_ = lean_ctor_get(v_toApplicative_2148_, 0);
v_toSeq_2150_ = lean_ctor_get(v_toApplicative_2148_, 2);
v_toSeqLeft_2151_ = lean_ctor_get(v_toApplicative_2148_, 3);
v_toSeqRight_2152_ = lean_ctor_get(v_toApplicative_2148_, 4);
v___f_2153_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2154_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2149_, 2);
v___f_2155_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2155_, 0, v_toFunctor_2149_);
v___f_2156_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2156_, 0, v_toFunctor_2149_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___f_2155_);
lean_ctor_set(v___x_2157_, 1, v___f_2156_);
lean_inc(v_toSeqRight_2152_);
v___f_2158_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2158_, 0, v_toSeqRight_2152_);
lean_inc(v_toSeqLeft_2151_);
v___f_2159_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2159_, 0, v_toSeqLeft_2151_);
lean_inc(v_toSeq_2150_);
v___f_2160_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2160_, 0, v_toSeq_2150_);
v___x_2161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2157_);
lean_ctor_set(v___x_2161_, 1, v___f_2153_);
lean_ctor_set(v___x_2161_, 2, v___f_2160_);
lean_ctor_set(v___x_2161_, 3, v___f_2159_);
lean_ctor_set(v___x_2161_, 4, v___f_2158_);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v___f_2154_);
v___x_2163_ = l_StateRefT_x27_instMonad___redArg(v___x_2162_);
v___x_2164_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2141_, v_inst_2138_);
if (lean_obj_tag(v___x_2164_) == 0)
{
size_t v_sz_2165_; size_t v___x_2166_; lean_object* v___x_236__overap_2167_; lean_object* v___x_2168_; 
lean_dec_ref(v_f_2139_);
v_sz_2165_ = lean_array_size(v_content_2142_);
v___x_2166_ = ((size_t)0ULL);
v___x_236__overap_2167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2163_, v_go_2140_, v_sz_2165_, v___x_2166_, v_content_2142_);
lean_inc(v_a_2145_);
lean_inc_ref(v_a_2144_);
lean_inc(v_a_2143_);
v___x_2168_ = lean_apply_4(v___x_236__overap_2167_, v_a_2143_, v_a_2144_, v_a_2145_, lean_box(0));
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2177_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2177_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2177_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2173_ = l_Lean_Doc_joinInlines(v_a_2169_);
lean_dec(v_a_2169_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2173_);
v___x_2175_ = v___x_2171_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
v_a_2178_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2168_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2168_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_val_2186_; lean_object* v___x_2187_; 
lean_dec_ref(v___x_2163_);
v_val_2186_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_val_2186_);
lean_dec_ref_known(v___x_2164_, 1);
lean_inc(v_a_2145_);
lean_inc_ref(v_a_2144_);
lean_inc(v_a_2143_);
v___x_2187_ = lean_apply_7(v_f_2139_, v_go_2140_, v_val_2186_, v_content_2142_, v_a_2143_, v_a_2144_, v_a_2145_, lean_box(0));
return v___x_2187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___redArg___boxed(lean_object* v_inst_2188_, lean_object* v_f_2189_, lean_object* v_go_2190_, lean_object* v_val_2191_, lean_object* v_content_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2188_, v_f_2189_, v_go_2190_, v_val_2191_, v_content_2192_, v_a_2193_, v_a_2194_, v_a_2195_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec(v_val_2191_);
lean_dec(v_inst_2188_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer(lean_object* v_00_u03b1_2198_, lean_object* v_inst_2199_, lean_object* v_f_2200_, lean_object* v_go_2201_, lean_object* v_val_2202_, lean_object* v_content_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Doc_mkInlineMdRenderer___redArg(v_inst_2199_, v_f_2200_, v_go_2201_, v_val_2202_, v_content_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkInlineMdRenderer___boxed(lean_object* v_00_u03b1_2209_, lean_object* v_inst_2210_, lean_object* v_f_2211_, lean_object* v_go_2212_, lean_object* v_val_2213_, lean_object* v_content_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_Doc_mkInlineMdRenderer(v_00_u03b1_2209_, v_inst_2210_, v_f_2211_, v_go_2212_, v_val_2213_, v_content_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec(v_val_2213_);
lean_dec(v_inst_2210_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg(lean_object* v_inst_2220_, lean_object* v_f_2221_, lean_object* v_goI_2222_, lean_object* v_goB_2223_, lean_object* v_val_2224_, lean_object* v_content_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v___x_2230_; lean_object* v_toApplicative_2231_; lean_object* v_toFunctor_2232_; lean_object* v_toSeq_2233_; lean_object* v_toSeqLeft_2234_; lean_object* v_toSeqRight_2235_; lean_object* v___f_2236_; lean_object* v___f_2237_; lean_object* v___f_2238_; lean_object* v___f_2239_; lean_object* v___x_2240_; lean_object* v___f_2241_; lean_object* v___f_2242_; lean_object* v___f_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2230_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2231_ = lean_ctor_get(v___x_2230_, 0);
v_toFunctor_2232_ = lean_ctor_get(v_toApplicative_2231_, 0);
v_toSeq_2233_ = lean_ctor_get(v_toApplicative_2231_, 2);
v_toSeqLeft_2234_ = lean_ctor_get(v_toApplicative_2231_, 3);
v_toSeqRight_2235_ = lean_ctor_get(v_toApplicative_2231_, 4);
v___f_2236_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2237_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2232_, 2);
v___f_2238_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2238_, 0, v_toFunctor_2232_);
v___f_2239_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2239_, 0, v_toFunctor_2232_);
v___x_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___f_2238_);
lean_ctor_set(v___x_2240_, 1, v___f_2239_);
lean_inc(v_toSeqRight_2235_);
v___f_2241_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2241_, 0, v_toSeqRight_2235_);
lean_inc(v_toSeqLeft_2234_);
v___f_2242_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2242_, 0, v_toSeqLeft_2234_);
lean_inc(v_toSeq_2233_);
v___f_2243_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2243_, 0, v_toSeq_2233_);
v___x_2244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2240_);
lean_ctor_set(v___x_2244_, 1, v___f_2236_);
lean_ctor_set(v___x_2244_, 2, v___f_2243_);
lean_ctor_set(v___x_2244_, 3, v___f_2242_);
lean_ctor_set(v___x_2244_, 4, v___f_2241_);
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set(v___x_2245_, 1, v___f_2237_);
v___x_2246_ = l_StateRefT_x27_instMonad___redArg(v___x_2245_);
v___x_2247_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_2224_, v_inst_2220_);
if (lean_obj_tag(v___x_2247_) == 0)
{
size_t v_sz_2248_; size_t v___x_2249_; lean_object* v___x_236__overap_2250_; lean_object* v___x_2251_; 
lean_dec_ref(v_goI_2222_);
lean_dec_ref(v_f_2221_);
v_sz_2248_ = lean_array_size(v_content_2225_);
v___x_2249_ = ((size_t)0ULL);
v___x_236__overap_2250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2246_, v_goB_2223_, v_sz_2248_, v___x_2249_, v_content_2225_);
lean_inc(v_a_2228_);
lean_inc_ref(v_a_2227_);
lean_inc(v_a_2226_);
v___x_2251_ = lean_apply_4(v___x_236__overap_2250_, v_a_2226_, v_a_2227_, v_a_2228_, lean_box(0));
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2260_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2260_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2260_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2256_ = l_Lean_Doc_joinBlocks(v_a_2252_);
lean_dec(v_a_2252_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2256_);
v___x_2258_ = v___x_2254_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
v_a_2261_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2251_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2251_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
else
{
lean_object* v_val_2269_; lean_object* v___x_2270_; 
lean_dec_ref(v___x_2246_);
v_val_2269_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_val_2269_);
lean_dec_ref_known(v___x_2247_, 1);
lean_inc(v_a_2228_);
lean_inc_ref(v_a_2227_);
lean_inc(v_a_2226_);
v___x_2270_ = lean_apply_8(v_f_2221_, v_goI_2222_, v_goB_2223_, v_val_2269_, v_content_2225_, v_a_2226_, v_a_2227_, v_a_2228_, lean_box(0));
return v___x_2270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___redArg___boxed(lean_object* v_inst_2271_, lean_object* v_f_2272_, lean_object* v_goI_2273_, lean_object* v_goB_2274_, lean_object* v_val_2275_, lean_object* v_content_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2271_, v_f_2272_, v_goI_2273_, v_goB_2274_, v_val_2275_, v_content_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
lean_dec(v_a_2279_);
lean_dec_ref(v_a_2278_);
lean_dec(v_a_2277_);
lean_dec(v_val_2275_);
lean_dec(v_inst_2271_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer(lean_object* v_00_u03b1_2282_, lean_object* v_inst_2283_, lean_object* v_f_2284_, lean_object* v_goI_2285_, lean_object* v_goB_2286_, lean_object* v_val_2287_, lean_object* v_content_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Doc_mkBlockMdRenderer___redArg(v_inst_2283_, v_f_2284_, v_goI_2285_, v_goB_2286_, v_val_2287_, v_content_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkBlockMdRenderer___boxed(lean_object* v_00_u03b1_2294_, lean_object* v_inst_2295_, lean_object* v_f_2296_, lean_object* v_goI_2297_, lean_object* v_goB_2298_, lean_object* v_val_2299_, lean_object* v_content_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_Doc_mkBlockMdRenderer(v_00_u03b1_2294_, v_inst_2295_, v_f_2296_, v_goI_2297_, v_goB_2298_, v_val_2299_, v_content_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec(v_val_2299_);
lean_dec(v_inst_2295_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(lean_object* v_as_2310_, size_t v_i_2311_, size_t v_stop_2312_, lean_object* v_b_2313_){
_start:
{
uint8_t v___x_2314_; 
v___x_2314_ = lean_usize_dec_eq(v_i_2311_, v_stop_2312_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; lean_object* v_fst_2316_; lean_object* v_snd_2317_; lean_object* v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; 
v___x_2315_ = lean_array_uget_borrowed(v_as_2310_, v_i_2311_);
v_fst_2316_ = lean_ctor_get(v___x_2315_, 0);
v_snd_2317_ = lean_ctor_get(v___x_2315_, 1);
lean_inc(v_snd_2317_);
lean_inc(v_fst_2316_);
v___x_2318_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2316_, v_snd_2317_, v_b_2313_);
v___x_2319_ = ((size_t)1ULL);
v___x_2320_ = lean_usize_add(v_i_2311_, v___x_2319_);
v_i_2311_ = v___x_2320_;
v_b_2313_ = v___x_2318_;
goto _start;
}
else
{
return v_b_2313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0___boxed(lean_object* v_as_2322_, lean_object* v_i_2323_, lean_object* v_stop_2324_, lean_object* v_b_2325_){
_start:
{
size_t v_i_boxed_2326_; size_t v_stop_boxed_2327_; lean_object* v_res_2328_; 
v_i_boxed_2326_ = lean_unbox_usize(v_i_2323_);
lean_dec(v_i_2323_);
v_stop_boxed_2327_ = lean_unbox_usize(v_stop_2324_);
lean_dec(v_stop_2324_);
v_res_2328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v_as_2322_, v_i_boxed_2326_, v_stop_boxed_2327_, v_b_2325_);
lean_dec_ref(v_as_2322_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(lean_object* v_as_2329_, size_t v_i_2330_, size_t v_stop_2331_, lean_object* v_b_2332_){
_start:
{
lean_object* v___y_2334_; uint8_t v___x_2338_; 
v___x_2338_ = lean_usize_dec_eq(v_i_2330_, v_stop_2331_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2339_ = lean_array_uget_borrowed(v_as_2329_, v_i_2330_);
v___x_2340_ = lean_unsigned_to_nat(0u);
v___x_2341_ = lean_array_get_size(v___x_2339_);
v___x_2342_ = lean_nat_dec_lt(v___x_2340_, v___x_2341_);
if (v___x_2342_ == 0)
{
v___y_2334_ = v_b_2332_;
goto v___jp_2333_;
}
else
{
uint8_t v___x_2343_; 
v___x_2343_ = lean_nat_dec_le(v___x_2341_, v___x_2341_);
if (v___x_2343_ == 0)
{
if (v___x_2342_ == 0)
{
v___y_2334_ = v_b_2332_;
goto v___jp_2333_;
}
else
{
size_t v___x_2344_; size_t v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = ((size_t)0ULL);
v___x_2345_ = lean_usize_of_nat(v___x_2341_);
v___x_2346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2339_, v___x_2344_, v___x_2345_, v_b_2332_);
v___y_2334_ = v___x_2346_;
goto v___jp_2333_;
}
}
else
{
size_t v___x_2347_; size_t v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = ((size_t)0ULL);
v___x_2348_ = lean_usize_of_nat(v___x_2341_);
v___x_2349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__0(v___x_2339_, v___x_2347_, v___x_2348_, v_b_2332_);
v___y_2334_ = v___x_2349_;
goto v___jp_2333_;
}
}
}
else
{
return v_b_2332_;
}
v___jp_2333_:
{
size_t v___x_2335_; size_t v___x_2336_; 
v___x_2335_ = ((size_t)1ULL);
v___x_2336_ = lean_usize_add(v_i_2330_, v___x_2335_);
v_i_2330_ = v___x_2336_;
v_b_2332_ = v___y_2334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1___boxed(lean_object* v_as_2350_, lean_object* v_i_2351_, lean_object* v_stop_2352_, lean_object* v_b_2353_){
_start:
{
size_t v_i_boxed_2354_; size_t v_stop_boxed_2355_; lean_object* v_res_2356_; 
v_i_boxed_2354_ = lean_unbox_usize(v_i_2351_);
lean_dec(v_i_2351_);
v_stop_boxed_2355_ = lean_unbox_usize(v_stop_2352_);
lean_dec(v_stop_2352_);
v_res_2356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_as_2350_, v_i_boxed_2354_, v_stop_boxed_2355_, v_b_2353_);
lean_dec_ref(v_as_2350_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(lean_object* v_init_2357_, lean_object* v_es_2358_){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v___x_2359_ = lean_unsigned_to_nat(0u);
v___x_2360_ = lean_array_get_size(v_es_2358_);
v___x_2361_ = lean_nat_dec_lt(v___x_2359_, v___x_2360_);
if (v___x_2361_ == 0)
{
return v_init_2357_;
}
else
{
uint8_t v___x_2362_; 
v___x_2362_ = lean_nat_dec_le(v___x_2360_, v___x_2360_);
if (v___x_2362_ == 0)
{
if (v___x_2361_ == 0)
{
return v_init_2357_;
}
else
{
size_t v___x_2363_; size_t v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = ((size_t)0ULL);
v___x_2364_ = lean_usize_of_nat(v___x_2360_);
v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2358_, v___x_2363_, v___x_2364_, v_init_2357_);
return v___x_2365_;
}
}
else
{
size_t v___x_2366_; size_t v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = ((size_t)0ULL);
v___x_2367_ = lean_usize_of_nat(v___x_2360_);
v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries_spec__1(v_es_2358_, v___x_2366_, v___x_2367_, v_init_2357_);
return v___x_2368_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries___boxed(lean_object* v_init_2369_, lean_object* v_es_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v_init_2369_, v_es_2370_);
lean_dec_ref(v_es_2370_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_2372_, lean_object* v_x_2373_){
_start:
{
if (lean_obj_tag(v_x_2373_) == 0)
{
lean_object* v_k_2374_; lean_object* v_v_2375_; lean_object* v_l_2376_; lean_object* v_r_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_k_2374_ = lean_ctor_get(v_x_2373_, 1);
v_v_2375_ = lean_ctor_get(v_x_2373_, 2);
v_l_2376_ = lean_ctor_get(v_x_2373_, 3);
v_r_2377_ = lean_ctor_get(v_x_2373_, 4);
v___x_2378_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2372_, v_l_2376_);
lean_inc(v_v_2375_);
lean_inc(v_k_2374_);
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v_k_2374_);
lean_ctor_set(v___x_2379_, 1, v_v_2375_);
v___x_2380_ = lean_array_push(v___x_2378_, v___x_2379_);
v_init_2372_ = v___x_2380_;
v_x_2373_ = v_r_2377_;
goto _start;
}
else
{
return v_init_2372_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_2382_, lean_object* v_x_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2382_, v_x_2383_);
lean_dec(v_x_2383_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2387_){
_start:
{
lean_object* v_current_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_current_2388_ = lean_ctor_get(v_s_2387_, 1);
v___x_2389_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2390_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2389_, v_current_2388_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_s_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_s_2391_);
lean_dec_ref(v_s_2391_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_box(0);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2395_);
lean_dec_ref(v_x_2395_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_x_2397_, lean_object* v_s_2398_){
_start:
{
lean_object* v_current_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_current_2399_ = lean_ctor_get(v_s_2398_, 1);
v___x_2400_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__0___closed__0_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2401_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v___x_2400_, v_current_2399_);
lean_inc_ref_n(v___x_2401_, 2);
v___x_2402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
lean_ctor_set(v___x_2402_, 2, v___x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_x_2403_, lean_object* v_s_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v_x_2403_, v_s_2404_);
lean_dec_ref(v_s_2404_);
lean_dec_ref(v_x_2403_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v_s_2406_, lean_object* v_x_2407_){
_start:
{
lean_object* v_fst_2408_; lean_object* v_snd_2409_; lean_object* v_imported_2410_; lean_object* v_current_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2419_; 
v_fst_2408_ = lean_ctor_get(v_x_2407_, 0);
lean_inc(v_fst_2408_);
v_snd_2409_ = lean_ctor_get(v_x_2407_, 1);
lean_inc(v_snd_2409_);
lean_dec_ref(v_x_2407_);
v_imported_2410_ = lean_ctor_get(v_s_2406_, 0);
v_current_2411_ = lean_ctor_get(v_s_2406_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_s_2406_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2413_ = v_s_2406_;
v_isShared_2414_ = v_isSharedCheck_2419_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_current_2411_);
lean_inc(v_imported_2410_);
lean_dec(v_s_2406_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2419_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2415_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2408_, v_snd_2409_, v_current_2411_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 1, v___x_2415_);
v___x_2417_ = v___x_2413_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_imported_2410_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2420_, lean_object* v_es_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_inc(v___x_2420_);
v___x_2424_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_foldEntries(v___x_2420_, v_es_2421_);
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
lean_ctor_set(v___x_2425_, 1, v___x_2420_);
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2427_, lean_object* v_es_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2427_, v_es_2428_, v___y_2429_);
lean_dec_ref(v___y_2429_);
lean_dec_ref(v_es_2428_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(lean_object* v___x_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2432_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v___x_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___lam__5_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(v___x_2435_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_));
v___x_2468_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2____boxed(lean_object* v_a_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2_();
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(lean_object* v_init_2471_, lean_object* v_t_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0_spec__0(v_init_2471_, v_t_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_2474_, lean_object* v_t_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_initFn_00___x40_Lean_DocString_Markdown_92810654____hygCtx___hyg_2__spec__0(v_init_2474_, v_t_2475_);
lean_dec(v_t_2475_);
return v_res_2476_;
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
v___x_2536_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2539_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2540_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_2541_ = lean_unsigned_to_nat(0u);
v___x_2542_ = lean_alloc_ctor(0, 12, 0);
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
lean_ctor_set(v___x_2542_, 10, v___x_2540_);
lean_ctor_set(v___x_2542_, 11, v___x_2539_);
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
lean_object* v___x_2560_; lean_object* v_toCold_2561_; lean_object* v_env_2562_; lean_object* v_options_2563_; uint8_t v___x_2564_; lean_object* v_env_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2560_ = lean_st_ref_get(v___y_2558_);
v_toCold_2561_ = lean_ctor_get(v___y_2557_, 0);
v_env_2562_ = lean_ctor_get(v___x_2560_, 0);
lean_inc_ref(v_env_2562_);
lean_dec(v___x_2560_);
v_options_2563_ = lean_ctor_get(v_toCold_2561_, 2);
v___x_2564_ = 0;
v_env_2565_ = l_Lean_Environment_setRecordingDeps(v_env_2562_, v___x_2564_);
v___x_2566_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_2567_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_2563_);
v___x_2568_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2568_, 0, v_env_2565_);
lean_ctor_set(v___x_2568_, 1, v___x_2566_);
lean_ctor_set(v___x_2568_, 2, v___x_2567_);
lean_ctor_set(v___x_2568_, 3, v_options_2563_);
v___x_2569_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
lean_ctor_set(v___x_2569_, 1, v_msgData_2556_);
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
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___y_2665_; lean_object* v_env_2696_; lean_object* v___x_2697_; lean_object* v_toEnvExtension_2698_; lean_object* v_asyncMode_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v_imported_2703_; lean_object* v_current_2704_; lean_object* v___x_2705_; 
v___x_2662_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2663_ = lean_st_ref_get(v_a_2660_);
v_env_2696_ = lean_ctor_get(v___x_2663_, 0);
lean_inc_ref(v_env_2696_);
lean_dec(v___x_2663_);
v___x_2697_ = l_Lean_Doc_docInlineMdExt;
v_toEnvExtension_2698_ = lean_ctor_get(v___x_2697_, 0);
v_asyncMode_2699_ = lean_ctor_get(v_toEnvExtension_2698_, 2);
v___x_2700_ = lean_box(0);
v___x_2701_ = 0;
v___x_2702_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2662_, v___x_2697_, v_env_2696_, v_asyncMode_2699_, v___x_2700_, v___x_2701_);
v_imported_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_imported_2703_);
v_current_2704_ = lean_ctor_get(v___x_2702_, 1);
lean_inc(v_current_2704_);
lean_dec(v___x_2702_);
v___x_2705_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2704_, v_type_2658_);
lean_dec(v_current_2704_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2703_, v_type_2658_);
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
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___y_2768_; lean_object* v_env_2799_; lean_object* v___x_2800_; lean_object* v_toEnvExtension_2801_; lean_object* v_asyncMode_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v_imported_2806_; lean_object* v_current_2807_; lean_object* v___x_2808_; 
v___x_2765_ = ((lean_object*)(l_Lean_Doc_instInhabitedMdRendererState_default));
v___x_2766_ = lean_st_ref_get(v_a_2763_);
v_env_2799_ = lean_ctor_get(v___x_2766_, 0);
lean_inc_ref(v_env_2799_);
lean_dec(v___x_2766_);
v___x_2800_ = l_Lean_Doc_docBlockMdExt;
v_toEnvExtension_2801_ = lean_ctor_get(v___x_2800_, 0);
v_asyncMode_2802_ = lean_ctor_get(v_toEnvExtension_2801_, 2);
v___x_2803_ = lean_box(0);
v___x_2804_ = 0;
v___x_2805_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2765_, v___x_2800_, v_env_2799_, v_asyncMode_2802_, v___x_2803_, v___x_2804_);
v_imported_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_imported_2806_);
v_current_2807_ = lean_ctor_get(v___x_2805_, 1);
lean_inc(v_current_2807_);
lean_dec(v___x_2805_);
v___x_2808_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_current_2807_, v_typeName_2761_);
lean_dec(v_current_2807_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_imported_2806_, v_typeName_2761_);
lean_dec(v_imported_2806_);
v___y_2768_ = v___x_2809_;
goto v___jp_2767_;
}
else
{
lean_dec(v_imported_2806_);
v___y_2768_ = v___x_2808_;
goto v___jp_2767_;
}
v___jp_2767_:
{
if (lean_obj_tag(v___y_2768_) == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2769_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_builtinBlockMdRenderers;
v___x_2770_ = lean_st_ref_get(v___x_2769_);
v___x_2771_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2770_, v_typeName_2761_);
lean_dec(v___x_2770_);
v___x_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
return v___x_2772_;
}
else
{
lean_object* v_val_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2798_; 
v_val_2773_ = lean_ctor_get(v___y_2768_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___y_2768_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2775_ = v___y_2768_;
v_isShared_2776_ = v_isSharedCheck_2798_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_val_2773_);
lean_dec(v___y_2768_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2798_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
uint8_t v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = 1;
v___x_2778_ = l_Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0___redArg(v_val_2773_, v___x_2777_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2789_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2789_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2789_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v_a_2779_);
v___x_2784_ = v___x_2775_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2786_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2784_);
v___x_2786_ = v___x_2781_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_del_object(v___x_2775_);
v_a_2790_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2778_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2778_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe___boxed(lean_object* v_typeName_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v_typeName_2810_, v_a_2811_, v_a_2812_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_typeName_2810_);
return v_res_2814_;
}
}
static lean_object* _init_l_Lean_Doc_mdRendererHeartbeats(void){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = lean_unsigned_to_nat(200000u);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_withMdRendererBudget___redArg(lean_object* v_x_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v___x_2821_; lean_object* v_toCold_2822_; lean_object* v_currRecDepth_2823_; lean_object* v_ref_2824_; uint16_t v_optionFlags_2825_; uint8_t v_suppressElabErrors_2826_; uint8_t v_isRecordingDeps_2827_; lean_object* v_fileName_2828_; lean_object* v_fileMap_2829_; lean_object* v_options_2830_; lean_object* v_maxRecDepth_2831_; lean_object* v_currNamespace_2832_; lean_object* v_openDecls_2833_; lean_object* v_quotContext_2834_; lean_object* v_currMacroScope_2835_; lean_object* v_cancelTk_x3f_2836_; lean_object* v_inheritedTraceOptions_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2821_ = lean_io_get_num_heartbeats();
v_toCold_2822_ = lean_ctor_get(v_a_2818_, 0);
v_currRecDepth_2823_ = lean_ctor_get(v_a_2818_, 1);
v_ref_2824_ = lean_ctor_get(v_a_2818_, 2);
v_optionFlags_2825_ = lean_ctor_get_uint16(v_a_2818_, sizeof(void*)*3);
v_suppressElabErrors_2826_ = lean_ctor_get_uint8(v_a_2818_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2827_ = lean_ctor_get_uint8(v_a_2818_, sizeof(void*)*3 + 3);
v_fileName_2828_ = lean_ctor_get(v_toCold_2822_, 0);
v_fileMap_2829_ = lean_ctor_get(v_toCold_2822_, 1);
v_options_2830_ = lean_ctor_get(v_toCold_2822_, 2);
v_maxRecDepth_2831_ = lean_ctor_get(v_toCold_2822_, 3);
v_currNamespace_2832_ = lean_ctor_get(v_toCold_2822_, 4);
v_openDecls_2833_ = lean_ctor_get(v_toCold_2822_, 5);
v_quotContext_2834_ = lean_ctor_get(v_toCold_2822_, 8);
v_currMacroScope_2835_ = lean_ctor_get(v_toCold_2822_, 9);
v_cancelTk_x3f_2836_ = lean_ctor_get(v_toCold_2822_, 10);
v_inheritedTraceOptions_2837_ = lean_ctor_get(v_toCold_2822_, 11);
v___x_2838_ = lean_unsigned_to_nat(200000u);
lean_inc_ref(v_inheritedTraceOptions_2837_);
lean_inc(v_cancelTk_x3f_2836_);
lean_inc(v_currMacroScope_2835_);
lean_inc(v_quotContext_2834_);
lean_inc(v_openDecls_2833_);
lean_inc(v_currNamespace_2832_);
lean_inc(v_maxRecDepth_2831_);
lean_inc_ref(v_options_2830_);
lean_inc_ref(v_fileMap_2829_);
lean_inc_ref(v_fileName_2828_);
v___x_2839_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2839_, 0, v_fileName_2828_);
lean_ctor_set(v___x_2839_, 1, v_fileMap_2829_);
lean_ctor_set(v___x_2839_, 2, v_options_2830_);
lean_ctor_set(v___x_2839_, 3, v_maxRecDepth_2831_);
lean_ctor_set(v___x_2839_, 4, v_currNamespace_2832_);
lean_ctor_set(v___x_2839_, 5, v_openDecls_2833_);
lean_ctor_set(v___x_2839_, 6, v___x_2821_);
lean_ctor_set(v___x_2839_, 7, v___x_2838_);
lean_ctor_set(v___x_2839_, 8, v_quotContext_2834_);
lean_ctor_set(v___x_2839_, 9, v_currMacroScope_2835_);
lean_ctor_set(v___x_2839_, 10, v_cancelTk_x3f_2836_);
lean_ctor_set(v___x_2839_, 11, v_inheritedTraceOptions_2837_);
lean_inc(v_ref_2824_);
lean_inc(v_currRecDepth_2823_);
v___x_2840_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v_currRecDepth_2823_);
lean_ctor_set(v___x_2840_, 2, v_ref_2824_);
lean_ctor_set_uint16(v___x_2840_, sizeof(void*)*3, v_optionFlags_2825_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*3 + 2, v_suppressElabErrors_2826_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*3 + 3, v_isRecordingDeps_2827_);
lean_inc(v_a_2819_);
lean_inc(v_a_2817_);
v___x_2841_ = lean_apply_4(v_x_2816_, v_a_2817_, v___x_2840_, v_a_2819_, lean_box(0));
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
v___x_2871_ = l_Lean_Exception_isInterrupt(v_a_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec_ref_known(v___x_2869_, 1);
v___x_2872_ = lean_st_ref_swap(v_a_2864_, v___x_2868_);
lean_dec(v___x_2872_);
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
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1(lean_object* v___x_2894_, lean_object* v___x_2895_, lean_object* v___f_2896_, lean_object* v_go_2897_, lean_object* v_container_2898_, lean_object* v_content_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
if (lean_obj_tag(v_container_2898_) == 0)
{
lean_object* v_val_2904_; size_t v_sz_2905_; size_t v___x_2906_; lean_object* v___x_2907_; lean_object* v_fallback_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_val_2904_ = lean_ctor_get(v_container_2898_, 0);
lean_inc(v_val_2904_);
lean_dec_ref_known(v_container_2898_, 1);
v_sz_2905_ = lean_array_size(v_content_2899_);
v___x_2906_ = ((size_t)0ULL);
lean_inc_ref(v_content_2899_);
lean_inc_ref(v_go_2897_);
lean_inc_ref(v___x_2894_);
v___x_2907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2894_, v_go_2897_, v_sz_2905_, v___x_2906_, v_content_2899_);
lean_inc_ref(v___f_2896_);
v_fallback_2908_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_2908_, 0, lean_box(0));
lean_closure_set(v_fallback_2908_, 1, lean_box(0));
lean_closure_set(v_fallback_2908_, 2, v___x_2895_);
lean_closure_set(v_fallback_2908_, 3, lean_box(0));
lean_closure_set(v_fallback_2908_, 4, lean_box(0));
lean_closure_set(v_fallback_2908_, 5, v___x_2907_);
lean_closure_set(v_fallback_2908_, 6, v___f_2896_);
v___x_2909_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2904_);
v___x_2910_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_2909_, v___y_2901_, v___y_2902_);
lean_dec(v___x_2909_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2910_, 1);
if (lean_obj_tag(v_a_2911_) == 0)
{
lean_object* v___x_543__overap_2912_; lean_object* v___x_2913_; 
lean_dec_ref(v_fallback_2908_);
lean_dec(v_val_2904_);
v___x_543__overap_2912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2894_, v_go_2897_, v_sz_2905_, v___x_2906_, v_content_2899_);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
lean_inc(v___y_2900_);
v___x_2913_ = lean_apply_4(v___x_543__overap_2912_, v___y_2900_, v___y_2901_, v___y_2902_, lean_box(0));
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2915_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2913_, 1);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
lean_inc(v___y_2900_);
v___x_2915_ = lean_apply_5(v___f_2896_, v_a_2914_, v___y_2900_, v___y_2901_, v___y_2902_, lean_box(0));
return v___x_2915_;
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref(v___f_2896_);
v_a_2916_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2913_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2913_);
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
lean_object* v_val_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_dec_ref(v___f_2896_);
lean_dec_ref(v___x_2894_);
v_val_2924_ = lean_ctor_get(v_a_2911_, 0);
lean_inc(v_val_2924_);
lean_dec_ref_known(v_a_2911_, 1);
v___x_2925_ = lean_apply_3(v_val_2924_, v_go_2897_, v_val_2904_, v_content_2899_);
v___x_2926_ = l_Lean_Doc_withRendererFallback(v_fallback_2908_, v___x_2925_, v___y_2900_, v___y_2901_, v___y_2902_);
return v___x_2926_;
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec_ref(v_fallback_2908_);
lean_dec(v_val_2904_);
lean_dec_ref(v_content_2899_);
lean_dec_ref(v_go_2897_);
lean_dec_ref(v___f_2896_);
lean_dec_ref(v___x_2894_);
v_a_2927_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2910_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2910_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
else
{
size_t v_sz_2935_; size_t v___x_2936_; lean_object* v___x_558__overap_2937_; lean_object* v___x_2938_; 
lean_dec_ref_known(v_container_2898_, 1);
lean_dec_ref(v___f_2896_);
lean_dec_ref(v___x_2895_);
v_sz_2935_ = lean_array_size(v_content_2899_);
v___x_2936_ = ((size_t)0ULL);
v___x_558__overap_2937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2894_, v_go_2897_, v_sz_2935_, v___x_2936_, v_content_2899_);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
lean_inc(v___y_2900_);
v___x_2938_ = lean_apply_4(v___x_558__overap_2937_, v___y_2900_, v___y_2901_, v___y_2902_, lean_box(0));
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2947_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2941_ = v___x_2938_;
v_isShared_2942_ = v_isSharedCheck_2947_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2938_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2947_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; lean_object* v___x_2945_; 
v___x_2943_ = l_Lean_Doc_joinInlines(v_a_2939_);
lean_dec(v_a_2939_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 0, v___x_2943_);
v___x_2945_ = v___x_2941_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
v_a_2948_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2938_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2938_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed(lean_object* v___x_2956_, lean_object* v___x_2957_, lean_object* v___f_2958_, lean_object* v_go_2959_, lean_object* v_container_2960_, lean_object* v_content_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_Doc_instMarkdownInlineElabInline___lam__1(v___x_2956_, v___x_2957_, v___f_2958_, v_go_2959_, v_container_2960_, v_content_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
return v_res_2966_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownInlineElabInline(void){
_start:
{
lean_object* v___x_2968_; lean_object* v_toApplicative_2969_; lean_object* v_toFunctor_2970_; lean_object* v_toSeq_2971_; lean_object* v_toSeqLeft_2972_; lean_object* v_toSeqRight_2973_; lean_object* v___f_2974_; lean_object* v___f_2975_; lean_object* v___f_2976_; lean_object* v___f_2977_; lean_object* v___f_2978_; lean_object* v___x_2979_; lean_object* v___f_2980_; lean_object* v___f_2981_; lean_object* v___f_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___f_2986_; 
v___x_2968_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_2969_ = lean_ctor_get(v___x_2968_, 0);
v_toFunctor_2970_ = lean_ctor_get(v_toApplicative_2969_, 0);
v_toSeq_2971_ = lean_ctor_get(v_toApplicative_2969_, 2);
v_toSeqLeft_2972_ = lean_ctor_get(v_toApplicative_2969_, 3);
v_toSeqRight_2973_ = lean_ctor_get(v_toApplicative_2969_, 4);
v___f_2974_ = ((lean_object*)(l_Lean_Doc_instMarkdownInlineElabInline___closed__0));
v___f_2975_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_2976_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2970_, 2);
v___f_2977_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2977_, 0, v_toFunctor_2970_);
v___f_2978_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2978_, 0, v_toFunctor_2970_);
v___x_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___f_2977_);
lean_ctor_set(v___x_2979_, 1, v___f_2978_);
lean_inc(v_toSeqRight_2973_);
v___f_2980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2980_, 0, v_toSeqRight_2973_);
lean_inc(v_toSeqLeft_2972_);
v___f_2981_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2981_, 0, v_toSeqLeft_2972_);
lean_inc(v_toSeq_2971_);
v___f_2982_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2982_, 0, v_toSeq_2971_);
v___x_2983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2979_);
lean_ctor_set(v___x_2983_, 1, v___f_2975_);
lean_ctor_set(v___x_2983_, 2, v___f_2982_);
lean_ctor_set(v___x_2983_, 3, v___f_2981_);
lean_ctor_set(v___x_2983_, 4, v___f_2980_);
v___x_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
lean_ctor_set(v___x_2984_, 1, v___f_2976_);
lean_inc_ref(v___x_2984_);
v___x_2985_ = l_StateRefT_x27_instMonad___redArg(v___x_2984_);
v___f_2986_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownInlineElabInline___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2986_, 0, v___x_2985_);
lean_closure_set(v___f_2986_, 1, v___x_2984_);
lean_closure_set(v___f_2986_, 2, v___f_2974_);
return v___f_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v_____do__lift_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = l_Lean_Doc_joinBlocks(v_____do__lift_2987_);
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object* v_____do__lift_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__0(v_____do__lift_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v_____do__lift_2994_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object* v___x_3000_, lean_object* v___x_3001_, lean_object* v___f_3002_, lean_object* v_goI_3003_, lean_object* v_goB_3004_, lean_object* v_container_3005_, lean_object* v_content_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
if (lean_obj_tag(v_container_3005_) == 0)
{
lean_object* v_val_3011_; size_t v_sz_3012_; size_t v___x_3013_; lean_object* v___x_3014_; lean_object* v_fallback_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_val_3011_ = lean_ctor_get(v_container_3005_, 0);
lean_inc(v_val_3011_);
lean_dec_ref_known(v_container_3005_, 1);
v_sz_3012_ = lean_array_size(v_content_3006_);
v___x_3013_ = ((size_t)0ULL);
lean_inc_ref(v_content_3006_);
lean_inc_ref(v_goB_3004_);
lean_inc_ref(v___x_3000_);
v___x_3014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3000_, v_goB_3004_, v_sz_3012_, v___x_3013_, v_content_3006_);
lean_inc_ref(v___f_3002_);
v_fallback_3015_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v_fallback_3015_, 0, lean_box(0));
lean_closure_set(v_fallback_3015_, 1, lean_box(0));
lean_closure_set(v_fallback_3015_, 2, v___x_3001_);
lean_closure_set(v_fallback_3015_, 3, lean_box(0));
lean_closure_set(v_fallback_3015_, 4, lean_box(0));
lean_closure_set(v_fallback_3015_, 5, v___x_3014_);
lean_closure_set(v_fallback_3015_, 6, v___f_3002_);
v___x_3016_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3011_);
v___x_3017_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_3016_, v___y_3008_, v___y_3009_);
lean_dec(v___x_3016_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
if (lean_obj_tag(v_a_3018_) == 0)
{
lean_object* v___x_543__overap_3019_; lean_object* v___x_3020_; 
lean_dec_ref(v_fallback_3015_);
lean_dec(v_val_3011_);
lean_dec_ref(v_goI_3003_);
v___x_543__overap_3019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3000_, v_goB_3004_, v_sz_3012_, v___x_3013_, v_content_3006_);
lean_inc(v___y_3009_);
lean_inc_ref(v___y_3008_);
lean_inc(v___y_3007_);
v___x_3020_ = lean_apply_4(v___x_543__overap_3019_, v___y_3007_, v___y_3008_, v___y_3009_, lean_box(0));
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
lean_inc(v___y_3009_);
lean_inc_ref(v___y_3008_);
lean_inc(v___y_3007_);
v___x_3022_ = lean_apply_5(v___f_3002_, v_a_3021_, v___y_3007_, v___y_3008_, v___y_3009_, lean_box(0));
return v___x_3022_;
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref(v___f_3002_);
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
lean_object* v_val_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec_ref(v___f_3002_);
lean_dec_ref(v___x_3000_);
v_val_3031_ = lean_ctor_get(v_a_3018_, 0);
lean_inc(v_val_3031_);
lean_dec_ref_known(v_a_3018_, 1);
v___x_3032_ = lean_apply_4(v_val_3031_, v_goI_3003_, v_goB_3004_, v_val_3011_, v_content_3006_);
v___x_3033_ = l_Lean_Doc_withRendererFallback(v_fallback_3015_, v___x_3032_, v___y_3007_, v___y_3008_, v___y_3009_);
return v___x_3033_;
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref(v_fallback_3015_);
lean_dec(v_val_3011_);
lean_dec_ref(v_content_3006_);
lean_dec_ref(v_goB_3004_);
lean_dec_ref(v_goI_3003_);
lean_dec_ref(v___f_3002_);
lean_dec_ref(v___x_3000_);
v_a_3034_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3017_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3017_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
else
{
size_t v_sz_3042_; size_t v___x_3043_; lean_object* v___x_558__overap_3044_; lean_object* v___x_3045_; 
lean_dec_ref_known(v_container_3005_, 1);
lean_dec_ref(v_goI_3003_);
lean_dec_ref(v___f_3002_);
lean_dec_ref(v___x_3001_);
v_sz_3042_ = lean_array_size(v_content_3006_);
v___x_3043_ = ((size_t)0ULL);
v___x_558__overap_3044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3000_, v_goB_3004_, v_sz_3042_, v___x_3043_, v_content_3006_);
lean_inc(v___y_3009_);
lean_inc_ref(v___y_3008_);
lean_inc(v___y_3007_);
v___x_3045_ = lean_apply_4(v___x_558__overap_3044_, v___y_3007_, v___y_3008_, v___y_3009_, lean_box(0));
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3054_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3048_ = v___x_3045_;
v_isShared_3049_ = v_isSharedCheck_3054_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3054_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3050_ = l_Lean_Doc_joinBlocks(v_a_3046_);
lean_dec(v_a_3046_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 0, v___x_3050_);
v___x_3052_ = v___x_3048_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
v_a_3055_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3045_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3045_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object* v___x_3063_, lean_object* v___x_3064_, lean_object* v___f_3065_, lean_object* v_goI_3066_, lean_object* v_goB_3067_, lean_object* v_container_3068_, lean_object* v_content_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_3063_, v___x_3064_, v___f_3065_, v_goI_3066_, v_goB_3067_, v_container_3068_, v_content_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
return v_res_3074_;
}
}
static lean_object* _init_l_Lean_Doc_instMarkdownBlockElabInlineElabBlock(void){
_start:
{
lean_object* v___x_3076_; lean_object* v_toApplicative_3077_; lean_object* v_toFunctor_3078_; lean_object* v_toSeq_3079_; lean_object* v_toSeqLeft_3080_; lean_object* v_toSeqRight_3081_; lean_object* v___f_3082_; lean_object* v___f_3083_; lean_object* v___f_3084_; lean_object* v___f_3085_; lean_object* v___f_3086_; lean_object* v___x_3087_; lean_object* v___f_3088_; lean_object* v___f_3089_; lean_object* v___f_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___f_3094_; 
v___x_3076_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3077_ = lean_ctor_get(v___x_3076_, 0);
v_toFunctor_3078_ = lean_ctor_get(v_toApplicative_3077_, 0);
v_toSeq_3079_ = lean_ctor_get(v_toApplicative_3077_, 2);
v_toSeqLeft_3080_ = lean_ctor_get(v_toApplicative_3077_, 3);
v_toSeqRight_3081_ = lean_ctor_get(v_toApplicative_3077_, 4);
v___f_3082_ = ((lean_object*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___closed__0));
v___f_3083_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3084_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3078_, 2);
v___f_3085_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3085_, 0, v_toFunctor_3078_);
v___f_3086_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3086_, 0, v_toFunctor_3078_);
v___x_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___f_3085_);
lean_ctor_set(v___x_3087_, 1, v___f_3086_);
lean_inc(v_toSeqRight_3081_);
v___f_3088_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3088_, 0, v_toSeqRight_3081_);
lean_inc(v_toSeqLeft_3080_);
v___f_3089_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3089_, 0, v_toSeqLeft_3080_);
lean_inc(v_toSeq_3079_);
v___f_3090_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3090_, 0, v_toSeq_3079_);
v___x_3091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3087_);
lean_ctor_set(v___x_3091_, 1, v___f_3083_);
lean_ctor_set(v___x_3091_, 2, v___f_3090_);
lean_ctor_set(v___x_3091_, 3, v___f_3089_);
lean_ctor_set(v___x_3091_, 4, v___f_3088_);
v___x_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v___f_3084_);
lean_inc_ref(v___x_3092_);
v___x_3093_ = l_StateRefT_x27_instMonad___redArg(v___x_3092_);
v___f_3094_ = lean_alloc_closure((void*)(l_Lean_Doc_instMarkdownBlockElabInlineElabBlock___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3094_, 0, v___x_3093_);
lean_closure_set(v___f_3094_, 1, v___x_3092_);
lean_closure_set(v___f_3094_, 2, v___f_3082_);
return v___f_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0(lean_object* v___x_3095_, lean_object* v___x_3096_, lean_object* v_part_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_unsigned_to_nat(0u);
v___x_3103_ = l_Lean_Doc_partMarkdown___redArg(v___x_3095_, v___x_3096_, v___x_3102_, v_part_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed(lean_object* v___x_3104_, lean_object* v___x_3105_, lean_object* v_part_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__0(v___x_3104_, v___x_3105_, v_part_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1(lean_object* v___x_3112_, lean_object* v___x_3113_, lean_object* v___x_3114_, lean_object* v___f_3115_, lean_object* v_x_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v_text_3121_; lean_object* v_subsections_3122_; lean_object* v___x_3123_; size_t v_sz_3124_; size_t v___x_3125_; lean_object* v___x_443__overap_3126_; lean_object* v___x_3127_; 
v_text_3121_ = lean_ctor_get(v_x_3116_, 0);
lean_inc_ref(v_text_3121_);
v_subsections_3122_ = lean_ctor_get(v_x_3116_, 1);
lean_inc_ref(v_subsections_3122_);
lean_dec_ref(v_x_3116_);
v___x_3123_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3123_, 0, lean_box(0));
lean_closure_set(v___x_3123_, 1, lean_box(0));
lean_closure_set(v___x_3123_, 2, v___x_3112_);
lean_closure_set(v___x_3123_, 3, v___x_3113_);
v_sz_3124_ = lean_array_size(v_text_3121_);
v___x_3125_ = ((size_t)0ULL);
lean_inc_ref(v___x_3114_);
v___x_443__overap_3126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3114_, v___x_3123_, v_sz_3124_, v___x_3125_, v_text_3121_);
lean_inc(v___y_3119_);
lean_inc_ref(v___y_3118_);
lean_inc(v___y_3117_);
v___x_3127_ = lean_apply_4(v___x_443__overap_3126_, v___y_3117_, v___y_3118_, v___y_3119_, lean_box(0));
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; size_t v_sz_3129_; lean_object* v___x_446__overap_3130_; lean_object* v___x_3131_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3127_, 1);
v_sz_3129_ = lean_array_size(v_subsections_3122_);
v___x_446__overap_3130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3114_, v___f_3115_, v_sz_3129_, v___x_3125_, v_subsections_3122_);
lean_inc(v___y_3119_);
lean_inc_ref(v___y_3118_);
lean_inc(v___y_3117_);
v___x_3131_ = lean_apply_4(v___x_446__overap_3130_, v___y_3117_, v___y_3118_, v___y_3119_, lean_box(0));
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3141_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3134_ = v___x_3131_;
v_isShared_3135_ = v_isSharedCheck_3141_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3131_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3141_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3136_ = l_Array_append___redArg(v_a_3128_, v_a_3132_);
lean_dec(v_a_3132_);
v___x_3137_ = l_Lean_Doc_joinBlocks(v___x_3136_);
lean_dec_ref(v___x_3136_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v___x_3137_);
v___x_3139_ = v___x_3134_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v_a_3128_);
v_a_3142_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3131_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3131_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec_ref(v_subsections_3122_);
lean_dec_ref(v___f_3115_);
lean_dec_ref(v___x_3114_);
v_a_3150_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3127_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3127_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed(lean_object* v___x_3158_, lean_object* v___x_3159_, lean_object* v___x_3160_, lean_object* v___f_3161_, lean_object* v_x_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Lean_Doc_instToMarkdownVersoDocString___lam__1(v___x_3158_, v___x_3159_, v___x_3160_, v___f_3161_, v_x_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
return v_res_3167_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___f_3170_; 
v___x_3168_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3169_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3170_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3170_, 0, v___x_3169_);
lean_closure_set(v___f_3170_, 1, v___x_3168_);
return v___f_3170_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownVersoDocString(void){
_start:
{
lean_object* v___x_3171_; lean_object* v_toApplicative_3172_; lean_object* v_toFunctor_3173_; lean_object* v_toSeq_3174_; lean_object* v_toSeqLeft_3175_; lean_object* v_toSeqRight_3176_; lean_object* v___f_3177_; lean_object* v___f_3178_; lean_object* v___f_3179_; lean_object* v___f_3180_; lean_object* v___x_3181_; lean_object* v___f_3182_; lean_object* v___f_3183_; lean_object* v___f_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___f_3190_; lean_object* v___f_3191_; 
v___x_3171_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3172_ = lean_ctor_get(v___x_3171_, 0);
v_toFunctor_3173_ = lean_ctor_get(v_toApplicative_3172_, 0);
v_toSeq_3174_ = lean_ctor_get(v_toApplicative_3172_, 2);
v_toSeqLeft_3175_ = lean_ctor_get(v_toApplicative_3172_, 3);
v_toSeqRight_3176_ = lean_ctor_get(v_toApplicative_3172_, 4);
v___f_3177_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3178_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3173_, 2);
v___f_3179_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3179_, 0, v_toFunctor_3173_);
v___f_3180_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3180_, 0, v_toFunctor_3173_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___f_3179_);
lean_ctor_set(v___x_3181_, 1, v___f_3180_);
lean_inc(v_toSeqRight_3176_);
v___f_3182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3182_, 0, v_toSeqRight_3176_);
lean_inc(v_toSeqLeft_3175_);
v___f_3183_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3183_, 0, v_toSeqLeft_3175_);
lean_inc(v_toSeq_3174_);
v___f_3184_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3184_, 0, v_toSeq_3174_);
v___x_3185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3181_);
lean_ctor_set(v___x_3185_, 1, v___f_3177_);
lean_ctor_set(v___x_3185_, 2, v___f_3184_);
lean_ctor_set(v___x_3185_, 3, v___f_3183_);
lean_ctor_set(v___x_3185_, 4, v___f_3182_);
v___x_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
lean_ctor_set(v___x_3186_, 1, v___f_3178_);
v___x_3187_ = l_StateRefT_x27_instMonad___redArg(v___x_3186_);
v___x_3188_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3189_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3190_ = lean_obj_once(&l_Lean_Doc_instToMarkdownVersoDocString___closed__0, &l_Lean_Doc_instToMarkdownVersoDocString___closed__0_once, _init_l_Lean_Doc_instToMarkdownVersoDocString___closed__0);
v___f_3191_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownVersoDocString___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3191_, 0, v___x_3188_);
lean_closure_set(v___f_3191_, 1, v___x_3189_);
lean_closure_set(v___f_3191_, 2, v___x_3187_);
lean_closure_set(v___f_3191_, 3, v___f_3190_);
return v___f_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0(lean_object* v___x_3192_, lean_object* v___x_3193_, lean_object* v_x_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_snd_3199_; lean_object* v_fst_3200_; lean_object* v_snd_3201_; lean_object* v___x_3202_; 
v_snd_3199_ = lean_ctor_get(v_x_3194_, 1);
lean_inc(v_snd_3199_);
v_fst_3200_ = lean_ctor_get(v_x_3194_, 0);
lean_inc(v_fst_3200_);
lean_dec_ref(v_x_3194_);
v_snd_3201_ = lean_ctor_get(v_snd_3199_, 1);
lean_inc(v_snd_3201_);
lean_dec(v_snd_3199_);
v___x_3202_ = l_Lean_Doc_partMarkdown___redArg(v___x_3192_, v___x_3193_, v_fst_3200_, v_snd_3201_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec(v_fst_3200_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_3203_, lean_object* v___x_3204_, lean_object* v_x_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Lean_Doc_instToMarkdownSnippet___lam__0(v___x_3203_, v___x_3204_, v_x_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1(lean_object* v___x_3211_, lean_object* v___x_3212_, lean_object* v___x_3213_, lean_object* v___f_3214_, lean_object* v_x_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_text_3220_; lean_object* v_sections_3221_; lean_object* v___x_3222_; size_t v_sz_3223_; size_t v___x_3224_; lean_object* v___x_490__overap_3225_; lean_object* v___x_3226_; 
v_text_3220_ = lean_ctor_get(v_x_3215_, 0);
lean_inc_ref(v_text_3220_);
v_sections_3221_ = lean_ctor_get(v_x_3215_, 1);
lean_inc_ref(v_sections_3221_);
lean_dec_ref(v_x_3215_);
v___x_3222_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___boxed), 9, 4);
lean_closure_set(v___x_3222_, 0, lean_box(0));
lean_closure_set(v___x_3222_, 1, lean_box(0));
lean_closure_set(v___x_3222_, 2, v___x_3211_);
lean_closure_set(v___x_3222_, 3, v___x_3212_);
v_sz_3223_ = lean_array_size(v_text_3220_);
v___x_3224_ = ((size_t)0ULL);
lean_inc_ref(v___x_3213_);
v___x_490__overap_3225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3213_, v___x_3222_, v_sz_3223_, v___x_3224_, v_text_3220_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3217_);
lean_inc(v___y_3216_);
v___x_3226_ = lean_apply_4(v___x_490__overap_3225_, v___y_3216_, v___y_3217_, v___y_3218_, lean_box(0));
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; size_t v_sz_3228_; lean_object* v___x_493__overap_3229_; lean_object* v___x_3230_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v_sz_3228_ = lean_array_size(v_sections_3221_);
v___x_493__overap_3229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3213_, v___f_3214_, v_sz_3228_, v___x_3224_, v_sections_3221_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3217_);
lean_inc(v___y_3216_);
v___x_3230_ = lean_apply_4(v___x_493__overap_3229_, v___y_3216_, v___y_3217_, v___y_3218_, lean_box(0));
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3240_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3233_ = v___x_3230_;
v_isShared_3234_ = v_isSharedCheck_3240_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3230_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3240_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3235_ = l_Array_append___redArg(v_a_3227_, v_a_3231_);
lean_dec(v_a_3231_);
v___x_3236_ = l_Lean_Doc_joinBlocks(v___x_3235_);
lean_dec_ref(v___x_3235_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v___x_3236_);
v___x_3238_ = v___x_3233_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
lean_dec(v_a_3227_);
v_a_3241_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3230_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3230_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec_ref(v_sections_3221_);
lean_dec_ref(v___f_3214_);
lean_dec_ref(v___x_3213_);
v_a_3249_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3226_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3226_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_3257_, lean_object* v___x_3258_, lean_object* v___x_3259_, lean_object* v___f_3260_, lean_object* v_x_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Lean_Doc_instToMarkdownSnippet___lam__1(v___x_3257_, v___x_3258_, v___x_3259_, v___f_3260_, v_x_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
return v_res_3266_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___f_3269_; 
v___x_3267_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___x_3268_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___f_3269_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3269_, 0, v___x_3268_);
lean_closure_set(v___f_3269_, 1, v___x_3267_);
return v___f_3269_;
}
}
static lean_object* _init_l_Lean_Doc_instToMarkdownSnippet(void){
_start:
{
lean_object* v___x_3270_; lean_object* v_toApplicative_3271_; lean_object* v_toFunctor_3272_; lean_object* v_toSeq_3273_; lean_object* v_toSeqLeft_3274_; lean_object* v_toSeqRight_3275_; lean_object* v___f_3276_; lean_object* v___f_3277_; lean_object* v___f_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; lean_object* v___f_3281_; lean_object* v___f_3282_; lean_object* v___f_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___f_3289_; lean_object* v___f_3290_; 
v___x_3270_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1);
v_toApplicative_3271_ = lean_ctor_get(v___x_3270_, 0);
v_toFunctor_3272_ = lean_ctor_get(v_toApplicative_3271_, 0);
v_toSeq_3273_ = lean_ctor_get(v_toApplicative_3271_, 2);
v_toSeqLeft_3274_ = lean_ctor_get(v_toApplicative_3271_, 3);
v_toSeqRight_3275_ = lean_ctor_get(v_toApplicative_3271_, 4);
v___f_3276_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2));
v___f_3277_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3272_, 2);
v___f_3278_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3278_, 0, v_toFunctor_3272_);
v___f_3279_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3279_, 0, v_toFunctor_3272_);
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___f_3278_);
lean_ctor_set(v___x_3280_, 1, v___f_3279_);
lean_inc(v_toSeqRight_3275_);
v___f_3281_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3281_, 0, v_toSeqRight_3275_);
lean_inc(v_toSeqLeft_3274_);
v___f_3282_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3282_, 0, v_toSeqLeft_3274_);
lean_inc(v_toSeq_3273_);
v___f_3283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3283_, 0, v_toSeq_3273_);
v___x_3284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3280_);
lean_ctor_set(v___x_3284_, 1, v___f_3276_);
lean_ctor_set(v___x_3284_, 2, v___f_3283_);
lean_ctor_set(v___x_3284_, 3, v___f_3282_);
lean_ctor_set(v___x_3284_, 4, v___f_3281_);
v___x_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v___f_3277_);
v___x_3286_ = l_StateRefT_x27_instMonad___redArg(v___x_3285_);
v___x_3287_ = l_Lean_Doc_instMarkdownInlineElabInline;
v___x_3288_ = l_Lean_Doc_instMarkdownBlockElabInlineElabBlock;
v___f_3289_ = lean_obj_once(&l_Lean_Doc_instToMarkdownSnippet___closed__0, &l_Lean_Doc_instToMarkdownSnippet___closed__0_once, _init_l_Lean_Doc_instToMarkdownSnippet___closed__0);
v___f_3290_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownSnippet___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3290_, 0, v___x_3287_);
lean_closure_set(v___f_3290_, 1, v___x_3288_);
lean_closure_set(v___f_3290_, 2, v___x_3286_);
lean_closure_set(v___f_3290_, 3, v___f_3289_);
return v___f_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(lean_object* v_opts_3291_, lean_object* v_opt_3292_){
_start:
{
lean_object* v_name_3293_; lean_object* v_defValue_3294_; lean_object* v_map_3295_; lean_object* v___x_3296_; 
v_name_3293_ = lean_ctor_get(v_opt_3292_, 0);
v_defValue_3294_ = lean_ctor_get(v_opt_3292_, 1);
v_map_3295_ = lean_ctor_get(v_opts_3291_, 0);
v___x_3296_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3295_, v_name_3293_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_inc(v_defValue_3294_);
return v_defValue_3294_;
}
else
{
lean_object* v_val_3297_; 
v_val_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_val_3297_);
lean_dec_ref_known(v___x_3296_, 1);
if (lean_obj_tag(v_val_3297_) == 3)
{
lean_object* v_v_3298_; 
v_v_3298_ = lean_ctor_get(v_val_3297_, 0);
lean_inc(v_v_3298_);
lean_dec_ref_known(v_val_3297_, 1);
return v_v_3298_;
}
else
{
lean_dec(v_val_3297_);
lean_inc(v_defValue_3294_);
return v_defValue_3294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0___boxed(lean_object* v_opts_3299_, lean_object* v_opt_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_opts_3299_, v_opt_3300_);
lean_dec_ref(v_opt_3300_);
lean_dec_ref(v_opts_3299_);
return v_res_3301_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__1(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = lean_unsigned_to_nat(1u);
v___x_3304_ = l_Lean_firstFrontendMacroScope;
v___x_3305_ = lean_nat_add(v___x_3304_, v___x_3303_);
return v___x_3305_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__6(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_unsigned_to_nat(32u);
v___x_3317_ = lean_mk_empty_array_with_capacity(v___x_3316_);
v___x_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
return v___x_3318_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__7(void){
_start:
{
size_t v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3319_ = ((size_t)5ULL);
v___x_3320_ = lean_unsigned_to_nat(0u);
v___x_3321_ = lean_unsigned_to_nat(32u);
v___x_3322_ = lean_mk_empty_array_with_capacity(v___x_3321_);
v___x_3323_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__6, &l_Lean_Doc_runMarkdown___redArg___closed__6_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__6);
v___x_3324_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v___x_3322_);
lean_ctor_set(v___x_3324_, 2, v___x_3320_);
lean_ctor_set(v___x_3324_, 3, v___x_3320_);
lean_ctor_set_usize(v___x_3324_, 4, v___x_3319_);
return v___x_3324_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__8(void){
_start:
{
lean_object* v___x_3325_; uint64_t v___x_3326_; lean_object* v___x_3327_; 
v___x_3325_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__7, &l_Lean_Doc_runMarkdown___redArg___closed__7_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__7);
v___x_3326_ = 0ULL;
v___x_3327_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set_uint64(v___x_3327_, sizeof(void*)*1, v___x_3326_);
return v___x_3327_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__9(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConst___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
return v___x_3329_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__10(void){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__9, &l_Lean_Doc_runMarkdown___redArg___closed__9_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__9);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
return v___x_3331_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__12(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3334_ = lean_unsigned_to_nat(0u);
v___x_3335_ = l_Lean_Options_empty;
v___x_3336_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__11));
v___x_3337_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
lean_ctor_set(v___x_3337_, 1, v___x_3335_);
lean_ctor_set(v___x_3337_, 2, v___x_3336_);
lean_ctor_set(v___x_3337_, 3, v___x_3334_);
lean_ctor_set(v___x_3337_, 4, v___x_3334_);
lean_ctor_set(v___x_3337_, 5, v___x_3334_);
return v___x_3337_;
}
}
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__13(void){
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
static lean_object* _init_l_Lean_Doc_runMarkdown___redArg___closed__14(void){
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
lean_object* v_a_3356_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; uint16_t v___x_3366_; uint8_t v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; uint8_t v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v_fileName_3382_; lean_object* v_fileMap_3383_; lean_object* v_currNamespace_3384_; lean_object* v_openDecls_3385_; lean_object* v_initHeartbeats_3386_; lean_object* v_maxHeartbeats_3387_; lean_object* v_quotContext_3388_; lean_object* v_currMacroScope_3389_; lean_object* v_cancelTk_x3f_3390_; lean_object* v_inheritedTraceOptions_3391_; lean_object* v_currRecDepth_3392_; lean_object* v_ref_3393_; uint8_t v_suppressElabErrors_3394_; uint8_t v_isRecordingDeps_3395_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___y_3436_; lean_object* v_env_3457_; uint8_t v___x_3458_; uint16_t v___x_3459_; uint16_t v___x_3460_; uint16_t v___x_3461_; uint8_t v___x_3462_; 
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
v___x_3375_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__13, &l_Lean_Doc_runMarkdown___redArg___closed__13_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__13);
v___x_3376_ = 1;
v___x_3377_ = lean_obj_once(&l_Lean_Doc_runMarkdown___redArg___closed__14, &l_Lean_Doc_runMarkdown___redArg___closed__14_once, _init_l_Lean_Doc_runMarkdown___redArg___closed__14);
v___x_3378_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3378_, 0, v_env_3348_);
lean_ctor_set(v___x_3378_, 1, v___x_3368_);
lean_ctor_set(v___x_3378_, 2, v___x_3369_);
lean_ctor_set(v___x_3378_, 3, v___x_3370_);
lean_ctor_set(v___x_3378_, 4, v___x_3371_);
lean_ctor_set(v___x_3378_, 5, v___x_3372_);
lean_ctor_set(v___x_3378_, 6, v___x_3374_);
lean_ctor_set(v___x_3378_, 7, v___x_3375_);
lean_ctor_set(v___x_3378_, 8, v___x_3377_);
lean_ctor_set(v___x_3378_, 9, v___x_3373_);
v___x_3379_ = lean_io_get_num_heartbeats();
v___x_3380_ = lean_st_mk_ref(v___x_3378_);
v___x_3432_ = l_Lean_inheritedTraceOptions;
v___x_3433_ = lean_st_ref_get(v___x_3432_);
v___x_3434_ = lean_st_ref_get(v___x_3380_);
v_env_3457_ = lean_ctor_get(v___x_3434_, 0);
lean_inc_ref(v_env_3457_);
lean_dec(v___x_3434_);
v___x_3458_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3457_);
lean_dec_ref(v_env_3457_);
v___x_3459_ = 512;
v___x_3460_ = lean_uint16_land(v___x_3366_, v___x_3459_);
v___x_3461_ = 0;
v___x_3462_ = lean_uint16_dec_eq(v___x_3460_, v___x_3461_);
if (v___x_3462_ == 0)
{
if (v___x_3458_ == 0)
{
v___y_3436_ = v___x_3376_;
goto v___jp_3435_;
}
else
{
v_fileName_3382_ = v___x_3359_;
v_fileMap_3383_ = v___x_3360_;
v_currNamespace_3384_ = v_currNamespace_3351_;
v_openDecls_3385_ = v_openDecls_3352_;
v_initHeartbeats_3386_ = v___x_3379_;
v_maxHeartbeats_3387_ = v___x_3362_;
v_quotContext_3388_ = v___x_3363_;
v_currMacroScope_3389_ = v___x_3364_;
v_cancelTk_x3f_3390_ = v_cancelTk_x3f_3353_;
v_inheritedTraceOptions_3391_ = v___x_3433_;
v_currRecDepth_3392_ = v___x_3361_;
v_ref_3393_ = v___x_3365_;
v_suppressElabErrors_3394_ = v___x_3367_;
v_isRecordingDeps_3395_ = v___x_3367_;
goto v___jp_3381_;
}
}
else
{
if (v___x_3458_ == 0)
{
v_fileName_3382_ = v___x_3359_;
v_fileMap_3383_ = v___x_3360_;
v_currNamespace_3384_ = v_currNamespace_3351_;
v_openDecls_3385_ = v_openDecls_3352_;
v_initHeartbeats_3386_ = v___x_3379_;
v_maxHeartbeats_3387_ = v___x_3362_;
v_quotContext_3388_ = v___x_3363_;
v_currMacroScope_3389_ = v___x_3364_;
v_cancelTk_x3f_3390_ = v_cancelTk_x3f_3353_;
v_inheritedTraceOptions_3391_ = v___x_3433_;
v_currRecDepth_3392_ = v___x_3361_;
v_ref_3393_ = v___x_3365_;
v_suppressElabErrors_3394_ = v___x_3367_;
v_isRecordingDeps_3395_ = v___x_3367_;
goto v___jp_3381_;
}
else
{
v___y_3436_ = v___x_3367_;
goto v___jp_3435_;
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
v___jp_3381_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3396_ = l_Lean_maxRecDepth;
v___x_3397_ = l_Lean_Option_get___at___00Lean_Doc_runMarkdown_spec__0(v_options_3350_, v___x_3396_);
lean_inc(v_currMacroScope_3389_);
lean_inc(v_quotContext_3388_);
lean_inc_ref(v_fileMap_3383_);
lean_inc_ref(v_fileName_3382_);
v___x_3398_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3398_, 0, v_fileName_3382_);
lean_ctor_set(v___x_3398_, 1, v_fileMap_3383_);
lean_ctor_set(v___x_3398_, 2, v_options_3350_);
lean_ctor_set(v___x_3398_, 3, v___x_3397_);
lean_ctor_set(v___x_3398_, 4, v_currNamespace_3384_);
lean_ctor_set(v___x_3398_, 5, v_openDecls_3385_);
lean_ctor_set(v___x_3398_, 6, v_initHeartbeats_3386_);
lean_ctor_set(v___x_3398_, 7, v_maxHeartbeats_3387_);
lean_ctor_set(v___x_3398_, 8, v_quotContext_3388_);
lean_ctor_set(v___x_3398_, 9, v_currMacroScope_3389_);
lean_ctor_set(v___x_3398_, 10, v_cancelTk_x3f_3390_);
lean_ctor_set(v___x_3398_, 11, v_inheritedTraceOptions_3391_);
lean_inc(v_ref_3393_);
v___x_3399_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
lean_ctor_set(v___x_3399_, 1, v_currRecDepth_3392_);
lean_ctor_set(v___x_3399_, 2, v_ref_3393_);
lean_ctor_set_uint16(v___x_3399_, sizeof(void*)*3, v___x_3366_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*3 + 2, v_suppressElabErrors_3394_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*3 + 3, v_isRecordingDeps_3395_);
lean_inc(v___x_3380_);
v___x_3400_ = lean_apply_3(v_act_3349_, v___x_3399_, v___x_3380_, lean_box(0));
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3409_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3409_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3409_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3405_ = lean_st_ref_get(v___x_3380_);
lean_dec(v___x_3380_);
lean_dec(v___x_3405_);
if (v_isShared_3404_ == 0)
{
v___x_3407_ = v___x_3403_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3401_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3431_; 
lean_dec(v___x_3380_);
v_a_3410_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3412_ = v___x_3400_;
v_isShared_3413_ = v_isSharedCheck_3431_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3400_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3431_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
if (lean_obj_tag(v_a_3410_) == 0)
{
lean_object* v_msg_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
v_msg_3414_ = lean_ctor_get(v_a_3410_, 1);
lean_inc_ref(v_msg_3414_);
lean_dec_ref_known(v_a_3410_, 2);
v___x_3415_ = l_Lean_MessageData_toString(v_msg_3414_);
v___x_3416_ = lean_mk_io_user_error(v___x_3415_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v___x_3416_);
v___x_3418_ = v___x_3412_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
else
{
lean_object* v_id_3420_; lean_object* v___x_3421_; 
lean_del_object(v___x_3412_);
v_id_3420_ = lean_ctor_get(v_a_3410_, 0);
lean_inc(v_id_3420_);
lean_dec_ref_known(v_a_3410_, 2);
v___x_3421_ = l_Lean_InternalExceptionId_getName(v_id_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
lean_dec(v_id_3420_);
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref_known(v___x_3421_, 1);
v___x_3423_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__15));
v___x_3424_ = l_Lean_Name_toString(v_a_3422_, v___x_3376_);
v___x_3425_ = lean_string_append(v___x_3423_, v___x_3424_);
lean_dec_ref(v___x_3424_);
v_a_3356_ = v___x_3425_;
goto v___jp_3355_;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
lean_dec_ref_known(v___x_3421_, 1);
v___x_3426_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__16));
v___x_3427_ = l_Nat_reprFast(v_id_3420_);
v___x_3428_ = lean_string_append(v___x_3426_, v___x_3427_);
lean_dec_ref(v___x_3427_);
v___x_3429_ = ((lean_object*)(l_Lean_Doc_runMarkdown___redArg___closed__17));
v___x_3430_ = lean_string_append(v___x_3428_, v___x_3429_);
v_a_3356_ = v___x_3430_;
goto v___jp_3355_;
}
}
}
}
}
v___jp_3435_:
{
lean_object* v___x_3437_; lean_object* v_env_3438_; lean_object* v_nextMacroScope_3439_; lean_object* v_ngen_3440_; lean_object* v_auxDeclNGen_3441_; lean_object* v_traceState_3442_; lean_object* v_recordedDeps_3443_; lean_object* v_messages_3444_; lean_object* v_infoState_3445_; lean_object* v_snapshotTasks_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3455_; 
v___x_3437_ = lean_st_ref_take(v___x_3380_);
v_env_3438_ = lean_ctor_get(v___x_3437_, 0);
v_nextMacroScope_3439_ = lean_ctor_get(v___x_3437_, 1);
v_ngen_3440_ = lean_ctor_get(v___x_3437_, 2);
v_auxDeclNGen_3441_ = lean_ctor_get(v___x_3437_, 3);
v_traceState_3442_ = lean_ctor_get(v___x_3437_, 4);
v_recordedDeps_3443_ = lean_ctor_get(v___x_3437_, 6);
v_messages_3444_ = lean_ctor_get(v___x_3437_, 7);
v_infoState_3445_ = lean_ctor_get(v___x_3437_, 8);
v_snapshotTasks_3446_ = lean_ctor_get(v___x_3437_, 9);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3455_ == 0)
{
lean_object* v_unused_3456_; 
v_unused_3456_ = lean_ctor_get(v___x_3437_, 5);
lean_dec(v_unused_3456_);
v___x_3448_ = v___x_3437_;
v_isShared_3449_ = v_isSharedCheck_3455_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_snapshotTasks_3446_);
lean_inc(v_infoState_3445_);
lean_inc(v_messages_3444_);
lean_inc(v_recordedDeps_3443_);
lean_inc(v_traceState_3442_);
lean_inc(v_auxDeclNGen_3441_);
lean_inc(v_ngen_3440_);
lean_inc(v_nextMacroScope_3439_);
lean_inc(v_env_3438_);
lean_dec(v___x_3437_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3455_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v___x_3452_; 
v___x_3450_ = l_Lean_Kernel_enableDiag(v_env_3438_, v___y_3436_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 5, v___x_3372_);
lean_ctor_set(v___x_3448_, 0, v___x_3450_);
v___x_3452_ = v___x_3448_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_nextMacroScope_3439_);
lean_ctor_set(v_reuseFailAlloc_3454_, 2, v_ngen_3440_);
lean_ctor_set(v_reuseFailAlloc_3454_, 3, v_auxDeclNGen_3441_);
lean_ctor_set(v_reuseFailAlloc_3454_, 4, v_traceState_3442_);
lean_ctor_set(v_reuseFailAlloc_3454_, 5, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3454_, 6, v_recordedDeps_3443_);
lean_ctor_set(v_reuseFailAlloc_3454_, 7, v_messages_3444_);
lean_ctor_set(v_reuseFailAlloc_3454_, 8, v_infoState_3445_);
lean_ctor_set(v_reuseFailAlloc_3454_, 9, v_snapshotTasks_3446_);
v___x_3452_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_st_ref_put(v___x_3380_, v___x_3452_);
v_fileName_3382_ = v___x_3359_;
v_fileMap_3383_ = v___x_3360_;
v_currNamespace_3384_ = v_currNamespace_3351_;
v_openDecls_3385_ = v_openDecls_3352_;
v_initHeartbeats_3386_ = v___x_3379_;
v_maxHeartbeats_3387_ = v___x_3362_;
v_quotContext_3388_ = v___x_3363_;
v_currMacroScope_3389_ = v___x_3364_;
v_cancelTk_x3f_3390_ = v_cancelTk_x3f_3353_;
v_inheritedTraceOptions_3391_ = v___x_3433_;
v_currRecDepth_3392_ = v___x_3361_;
v_ref_3393_ = v___x_3365_;
v_suppressElabErrors_3394_ = v___x_3367_;
v_isRecordingDeps_3395_ = v___x_3367_;
goto v___jp_3381_;
}
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
lean_object* v_v_3499_; lean_object* v___x_3500_; lean_object* v_bs_x27_3501_; lean_object* v___x_3502_; 
v_v_3499_ = lean_array_uget(v_bs_3492_, v_i_3491_);
v___x_3500_ = lean_unsigned_to_nat(0u);
v_bs_x27_3501_ = lean_array_uset(v_bs_3492_, v_i_3491_, v___x_3500_);
lean_inc_ref(v_x_3489_);
v___x_3502_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3489_, v_v_3499_, v___y_3493_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; size_t v___x_3504_; size_t v___x_3505_; lean_object* v___x_3506_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v___x_3504_ = ((size_t)1ULL);
v___x_3505_ = lean_usize_add(v_i_3491_, v___x_3504_);
v___x_3506_ = lean_array_uset(v_bs_x27_3501_, v_i_3491_, v_a_3503_);
v_i_3491_ = v___x_3505_;
v_bs_3492_ = v___x_3506_;
goto _start;
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v_bs_x27_3501_);
lean_dec_ref(v_x_3489_);
v_a_3508_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3502_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3502_);
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
size_t v_sz_boxed_3559_; size_t v___x_3984__boxed_3560_; lean_object* v_res_3561_; 
v_sz_boxed_3559_ = lean_unbox_usize(v_sz_3552_);
lean_dec(v_sz_3552_);
v___x_3984__boxed_3560_ = lean_unbox_usize(v___x_3553_);
lean_dec(v___x_3553_);
v_res_3561_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1(v_x_3551_, v_sz_boxed_3559_, v___x_3984__boxed_3560_, v_content_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
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
lean_object* v_content_3856_; lean_object* v_val_3857_; lean_object* v___f_3858_; size_t v_sz_3859_; size_t v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v_fallback_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
lean_inc_ref(v_container_3855_);
v_content_3856_ = lean_ctor_get(v_x_3563_, 1);
lean_inc_ref_n(v_content_3856_, 2);
lean_dec_ref_known(v_x_3563_, 2);
v_val_3857_ = lean_ctor_get(v_container_3855_, 0);
lean_inc(v_val_3857_);
lean_dec_ref_known(v_container_3855_, 1);
lean_inc_ref_n(v_x_3562_, 2);
v___f_3858_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3858_, 0, v_x_3562_);
v_sz_3859_ = lean_array_size(v_content_3856_);
v___x_3860_ = ((size_t)0ULL);
v___x_3861_ = lean_box_usize(v_sz_3859_);
v___x_3862_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
v_fallback_3863_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v_fallback_3863_, 0, v_x_3562_);
lean_closure_set(v_fallback_3863_, 1, v___x_3861_);
lean_closure_set(v_fallback_3863_, 2, v___x_3862_);
lean_closure_set(v_fallback_3863_, 3, v_content_3856_);
v___x_3864_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3857_);
v___x_3865_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_3864_, v_a_3565_, v_a_3566_);
lean_dec(v___x_3864_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
lean_dec_ref_known(v___x_3865_, 1);
if (lean_obj_tag(v_a_3866_) == 0)
{
lean_object* v___x_3867_; 
lean_dec_ref(v_fallback_3863_);
lean_dec_ref(v___f_3858_);
lean_dec(v_val_3857_);
v___x_3867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3562_, v_sz_3859_, v___x_3860_, v_content_3856_, v_a_3564_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3876_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3870_ = v___x_3867_;
v_isShared_3871_ = v_isSharedCheck_3876_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3867_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3876_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v___x_3874_; 
v___x_3872_ = l_Lean_Doc_joinInlines(v_a_3868_);
lean_dec(v_a_3868_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3872_);
v___x_3874_ = v___x_3870_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
v_a_3877_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3867_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3867_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_object* v_val_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
lean_dec_ref(v_x_3562_);
v_val_3885_ = lean_ctor_get(v_a_3866_, 0);
lean_inc(v_val_3885_);
lean_dec_ref_known(v_a_3866_, 1);
v___x_3886_ = lean_apply_3(v_val_3885_, v___f_3858_, v_val_3857_, v_content_3856_);
v___x_3887_ = l_Lean_Doc_withRendererFallback(v_fallback_3863_, v___x_3886_, v_a_3564_, v_a_3565_, v_a_3566_);
return v___x_3887_;
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec_ref(v_fallback_3863_);
lean_dec_ref(v___f_3858_);
lean_dec(v_val_3857_);
lean_dec_ref(v_content_3856_);
lean_dec_ref(v_x_3562_);
v_a_3888_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3865_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3865_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
else
{
lean_object* v_content_3896_; size_t v_sz_3897_; size_t v___x_3898_; lean_object* v___x_3899_; 
v_content_3896_ = lean_ctor_get(v_x_3563_, 1);
lean_inc_ref(v_content_3896_);
lean_dec_ref_known(v_x_3563_, 2);
v_sz_3897_ = lean_array_size(v_content_3896_);
v___x_3898_ = ((size_t)0ULL);
v___x_3899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3562_, v_sz_3897_, v___x_3898_, v_content_3896_, v_a_3564_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3908_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3902_ = v___x_3899_;
v_isShared_3903_ = v_isSharedCheck_3908_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3908_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3904_; lean_object* v___x_3906_; 
v___x_3904_ = l_Lean_Doc_joinInlines(v_a_3900_);
lean_dec(v_a_3900_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3904_);
v___x_3906_ = v___x_3902_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3904_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
v_a_3909_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3899_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3899_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___lam__0(lean_object* v_x_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3924_, lean_object* v_sz_3925_, lean_object* v_i_3926_, lean_object* v_bs_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
size_t v_sz_boxed_3932_; size_t v_i_boxed_3933_; lean_object* v_res_3934_; 
v_sz_boxed_3932_ = lean_unbox_usize(v_sz_3925_);
lean_dec(v_sz_3925_);
v_i_boxed_3933_ = lean_unbox_usize(v_i_3926_);
lean_dec(v_i_3926_);
v_res_3934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0_spec__1(v_x_3924_, v_sz_boxed_3932_, v_i_boxed_3933_, v_bs_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed(lean_object* v_x_3935_, lean_object* v_x_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v_x_3935_, v_x_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
lean_dec(v_a_3937_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(lean_object* v___x_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v___x_3948_; 
v___x_3948_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0___boxed(lean_object* v___x_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__0(v___x_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(lean_object* v_x_3956_, lean_object* v_x_3957_){
_start:
{
lean_object* v_zero_3958_; uint8_t v_isZero_3959_; 
v_zero_3958_ = lean_unsigned_to_nat(0u);
v_isZero_3959_ = lean_nat_dec_eq(v_x_3956_, v_zero_3958_);
if (v_isZero_3959_ == 1)
{
lean_dec(v_x_3956_);
return v_x_3957_;
}
else
{
uint32_t v___x_3960_; lean_object* v_one_3961_; lean_object* v_n_3962_; lean_object* v___x_3963_; 
v___x_3960_ = 32;
v_one_3961_ = lean_unsigned_to_nat(1u);
v_n_3962_ = lean_nat_sub(v_x_3956_, v_one_3961_);
lean_dec(v_x_3956_);
v___x_3963_ = lean_string_push(v_x_3957_, v___x_3960_);
v_x_3956_ = v_n_3962_;
v_x_3957_ = v___x_3963_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(size_t v_sz_3965_, size_t v_i_3966_, lean_object* v_bs_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
uint8_t v___x_3972_; 
v___x_3972_ = lean_usize_dec_lt(v_i_3966_, v_sz_3965_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; 
v___x_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3973_, 0, v_bs_3967_);
return v___x_3973_;
}
else
{
lean_object* v_v_3974_; lean_object* v___x_3975_; lean_object* v_bs_x27_3976_; size_t v_sz_3977_; size_t v___x_3978_; lean_object* v___x_3979_; 
v_v_3974_ = lean_array_uget(v_bs_3967_, v_i_3966_);
v___x_3975_ = lean_unsigned_to_nat(0u);
v_bs_x27_3976_ = lean_array_uset(v_bs_3967_, v_i_3966_, v___x_3975_);
v_sz_3977_ = lean_array_size(v_v_3974_);
v___x_3978_ = ((size_t)0ULL);
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_3977_, v___x_3978_, v_v_3974_, v___y_3968_, v___y_3969_, v___y_3970_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; size_t v___x_3985_; size_t v___x_3986_; lean_object* v___x_3987_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref_known(v___x_3979_, 1);
v___x_3981_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_3982_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_3983_ = l_Lean_Doc_joinBlocks(v_a_3980_);
lean_dec(v_a_3980_);
v___x_3984_ = l_Lean_Doc_prefixListLines(v___x_3981_, v___x_3982_, v___x_3983_);
v___x_3985_ = ((size_t)1ULL);
v___x_3986_ = lean_usize_add(v_i_3966_, v___x_3985_);
v___x_3987_ = lean_array_uset(v_bs_x27_3976_, v_i_3966_, v___x_3984_);
v_i_3966_ = v___x_3986_;
v_bs_3967_ = v___x_3987_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_3976_);
return v___x_3979_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(lean_object* v_as_3989_, size_t v_sz_3990_, size_t v_i_3991_, lean_object* v_b_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
uint8_t v___x_3997_; 
v___x_3997_ = lean_usize_dec_lt(v_i_3991_, v_sz_3990_);
if (v___x_3997_ == 0)
{
lean_object* v___x_3998_; 
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v_b_3992_);
return v___x_3998_;
}
else
{
lean_object* v_fst_3999_; lean_object* v_snd_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4034_; 
v_fst_3999_ = lean_ctor_get(v_b_3992_, 0);
v_snd_4000_ = lean_ctor_get(v_b_3992_, 1);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_b_3992_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4002_ = v_b_3992_;
v_isShared_4003_ = v_isSharedCheck_4034_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_snd_4000_);
lean_inc(v_fst_3999_);
lean_dec(v_b_3992_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4034_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4004_; lean_object* v_a_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; size_t v_sz_4012_; size_t v___x_4013_; lean_object* v___x_4014_; 
v___x_4004_ = lean_unsigned_to_nat(1u);
v_a_4005_ = lean_array_uget_borrowed(v_as_3989_, v_i_3991_);
lean_inc(v_snd_4000_);
v___x_4006_ = l_Nat_reprFast(v_snd_4000_);
v___x_4007_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0));
v___x_4008_ = lean_string_append(v___x_4006_, v___x_4007_);
v___x_4009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4010_ = lean_string_utf8_byte_size(v___x_4008_);
v___x_4011_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__6(v___x_4010_, v___x_4009_);
v_sz_4012_ = lean_array_size(v_a_4005_);
v___x_4013_ = ((size_t)0ULL);
lean_inc(v_a_4005_);
v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4012_, v___x_4013_, v_a_4005_, v___y_3993_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4021_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_a_4015_);
lean_dec_ref_known(v___x_4014_, 1);
v___x_4016_ = l_Lean_Doc_joinBlocks(v_a_4015_);
lean_dec(v_a_4015_);
v___x_4017_ = l_Lean_Doc_prefixListLines(v___x_4008_, v___x_4011_, v___x_4016_);
v___x_4018_ = lean_array_push(v_fst_3999_, v___x_4017_);
v___x_4019_ = lean_nat_add(v_snd_4000_, v___x_4004_);
lean_dec(v_snd_4000_);
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 1, v___x_4019_);
lean_ctor_set(v___x_4002_, 0, v___x_4018_);
v___x_4021_ = v___x_4002_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4018_);
lean_ctor_set(v_reuseFailAlloc_4025_, 1, v___x_4019_);
v___x_4021_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
size_t v___x_4022_; size_t v___x_4023_; 
v___x_4022_ = ((size_t)1ULL);
v___x_4023_ = lean_usize_add(v_i_3991_, v___x_4022_);
v_i_3991_ = v___x_4023_;
v_b_3992_ = v___x_4021_;
goto _start;
}
}
else
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4033_; 
lean_dec_ref(v___x_4011_);
lean_dec_ref(v___x_4008_);
lean_del_object(v___x_4002_);
lean_dec(v_snd_4000_);
lean_dec(v_fst_3999_);
v_a_4026_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4028_ = v___x_4014_;
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_4014_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(size_t v_sz_4035_, size_t v_i_4036_, lean_object* v_bs_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
uint8_t v___x_4042_; 
v___x_4042_ = lean_usize_dec_lt(v_i_4036_, v_sz_4035_);
if (v___x_4042_ == 0)
{
lean_object* v___x_4043_; 
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v_bs_4037_);
return v___x_4043_;
}
else
{
lean_object* v_v_4044_; lean_object* v___x_4045_; lean_object* v_term_4046_; lean_object* v_desc_4047_; lean_object* v___x_4048_; lean_object* v_bs_x27_4049_; lean_object* v_a_4051_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v_v_4044_ = lean_array_uget_borrowed(v_bs_4037_, v_i_4036_);
v___x_4045_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v_term_4046_ = lean_ctor_get(v_v_4044_, 0);
lean_inc_ref(v_term_4046_);
v_desc_4047_ = lean_ctor_get(v_v_4044_, 1);
lean_inc_ref(v_desc_4047_);
v___x_4048_ = lean_unsigned_to_nat(0u);
v_bs_x27_4049_ = lean_array_uset(v_bs_4037_, v_i_4036_, v___x_4048_);
v___x_4056_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4056_, 0, v_term_4046_);
v___x_4057_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4045_, v___x_4056_, v___y_4038_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_a_4058_; size_t v_sz_4059_; size_t v___x_4060_; lean_object* v___x_4061_; 
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_a_4058_);
lean_dec_ref_known(v___x_4057_, 1);
v_sz_4059_ = lean_array_size(v_desc_4047_);
v___x_4060_ = ((size_t)0ULL);
lean_inc_ref(v_desc_4047_);
v___x_4061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4059_, v___x_4060_, v_desc_4047_, v___y_4038_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___y_4064_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___x_4061_, 1);
v___x_4068_ = lean_unsigned_to_nat(1u);
v___x_4069_ = lean_mk_empty_array_with_capacity(v___x_4068_);
v___x_4070_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1));
v___x_4071_ = lean_unsigned_to_nat(2u);
v___x_4072_ = lean_mk_empty_array_with_capacity(v___x_4071_);
v___x_4073_ = lean_array_push(v___x_4072_, v_a_4058_);
v___x_4074_ = lean_array_push(v___x_4073_, v___x_4070_);
v___x_4075_ = l_Lean_Doc_joinInlines(v___x_4074_);
lean_dec_ref(v___x_4074_);
v___x_4076_ = lean_array_get_size(v_desc_4047_);
lean_dec_ref(v_desc_4047_);
v___x_4077_ = lean_nat_dec_le(v___x_4076_, v___x_4068_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4078_ = lean_array_push(v___x_4069_, v___x_4075_);
v___x_4079_ = l_Array_append___redArg(v___x_4078_, v_a_4062_);
lean_dec(v_a_4062_);
v___x_4080_ = l_Lean_Doc_joinBlocks(v___x_4079_);
lean_dec_ref(v___x_4079_);
v___y_4064_ = v___x_4080_;
goto v___jp_4063_;
}
else
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
lean_dec_ref(v___x_4069_);
v___x_4081_ = l_Lean_Doc_joinBlocks(v_a_4062_);
lean_dec(v_a_4062_);
v___x_4082_ = l_Array_append___redArg(v___x_4075_, v___x_4081_);
lean_dec_ref(v___x_4081_);
v___y_4064_ = v___x_4082_;
goto v___jp_4063_;
}
v___jp_4063_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0));
v___x_4066_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1));
v___x_4067_ = l_Lean_Doc_prefixListLines(v___x_4065_, v___x_4066_, v___y_4064_);
v_a_4051_ = v___x_4067_;
goto v___jp_4050_;
}
}
else
{
lean_dec(v_a_4058_);
lean_dec_ref(v_bs_x27_4049_);
lean_dec_ref(v_desc_4047_);
return v___x_4061_;
}
}
else
{
lean_dec_ref(v_desc_4047_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_a_4083_; 
v_a_4083_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___x_4057_, 1);
v_a_4051_ = v_a_4083_;
goto v___jp_4050_;
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec_ref(v_bs_x27_4049_);
v_a_4084_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4057_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4057_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
v___jp_4050_:
{
size_t v___x_4052_; size_t v___x_4053_; lean_object* v___x_4054_; 
v___x_4052_ = ((size_t)1ULL);
v___x_4053_ = lean_usize_add(v_i_4036_, v___x_4052_);
v___x_4054_ = lean_array_uset(v_bs_x27_4049_, v_i_4036_, v_a_4051_);
v_i_4036_ = v___x_4053_;
v_bs_4037_ = v___x_4054_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed(lean_object* v_x_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_x_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
lean_dec(v_a_4095_);
lean_dec_ref(v_a_4094_);
lean_dec(v_a_4093_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed(lean_object* v_sz_4100_, lean_object* v___x_4101_, lean_object* v_content_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
size_t v_sz_boxed_4107_; size_t v___x_4839__boxed_4108_; lean_object* v_res_4109_; 
v_sz_boxed_4107_ = lean_unbox_usize(v_sz_4100_);
lean_dec(v_sz_4100_);
v___x_4839__boxed_4108_ = lean_unbox_usize(v___x_4101_);
lean_dec(v___x_4101_);
v_res_4109_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(v_sz_boxed_4107_, v___x_4839__boxed_4108_, v_content_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(lean_object* v_x_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_){
_start:
{
switch(lean_obj_tag(v_x_4110_))
{
case 0:
{
lean_object* v_contents_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4124_; 
v_contents_4115_ = lean_ctor_get(v_x_4110_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v_x_4110_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4117_ = v_x_4110_;
v_isShared_4118_ = v_isSharedCheck_4124_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_contents_4115_);
lean_dec(v_x_4110_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4124_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4119_; lean_object* v___x_4121_; 
v___x_4119_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
if (v_isShared_4118_ == 0)
{
lean_ctor_set_tag(v___x_4117_, 9);
v___x_4121_ = v___x_4117_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_contents_4115_);
v___x_4121_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
lean_object* v___x_4122_; 
v___x_4122_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4119_, v___x_4121_, v_a_4111_, v_a_4112_, v_a_4113_);
return v___x_4122_;
}
}
}
case 1:
{
lean_object* v_content_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4133_; 
v_content_4125_ = lean_ctor_get(v_x_4110_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_x_4110_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4127_ = v_x_4110_;
v_isShared_4128_ = v_isSharedCheck_4133_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_content_4125_);
lean_dec(v_x_4110_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4133_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4129_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_4125_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set_tag(v___x_4127_, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4129_);
v___x_4131_ = v___x_4127_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
case 2:
{
lean_object* v_items_4134_; size_t v_sz_4135_; size_t v___x_4136_; lean_object* v___x_4137_; 
v_items_4134_ = lean_ctor_get(v_x_4110_, 0);
lean_inc_ref(v_items_4134_);
lean_dec_ref_known(v_x_4110_, 1);
v_sz_4135_ = lean_array_size(v_items_4134_);
v___x_4136_ = ((size_t)0ULL);
v___x_4137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_4135_, v___x_4136_, v_items_4134_, v_a_4111_, v_a_4112_, v_a_4113_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4146_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4140_ = v___x_4137_;
v_isShared_4141_ = v_isSharedCheck_4146_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4137_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4146_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4142_; lean_object* v___x_4144_; 
v___x_4142_ = l_Lean_Doc_joinBlocks(v_a_4138_);
lean_dec(v_a_4138_);
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 0, v___x_4142_);
v___x_4144_ = v___x_4140_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4142_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
v_a_4147_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4137_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4137_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
case 3:
{
lean_object* v_start_4155_; lean_object* v_items_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4190_; 
v_start_4155_ = lean_ctor_get(v_x_4110_, 0);
v_items_4156_ = lean_ctor_get(v_x_4110_, 1);
v_isSharedCheck_4190_ = !lean_is_exclusive(v_x_4110_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4158_ = v_x_4110_;
v_isShared_4159_ = v_isSharedCheck_4190_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_items_4156_);
lean_inc(v_start_4155_);
lean_dec(v_x_4110_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4190_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v_out_4160_; lean_object* v___y_4162_; lean_object* v___x_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; 
v_out_4160_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6));
v___x_4187_ = lean_unsigned_to_nat(1u);
v___x_4188_ = l_Int_toNat(v_start_4155_);
lean_dec(v_start_4155_);
v___x_4189_ = lean_nat_dec_le(v___x_4187_, v___x_4188_);
if (v___x_4189_ == 0)
{
lean_dec(v___x_4188_);
v___y_4162_ = v___x_4187_;
goto v___jp_4161_;
}
else
{
v___y_4162_ = v___x_4188_;
goto v___jp_4161_;
}
v___jp_4161_:
{
lean_object* v___x_4164_; 
if (v_isShared_4159_ == 0)
{
lean_ctor_set_tag(v___x_4158_, 0);
lean_ctor_set(v___x_4158_, 1, v___y_4162_);
lean_ctor_set(v___x_4158_, 0, v_out_4160_);
v___x_4164_ = v___x_4158_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_out_4160_);
lean_ctor_set(v_reuseFailAlloc_4186_, 1, v___y_4162_);
v___x_4164_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
size_t v_sz_4165_; size_t v___x_4166_; lean_object* v___x_4167_; 
v_sz_4165_ = lean_array_size(v_items_4156_);
v___x_4166_ = ((size_t)0ULL);
v___x_4167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_items_4156_, v_sz_4165_, v___x_4166_, v___x_4164_, v_a_4111_, v_a_4112_, v_a_4113_);
lean_dec_ref(v_items_4156_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4177_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4170_ = v___x_4167_;
v_isShared_4171_ = v_isSharedCheck_4177_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4167_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4177_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v_fst_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
v_fst_4172_ = lean_ctor_get(v_a_4168_, 0);
lean_inc(v_fst_4172_);
lean_dec(v_a_4168_);
v___x_4173_ = l_Lean_Doc_joinBlocks(v_fst_4172_);
lean_dec(v_fst_4172_);
if (v_isShared_4171_ == 0)
{
lean_ctor_set(v___x_4170_, 0, v___x_4173_);
v___x_4175_ = v___x_4170_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
else
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
v_a_4178_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___x_4167_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4167_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_a_4178_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_4191_; size_t v_sz_4192_; size_t v___x_4193_; lean_object* v___x_4194_; 
v_items_4191_ = lean_ctor_get(v_x_4110_, 0);
lean_inc_ref(v_items_4191_);
lean_dec_ref_known(v_x_4110_, 1);
v_sz_4192_ = lean_array_size(v_items_4191_);
v___x_4193_ = ((size_t)0ULL);
v___x_4194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_4192_, v___x_4193_, v_items_4191_, v_a_4111_, v_a_4112_, v_a_4113_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4203_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4197_ = v___x_4194_;
v_isShared_4198_ = v_isSharedCheck_4203_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4194_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4203_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4199_; lean_object* v___x_4201_; 
v___x_4199_ = l_Lean_Doc_joinBlocks(v_a_4195_);
lean_dec(v_a_4195_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 0, v___x_4199_);
v___x_4201_ = v___x_4197_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4199_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
v_a_4204_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___x_4194_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4194_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
case 5:
{
lean_object* v_items_4212_; size_t v_sz_4213_; size_t v___x_4214_; lean_object* v___x_4215_; 
v_items_4212_ = lean_ctor_get(v_x_4110_, 0);
lean_inc_ref(v_items_4212_);
lean_dec_ref_known(v_x_4110_, 1);
v_sz_4213_ = lean_array_size(v_items_4212_);
v___x_4214_ = ((size_t)0ULL);
v___x_4215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4213_, v___x_4214_, v_items_4212_, v_a_4111_, v_a_4112_, v_a_4113_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4226_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4218_ = v___x_4215_;
v_isShared_4219_ = v_isSharedCheck_4226_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4215_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4226_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4224_; 
v___x_4220_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0));
v___x_4221_ = l_Lean_Doc_joinBlocks(v_a_4216_);
lean_dec(v_a_4216_);
v___x_4222_ = l_Lean_Doc_prefixLines(v___x_4220_, v___x_4221_);
if (v_isShared_4219_ == 0)
{
lean_ctor_set(v___x_4218_, 0, v___x_4222_);
v___x_4224_ = v___x_4218_;
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
v_a_4227_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4215_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4215_);
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
case 6:
{
lean_object* v_content_4235_; size_t v_sz_4236_; size_t v___x_4237_; lean_object* v___x_4238_; 
v_content_4235_ = lean_ctor_get(v_x_4110_, 0);
lean_inc_ref(v_content_4235_);
lean_dec_ref_known(v_x_4110_, 1);
v_sz_4236_ = lean_array_size(v_content_4235_);
v___x_4237_ = ((size_t)0ULL);
v___x_4238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4236_, v___x_4237_, v_content_4235_, v_a_4111_, v_a_4112_, v_a_4113_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4247_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4241_ = v___x_4238_;
v_isShared_4242_ = v_isSharedCheck_4247_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4238_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4247_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4243_; lean_object* v___x_4245_; 
v___x_4243_ = l_Lean_Doc_joinBlocks(v_a_4239_);
lean_dec(v_a_4239_);
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 0, v___x_4243_);
v___x_4245_ = v___x_4241_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4243_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
else
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
v_a_4248_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4238_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4238_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
default: 
{
lean_object* v_container_4256_; 
v_container_4256_ = lean_ctor_get(v_x_4110_, 0);
if (lean_obj_tag(v_container_4256_) == 0)
{
lean_object* v_content_4257_; lean_object* v_val_4258_; lean_object* v___f_4259_; lean_object* v___f_4260_; size_t v_sz_4261_; size_t v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v_fallback_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_inc_ref(v_container_4256_);
v_content_4257_ = lean_ctor_get(v_x_4110_, 1);
lean_inc_ref_n(v_content_4257_, 2);
lean_dec_ref_known(v_x_4110_, 2);
v_val_4258_ = lean_ctor_get(v_container_4256_, 0);
lean_inc(v_val_4258_);
lean_dec_ref_known(v_container_4256_, 1);
v___f_4259_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___boxed), 5, 0);
v___f_4260_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___closed__0));
v_sz_4261_ = lean_array_size(v_content_4257_);
v___x_4262_ = ((size_t)0ULL);
v___x_4263_ = lean_box_usize(v_sz_4261_);
v___x_4264_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0___boxed__const__1));
v_fallback_4265_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v_fallback_4265_, 0, v___x_4263_);
lean_closure_set(v_fallback_4265_, 1, v___x_4264_);
lean_closure_set(v_fallback_4265_, 2, v_content_4257_);
v___x_4266_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_4258_);
v___x_4267_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_4266_, v_a_4112_, v_a_4113_);
lean_dec(v___x_4266_);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_object* v_a_4268_; 
v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
lean_inc(v_a_4268_);
lean_dec_ref_known(v___x_4267_, 1);
if (lean_obj_tag(v_a_4268_) == 0)
{
lean_object* v___x_4269_; 
lean_dec_ref(v_fallback_4265_);
lean_dec_ref(v___f_4259_);
lean_dec(v_val_4258_);
v___x_4269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4261_, v___x_4262_, v_content_4257_, v_a_4111_, v_a_4112_, v_a_4113_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4278_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4272_ = v___x_4269_;
v_isShared_4273_ = v_isSharedCheck_4278_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4278_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4274_; lean_object* v___x_4276_; 
v___x_4274_ = l_Lean_Doc_joinBlocks(v_a_4270_);
lean_dec(v_a_4270_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v___x_4274_);
v___x_4276_ = v___x_4272_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
v_a_4279_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4269_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4269_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
else
{
lean_object* v_val_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v_val_4287_ = lean_ctor_get(v_a_4268_, 0);
lean_inc(v_val_4287_);
lean_dec_ref_known(v_a_4268_, 1);
v___x_4288_ = lean_apply_4(v_val_4287_, v___f_4260_, v___f_4259_, v_val_4258_, v_content_4257_);
v___x_4289_ = l_Lean_Doc_withRendererFallback(v_fallback_4265_, v___x_4288_, v_a_4111_, v_a_4112_, v_a_4113_);
return v___x_4289_;
}
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
lean_dec_ref(v_fallback_4265_);
lean_dec_ref(v___f_4259_);
lean_dec(v_val_4258_);
lean_dec_ref(v_content_4257_);
v_a_4290_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4292_ = v___x_4267_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4267_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
else
{
lean_object* v_content_4298_; size_t v_sz_4299_; size_t v___x_4300_; lean_object* v___x_4301_; 
v_content_4298_ = lean_ctor_get(v_x_4110_, 1);
lean_inc_ref(v_content_4298_);
lean_dec_ref_known(v_x_4110_, 2);
v_sz_4299_ = lean_array_size(v_content_4298_);
v___x_4300_ = ((size_t)0ULL);
v___x_4301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4299_, v___x_4300_, v_content_4298_, v_a_4111_, v_a_4112_, v_a_4113_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4310_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4304_ = v___x_4301_;
v_isShared_4305_ = v_isSharedCheck_4310_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4301_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4310_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4306_; lean_object* v___x_4308_; 
v___x_4306_ = l_Lean_Doc_joinBlocks(v_a_4302_);
lean_dec(v_a_4302_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v___x_4306_);
v___x_4308_ = v___x_4304_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4306_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
v_a_4311_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___x_4301_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4301_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(size_t v_sz_4319_, size_t v_i_4320_, lean_object* v_bs_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
uint8_t v___x_4326_; 
v___x_4326_ = lean_usize_dec_lt(v_i_4320_, v_sz_4319_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; 
v___x_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4327_, 0, v_bs_4321_);
return v___x_4327_;
}
else
{
lean_object* v_v_4328_; lean_object* v___x_4329_; lean_object* v_bs_x27_4330_; lean_object* v___x_4331_; 
v_v_4328_ = lean_array_uget(v_bs_4321_, v_i_4320_);
v___x_4329_ = lean_unsigned_to_nat(0u);
v_bs_x27_4330_ = lean_array_uset(v_bs_4321_, v_i_4320_, v___x_4329_);
v___x_4331_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1(v_v_4328_, v___y_4322_, v___y_4323_, v___y_4324_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v_a_4332_; size_t v___x_4333_; size_t v___x_4334_; lean_object* v___x_4335_; 
v_a_4332_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v___x_4331_, 1);
v___x_4333_ = ((size_t)1ULL);
v___x_4334_ = lean_usize_add(v_i_4320_, v___x_4333_);
v___x_4335_ = lean_array_uset(v_bs_x27_4330_, v_i_4320_, v_a_4332_);
v_i_4320_ = v___x_4334_;
v_bs_4321_ = v___x_4335_;
goto _start;
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
lean_dec_ref(v_bs_x27_4330_);
v_a_4337_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4331_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4331_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1___lam__1(size_t v_sz_4345_, size_t v___x_4346_, lean_object* v_content_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
lean_object* v___x_4352_; 
v___x_4352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4345_, v___x_4346_, v_content_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4361_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4355_ = v___x_4352_;
v_isShared_4356_ = v_isSharedCheck_4361_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4352_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4361_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4357_; lean_object* v___x_4359_; 
v___x_4357_ = l_Lean_Doc_joinBlocks(v_a_4353_);
lean_dec(v_a_4353_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v___x_4357_);
v___x_4359_ = v___x_4355_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4357_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
else
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4369_; 
v_a_4362_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4364_ = v___x_4352_;
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4352_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4367_; 
if (v_isShared_4365_ == 0)
{
v___x_4367_ = v___x_4364_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2___boxed(lean_object* v_sz_4370_, lean_object* v_i_4371_, lean_object* v_bs_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
size_t v_sz_boxed_4377_; size_t v_i_boxed_4378_; lean_object* v_res_4379_; 
v_sz_boxed_4377_ = lean_unbox_usize(v_sz_4370_);
lean_dec(v_sz_4370_);
v_i_boxed_4378_ = lean_unbox_usize(v_i_4371_);
lean_dec(v_i_4371_);
v_res_4379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_boxed_4377_, v_i_boxed_4378_, v_bs_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5___boxed(lean_object* v_sz_4380_, lean_object* v_i_4381_, lean_object* v_bs_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
size_t v_sz_boxed_4387_; size_t v_i_boxed_4388_; lean_object* v_res_4389_; 
v_sz_boxed_4387_ = lean_unbox_usize(v_sz_4380_);
lean_dec(v_sz_4380_);
v_i_boxed_4388_ = lean_unbox_usize(v_i_4381_);
lean_dec(v_i_4381_);
v_res_4389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__5(v_sz_boxed_4387_, v_i_boxed_4388_, v_bs_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
lean_dec(v___y_4383_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7___boxed(lean_object* v_as_4390_, lean_object* v_sz_4391_, lean_object* v_i_4392_, lean_object* v_b_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
size_t v_sz_boxed_4398_; size_t v_i_boxed_4399_; lean_object* v_res_4400_; 
v_sz_boxed_4398_ = lean_unbox_usize(v_sz_4391_);
lean_dec(v_sz_4391_);
v_i_boxed_4399_ = lean_unbox_usize(v_i_4392_);
lean_dec(v_i_4392_);
v_res_4400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__7(v_as_4390_, v_sz_boxed_4398_, v_i_boxed_4399_, v_b_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v_as_4390_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8___boxed(lean_object* v_sz_4401_, lean_object* v_i_4402_, lean_object* v_bs_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
size_t v_sz_boxed_4408_; size_t v_i_boxed_4409_; lean_object* v_res_4410_; 
v_sz_boxed_4408_ = lean_unbox_usize(v_sz_4401_);
lean_dec(v_sz_4401_);
v_i_boxed_4409_ = lean_unbox_usize(v_i_4402_);
lean_dec(v_i_4402_);
v_res_4410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00Lean_findSimpleDocString_x3f_spec__1_spec__8(v_sz_boxed_4408_, v_i_boxed_4409_, v_bs_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(size_t v_sz_4411_, size_t v_i_4412_, lean_object* v_bs_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
uint8_t v___x_4418_; 
v___x_4418_ = lean_usize_dec_lt(v_i_4412_, v_sz_4411_);
if (v___x_4418_ == 0)
{
lean_object* v___x_4419_; 
v___x_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4419_, 0, v_bs_4413_);
return v___x_4419_;
}
else
{
lean_object* v_v_4420_; lean_object* v___x_4421_; lean_object* v_bs_x27_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v_v_4420_ = lean_array_uget(v_bs_4413_, v_i_4412_);
v___x_4421_ = lean_unsigned_to_nat(0u);
v_bs_x27_4422_ = lean_array_uset(v_bs_4413_, v_i_4412_, v___x_4421_);
v___x_4423_ = ((lean_object*)(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0));
v___x_4424_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__0(v___x_4423_, v_v_4420_, v___y_4414_, v___y_4415_, v___y_4416_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; size_t v___x_4426_; size_t v___x_4427_; lean_object* v___x_4428_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4425_);
lean_dec_ref_known(v___x_4424_, 1);
v___x_4426_ = ((size_t)1ULL);
v___x_4427_ = lean_usize_add(v_i_4412_, v___x_4426_);
v___x_4428_ = lean_array_uset(v_bs_x27_4422_, v_i_4412_, v_a_4425_);
v_i_4412_ = v___x_4427_;
v_bs_4413_ = v___x_4428_;
goto _start;
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec_ref(v_bs_x27_4422_);
v_a_4430_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4424_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4424_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1___boxed(lean_object* v_sz_4438_, lean_object* v_i_4439_, lean_object* v_bs_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
size_t v_sz_boxed_4445_; size_t v_i_boxed_4446_; lean_object* v_res_4447_; 
v_sz_boxed_4445_ = lean_unbox_usize(v_sz_4438_);
lean_dec(v_sz_4438_);
v_i_boxed_4446_ = lean_unbox_usize(v_i_4439_);
lean_dec(v_i_4439_);
v_res_4447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_boxed_4445_, v_i_boxed_4446_, v_bs_4440_, v___y_4441_, v___y_4442_, v___y_4443_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
lean_dec(v___y_4441_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(lean_object* v_x_4448_, lean_object* v_x_4449_){
_start:
{
lean_object* v_zero_4450_; uint8_t v_isZero_4451_; 
v_zero_4450_ = lean_unsigned_to_nat(0u);
v_isZero_4451_ = lean_nat_dec_eq(v_x_4448_, v_zero_4450_);
if (v_isZero_4451_ == 1)
{
lean_dec(v_x_4448_);
return v_x_4449_;
}
else
{
uint32_t v___x_4452_; lean_object* v_one_4453_; lean_object* v_n_4454_; lean_object* v___x_4455_; 
v___x_4452_ = 35;
v_one_4453_ = lean_unsigned_to_nat(1u);
v_n_4454_ = lean_nat_sub(v_x_4448_, v_one_4453_);
lean_dec(v_x_4448_);
v___x_4455_ = lean_string_push(v_x_4449_, v___x_4452_);
v_x_4448_ = v_n_4454_;
v_x_4449_ = v___x_4455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(lean_object* v_level_4457_, lean_object* v_part_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
lean_object* v_title_4463_; lean_object* v_content_4464_; lean_object* v_subParts_4465_; size_t v_sz_4466_; size_t v___x_4467_; lean_object* v___x_4468_; 
v_title_4463_ = lean_ctor_get(v_part_4458_, 0);
lean_inc_ref(v_title_4463_);
v_content_4464_ = lean_ctor_get(v_part_4458_, 3);
lean_inc_ref(v_content_4464_);
v_subParts_4465_ = lean_ctor_get(v_part_4458_, 4);
lean_inc_ref(v_subParts_4465_);
lean_dec_ref(v_part_4458_);
v_sz_4466_ = lean_array_size(v_title_4463_);
v___x_4467_ = ((size_t)0ULL);
v___x_4468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__1(v_sz_4466_, v___x_4467_, v_title_4463_, v_a_4459_, v_a_4460_, v_a_4461_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v_a_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; size_t v_sz_4481_; lean_object* v___x_4482_; 
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
lean_inc(v_a_4469_);
lean_dec_ref_known(v___x_4468_, 1);
v___x_4470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0));
v___x_4471_ = lean_unsigned_to_nat(1u);
v___x_4472_ = lean_nat_add(v_level_4457_, v___x_4471_);
lean_inc(v___x_4472_);
v___x_4473_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__2(v___x_4472_, v___x_4470_);
v___x_4474_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0));
v___x_4475_ = lean_string_append(v___x_4473_, v___x_4474_);
v___x_4476_ = lean_mk_empty_array_with_capacity(v___x_4471_);
lean_inc_ref_n(v___x_4476_, 2);
v___x_4477_ = lean_array_push(v___x_4476_, v___x_4475_);
v___x_4478_ = lean_array_push(v___x_4476_, v___x_4477_);
v___x_4479_ = l_Array_append___redArg(v___x_4478_, v_a_4469_);
lean_dec(v_a_4469_);
v___x_4480_ = l_Lean_Doc_joinInlines(v___x_4479_);
lean_dec_ref(v___x_4479_);
v_sz_4481_ = lean_array_size(v_content_4464_);
v___x_4482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4481_, v___x_4467_, v_content_4464_, v_a_4459_, v_a_4460_, v_a_4461_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v_a_4483_; size_t v_sz_4484_; lean_object* v___x_4485_; 
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_a_4483_);
lean_dec_ref_known(v___x_4482_, 1);
v_sz_4484_ = lean_array_size(v_subParts_4465_);
v___x_4485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4472_, v_sz_4484_, v___x_4467_, v_subParts_4465_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v___x_4472_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4497_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4488_ = v___x_4485_;
v_isShared_4489_ = v_isSharedCheck_4497_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4485_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4497_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4495_; 
v___x_4490_ = lean_array_push(v___x_4476_, v___x_4480_);
v___x_4491_ = l_Array_append___redArg(v___x_4490_, v_a_4483_);
lean_dec(v_a_4483_);
v___x_4492_ = l_Array_append___redArg(v___x_4491_, v_a_4486_);
lean_dec(v_a_4486_);
v___x_4493_ = l_Lean_Doc_joinBlocks(v___x_4492_);
lean_dec_ref(v___x_4492_);
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 0, v___x_4493_);
v___x_4495_ = v___x_4488_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4493_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4505_; 
lean_dec(v_a_4483_);
lean_dec_ref(v___x_4480_);
lean_dec_ref(v___x_4476_);
v_a_4498_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4500_ = v___x_4485_;
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4485_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec_ref(v___x_4480_);
lean_dec_ref(v___x_4476_);
lean_dec(v___x_4472_);
lean_dec_ref(v_subParts_4465_);
v_a_4506_ = lean_ctor_get(v___x_4482_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4482_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4482_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
lean_dec_ref(v_subParts_4465_);
lean_dec_ref(v_content_4464_);
v_a_4514_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4468_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4468_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(lean_object* v___x_4522_, size_t v_sz_4523_, size_t v_i_4524_, lean_object* v_bs_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
uint8_t v___x_4530_; 
v___x_4530_ = lean_usize_dec_lt(v_i_4524_, v_sz_4523_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; 
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v_bs_4525_);
return v___x_4531_;
}
else
{
lean_object* v_v_4532_; lean_object* v___x_4533_; lean_object* v_bs_x27_4534_; lean_object* v___x_4535_; 
v_v_4532_ = lean_array_uget(v_bs_4525_, v_i_4524_);
v___x_4533_ = lean_unsigned_to_nat(0u);
v_bs_x27_4534_ = lean_array_uset(v_bs_4525_, v_i_4524_, v___x_4533_);
v___x_4535_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4522_, v_v_4532_, v___y_4526_, v___y_4527_, v___y_4528_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; size_t v___x_4537_; size_t v___x_4538_; lean_object* v___x_4539_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref_known(v___x_4535_, 1);
v___x_4537_ = ((size_t)1ULL);
v___x_4538_ = lean_usize_add(v_i_4524_, v___x_4537_);
v___x_4539_ = lean_array_uset(v_bs_x27_4534_, v_i_4524_, v_a_4536_);
v_i_4524_ = v___x_4538_;
v_bs_4525_ = v___x_4539_;
goto _start;
}
else
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4548_; 
lean_dec_ref(v_bs_x27_4534_);
v_a_4541_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4543_ = v___x_4535_;
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4535_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4544_ == 0)
{
v___x_4546_ = v___x_4543_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4541_);
v___x_4546_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
return v___x_4546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg___boxed(lean_object* v___x_4549_, lean_object* v_sz_4550_, lean_object* v_i_4551_, lean_object* v_bs_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
size_t v_sz_boxed_4557_; size_t v_i_boxed_4558_; lean_object* v_res_4559_; 
v_sz_boxed_4557_ = lean_unbox_usize(v_sz_4550_);
lean_dec(v_sz_4550_);
v_i_boxed_4558_ = lean_unbox_usize(v_i_4551_);
lean_dec(v_i_4551_);
v_res_4559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4549_, v_sz_boxed_4557_, v_i_boxed_4558_, v_bs_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec(v___x_4549_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg___boxed(lean_object* v_level_4560_, lean_object* v_part_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4560_, v_part_4561_, v_a_4562_, v_a_4563_, v_a_4564_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
lean_dec(v_a_4562_);
lean_dec(v_level_4560_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(size_t v_sz_4567_, size_t v_i_4568_, lean_object* v_bs_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
uint8_t v___x_4574_; 
v___x_4574_ = lean_usize_dec_lt(v_i_4568_, v_sz_4567_);
if (v___x_4574_ == 0)
{
lean_object* v___x_4575_; 
v___x_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4575_, 0, v_bs_4569_);
return v___x_4575_;
}
else
{
lean_object* v_v_4576_; lean_object* v___x_4577_; lean_object* v_bs_x27_4578_; lean_object* v___x_4579_; 
v_v_4576_ = lean_array_uget(v_bs_4569_, v_i_4568_);
v___x_4577_ = lean_unsigned_to_nat(0u);
v_bs_x27_4578_ = lean_array_uset(v_bs_4569_, v_i_4568_, v___x_4577_);
v___x_4579_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v___x_4577_, v_v_4576_, v___y_4570_, v___y_4571_, v___y_4572_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; size_t v___x_4581_; size_t v___x_4582_; lean_object* v___x_4583_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
lean_dec_ref_known(v___x_4579_, 1);
v___x_4581_ = ((size_t)1ULL);
v___x_4582_ = lean_usize_add(v_i_4568_, v___x_4581_);
v___x_4583_ = lean_array_uset(v_bs_x27_4578_, v_i_4568_, v_a_4580_);
v_i_4568_ = v___x_4582_;
v_bs_4569_ = v___x_4583_;
goto _start;
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_dec_ref(v_bs_x27_4578_);
v_a_4585_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4579_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4579_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3___boxed(lean_object* v_sz_4593_, lean_object* v_i_4594_, lean_object* v_bs_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
size_t v_sz_boxed_4600_; size_t v_i_boxed_4601_; lean_object* v_res_4602_; 
v_sz_boxed_4600_ = lean_unbox_usize(v_sz_4593_);
lean_dec(v_sz_4593_);
v_i_boxed_4601_ = lean_unbox_usize(v_i_4594_);
lean_dec(v_i_4594_);
v_res_4602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_boxed_4600_, v_i_boxed_4601_, v_bs_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec(v___y_4596_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0(lean_object* v_val_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v_text_4608_; lean_object* v_subsections_4609_; size_t v_sz_4610_; size_t v___x_4611_; lean_object* v___x_4612_; 
v_text_4608_ = lean_ctor_get(v_val_4603_, 0);
lean_inc_ref(v_text_4608_);
v_subsections_4609_ = lean_ctor_get(v_val_4603_, 1);
lean_inc_ref(v_subsections_4609_);
lean_dec_ref(v_val_4603_);
v_sz_4610_ = lean_array_size(v_text_4608_);
v___x_4611_ = ((size_t)0ULL);
v___x_4612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__2(v_sz_4610_, v___x_4611_, v_text_4608_, v___y_4604_, v___y_4605_, v___y_4606_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; size_t v_sz_4614_; lean_object* v___x_4615_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
lean_inc(v_a_4613_);
lean_dec_ref_known(v___x_4612_, 1);
v_sz_4614_ = lean_array_size(v_subsections_4609_);
v___x_4615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_findSimpleDocString_x3f_spec__3(v_sz_4614_, v___x_4611_, v_subsections_4609_, v___y_4604_, v___y_4605_, v___y_4606_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4625_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4618_ = v___x_4615_;
v_isShared_4619_ = v_isSharedCheck_4625_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4615_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4625_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4623_; 
v___x_4620_ = l_Array_append___redArg(v_a_4613_, v_a_4616_);
lean_dec(v_a_4616_);
v___x_4621_ = l_Lean_Doc_joinBlocks(v___x_4620_);
lean_dec_ref(v___x_4620_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4621_);
v___x_4623_ = v___x_4618_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v___x_4621_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
else
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4633_; 
lean_dec(v_a_4613_);
v_a_4626_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4628_ = v___x_4615_;
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4615_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4631_; 
if (v_isShared_4629_ == 0)
{
v___x_4631_ = v___x_4628_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_a_4626_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
}
}
else
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4641_; 
lean_dec_ref(v_subsections_4609_);
v_a_4634_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4636_ = v___x_4612_;
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4612_);
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
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___lam__0___boxed(lean_object* v_val_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_findSimpleDocString_x3f___lam__0(v_val_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
lean_dec(v___y_4643_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_4648_, lean_object* v_declName_4649_, uint8_t v_includeBuiltin_4650_, lean_object* v_options_4651_, lean_object* v_currNamespace_4652_, lean_object* v_openDecls_4653_, lean_object* v_cancelTk_x3f_4654_){
_start:
{
lean_object* v___x_4656_; 
lean_inc_ref(v_env_4648_);
v___x_4656_ = l_Lean_findInternalDocString_x3f(v_env_4648_, v_declName_4649_, v_includeBuiltin_4650_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4700_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4659_ = v___x_4656_;
v_isShared_4660_ = v_isSharedCheck_4700_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v___x_4656_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4700_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
if (lean_obj_tag(v_a_4657_) == 0)
{
lean_object* v___x_4661_; lean_object* v___x_4663_; 
lean_dec(v_cancelTk_x3f_4654_);
lean_dec(v_openDecls_4653_);
lean_dec(v_currNamespace_4652_);
lean_dec_ref(v_options_4651_);
lean_dec_ref(v_env_4648_);
v___x_4661_ = lean_box(0);
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 0, v___x_4661_);
v___x_4663_ = v___x_4659_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4661_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
else
{
lean_object* v_val_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4699_; 
v_val_4665_ = lean_ctor_get(v_a_4657_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v_a_4657_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4667_ = v_a_4657_;
v_isShared_4668_ = v_isSharedCheck_4699_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_val_4665_);
lean_dec(v_a_4657_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4699_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
if (lean_obj_tag(v_val_4665_) == 0)
{
lean_object* v_val_4669_; lean_object* v___x_4671_; 
lean_dec(v_cancelTk_x3f_4654_);
lean_dec(v_openDecls_4653_);
lean_dec(v_currNamespace_4652_);
lean_dec_ref(v_options_4651_);
lean_dec_ref(v_env_4648_);
v_val_4669_ = lean_ctor_get(v_val_4665_, 0);
lean_inc(v_val_4669_);
lean_dec_ref_known(v_val_4665_, 1);
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 0, v_val_4669_);
v___x_4671_ = v___x_4667_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_val_4669_);
v___x_4671_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
lean_object* v___x_4673_; 
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 0, v___x_4671_);
v___x_4673_ = v___x_4659_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v___x_4671_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
else
{
lean_object* v_val_4676_; lean_object* v___f_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
lean_del_object(v___x_4659_);
v_val_4676_ = lean_ctor_get(v_val_4665_, 0);
lean_inc(v_val_4676_);
lean_dec_ref_known(v_val_4665_, 1);
v___f_4677_ = lean_alloc_closure((void*)(l_Lean_findSimpleDocString_x3f___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4677_, 0, v_val_4676_);
v___x_4678_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_4678_, 0, v___f_4677_);
v___x_4679_ = l_Lean_Doc_runMarkdown___redArg(v_env_4648_, v___x_4678_, v_options_4651_, v_currNamespace_4652_, v_openDecls_4653_, v_cancelTk_x3f_4654_);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4690_; 
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4682_ = v___x_4679_;
v_isShared_4683_ = v_isSharedCheck_4690_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4679_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4690_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4685_; 
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 0, v_a_4680_);
v___x_4685_ = v___x_4667_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4680_);
v___x_4685_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
lean_object* v___x_4687_; 
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 0, v___x_4685_);
v___x_4687_ = v___x_4682_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4685_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
}
else
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4698_; 
lean_del_object(v___x_4667_);
v_a_4691_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4693_ = v___x_4679_;
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4679_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4696_; 
if (v_isShared_4694_ == 0)
{
v___x_4696_ = v___x_4693_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4691_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
return v___x_4696_;
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
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
lean_dec(v_cancelTk_x3f_4654_);
lean_dec(v_openDecls_4653_);
lean_dec(v_currNamespace_4652_);
lean_dec_ref(v_options_4651_);
lean_dec_ref(v_env_4648_);
v_a_4701_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4703_ = v___x_4656_;
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v___x_4656_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4706_; 
if (v_isShared_4704_ == 0)
{
v___x_4706_ = v___x_4703_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4701_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_4709_, lean_object* v_declName_4710_, lean_object* v_includeBuiltin_4711_, lean_object* v_options_4712_, lean_object* v_currNamespace_4713_, lean_object* v_openDecls_4714_, lean_object* v_cancelTk_x3f_4715_, lean_object* v_a_4716_){
_start:
{
uint8_t v_includeBuiltin_boxed_4717_; lean_object* v_res_4718_; 
v_includeBuiltin_boxed_4717_ = lean_unbox(v_includeBuiltin_4711_);
v_res_4718_ = l_Lean_findSimpleDocString_x3f(v_env_4709_, v_declName_4710_, v_includeBuiltin_boxed_4717_, v_options_4712_, v_currNamespace_4713_, v_openDecls_4714_, v_cancelTk_x3f_4715_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(lean_object* v_p_4719_, lean_object* v_level_4720_, lean_object* v_part_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___redArg(v_level_4720_, v_part_4721_, v_a_4722_, v_a_4723_, v_a_4724_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0___boxed(lean_object* v_p_4727_, lean_object* v_level_4728_, lean_object* v_part_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l_Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0(v_p_4727_, v_level_4728_, v_part_4729_, v_a_4730_, v_a_4731_, v_a_4732_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
lean_dec(v_a_4730_);
lean_dec(v_level_4728_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(lean_object* v_p_4735_, lean_object* v___x_4736_, size_t v_sz_4737_, size_t v_i_4738_, lean_object* v_bs_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
lean_object* v___x_4744_; 
v___x_4744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___redArg(v___x_4736_, v_sz_4737_, v_i_4738_, v_bs_4739_, v___y_4740_, v___y_4741_, v___y_4742_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3___boxed(lean_object* v_p_4745_, lean_object* v___x_4746_, lean_object* v_sz_4747_, lean_object* v_i_4748_, lean_object* v_bs_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_){
_start:
{
size_t v_sz_boxed_4754_; size_t v_i_boxed_4755_; lean_object* v_res_4756_; 
v_sz_boxed_4754_ = lean_unbox_usize(v_sz_4747_);
lean_dec(v_sz_4747_);
v_i_boxed_4755_ = lean_unbox_usize(v_i_4748_);
lean_dec(v_i_4748_);
v_res_4756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00Lean_findSimpleDocString_x3f_spec__0_spec__3(v_p_4745_, v___x_4746_, v_sz_boxed_4754_, v_i_boxed_4755_, v_bs_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
lean_dec(v___y_4752_);
lean_dec_ref(v___y_4751_);
lean_dec(v___y_4750_);
lean_dec(v___x_4746_);
return v_res_4756_;
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
