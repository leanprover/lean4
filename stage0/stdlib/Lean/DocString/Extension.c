// Lean compiler output
// Module: Lean.DocString.Extension
// Imports: public import Lean.DeclarationRange public import Lean.DocString.Markdown public import Init.Data.String.Extra import Init.Omega
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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_instReprDeclarationRange_repr___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Doc_instReprMathMode_repr(uint8_t, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Std_Format_nestD(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Doc_MarkdownM_push___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object*);
lean_object* l_Lean_Doc_MarkdownM_endsWith___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Doc_MarkdownM_endBlock___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_Doc_MarkdownM_run_x27(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRange_default;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "{ name :="};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__2 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__2_value;
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "val :="};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__3 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__3_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__4 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__5 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__5_value;
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Dynamic.mk "};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__6 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__6_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__7 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__5_value),((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__7_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__8 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__8_value;
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " _ }"};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__9 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__9_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__10 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprElabInline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprElabInline___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprElabInline___closed__0 = (const lean_object*)&l_Lean_instReprElabInline___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprElabInline = (const lean_object*)&l_Lean_instReprElabInline___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__0 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__0_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__1 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__1_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__2 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__2_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__3 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__3_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__4 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__4_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__5 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__5_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__6 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__6_value;
static const lean_ctor_object l_Lean_instMarkdownInlineElabInline___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__0_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__1_value)}};
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__7 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__7_value;
static const lean_ctor_object l_Lean_instMarkdownInlineElabInline___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__7_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__2_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__3_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__4_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__5_value)}};
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__8 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__8_value;
static const lean_ctor_object l_Lean_instMarkdownInlineElabInline___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__8_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__6_value)}};
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__9 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__10 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__10_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__11 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__11_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__12 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__12_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__13 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__13_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__14 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__14_value;
static const lean_ctor_object l_Lean_instMarkdownInlineElabInline___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__14_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__10_value)}};
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__15 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__15_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__16 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__16_value;
static const lean_ctor_object l_Lean_instMarkdownInlineElabInline___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__15_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__16_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__11_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__12_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__13_value)}};
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__17 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__17_value;
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__9_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__18 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__18_value;
static const lean_ctor_object l_Lean_instMarkdownInlineElabInline___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__17_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__18_value)}};
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__19 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__19_value;
static lean_once_cell_t l_Lean_instMarkdownInlineElabInline___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instMarkdownInlineElabInline___closed__20;
static lean_once_cell_t l_Lean_instMarkdownInlineElabInline___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instMarkdownInlineElabInline___closed__21;
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline;
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprElabBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprElabBlock___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprElabBlock___closed__0 = (const lean_object*)&l_Lean_instReprElabBlock___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprElabBlock = (const lean_object*)&l_Lean_instReprElabBlock___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0;
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock;
static const lean_array_object l_Lean_instInhabitedVersoDocString_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedVersoDocString_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedVersoDocString_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedVersoDocString_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedVersoDocString_default = (const lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedVersoDocString = (const lean_object*)&l_Lean_instInhabitedVersoDocString_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "doc"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "verso"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(146, 8, 133, 236, 68, 139, 240, 234)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(153, 72, 77, 160, 222, 42, 129, 126)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "whether to use Verso syntax in docstrings"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(3, 233, 138, 33, 66, 196, 218, 104)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 198, 182, 78, 108, 58, 220, 60)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_doc_verso;
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(146, 8, 133, 236, 68, 139, 240, 234)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(153, 72, 77, 160, 222, 42, 129, 126)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(237, 134, 110, 210, 89, 29, 102, 103)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "whether to use Verso syntax in module docstrings (falls back to `doc.verso` if not set)"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(3, 233, 138, 33, 66, 196, 218, 104)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 198, 182, 78, 108, 58, 220, 60)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(228, 159, 139, 71, 221, 243, 206, 45)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_doc_verso_module;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "docStringExt"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(220, 176, 252, 112, 223, 70, 141, 135)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_docStringExt;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DocString"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 151, 103, 225, 164, 122, 118, 127)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Extension"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 24, 255, 250, 40, 109, 111, 101)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(90, 73, 37, 46, 133, 14, 26, 13)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(251, 17, 71, 28, 211, 27, 155, 40)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inheritDocStringExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 170, 221, 64, 52, 198, 31, 56)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "versoDocStringExt"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 29, 13, 95, 132, 33, 43, 178)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringExt;
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings();
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addDocStringCore___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "invalid doc string, declaration `"};
static const lean_object* l_Lean_addDocStringCore___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_addDocStringCore___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_addDocStringCore___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDocStringCore___redArg___lam__2___closed__1;
static const lean_string_object l_Lean_addDocStringCore___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is in an imported module"};
static const lean_object* l_Lean_addDocStringCore___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_addDocStringCore___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_addDocStringCore___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDocStringCore___redArg___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_removeDocStringCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_removeDocStringCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_removeDocStringCore___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_removeDocStringCore___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "invalid doc string removal, declaration `"};
static const lean_object* l_Lean_removeDocStringCore___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_removeDocStringCore___redArg___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_removeDocStringCore___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_removeDocStringCore___redArg___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addInheritedDocString___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "invalid `[inherit_doc]` attribute, cycle detected"};
static const lean_object* l_Lean_addInheritedDocString___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_addInheritedDocString___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_addInheritedDocString___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addInheritedDocString___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addInheritedDocString___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "invalid `[inherit_doc]` attribute, declaration `"};
static const lean_object* l_Lean_addInheritedDocString___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_addInheritedDocString___redArg___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addInheritedDocString___redArg___lam__3___closed__1;
static const lean_string_object l_Lean_addInheritedDocString___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` already has an `[inherit_doc]` attribute"};
static const lean_object* l_Lean_addInheritedDocString___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_addInheritedDocString___redArg___lam__3___closed__2_value;
static lean_once_cell_t l_Lean_addInheritedDocString___redArg___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addInheritedDocString___redArg___lam__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_addInheritedDocString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addInheritedDocString___redArg___closed__0 = (const lean_object*)&l_Lean_addInheritedDocString___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_findInternalDocString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_findInternalDocString_x3f___closed__0 = (const lean_object*)&l_Lean_findInternalDocString_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5;
static const lean_ctor_object l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__6 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "**"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__2 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "​"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__3 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__3_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__4 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__5 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__6 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]("};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 3, .m_data = "[ˆ^"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__9 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_findInternalDocString_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__12 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__12_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_findInternalDocString_x3f___closed__0_value),((lean_object*)&l_Lean_findInternalDocString_x3f___closed__0_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__12_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__14 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentArray_push___redArg, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "moduleDocExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 198, 210, 20, 250, 243, 120, 74)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_getMainModuleDoc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getMainModuleDoc___closed__0;
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object*);
static lean_once_cell_t l_Lean_getModuleDoc_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getModuleDoc_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_getDocStringText___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___redArg___closed__0 = (const lean_object*)&l_Lean_getDocStringText___redArg___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___redArg___closed__1;
static const lean_string_object l_Lean_getDocStringText___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_getDocStringText___redArg___closed__2 = (const lean_object*)&l_Lean_getDocStringText___redArg___closed__2_value;
static const lean_string_object l_Lean_getDocStringText___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_getDocStringText___redArg___closed__3 = (const lean_object*)&l_Lean_getDocStringText___redArg___closed__3_value;
static const lean_string_object l_Lean_getDocStringText___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_getDocStringText___redArg___closed__4 = (const lean_object*)&l_Lean_getDocStringText___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instInhabitedSnippet;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object*);
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.text"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__1 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3;
static lean_once_cell_t l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.emph"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__5 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__5_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__6 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__6_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7_value;
static const lean_string_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4;
static lean_once_cell_t l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7_value;
static const lean_string_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object*);
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.bold"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__8 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__8_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__8_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__9 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__9_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.code"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__11 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__11_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__11_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__12 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__12_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.math"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__14 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__14_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__14_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__15 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__15_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Doc.Inline.linebreak"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__17 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__17_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__17_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__18 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__18_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Inline.link"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__20 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__20_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__20_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__21 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__21_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__21_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Doc.Inline.footnote"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__23 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__23_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__23_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__24 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__24_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__24_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Doc.Inline.image"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__26 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__26_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__26_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__27 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__27_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__27_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Doc.Inline.concat"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__29 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__29_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__29_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__30 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__30_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__30_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31_value;
static const lean_string_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Doc.Inline.other"};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__32 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__32_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__32_value)}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__33 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__33_value;
static const lean_ctor_object l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__33_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34 = (const lean_object*)&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object*);
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Doc.Block.para"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Doc.Block.code"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__3 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__3_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__3_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__4 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__4_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Doc.Block.ul"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__6 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__6_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__6_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__7 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8_value;
static const lean_string_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__4 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__4_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5_value;
static const lean_string_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "contents"};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__1_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__2_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__3_value),((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object*);
static const lean_string_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9;
static lean_once_cell_t l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11_value;
static const lean_string_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__8_value)}};
static const lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object*);
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Doc.Block.ol"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__9 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__9_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__9_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__10 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__10_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Doc.Block.dl"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__13 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__13_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__13_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__14 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__14_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15_value;
static const lean_string_object l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__1_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__2_value),((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4;
static const lean_string_object l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "desc"};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6 = (const lean_object*)&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object*);
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Doc.Block.blockquote"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__16 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__16_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__16_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__17 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__17_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__17_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Doc.Block.concat"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__19 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__19_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__19_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__20 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__20_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__20_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21_value;
static const lean_string_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Doc.Block.other"};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__22 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__22_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__22_value)}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__23 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__23_value;
static const lean_ctor_object l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__23_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24 = (const lean_object*)&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object*);
static const lean_string_object l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "title"};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__1_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__2_value),((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4;
static const lean_string_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "titleString"};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7;
static const lean_string_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "metadata"};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__8 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__8_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9_value;
static const lean_string_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "content"};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__10 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__10_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12;
static const lean_string_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "subParts"};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__13 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__13_value)}};
static const lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14 = (const lean_object*)&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__1 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__2 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5_value)}};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sections"};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__4 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5_value;
static const lean_string_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "declarationRange"};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__6 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__6_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__6_value)}};
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7_value;
static lean_once_cell_t l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_VersoModuleDocs_instReprSnippet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_VersoModuleDocs_instReprSnippet___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_VersoModuleDocs_instReprSnippet = (const lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_instToMarkdownSnippet___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMarkdownSnippet___lam__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instToMarkdownSnippet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMarkdownSnippet___closed__0;
static lean_once_cell_t l_Lean_instToMarkdownSnippet___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMarkdownSnippet___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet;
static lean_once_cell_t l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoModuleDocs_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoModuleDocs_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoModuleDocs_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoModuleDocs;
static const lean_string_object l_Lean_instReprVersoModuleDocs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "snippets := "};
static const lean_object* l_Lean_instReprVersoModuleDocs___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprVersoModuleDocs___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instReprVersoModuleDocs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprVersoModuleDocs___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instReprVersoModuleDocs___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprVersoModuleDocs___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instReprVersoModuleDocs___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprVersoModuleDocs___lam__0___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprVersoModuleDocs___lam__0___closed__2 = (const lean_object*)&l_Lean_instReprVersoModuleDocs___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprVersoModuleDocs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprVersoModuleDocs___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instReprSnippet___closed__0_value)} };
static const lean_object* l_Lean_instReprVersoModuleDocs___closed__0 = (const lean_object*)&l_Lean_instReprVersoModuleDocs___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprVersoModuleDocs = (const lean_object*)&l_Lean_instReprVersoModuleDocs___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_VersoModuleDocs_add___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Can't nest this snippet here"};
static const lean_object* l_Lean_VersoModuleDocs_add___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_add___closed__0_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_add___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_add___closed__0_value)}};
static const lean_object* l_Lean_VersoModuleDocs_add___closed__1 = (const lean_object*)&l_Lean_VersoModuleDocs_add___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_VersoModuleDocs_add_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.DocString.Extension"};
static const lean_object* l_Lean_VersoModuleDocs_add_x21___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_add_x21___closed__0_value;
static const lean_string_object l_Lean_VersoModuleDocs_add_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.VersoModuleDocs.add!"};
static const lean_object* l_Lean_VersoModuleDocs_add_x21___closed__1 = (const lean_object*)&l_Lean_VersoModuleDocs_add_x21___closed__1_value;
static lean_once_cell_t l_Lean_VersoModuleDocs_add_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_VersoModuleDocs_add_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Can't close a section: none are open"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__0 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object*);
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Invalid nesting: expected at most "};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " but got "};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Can't add content after sub-parts"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__0 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_VersoModuleDocs_assemble___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_VersoModuleDocs_assemble___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_assemble___closed__0_value;
static const lean_ctor_object l_Lean_VersoModuleDocs_assemble___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_assemble___closed__0_value),((lean_object*)&l_Lean_VersoModuleDocs_assemble___closed__0_value),((lean_object*)&l_Lean_VersoModuleDocs_assemble___closed__0_value)}};
static const lean_object* l_Lean_VersoModuleDocs_assemble___closed__1 = (const lean_object*)&l_Lean_VersoModuleDocs_assemble___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_VersoModuleDocs_add_x21, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "versoModuleDocExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 74, 101, 232, 220, 166, 152, 230)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object*);
static lean_once_cell_t l_Lean_getVersoModuleDoc_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getVersoModuleDoc_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModuleDocSnippet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Can't add - incorrect nesting "};
static const lean_object* l_Lean_addVersoModuleDocSnippet___closed__0 = (const lean_object*)&l_Lean_addVersoModuleDocSnippet___closed__0_value;
static const lean_string_object l_Lean_addVersoModuleDocSnippet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "(expected at most "};
static const lean_object* l_Lean_addVersoModuleDocSnippet___closed__1 = (const lean_object*)&l_Lean_addVersoModuleDocSnippet___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0(lean_object* v_v_22_, lean_object* v_x_23_){
_start:
{
lean_object* v_name_24_; lean_object* v_val_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_51_; 
v_name_24_ = lean_ctor_get(v_v_22_, 0);
v_val_25_ = lean_ctor_get(v_v_22_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_v_22_);
if (v_isSharedCheck_51_ == 0)
{
v___x_27_ = v_v_22_;
v_isShared_28_ = v_isSharedCheck_51_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_val_25_);
lean_inc(v_name_24_);
lean_dec(v_v_22_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_51_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_29_ = lean_box(1);
v___x_30_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = l_Lean_Name_reprPrec(v_name_24_, v___x_31_);
if (v_isShared_28_ == 0)
{
lean_ctor_set_tag(v___x_27_, 5);
lean_ctor_set(v___x_27_, 1, v___x_32_);
lean_ctor_set(v___x_27_, 0, v___x_30_);
v___x_34_ = v___x_27_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v___x_32_);
v___x_34_ = v_reuseFailAlloc_50_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
lean_object* v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_35_ = l_Std_Format_nestD(v___x_34_);
v___x_36_ = 0;
v___x_37_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_37_, 0, v___x_35_);
lean_ctor_set_uint8(v___x_37_, sizeof(void*)*1, v___x_36_);
v___x_38_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_29_);
v___x_39_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_40_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_25_);
lean_dec(v_val_25_);
v___x_41_ = l_Lean_Name_reprPrec(v___x_40_, v___x_31_);
v___x_42_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_39_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v___x_43_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_44_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = l_Std_Format_nestD(v___x_44_);
v___x_46_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set_uint8(v___x_46_, sizeof(void*)*1, v___x_36_);
v___x_47_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_38_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = l_Std_Format_nestD(v___x_47_);
v___x_49_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*1, v___x_36_);
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0___boxed(lean_object* v_v_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_instReprElabInline___lam__0(v_v_52_, v_x_53_);
lean_dec(v_x_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__0(lean_object* v_go_57_, lean_object* v_x_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___x_62_; 
lean_inc_ref(v___y_60_);
v___x_62_ = lean_apply_3(v_go_57_, v___y_59_, v___y_60_, v___y_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__0___boxed(lean_object* v_go_63_, lean_object* v_x_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_instMarkdownInlineElabInline___lam__0(v_go_63_, v_x_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec_ref(v___y_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__1(lean_object* v___x_69_, lean_object* v_go_70_, lean_object* v___i_71_, lean_object* v_content_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_array_get_size(v_content_72_);
v___x_77_ = lean_box(0);
v___x_78_ = lean_nat_dec_lt(v___x_75_, v___x_76_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
lean_dec_ref(v_content_72_);
lean_dec_ref(v_go_70_);
lean_dec_ref(v___x_69_);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___y_74_);
return v___x_79_;
}
else
{
lean_object* v___f_80_; uint8_t v___x_81_; 
v___f_80_ = lean_alloc_closure((void*)(l_Lean_instMarkdownInlineElabInline___lam__0___boxed), 5, 1);
lean_closure_set(v___f_80_, 0, v_go_70_);
v___x_81_ = lean_nat_dec_le(v___x_76_, v___x_76_);
if (v___x_81_ == 0)
{
if (v___x_78_ == 0)
{
lean_object* v___x_82_; 
lean_dec_ref(v___f_80_);
lean_dec_ref(v_content_72_);
lean_dec_ref(v___x_69_);
v___x_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_77_);
lean_ctor_set(v___x_82_, 1, v___y_74_);
return v___x_82_;
}
else
{
size_t v___x_83_; size_t v___x_84_; lean_object* v___x_499__overap_85_; lean_object* v___x_86_; 
v___x_83_ = ((size_t)0ULL);
v___x_84_ = lean_usize_of_nat(v___x_76_);
v___x_499__overap_85_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_69_, v___f_80_, v_content_72_, v___x_83_, v___x_84_, v___x_77_);
lean_inc_ref(v___y_73_);
v___x_86_ = lean_apply_2(v___x_499__overap_85_, v___y_73_, v___y_74_);
return v___x_86_;
}
}
else
{
size_t v___x_87_; size_t v___x_88_; lean_object* v___x_502__overap_89_; lean_object* v___x_90_; 
v___x_87_ = ((size_t)0ULL);
v___x_88_ = lean_usize_of_nat(v___x_76_);
v___x_502__overap_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_69_, v___f_80_, v_content_72_, v___x_87_, v___x_88_, v___x_77_);
lean_inc_ref(v___y_73_);
v___x_90_ = lean_apply_2(v___x_502__overap_89_, v___y_73_, v___y_74_);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__1___boxed(lean_object* v___x_91_, lean_object* v_go_92_, lean_object* v___i_93_, lean_object* v_content_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_instMarkdownInlineElabInline___lam__1(v___x_91_, v_go_92_, v___i_93_, v_content_94_, v___y_95_, v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec_ref(v___i_93_);
return v_res_97_;
}
}
static lean_object* _init_l_Lean_instMarkdownInlineElabInline___closed__20(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_instMarkdownInlineElabInline___closed__19));
v___x_144_ = l_ReaderT_instMonad___redArg(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_instMarkdownInlineElabInline___closed__21(void){
_start:
{
lean_object* v___x_145_; lean_object* v___f_146_; 
v___x_145_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__20, &l_Lean_instMarkdownInlineElabInline___closed__20_once, _init_l_Lean_instMarkdownInlineElabInline___closed__20);
v___f_146_ = lean_alloc_closure((void*)(l_Lean_instMarkdownInlineElabInline___lam__1___boxed), 6, 1);
lean_closure_set(v___f_146_, 0, v___x_145_);
return v___f_146_;
}
}
static lean_object* _init_l_Lean_instMarkdownInlineElabInline(void){
_start:
{
lean_object* v___f_147_; 
v___f_147_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__21, &l_Lean_instMarkdownInlineElabInline___closed__21_once, _init_l_Lean_instMarkdownInlineElabInline___closed__21);
return v___f_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0(lean_object* v_v_148_, lean_object* v_x_149_){
_start:
{
lean_object* v_name_150_; lean_object* v_val_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_177_; 
v_name_150_ = lean_ctor_get(v_v_148_, 0);
v_val_151_ = lean_ctor_get(v_v_148_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_v_148_);
if (v_isSharedCheck_177_ == 0)
{
v___x_153_ = v_v_148_;
v_isShared_154_ = v_isSharedCheck_177_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_val_151_);
lean_inc(v_name_150_);
lean_dec(v_v_148_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_177_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_155_ = lean_box(1);
v___x_156_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = l_Lean_Name_reprPrec(v_name_150_, v___x_157_);
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 5);
lean_ctor_set(v___x_153_, 1, v___x_158_);
lean_ctor_set(v___x_153_, 0, v___x_156_);
v___x_160_ = v___x_153_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_158_);
v___x_160_ = v_reuseFailAlloc_176_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_161_ = l_Std_Format_nestD(v___x_160_);
v___x_162_ = 0;
v___x_163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*1, v___x_162_);
v___x_164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_155_);
v___x_165_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_166_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_151_);
lean_dec(v_val_151_);
v___x_167_ = l_Lean_Name_reprPrec(v___x_166_, v___x_157_);
v___x_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_165_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = l_Std_Format_nestD(v___x_170_);
v___x_172_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*1, v___x_162_);
v___x_173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_164_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = l_Std_Format_nestD(v___x_173_);
v___x_175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*1, v___x_162_);
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0___boxed(lean_object* v_v_178_, lean_object* v_x_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_instReprElabBlock___lam__0(v_v_178_, v_x_179_);
lean_dec(v_x_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v_goB_183_, lean_object* v_x_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v___x_188_; 
lean_inc_ref(v___y_186_);
v___x_188_ = lean_apply_3(v_goB_183_, v___y_185_, v___y_186_, v___y_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object* v_goB_189_, lean_object* v_x_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0(v_goB_189_, v_x_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object* v___x_195_, lean_object* v___goI_196_, lean_object* v_goB_197_, lean_object* v___b_198_, lean_object* v_content_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_array_get_size(v_content_199_);
v___x_204_ = lean_box(0);
v___x_205_ = lean_nat_dec_lt(v___x_202_, v___x_203_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_dec_ref(v_content_199_);
lean_dec_ref(v_goB_197_);
lean_dec_ref(v___x_195_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___y_201_);
return v___x_206_;
}
else
{
lean_object* v___f_207_; uint8_t v___x_208_; 
v___f_207_ = lean_alloc_closure((void*)(l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0___boxed), 5, 1);
lean_closure_set(v___f_207_, 0, v_goB_197_);
v___x_208_ = lean_nat_dec_le(v___x_203_, v___x_203_);
if (v___x_208_ == 0)
{
if (v___x_205_ == 0)
{
lean_object* v___x_209_; 
lean_dec_ref(v___f_207_);
lean_dec_ref(v_content_199_);
lean_dec_ref(v___x_195_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_204_);
lean_ctor_set(v___x_209_, 1, v___y_201_);
return v___x_209_;
}
else
{
size_t v___x_210_; size_t v___x_211_; lean_object* v___x_499__overap_212_; lean_object* v___x_213_; 
v___x_210_ = ((size_t)0ULL);
v___x_211_ = lean_usize_of_nat(v___x_203_);
v___x_499__overap_212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_195_, v___f_207_, v_content_199_, v___x_210_, v___x_211_, v___x_204_);
lean_inc_ref(v___y_200_);
v___x_213_ = lean_apply_2(v___x_499__overap_212_, v___y_200_, v___y_201_);
return v___x_213_;
}
}
else
{
size_t v___x_214_; size_t v___x_215_; lean_object* v___x_502__overap_216_; lean_object* v___x_217_; 
v___x_214_ = ((size_t)0ULL);
v___x_215_ = lean_usize_of_nat(v___x_203_);
v___x_502__overap_216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_195_, v___f_207_, v_content_199_, v___x_214_, v___x_215_, v___x_204_);
lean_inc_ref(v___y_200_);
v___x_217_ = lean_apply_2(v___x_502__overap_216_, v___y_200_, v___y_201_);
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object* v___x_218_, lean_object* v___goI_219_, lean_object* v_goB_220_, lean_object* v___b_221_, lean_object* v_content_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_218_, v___goI_219_, v_goB_220_, v___b_221_, v_content_222_, v___y_223_, v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec_ref(v___b_221_);
lean_dec_ref(v___goI_219_);
return v_res_225_;
}
}
static lean_object* _init_l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0(void){
_start:
{
lean_object* v___x_226_; lean_object* v___f_227_; 
v___x_226_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__20, &l_Lean_instMarkdownInlineElabInline___closed__20_once, _init_l_Lean_instMarkdownInlineElabInline___closed__20);
v___f_227_ = lean_alloc_closure((void*)(l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1___boxed), 7, 1);
lean_closure_set(v___f_227_, 0, v___x_226_);
return v___f_227_;
}
}
static lean_object* _init_l_Lean_instMarkdownBlockElabInlineElabBlock(void){
_start:
{
lean_object* v___f_228_; 
v___f_228_ = lean_obj_once(&l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0, &l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0_once, _init_l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0);
return v___f_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(lean_object* v_name_235_, lean_object* v_decl_236_, lean_object* v_ref_237_){
_start:
{
lean_object* v_defValue_239_; lean_object* v_descr_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_267_; 
v_defValue_239_ = lean_ctor_get(v_decl_236_, 0);
v_descr_240_ = lean_ctor_get(v_decl_236_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_decl_236_);
if (v_isSharedCheck_267_ == 0)
{
v___x_242_ = v_decl_236_;
v_isShared_243_ = v_isSharedCheck_267_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_descr_240_);
lean_inc(v_defValue_239_);
lean_dec(v_decl_236_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_267_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_244_ = lean_alloc_ctor(1, 0, 1);
v___x_245_ = lean_unbox(v_defValue_239_);
lean_ctor_set_uint8(v___x_244_, 0, v___x_245_);
lean_inc_n(v_name_235_, 2);
v___x_246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_246_, 0, v_name_235_);
lean_ctor_set(v___x_246_, 1, v_ref_237_);
lean_ctor_set(v___x_246_, 2, v___x_244_);
lean_ctor_set(v___x_246_, 3, v_descr_240_);
v___x_247_ = lean_register_option(v_name_235_, v___x_246_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_257_; 
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v___x_247_, 0);
lean_dec(v_unused_258_);
v___x_249_ = v___x_247_;
v_isShared_250_ = v_isSharedCheck_257_;
goto v_resetjp_248_;
}
else
{
lean_dec(v___x_247_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_257_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_defValue_239_);
lean_ctor_set(v___x_242_, 0, v_name_235_);
v___x_252_ = v___x_242_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_name_235_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_defValue_239_);
v___x_252_ = v_reuseFailAlloc_256_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_252_);
v___x_254_ = v___x_249_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_del_object(v___x_242_);
lean_dec(v_defValue_239_);
lean_dec(v_name_235_);
v_a_259_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_247_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_247_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_268_, lean_object* v_decl_269_, lean_object* v_ref_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v_name_268_, v_decl_269_, v_ref_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_290_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_291_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_292_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_289_, v___x_290_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4____boxed(lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_312_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_313_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_314_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_311_, v___x_312_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4____boxed(lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = lean_box(1);
v___x_319_ = lean_st_mk_ref(v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2____boxed(lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v_k_325_; lean_object* v_v_326_; lean_object* v_l_327_; lean_object* v_r_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_k_325_ = lean_ctor_get(v_x_324_, 1);
v_v_326_ = lean_ctor_get(v_x_324_, 2);
v_l_327_ = lean_ctor_get(v_x_324_, 3);
v_r_328_ = lean_ctor_get(v_x_324_, 4);
v___x_329_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_323_, v_l_327_);
lean_inc(v_v_326_);
lean_inc(v_k_325_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_k_325_);
lean_ctor_set(v___x_330_, 1, v_v_326_);
v___x_331_ = lean_array_push(v___x_329_, v___x_330_);
v_init_323_ = v___x_331_;
v_x_324_ = v_r_328_;
goto _start;
}
else
{
return v_init_323_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_333_, lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_333_, v_x_334_);
lean_dec(v_x_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(lean_object* v_x_340_, lean_object* v_s_341_){
_start:
{
lean_object* v___x_342_; lean_object* v_ents_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_342_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v_ents_343_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v___x_342_, v_s_341_);
v___x_344_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
lean_inc_ref(v_ents_343_);
v___x_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_ents_343_);
lean_ctor_set(v___x_345_, 2, v_ents_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object* v_x_346_, lean_object* v_s_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(v_x_346_, v_s_347_);
lean_dec(v_s_347_);
lean_dec_ref(v_x_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___f_357_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_358_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_359_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_360_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_358_, v___x_359_, v___f_357_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(lean_object* v_init_363_, lean_object* v_t_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_363_, v_t_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_366_, lean_object* v_t_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(v_init_366_, v_t_367_);
lean_dec(v_t_367_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_369_, lean_object* v_x_370_){
_start:
{
if (lean_obj_tag(v_x_370_) == 0)
{
lean_object* v_k_371_; lean_object* v_v_372_; lean_object* v_l_373_; lean_object* v_r_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_k_371_ = lean_ctor_get(v_x_370_, 1);
v_v_372_ = lean_ctor_get(v_x_370_, 2);
v_l_373_ = lean_ctor_get(v_x_370_, 3);
v_r_374_ = lean_ctor_get(v_x_370_, 4);
v___x_375_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_369_, v_l_373_);
lean_inc(v_v_372_);
lean_inc(v_k_371_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v_k_371_);
lean_ctor_set(v___x_376_, 1, v_v_372_);
v___x_377_ = lean_array_push(v___x_375_, v___x_376_);
v_init_369_ = v___x_377_;
v_x_370_ = v_r_374_;
goto _start;
}
else
{
return v_init_369_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_379_, lean_object* v_x_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_379_, v_x_380_);
lean_dec(v_x_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(lean_object* v_x_386_, lean_object* v_s_387_){
_start:
{
lean_object* v___x_388_; lean_object* v_ents_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_388_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v_ents_389_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v___x_388_, v_s_387_);
v___x_390_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
lean_inc_ref(v_ents_389_);
v___x_391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v_ents_389_);
lean_ctor_set(v___x_391_, 2, v_ents_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object* v_x_392_, lean_object* v_s_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(v_x_392_, v_s_393_);
lean_dec(v_s_393_);
lean_dec_ref(v_x_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___f_424_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_425_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_426_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_427_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_425_, v___x_426_, v___f_424_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_();
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(lean_object* v_init_430_, lean_object* v_t_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_430_, v_t_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_433_, lean_object* v_t_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(v_init_433_, v_t_434_);
lean_dec(v_t_434_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_box(1);
v___x_438_ = lean_st_mk_ref(v___x_437_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_442_, lean_object* v_x_443_){
_start:
{
if (lean_obj_tag(v_x_443_) == 0)
{
lean_object* v_k_444_; lean_object* v_v_445_; lean_object* v_l_446_; lean_object* v_r_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_k_444_ = lean_ctor_get(v_x_443_, 1);
v_v_445_ = lean_ctor_get(v_x_443_, 2);
v_l_446_ = lean_ctor_get(v_x_443_, 3);
v_r_447_ = lean_ctor_get(v_x_443_, 4);
v___x_448_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_442_, v_l_446_);
lean_inc(v_v_445_);
lean_inc(v_k_444_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_k_444_);
lean_ctor_set(v___x_449_, 1, v_v_445_);
v___x_450_ = lean_array_push(v___x_448_, v___x_449_);
v_init_442_ = v___x_450_;
v_x_443_ = v_r_447_;
goto _start;
}
else
{
return v_init_442_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_452_, lean_object* v_x_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_452_, v_x_453_);
lean_dec(v_x_453_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(lean_object* v_x_459_, lean_object* v_s_460_){
_start:
{
lean_object* v___x_461_; lean_object* v_ents_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_461_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v_ents_462_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v___x_461_, v_s_460_);
v___x_463_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
lean_inc_ref(v_ents_462_);
v___x_464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v_ents_462_);
lean_ctor_set(v___x_464_, 2, v_ents_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object* v_x_465_, lean_object* v_s_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(v_x_465_, v_s_466_);
lean_dec(v_s_466_);
lean_dec_ref(v_x_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___f_474_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v___x_475_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v___x_476_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_477_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_475_, v___x_476_, v___f_474_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(lean_object* v_init_480_, lean_object* v_t_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_480_, v_t_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_483_, lean_object* v_t_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(v_init_483_, v_t_484_);
lean_dec(v_t_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString(lean_object* v_declName_486_, lean_object* v_docString_487_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_489_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_490_ = lean_st_ref_take(v___x_489_);
v___x_491_ = l_String_removeLeadingSpaces(v_docString_487_);
v___x_492_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_486_, v___x_491_, v___x_490_);
v___x_493_ = lean_st_ref_set(v___x_489_, v___x_492_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString___boxed(lean_object* v_declName_495_, lean_object* v_docString_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_addBuiltinDocString(v_declName_495_, v_docString_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object* v_k_499_, lean_object* v_t_500_){
_start:
{
if (lean_obj_tag(v_t_500_) == 0)
{
lean_object* v_k_501_; lean_object* v_v_502_; lean_object* v_l_503_; lean_object* v_r_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_1158_; 
v_k_501_ = lean_ctor_get(v_t_500_, 1);
v_v_502_ = lean_ctor_get(v_t_500_, 2);
v_l_503_ = lean_ctor_get(v_t_500_, 3);
v_r_504_ = lean_ctor_get(v_t_500_, 4);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_t_500_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v_t_500_, 0);
lean_dec(v_unused_1159_);
v___x_506_ = v_t_500_;
v_isShared_507_ = v_isSharedCheck_1158_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_r_504_);
lean_inc(v_l_503_);
lean_inc(v_v_502_);
lean_inc(v_k_501_);
lean_dec(v_t_500_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_1158_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
uint8_t v___x_508_; 
v___x_508_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_499_, v_k_501_);
switch(v___x_508_)
{
case 0:
{
lean_object* v_impl_509_; lean_object* v___x_510_; 
v_impl_509_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_499_, v_l_503_);
v___x_510_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_509_) == 0)
{
if (lean_obj_tag(v_r_504_) == 0)
{
lean_object* v_size_511_; lean_object* v_size_512_; lean_object* v_k_513_; lean_object* v_v_514_; lean_object* v_l_515_; lean_object* v_r_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_size_511_ = lean_ctor_get(v_impl_509_, 0);
lean_inc(v_size_511_);
v_size_512_ = lean_ctor_get(v_r_504_, 0);
v_k_513_ = lean_ctor_get(v_r_504_, 1);
v_v_514_ = lean_ctor_get(v_r_504_, 2);
v_l_515_ = lean_ctor_get(v_r_504_, 3);
lean_inc(v_l_515_);
v_r_516_ = lean_ctor_get(v_r_504_, 4);
v___x_517_ = lean_unsigned_to_nat(3u);
v___x_518_ = lean_nat_mul(v___x_517_, v_size_511_);
v___x_519_ = lean_nat_dec_lt(v___x_518_, v_size_512_);
lean_dec(v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
lean_dec(v_l_515_);
v___x_520_ = lean_nat_add(v___x_510_, v_size_511_);
lean_dec(v_size_511_);
v___x_521_ = lean_nat_add(v___x_520_, v_size_512_);
lean_dec(v___x_520_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 3, v_impl_509_);
lean_ctor_set(v___x_506_, 0, v___x_521_);
v___x_523_ = v___x_506_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_impl_509_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_r_504_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
else
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_588_; 
lean_inc(v_r_516_);
lean_inc(v_v_514_);
lean_inc(v_k_513_);
lean_inc(v_size_512_);
v_isSharedCheck_588_ = !lean_is_exclusive(v_r_504_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; lean_object* v_unused_590_; lean_object* v_unused_591_; lean_object* v_unused_592_; lean_object* v_unused_593_; 
v_unused_589_ = lean_ctor_get(v_r_504_, 4);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_r_504_, 3);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_r_504_, 2);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_r_504_, 1);
lean_dec(v_unused_592_);
v_unused_593_ = lean_ctor_get(v_r_504_, 0);
lean_dec(v_unused_593_);
v___x_526_ = v_r_504_;
v_isShared_527_ = v_isSharedCheck_588_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_r_504_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_588_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_size_528_; lean_object* v_k_529_; lean_object* v_v_530_; lean_object* v_l_531_; lean_object* v_r_532_; lean_object* v_size_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_size_528_ = lean_ctor_get(v_l_515_, 0);
v_k_529_ = lean_ctor_get(v_l_515_, 1);
v_v_530_ = lean_ctor_get(v_l_515_, 2);
v_l_531_ = lean_ctor_get(v_l_515_, 3);
v_r_532_ = lean_ctor_get(v_l_515_, 4);
v_size_533_ = lean_ctor_get(v_r_516_, 0);
v___x_534_ = lean_unsigned_to_nat(2u);
v___x_535_ = lean_nat_mul(v___x_534_, v_size_533_);
v___x_536_ = lean_nat_dec_lt(v_size_528_, v___x_535_);
lean_dec(v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_564_; 
lean_inc(v_r_532_);
lean_inc(v_l_531_);
lean_inc(v_v_530_);
lean_inc(v_k_529_);
v_isSharedCheck_564_ = !lean_is_exclusive(v_l_515_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; lean_object* v_unused_568_; lean_object* v_unused_569_; 
v_unused_565_ = lean_ctor_get(v_l_515_, 4);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_l_515_, 3);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_l_515_, 2);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_l_515_, 1);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_l_515_, 0);
lean_dec(v_unused_569_);
v___x_538_ = v_l_515_;
v_isShared_539_ = v_isSharedCheck_564_;
goto v_resetjp_537_;
}
else
{
lean_dec(v_l_515_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_564_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_554_; 
v___x_540_ = lean_nat_add(v___x_510_, v_size_511_);
lean_dec(v_size_511_);
v___x_541_ = lean_nat_add(v___x_540_, v_size_512_);
lean_dec(v_size_512_);
if (lean_obj_tag(v_l_531_) == 0)
{
lean_object* v_size_562_; 
v_size_562_ = lean_ctor_get(v_l_531_, 0);
lean_inc(v_size_562_);
v___y_554_ = v_size_562_;
goto v___jp_553_;
}
else
{
lean_object* v___x_563_; 
v___x_563_ = lean_unsigned_to_nat(0u);
v___y_554_ = v___x_563_;
goto v___jp_553_;
}
v___jp_542_:
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = lean_nat_add(v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec(v___y_544_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v_r_516_);
lean_ctor_set(v___x_538_, 3, v_r_532_);
lean_ctor_set(v___x_538_, 2, v_v_514_);
lean_ctor_set(v___x_538_, 1, v_k_513_);
lean_ctor_set(v___x_538_, 0, v___x_546_);
v___x_548_ = v___x_538_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_k_513_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_v_514_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_r_532_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_r_516_);
v___x_548_ = v_reuseFailAlloc_552_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 4, v___x_548_);
lean_ctor_set(v___x_526_, 3, v___y_543_);
lean_ctor_set(v___x_526_, 2, v_v_530_);
lean_ctor_set(v___x_526_, 1, v_k_529_);
lean_ctor_set(v___x_526_, 0, v___x_541_);
v___x_550_ = v___x_526_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_k_529_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_v_530_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v___y_543_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
v___jp_553_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = lean_nat_add(v___x_540_, v___y_554_);
lean_dec(v___y_554_);
lean_dec(v___x_540_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v_l_531_);
lean_ctor_set(v___x_506_, 3, v_impl_509_);
lean_ctor_set(v___x_506_, 0, v___x_555_);
v___x_557_ = v___x_506_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_impl_509_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_l_531_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; 
v___x_558_ = lean_nat_add(v___x_510_, v_size_533_);
if (lean_obj_tag(v_r_532_) == 0)
{
lean_object* v_size_559_; 
v_size_559_ = lean_ctor_get(v_r_532_, 0);
lean_inc(v_size_559_);
v___y_543_ = v___x_557_;
v___y_544_ = v___x_558_;
v___y_545_ = v_size_559_;
goto v___jp_542_;
}
else
{
lean_object* v___x_560_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___y_543_ = v___x_557_;
v___y_544_ = v___x_558_;
v___y_545_ = v___x_560_;
goto v___jp_542_;
}
}
}
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
lean_del_object(v___x_506_);
v___x_570_ = lean_nat_add(v___x_510_, v_size_511_);
lean_dec(v_size_511_);
v___x_571_ = lean_nat_add(v___x_570_, v_size_512_);
lean_dec(v_size_512_);
v___x_572_ = lean_nat_add(v___x_570_, v_size_528_);
lean_dec(v___x_570_);
lean_inc_ref(v_impl_509_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 4, v_l_515_);
lean_ctor_set(v___x_526_, 3, v_impl_509_);
lean_ctor_set(v___x_526_, 2, v_v_502_);
lean_ctor_set(v___x_526_, 1, v_k_501_);
lean_ctor_set(v___x_526_, 0, v___x_572_);
v___x_574_ = v___x_526_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v_impl_509_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v_l_515_);
v___x_574_ = v_reuseFailAlloc_587_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
v_isSharedCheck_581_ = !lean_is_exclusive(v_impl_509_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; lean_object* v_unused_583_; lean_object* v_unused_584_; lean_object* v_unused_585_; lean_object* v_unused_586_; 
v_unused_582_ = lean_ctor_get(v_impl_509_, 4);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_impl_509_, 3);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_impl_509_, 2);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_impl_509_, 1);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_impl_509_, 0);
lean_dec(v_unused_586_);
v___x_576_ = v_impl_509_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_dec(v_impl_509_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 4, v_r_516_);
lean_ctor_set(v___x_576_, 3, v___x_574_);
lean_ctor_set(v___x_576_, 2, v_v_514_);
lean_ctor_set(v___x_576_, 1, v_k_513_);
lean_ctor_set(v___x_576_, 0, v___x_571_);
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_k_513_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_v_514_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v_r_516_);
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
else
{
lean_object* v_size_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v_size_594_ = lean_ctor_get(v_impl_509_, 0);
lean_inc(v_size_594_);
v___x_595_ = lean_nat_add(v___x_510_, v_size_594_);
lean_dec(v_size_594_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 3, v_impl_509_);
lean_ctor_set(v___x_506_, 0, v___x_595_);
v___x_597_ = v___x_506_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_impl_509_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_r_504_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
if (lean_obj_tag(v_r_504_) == 0)
{
lean_object* v_l_599_; 
v_l_599_ = lean_ctor_get(v_r_504_, 3);
lean_inc(v_l_599_);
if (lean_obj_tag(v_l_599_) == 0)
{
lean_object* v_r_600_; 
v_r_600_ = lean_ctor_get(v_r_504_, 4);
lean_inc(v_r_600_);
if (lean_obj_tag(v_r_600_) == 0)
{
lean_object* v_size_601_; lean_object* v_k_602_; lean_object* v_v_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_616_; 
v_size_601_ = lean_ctor_get(v_r_504_, 0);
v_k_602_ = lean_ctor_get(v_r_504_, 1);
v_v_603_ = lean_ctor_get(v_r_504_, 2);
v_isSharedCheck_616_ = !lean_is_exclusive(v_r_504_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; lean_object* v_unused_618_; 
v_unused_617_ = lean_ctor_get(v_r_504_, 4);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_r_504_, 3);
lean_dec(v_unused_618_);
v___x_605_ = v_r_504_;
v_isShared_606_ = v_isSharedCheck_616_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_v_603_);
lean_inc(v_k_602_);
lean_inc(v_size_601_);
lean_dec(v_r_504_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_616_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_size_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v_size_607_ = lean_ctor_get(v_l_599_, 0);
v___x_608_ = lean_nat_add(v___x_510_, v_size_601_);
lean_dec(v_size_601_);
v___x_609_ = lean_nat_add(v___x_510_, v_size_607_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 4, v_l_599_);
lean_ctor_set(v___x_605_, 3, v_impl_509_);
lean_ctor_set(v___x_605_, 2, v_v_502_);
lean_ctor_set(v___x_605_, 1, v_k_501_);
lean_ctor_set(v___x_605_, 0, v___x_609_);
v___x_611_ = v___x_605_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_impl_509_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_l_599_);
v___x_611_ = v_reuseFailAlloc_615_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v_r_600_);
lean_ctor_set(v___x_506_, 3, v___x_611_);
lean_ctor_set(v___x_506_, 2, v_v_603_);
lean_ctor_set(v___x_506_, 1, v_k_602_);
lean_ctor_set(v___x_506_, 0, v___x_608_);
v___x_613_ = v___x_506_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v_r_600_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v_k_619_; lean_object* v_v_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_643_; 
v_k_619_ = lean_ctor_get(v_r_504_, 1);
v_v_620_ = lean_ctor_get(v_r_504_, 2);
v_isSharedCheck_643_ = !lean_is_exclusive(v_r_504_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; lean_object* v_unused_645_; lean_object* v_unused_646_; 
v_unused_644_ = lean_ctor_get(v_r_504_, 4);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_r_504_, 3);
lean_dec(v_unused_645_);
v_unused_646_ = lean_ctor_get(v_r_504_, 0);
lean_dec(v_unused_646_);
v___x_622_ = v_r_504_;
v_isShared_623_ = v_isSharedCheck_643_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_v_620_);
lean_inc(v_k_619_);
lean_dec(v_r_504_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_643_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_k_624_; lean_object* v_v_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_639_; 
v_k_624_ = lean_ctor_get(v_l_599_, 1);
v_v_625_ = lean_ctor_get(v_l_599_, 2);
v_isSharedCheck_639_ = !lean_is_exclusive(v_l_599_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; lean_object* v_unused_641_; lean_object* v_unused_642_; 
v_unused_640_ = lean_ctor_get(v_l_599_, 4);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_l_599_, 3);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_l_599_, 0);
lean_dec(v_unused_642_);
v___x_627_ = v_l_599_;
v_isShared_628_ = v_isSharedCheck_639_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_v_625_);
lean_inc(v_k_624_);
lean_dec(v_l_599_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_639_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = lean_unsigned_to_nat(3u);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 4, v_r_600_);
lean_ctor_set(v___x_627_, 3, v_r_600_);
lean_ctor_set(v___x_627_, 2, v_v_502_);
lean_ctor_set(v___x_627_, 1, v_k_501_);
lean_ctor_set(v___x_627_, 0, v___x_510_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_r_600_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v_r_600_);
v___x_631_ = v_reuseFailAlloc_638_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 3, v_r_600_);
lean_ctor_set(v___x_622_, 0, v___x_510_);
v___x_633_ = v___x_622_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_r_600_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_r_600_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v___x_633_);
lean_ctor_set(v___x_506_, 3, v___x_631_);
lean_ctor_set(v___x_506_, 2, v_v_625_);
lean_ctor_set(v___x_506_, 1, v_k_624_);
lean_ctor_set(v___x_506_, 0, v___x_629_);
v___x_635_ = v___x_506_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_624_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_625_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_647_; 
v_r_647_ = lean_ctor_get(v_r_504_, 4);
lean_inc(v_r_647_);
if (lean_obj_tag(v_r_647_) == 0)
{
lean_object* v_k_648_; lean_object* v_v_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_660_; 
v_k_648_ = lean_ctor_get(v_r_504_, 1);
v_v_649_ = lean_ctor_get(v_r_504_, 2);
v_isSharedCheck_660_ = !lean_is_exclusive(v_r_504_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; lean_object* v_unused_662_; lean_object* v_unused_663_; 
v_unused_661_ = lean_ctor_get(v_r_504_, 4);
lean_dec(v_unused_661_);
v_unused_662_ = lean_ctor_get(v_r_504_, 3);
lean_dec(v_unused_662_);
v_unused_663_ = lean_ctor_get(v_r_504_, 0);
lean_dec(v_unused_663_);
v___x_651_ = v_r_504_;
v_isShared_652_ = v_isSharedCheck_660_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_v_649_);
lean_inc(v_k_648_);
lean_dec(v_r_504_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_660_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_unsigned_to_nat(3u);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v_l_599_);
lean_ctor_set(v___x_651_, 2, v_v_502_);
lean_ctor_set(v___x_651_, 1, v_k_501_);
lean_ctor_set(v___x_651_, 0, v___x_510_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_659_, 3, v_l_599_);
lean_ctor_set(v_reuseFailAlloc_659_, 4, v_l_599_);
v___x_655_ = v_reuseFailAlloc_659_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_657_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v_r_647_);
lean_ctor_set(v___x_506_, 3, v___x_655_);
lean_ctor_set(v___x_506_, 2, v_v_649_);
lean_ctor_set(v___x_506_, 1, v_k_648_);
lean_ctor_set(v___x_506_, 0, v___x_653_);
v___x_657_ = v___x_506_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_k_648_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_v_649_);
lean_ctor_set(v_reuseFailAlloc_658_, 3, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_658_, 4, v_r_647_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_size_664_; lean_object* v_k_665_; lean_object* v_v_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_677_; 
v_size_664_ = lean_ctor_get(v_r_504_, 0);
v_k_665_ = lean_ctor_get(v_r_504_, 1);
v_v_666_ = lean_ctor_get(v_r_504_, 2);
v_isSharedCheck_677_ = !lean_is_exclusive(v_r_504_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; lean_object* v_unused_679_; 
v_unused_678_ = lean_ctor_get(v_r_504_, 4);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v_r_504_, 3);
lean_dec(v_unused_679_);
v___x_668_ = v_r_504_;
v_isShared_669_ = v_isSharedCheck_677_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_v_666_);
lean_inc(v_k_665_);
lean_inc(v_size_664_);
lean_dec(v_r_504_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_677_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 3, v_r_647_);
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_size_664_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_k_665_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_v_666_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_r_647_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v_r_647_);
v___x_671_ = v_reuseFailAlloc_676_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_unsigned_to_nat(2u);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v___x_671_);
lean_ctor_set(v___x_506_, 3, v_r_647_);
lean_ctor_set(v___x_506_, 0, v___x_672_);
v___x_674_ = v___x_506_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_r_647_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v___x_671_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
}
else
{
lean_object* v___x_681_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 3, v_r_504_);
lean_ctor_set(v___x_506_, 0, v___x_510_);
v___x_681_ = v___x_506_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_r_504_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_r_504_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
case 1:
{
lean_del_object(v___x_506_);
lean_dec(v_v_502_);
lean_dec(v_k_501_);
if (lean_obj_tag(v_l_503_) == 0)
{
if (lean_obj_tag(v_r_504_) == 0)
{
lean_object* v_size_683_; lean_object* v_k_684_; lean_object* v_v_685_; lean_object* v_l_686_; lean_object* v_r_687_; lean_object* v_size_688_; lean_object* v_k_689_; lean_object* v_v_690_; lean_object* v_l_691_; lean_object* v_r_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_size_683_ = lean_ctor_get(v_l_503_, 0);
v_k_684_ = lean_ctor_get(v_l_503_, 1);
v_v_685_ = lean_ctor_get(v_l_503_, 2);
v_l_686_ = lean_ctor_get(v_l_503_, 3);
v_r_687_ = lean_ctor_get(v_l_503_, 4);
lean_inc(v_r_687_);
v_size_688_ = lean_ctor_get(v_r_504_, 0);
v_k_689_ = lean_ctor_get(v_r_504_, 1);
v_v_690_ = lean_ctor_get(v_r_504_, 2);
v_l_691_ = lean_ctor_get(v_r_504_, 3);
lean_inc(v_l_691_);
v_r_692_ = lean_ctor_get(v_r_504_, 4);
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_nat_dec_lt(v_size_683_, v_size_688_);
if (v___x_694_ == 0)
{
lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_830_; 
lean_inc(v_l_686_);
lean_inc(v_v_685_);
lean_inc(v_k_684_);
v_isSharedCheck_830_ = !lean_is_exclusive(v_l_503_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; 
v_unused_831_ = lean_ctor_get(v_l_503_, 4);
lean_dec(v_unused_831_);
v_unused_832_ = lean_ctor_get(v_l_503_, 3);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_l_503_, 2);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_l_503_, 1);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_l_503_, 0);
lean_dec(v_unused_835_);
v___x_696_ = v_l_503_;
v_isShared_697_ = v_isSharedCheck_830_;
goto v_resetjp_695_;
}
else
{
lean_dec(v_l_503_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_830_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v_tree_699_; 
v___x_698_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_684_, v_v_685_, v_l_686_, v_r_687_);
v_tree_699_ = lean_ctor_get(v___x_698_, 2);
lean_inc(v_tree_699_);
if (lean_obj_tag(v_tree_699_) == 0)
{
lean_object* v_k_700_; lean_object* v_v_701_; lean_object* v_size_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_k_700_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_k_700_);
v_v_701_ = lean_ctor_get(v___x_698_, 1);
lean_inc(v_v_701_);
lean_dec_ref(v___x_698_);
v_size_702_ = lean_ctor_get(v_tree_699_, 0);
v___x_703_ = lean_unsigned_to_nat(3u);
v___x_704_ = lean_nat_mul(v___x_703_, v_size_702_);
v___x_705_ = lean_nat_dec_lt(v___x_704_, v_size_688_);
lean_dec(v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
lean_dec(v_l_691_);
v___x_706_ = lean_nat_add(v___x_693_, v_size_702_);
v___x_707_ = lean_nat_add(v___x_706_, v_size_688_);
lean_dec(v___x_706_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 4, v_r_504_);
lean_ctor_set(v___x_696_, 3, v_tree_699_);
lean_ctor_set(v___x_696_, 2, v_v_701_);
lean_ctor_set(v___x_696_, 1, v_k_700_);
lean_ctor_set(v___x_696_, 0, v___x_707_);
v___x_709_ = v___x_696_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_k_700_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_v_701_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_tree_699_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v_r_504_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
else
{
lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_765_; 
lean_inc(v_r_692_);
lean_inc(v_v_690_);
lean_inc(v_k_689_);
lean_inc(v_size_688_);
v_isSharedCheck_765_ = !lean_is_exclusive(v_r_504_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; lean_object* v_unused_767_; lean_object* v_unused_768_; lean_object* v_unused_769_; lean_object* v_unused_770_; 
v_unused_766_ = lean_ctor_get(v_r_504_, 4);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_r_504_, 3);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_r_504_, 2);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_r_504_, 1);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_r_504_, 0);
lean_dec(v_unused_770_);
v___x_712_ = v_r_504_;
v_isShared_713_ = v_isSharedCheck_765_;
goto v_resetjp_711_;
}
else
{
lean_dec(v_r_504_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_765_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_size_714_; lean_object* v_k_715_; lean_object* v_v_716_; lean_object* v_l_717_; lean_object* v_r_718_; lean_object* v_size_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_size_714_ = lean_ctor_get(v_l_691_, 0);
v_k_715_ = lean_ctor_get(v_l_691_, 1);
v_v_716_ = lean_ctor_get(v_l_691_, 2);
v_l_717_ = lean_ctor_get(v_l_691_, 3);
v_r_718_ = lean_ctor_get(v_l_691_, 4);
v_size_719_ = lean_ctor_get(v_r_692_, 0);
v___x_720_ = lean_unsigned_to_nat(2u);
v___x_721_ = lean_nat_mul(v___x_720_, v_size_719_);
v___x_722_ = lean_nat_dec_lt(v_size_714_, v___x_721_);
lean_dec(v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_750_; 
lean_inc(v_r_718_);
lean_inc(v_l_717_);
lean_inc(v_v_716_);
lean_inc(v_k_715_);
v_isSharedCheck_750_ = !lean_is_exclusive(v_l_691_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; lean_object* v_unused_754_; lean_object* v_unused_755_; 
v_unused_751_ = lean_ctor_get(v_l_691_, 4);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_l_691_, 3);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_l_691_, 2);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_l_691_, 1);
lean_dec(v_unused_754_);
v_unused_755_ = lean_ctor_get(v_l_691_, 0);
lean_dec(v_unused_755_);
v___x_724_ = v_l_691_;
v_isShared_725_ = v_isSharedCheck_750_;
goto v_resetjp_723_;
}
else
{
lean_dec(v_l_691_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_750_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_740_; 
v___x_726_ = lean_nat_add(v___x_693_, v_size_702_);
v___x_727_ = lean_nat_add(v___x_726_, v_size_688_);
lean_dec(v_size_688_);
if (lean_obj_tag(v_l_717_) == 0)
{
lean_object* v_size_748_; 
v_size_748_ = lean_ctor_get(v_l_717_, 0);
lean_inc(v_size_748_);
v___y_740_ = v_size_748_;
goto v___jp_739_;
}
else
{
lean_object* v___x_749_; 
v___x_749_ = lean_unsigned_to_nat(0u);
v___y_740_ = v___x_749_;
goto v___jp_739_;
}
v___jp_728_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = lean_nat_add(v___y_729_, v___y_731_);
lean_dec(v___y_731_);
lean_dec(v___y_729_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 4, v_r_692_);
lean_ctor_set(v___x_724_, 3, v_r_718_);
lean_ctor_set(v___x_724_, 2, v_v_690_);
lean_ctor_set(v___x_724_, 1, v_k_689_);
lean_ctor_set(v___x_724_, 0, v___x_732_);
v___x_734_ = v___x_724_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_k_689_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_v_690_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_r_718_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v_r_692_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_736_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 4, v___x_734_);
lean_ctor_set(v___x_712_, 3, v___y_730_);
lean_ctor_set(v___x_712_, 2, v_v_716_);
lean_ctor_set(v___x_712_, 1, v_k_715_);
lean_ctor_set(v___x_712_, 0, v___x_727_);
v___x_736_ = v___x_712_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_k_715_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_v_716_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v___y_730_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
v___jp_739_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = lean_nat_add(v___x_726_, v___y_740_);
lean_dec(v___y_740_);
lean_dec(v___x_726_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 4, v_l_717_);
lean_ctor_set(v___x_696_, 3, v_tree_699_);
lean_ctor_set(v___x_696_, 2, v_v_701_);
lean_ctor_set(v___x_696_, 1, v_k_700_);
lean_ctor_set(v___x_696_, 0, v___x_741_);
v___x_743_ = v___x_696_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_k_700_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_v_701_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_tree_699_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_l_717_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; 
v___x_744_ = lean_nat_add(v___x_693_, v_size_719_);
if (lean_obj_tag(v_r_718_) == 0)
{
lean_object* v_size_745_; 
v_size_745_ = lean_ctor_get(v_r_718_, 0);
lean_inc(v_size_745_);
v___y_729_ = v___x_744_;
v___y_730_ = v___x_743_;
v___y_731_ = v_size_745_;
goto v___jp_728_;
}
else
{
lean_object* v___x_746_; 
v___x_746_ = lean_unsigned_to_nat(0u);
v___y_729_ = v___x_744_;
v___y_730_ = v___x_743_;
v___y_731_ = v___x_746_;
goto v___jp_728_;
}
}
}
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_756_ = lean_nat_add(v___x_693_, v_size_702_);
v___x_757_ = lean_nat_add(v___x_756_, v_size_688_);
lean_dec(v_size_688_);
v___x_758_ = lean_nat_add(v___x_756_, v_size_714_);
lean_dec(v___x_756_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 4, v_l_691_);
lean_ctor_set(v___x_712_, 3, v_tree_699_);
lean_ctor_set(v___x_712_, 2, v_v_701_);
lean_ctor_set(v___x_712_, 1, v_k_700_);
lean_ctor_set(v___x_712_, 0, v___x_758_);
v___x_760_ = v___x_712_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_k_700_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_v_701_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_tree_699_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_l_691_);
v___x_760_ = v_reuseFailAlloc_764_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 4, v_r_692_);
lean_ctor_set(v___x_696_, 3, v___x_760_);
lean_ctor_set(v___x_696_, 2, v_v_690_);
lean_ctor_set(v___x_696_, 1, v_k_689_);
lean_ctor_set(v___x_696_, 0, v___x_757_);
v___x_762_ = v___x_696_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_k_689_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_v_690_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_r_692_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
else
{
lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_824_; 
lean_inc(v_r_692_);
lean_inc(v_v_690_);
lean_inc(v_k_689_);
lean_inc(v_size_688_);
v_isSharedCheck_824_ = !lean_is_exclusive(v_r_504_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; lean_object* v_unused_826_; lean_object* v_unused_827_; lean_object* v_unused_828_; lean_object* v_unused_829_; 
v_unused_825_ = lean_ctor_get(v_r_504_, 4);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_r_504_, 3);
lean_dec(v_unused_826_);
v_unused_827_ = lean_ctor_get(v_r_504_, 2);
lean_dec(v_unused_827_);
v_unused_828_ = lean_ctor_get(v_r_504_, 1);
lean_dec(v_unused_828_);
v_unused_829_ = lean_ctor_get(v_r_504_, 0);
lean_dec(v_unused_829_);
v___x_772_ = v_r_504_;
v_isShared_773_ = v_isSharedCheck_824_;
goto v_resetjp_771_;
}
else
{
lean_dec(v_r_504_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_824_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
if (lean_obj_tag(v_l_691_) == 0)
{
if (lean_obj_tag(v_r_692_) == 0)
{
lean_object* v_k_774_; lean_object* v_v_775_; lean_object* v_size_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v_k_774_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_k_774_);
v_v_775_ = lean_ctor_get(v___x_698_, 1);
lean_inc(v_v_775_);
lean_dec_ref(v___x_698_);
v_size_776_ = lean_ctor_get(v_l_691_, 0);
v___x_777_ = lean_nat_add(v___x_693_, v_size_688_);
lean_dec(v_size_688_);
v___x_778_ = lean_nat_add(v___x_693_, v_size_776_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v_l_691_);
lean_ctor_set(v___x_772_, 3, v_tree_699_);
lean_ctor_set(v___x_772_, 2, v_v_775_);
lean_ctor_set(v___x_772_, 1, v_k_774_);
lean_ctor_set(v___x_772_, 0, v___x_778_);
v___x_780_ = v___x_772_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_k_774_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_v_775_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_tree_699_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_l_691_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 4, v_r_692_);
lean_ctor_set(v___x_696_, 3, v___x_780_);
lean_ctor_set(v___x_696_, 2, v_v_690_);
lean_ctor_set(v___x_696_, 1, v_k_689_);
lean_ctor_set(v___x_696_, 0, v___x_777_);
v___x_782_ = v___x_696_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_k_689_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_v_690_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_r_692_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
else
{
lean_object* v_k_785_; lean_object* v_v_786_; lean_object* v_k_787_; lean_object* v_v_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_802_; 
lean_dec(v_size_688_);
v_k_785_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_k_785_);
v_v_786_ = lean_ctor_get(v___x_698_, 1);
lean_inc(v_v_786_);
lean_dec_ref(v___x_698_);
v_k_787_ = lean_ctor_get(v_l_691_, 1);
v_v_788_ = lean_ctor_get(v_l_691_, 2);
v_isSharedCheck_802_ = !lean_is_exclusive(v_l_691_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; lean_object* v_unused_804_; lean_object* v_unused_805_; 
v_unused_803_ = lean_ctor_get(v_l_691_, 4);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_l_691_, 3);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_l_691_, 0);
lean_dec(v_unused_805_);
v___x_790_ = v_l_691_;
v_isShared_791_ = v_isSharedCheck_802_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_v_788_);
lean_inc(v_k_787_);
lean_dec(v_l_691_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_802_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_unsigned_to_nat(3u);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 4, v_r_692_);
lean_ctor_set(v___x_790_, 3, v_r_692_);
lean_ctor_set(v___x_790_, 2, v_v_786_);
lean_ctor_set(v___x_790_, 1, v_k_785_);
lean_ctor_set(v___x_790_, 0, v___x_693_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_k_785_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_v_786_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_r_692_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v_r_692_);
v___x_794_ = v_reuseFailAlloc_801_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_796_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 3, v_r_692_);
lean_ctor_set(v___x_772_, 0, v___x_693_);
v___x_796_ = v___x_772_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_k_689_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v_v_690_);
lean_ctor_set(v_reuseFailAlloc_800_, 3, v_r_692_);
lean_ctor_set(v_reuseFailAlloc_800_, 4, v_r_692_);
v___x_796_ = v_reuseFailAlloc_800_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_798_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 4, v___x_796_);
lean_ctor_set(v___x_696_, 3, v___x_794_);
lean_ctor_set(v___x_696_, 2, v_v_788_);
lean_ctor_set(v___x_696_, 1, v_k_787_);
lean_ctor_set(v___x_696_, 0, v___x_792_);
v___x_798_ = v___x_696_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_k_787_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v_v_788_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_692_) == 0)
{
lean_object* v_k_806_; lean_object* v_v_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
lean_dec(v_size_688_);
v_k_806_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_k_806_);
v_v_807_ = lean_ctor_get(v___x_698_, 1);
lean_inc(v_v_807_);
lean_dec_ref(v___x_698_);
v___x_808_ = lean_unsigned_to_nat(3u);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v_l_691_);
lean_ctor_set(v___x_772_, 2, v_v_807_);
lean_ctor_set(v___x_772_, 1, v_k_806_);
lean_ctor_set(v___x_772_, 0, v___x_693_);
v___x_810_ = v___x_772_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_k_806_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_v_807_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_l_691_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_l_691_);
v___x_810_ = v_reuseFailAlloc_814_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_812_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 4, v_r_692_);
lean_ctor_set(v___x_696_, 3, v___x_810_);
lean_ctor_set(v___x_696_, 2, v_v_690_);
lean_ctor_set(v___x_696_, 1, v_k_689_);
lean_ctor_set(v___x_696_, 0, v___x_808_);
v___x_812_ = v___x_696_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_k_689_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_v_690_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_r_692_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
else
{
lean_object* v_k_815_; lean_object* v_v_816_; lean_object* v___x_818_; 
v_k_815_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_k_815_);
v_v_816_ = lean_ctor_get(v___x_698_, 1);
lean_inc(v_v_816_);
lean_dec_ref(v___x_698_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 3, v_r_692_);
v___x_818_ = v___x_772_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_size_688_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_k_689_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_v_690_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v_r_692_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v_r_692_);
v___x_818_ = v_reuseFailAlloc_823_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = lean_unsigned_to_nat(2u);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 4, v___x_818_);
lean_ctor_set(v___x_696_, 3, v_r_692_);
lean_ctor_set(v___x_696_, 2, v_v_816_);
lean_ctor_set(v___x_696_, 1, v_k_815_);
lean_ctor_set(v___x_696_, 0, v___x_819_);
v___x_821_ = v___x_696_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_k_815_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_v_816_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_r_692_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v___x_818_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
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
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_988_; 
lean_inc(v_r_692_);
lean_inc(v_v_690_);
lean_inc(v_k_689_);
v_isSharedCheck_988_ = !lean_is_exclusive(v_r_504_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; lean_object* v_unused_990_; lean_object* v_unused_991_; lean_object* v_unused_992_; lean_object* v_unused_993_; 
v_unused_989_ = lean_ctor_get(v_r_504_, 4);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_r_504_, 3);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v_r_504_, 2);
lean_dec(v_unused_991_);
v_unused_992_ = lean_ctor_get(v_r_504_, 1);
lean_dec(v_unused_992_);
v_unused_993_ = lean_ctor_get(v_r_504_, 0);
lean_dec(v_unused_993_);
v___x_837_ = v_r_504_;
v_isShared_838_ = v_isSharedCheck_988_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_r_504_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_988_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v_tree_840_; 
v___x_839_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_689_, v_v_690_, v_l_691_, v_r_692_);
v_tree_840_ = lean_ctor_get(v___x_839_, 2);
lean_inc(v_tree_840_);
if (lean_obj_tag(v_tree_840_) == 0)
{
lean_object* v_k_841_; lean_object* v_v_842_; lean_object* v_size_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_k_841_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_k_841_);
v_v_842_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_v_842_);
lean_dec_ref(v___x_839_);
v_size_843_ = lean_ctor_get(v_tree_840_, 0);
v___x_844_ = lean_unsigned_to_nat(3u);
v___x_845_ = lean_nat_mul(v___x_844_, v_size_843_);
v___x_846_ = lean_nat_dec_lt(v___x_845_, v_size_683_);
lean_dec(v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
lean_dec(v_r_687_);
v___x_847_ = lean_nat_add(v___x_693_, v_size_683_);
v___x_848_ = lean_nat_add(v___x_847_, v_size_843_);
lean_dec(v___x_847_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 4, v_tree_840_);
lean_ctor_set(v___x_837_, 3, v_l_503_);
lean_ctor_set(v___x_837_, 2, v_v_842_);
lean_ctor_set(v___x_837_, 1, v_k_841_);
lean_ctor_set(v___x_837_, 0, v___x_848_);
v___x_850_ = v___x_837_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_k_841_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_v_842_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_l_503_);
lean_ctor_set(v_reuseFailAlloc_851_, 4, v_tree_840_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
else
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_917_; 
lean_inc(v_l_686_);
lean_inc(v_v_685_);
lean_inc(v_k_684_);
lean_inc(v_size_683_);
v_isSharedCheck_917_ = !lean_is_exclusive(v_l_503_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; lean_object* v_unused_919_; lean_object* v_unused_920_; lean_object* v_unused_921_; lean_object* v_unused_922_; 
v_unused_918_ = lean_ctor_get(v_l_503_, 4);
lean_dec(v_unused_918_);
v_unused_919_ = lean_ctor_get(v_l_503_, 3);
lean_dec(v_unused_919_);
v_unused_920_ = lean_ctor_get(v_l_503_, 2);
lean_dec(v_unused_920_);
v_unused_921_ = lean_ctor_get(v_l_503_, 1);
lean_dec(v_unused_921_);
v_unused_922_ = lean_ctor_get(v_l_503_, 0);
lean_dec(v_unused_922_);
v___x_853_ = v_l_503_;
v_isShared_854_ = v_isSharedCheck_917_;
goto v_resetjp_852_;
}
else
{
lean_dec(v_l_503_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_917_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v_size_855_; lean_object* v_size_856_; lean_object* v_k_857_; lean_object* v_v_858_; lean_object* v_l_859_; lean_object* v_r_860_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_size_855_ = lean_ctor_get(v_l_686_, 0);
v_size_856_ = lean_ctor_get(v_r_687_, 0);
v_k_857_ = lean_ctor_get(v_r_687_, 1);
v_v_858_ = lean_ctor_get(v_r_687_, 2);
v_l_859_ = lean_ctor_get(v_r_687_, 3);
v_r_860_ = lean_ctor_get(v_r_687_, 4);
v___x_861_ = lean_unsigned_to_nat(2u);
v___x_862_ = lean_nat_mul(v___x_861_, v_size_855_);
v___x_863_ = lean_nat_dec_lt(v_size_856_, v___x_862_);
lean_dec(v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_901_; 
lean_inc(v_r_860_);
lean_inc(v_l_859_);
lean_inc(v_v_858_);
lean_inc(v_k_857_);
lean_del_object(v___x_853_);
v_isSharedCheck_901_ = !lean_is_exclusive(v_r_687_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; lean_object* v_unused_903_; lean_object* v_unused_904_; lean_object* v_unused_905_; lean_object* v_unused_906_; 
v_unused_902_ = lean_ctor_get(v_r_687_, 4);
lean_dec(v_unused_902_);
v_unused_903_ = lean_ctor_get(v_r_687_, 3);
lean_dec(v_unused_903_);
v_unused_904_ = lean_ctor_get(v_r_687_, 2);
lean_dec(v_unused_904_);
v_unused_905_ = lean_ctor_get(v_r_687_, 1);
lean_dec(v_unused_905_);
v_unused_906_ = lean_ctor_get(v_r_687_, 0);
lean_dec(v_unused_906_);
v___x_865_ = v_r_687_;
v_isShared_866_ = v_isSharedCheck_901_;
goto v_resetjp_864_;
}
else
{
lean_dec(v_r_687_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_901_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___x_889_; lean_object* v___y_891_; 
v___x_867_ = lean_nat_add(v___x_693_, v_size_683_);
lean_dec(v_size_683_);
v___x_868_ = lean_nat_add(v___x_867_, v_size_843_);
lean_dec(v___x_867_);
v___x_889_ = lean_nat_add(v___x_693_, v_size_855_);
if (lean_obj_tag(v_l_859_) == 0)
{
lean_object* v_size_899_; 
v_size_899_ = lean_ctor_get(v_l_859_, 0);
lean_inc(v_size_899_);
v___y_891_ = v_size_899_;
goto v___jp_890_;
}
else
{
lean_object* v___x_900_; 
v___x_900_ = lean_unsigned_to_nat(0u);
v___y_891_ = v___x_900_;
goto v___jp_890_;
}
v___jp_869_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = lean_nat_add(v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec(v___y_871_);
lean_inc_ref(v_tree_840_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 4, v_tree_840_);
lean_ctor_set(v___x_865_, 3, v_r_860_);
lean_ctor_set(v___x_865_, 2, v_v_842_);
lean_ctor_set(v___x_865_, 1, v_k_841_);
lean_ctor_set(v___x_865_, 0, v___x_873_);
v___x_875_ = v___x_865_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_841_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_v_842_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_r_860_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_tree_840_);
v___x_875_ = v_reuseFailAlloc_888_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_isSharedCheck_882_ = !lean_is_exclusive(v_tree_840_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; lean_object* v_unused_884_; lean_object* v_unused_885_; lean_object* v_unused_886_; lean_object* v_unused_887_; 
v_unused_883_ = lean_ctor_get(v_tree_840_, 4);
lean_dec(v_unused_883_);
v_unused_884_ = lean_ctor_get(v_tree_840_, 3);
lean_dec(v_unused_884_);
v_unused_885_ = lean_ctor_get(v_tree_840_, 2);
lean_dec(v_unused_885_);
v_unused_886_ = lean_ctor_get(v_tree_840_, 1);
lean_dec(v_unused_886_);
v_unused_887_ = lean_ctor_get(v_tree_840_, 0);
lean_dec(v_unused_887_);
v___x_877_ = v_tree_840_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_dec(v_tree_840_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 4, v___x_875_);
lean_ctor_set(v___x_877_, 3, v___y_870_);
lean_ctor_set(v___x_877_, 2, v_v_858_);
lean_ctor_set(v___x_877_, 1, v_k_857_);
lean_ctor_set(v___x_877_, 0, v___x_868_);
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_k_857_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_v_858_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v___y_870_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v___x_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
v___jp_890_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_nat_add(v___x_889_, v___y_891_);
lean_dec(v___y_891_);
lean_dec(v___x_889_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 4, v_l_859_);
lean_ctor_set(v___x_837_, 3, v_l_686_);
lean_ctor_set(v___x_837_, 2, v_v_685_);
lean_ctor_set(v___x_837_, 1, v_k_684_);
lean_ctor_set(v___x_837_, 0, v___x_892_);
v___x_894_ = v___x_837_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_k_684_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_v_685_);
lean_ctor_set(v_reuseFailAlloc_898_, 3, v_l_686_);
lean_ctor_set(v_reuseFailAlloc_898_, 4, v_l_859_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; 
v___x_895_ = lean_nat_add(v___x_693_, v_size_843_);
if (lean_obj_tag(v_r_860_) == 0)
{
lean_object* v_size_896_; 
v_size_896_ = lean_ctor_get(v_r_860_, 0);
lean_inc(v_size_896_);
v___y_870_ = v___x_894_;
v___y_871_ = v___x_895_;
v___y_872_ = v_size_896_;
goto v___jp_869_;
}
else
{
lean_object* v___x_897_; 
v___x_897_ = lean_unsigned_to_nat(0u);
v___y_870_ = v___x_894_;
v___y_871_ = v___x_895_;
v___y_872_ = v___x_897_;
goto v___jp_869_;
}
}
}
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_907_ = lean_nat_add(v___x_693_, v_size_683_);
lean_dec(v_size_683_);
v___x_908_ = lean_nat_add(v___x_907_, v_size_843_);
lean_dec(v___x_907_);
v___x_909_ = lean_nat_add(v___x_693_, v_size_843_);
v___x_910_ = lean_nat_add(v___x_909_, v_size_856_);
lean_dec(v___x_909_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 4, v_tree_840_);
lean_ctor_set(v___x_837_, 3, v_r_687_);
lean_ctor_set(v___x_837_, 2, v_v_842_);
lean_ctor_set(v___x_837_, 1, v_k_841_);
lean_ctor_set(v___x_837_, 0, v___x_910_);
v___x_912_ = v___x_837_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_k_841_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_v_842_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_r_687_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_tree_840_);
v___x_912_ = v_reuseFailAlloc_916_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 4, v___x_912_);
lean_ctor_set(v___x_853_, 0, v___x_908_);
v___x_914_ = v___x_853_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_k_684_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_v_685_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_l_686_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_686_) == 0)
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_946_; 
lean_inc_ref(v_l_686_);
lean_inc(v_v_685_);
lean_inc(v_k_684_);
lean_inc(v_size_683_);
v_isSharedCheck_946_ = !lean_is_exclusive(v_l_503_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; lean_object* v_unused_948_; lean_object* v_unused_949_; lean_object* v_unused_950_; lean_object* v_unused_951_; 
v_unused_947_ = lean_ctor_get(v_l_503_, 4);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_l_503_, 3);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_l_503_, 2);
lean_dec(v_unused_949_);
v_unused_950_ = lean_ctor_get(v_l_503_, 1);
lean_dec(v_unused_950_);
v_unused_951_ = lean_ctor_get(v_l_503_, 0);
lean_dec(v_unused_951_);
v___x_924_ = v_l_503_;
v_isShared_925_ = v_isSharedCheck_946_;
goto v_resetjp_923_;
}
else
{
lean_dec(v_l_503_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_946_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
if (lean_obj_tag(v_r_687_) == 0)
{
lean_object* v_k_926_; lean_object* v_v_927_; lean_object* v_size_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v_k_926_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_k_926_);
v_v_927_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_v_927_);
lean_dec_ref(v___x_839_);
v_size_928_ = lean_ctor_get(v_r_687_, 0);
v___x_929_ = lean_nat_add(v___x_693_, v_size_683_);
lean_dec(v_size_683_);
v___x_930_ = lean_nat_add(v___x_693_, v_size_928_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 4, v_tree_840_);
lean_ctor_set(v___x_837_, 3, v_r_687_);
lean_ctor_set(v___x_837_, 2, v_v_927_);
lean_ctor_set(v___x_837_, 1, v_k_926_);
lean_ctor_set(v___x_837_, 0, v___x_930_);
v___x_932_ = v___x_837_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v_r_687_);
lean_ctor_set(v_reuseFailAlloc_936_, 4, v_tree_840_);
v___x_932_ = v_reuseFailAlloc_936_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_934_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 4, v___x_932_);
lean_ctor_set(v___x_924_, 0, v___x_929_);
v___x_934_ = v___x_924_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_k_684_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_v_685_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v_l_686_);
lean_ctor_set(v_reuseFailAlloc_935_, 4, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
else
{
lean_object* v_k_937_; lean_object* v_v_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
lean_dec(v_size_683_);
v_k_937_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_k_937_);
v_v_938_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_v_938_);
lean_dec_ref(v___x_839_);
v___x_939_ = lean_unsigned_to_nat(3u);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 4, v_r_687_);
lean_ctor_set(v___x_837_, 3, v_r_687_);
lean_ctor_set(v___x_837_, 2, v_v_938_);
lean_ctor_set(v___x_837_, 1, v_k_937_);
lean_ctor_set(v___x_837_, 0, v___x_693_);
v___x_941_ = v___x_837_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_k_937_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_v_938_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_r_687_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_r_687_);
v___x_941_ = v_reuseFailAlloc_945_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 4, v___x_941_);
lean_ctor_set(v___x_924_, 0, v___x_939_);
v___x_943_ = v___x_924_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_k_684_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_v_685_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v_l_686_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_687_) == 0)
{
lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_976_; 
lean_inc(v_l_686_);
lean_inc(v_v_685_);
lean_inc(v_k_684_);
v_isSharedCheck_976_ = !lean_is_exclusive(v_l_503_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; 
v_unused_977_ = lean_ctor_get(v_l_503_, 4);
lean_dec(v_unused_977_);
v_unused_978_ = lean_ctor_get(v_l_503_, 3);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_l_503_, 2);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_l_503_, 1);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_l_503_, 0);
lean_dec(v_unused_981_);
v___x_953_ = v_l_503_;
v_isShared_954_ = v_isSharedCheck_976_;
goto v_resetjp_952_;
}
else
{
lean_dec(v_l_503_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_976_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_k_955_; lean_object* v_v_956_; lean_object* v_k_957_; lean_object* v_v_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_972_; 
v_k_955_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_k_955_);
v_v_956_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_v_956_);
lean_dec_ref(v___x_839_);
v_k_957_ = lean_ctor_get(v_r_687_, 1);
v_v_958_ = lean_ctor_get(v_r_687_, 2);
v_isSharedCheck_972_ = !lean_is_exclusive(v_r_687_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; lean_object* v_unused_974_; lean_object* v_unused_975_; 
v_unused_973_ = lean_ctor_get(v_r_687_, 4);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_r_687_, 3);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_r_687_, 0);
lean_dec(v_unused_975_);
v___x_960_ = v_r_687_;
v_isShared_961_ = v_isSharedCheck_972_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_v_958_);
lean_inc(v_k_957_);
lean_dec(v_r_687_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_972_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = lean_unsigned_to_nat(3u);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 4, v_l_686_);
lean_ctor_set(v___x_960_, 3, v_l_686_);
lean_ctor_set(v___x_960_, 2, v_v_685_);
lean_ctor_set(v___x_960_, 1, v_k_684_);
lean_ctor_set(v___x_960_, 0, v___x_693_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_k_684_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_v_685_);
lean_ctor_set(v_reuseFailAlloc_971_, 3, v_l_686_);
lean_ctor_set(v_reuseFailAlloc_971_, 4, v_l_686_);
v___x_964_ = v_reuseFailAlloc_971_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_966_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 4, v_l_686_);
lean_ctor_set(v___x_837_, 3, v_l_686_);
lean_ctor_set(v___x_837_, 2, v_v_956_);
lean_ctor_set(v___x_837_, 1, v_k_955_);
lean_ctor_set(v___x_837_, 0, v___x_693_);
v___x_966_ = v___x_837_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_k_955_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_v_956_);
lean_ctor_set(v_reuseFailAlloc_970_, 3, v_l_686_);
lean_ctor_set(v_reuseFailAlloc_970_, 4, v_l_686_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 4, v___x_966_);
lean_ctor_set(v___x_953_, 3, v___x_964_);
lean_ctor_set(v___x_953_, 2, v_v_958_);
lean_ctor_set(v___x_953_, 1, v_k_957_);
lean_ctor_set(v___x_953_, 0, v___x_962_);
v___x_968_ = v___x_953_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_k_957_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_v_958_);
lean_ctor_set(v_reuseFailAlloc_969_, 3, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_969_, 4, v___x_966_);
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
else
{
lean_object* v_k_982_; lean_object* v_v_983_; lean_object* v___x_984_; lean_object* v___x_986_; 
v_k_982_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_k_982_);
v_v_983_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_v_983_);
lean_dec_ref(v___x_839_);
v___x_984_ = lean_unsigned_to_nat(2u);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 4, v_r_687_);
lean_ctor_set(v___x_837_, 3, v_l_503_);
lean_ctor_set(v___x_837_, 2, v_v_983_);
lean_ctor_set(v___x_837_, 1, v_k_982_);
lean_ctor_set(v___x_837_, 0, v___x_984_);
v___x_986_ = v___x_837_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_k_982_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_v_983_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_l_503_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v_r_687_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
}
else
{
return v_l_503_;
}
}
else
{
return v_r_504_;
}
}
default: 
{
lean_object* v_impl_994_; lean_object* v___x_995_; 
v_impl_994_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_499_, v_r_504_);
v___x_995_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_994_) == 0)
{
if (lean_obj_tag(v_l_503_) == 0)
{
lean_object* v_size_996_; lean_object* v_size_997_; lean_object* v_k_998_; lean_object* v_v_999_; lean_object* v_l_1000_; lean_object* v_r_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_size_996_ = lean_ctor_get(v_impl_994_, 0);
lean_inc(v_size_996_);
v_size_997_ = lean_ctor_get(v_l_503_, 0);
v_k_998_ = lean_ctor_get(v_l_503_, 1);
v_v_999_ = lean_ctor_get(v_l_503_, 2);
v_l_1000_ = lean_ctor_get(v_l_503_, 3);
v_r_1001_ = lean_ctor_get(v_l_503_, 4);
lean_inc(v_r_1001_);
v___x_1002_ = lean_unsigned_to_nat(3u);
v___x_1003_ = lean_nat_mul(v___x_1002_, v_size_996_);
v___x_1004_ = lean_nat_dec_lt(v___x_1003_, v_size_997_);
lean_dec(v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
lean_dec(v_r_1001_);
v___x_1005_ = lean_nat_add(v___x_995_, v_size_997_);
v___x_1006_ = lean_nat_add(v___x_1005_, v_size_996_);
lean_dec(v_size_996_);
lean_dec(v___x_1005_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v_impl_994_);
lean_ctor_set(v___x_506_, 0, v___x_1006_);
v___x_1008_ = v___x_506_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v_l_503_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v_impl_994_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
else
{
lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1075_; 
lean_inc(v_l_1000_);
lean_inc(v_v_999_);
lean_inc(v_k_998_);
lean_inc(v_size_997_);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_l_503_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; lean_object* v_unused_1077_; lean_object* v_unused_1078_; lean_object* v_unused_1079_; lean_object* v_unused_1080_; 
v_unused_1076_ = lean_ctor_get(v_l_503_, 4);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_l_503_, 3);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_l_503_, 2);
lean_dec(v_unused_1078_);
v_unused_1079_ = lean_ctor_get(v_l_503_, 1);
lean_dec(v_unused_1079_);
v_unused_1080_ = lean_ctor_get(v_l_503_, 0);
lean_dec(v_unused_1080_);
v___x_1011_ = v_l_503_;
v_isShared_1012_ = v_isSharedCheck_1075_;
goto v_resetjp_1010_;
}
else
{
lean_dec(v_l_503_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1075_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v_size_1013_; lean_object* v_size_1014_; lean_object* v_k_1015_; lean_object* v_v_1016_; lean_object* v_l_1017_; lean_object* v_r_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v_size_1013_ = lean_ctor_get(v_l_1000_, 0);
v_size_1014_ = lean_ctor_get(v_r_1001_, 0);
v_k_1015_ = lean_ctor_get(v_r_1001_, 1);
v_v_1016_ = lean_ctor_get(v_r_1001_, 2);
v_l_1017_ = lean_ctor_get(v_r_1001_, 3);
v_r_1018_ = lean_ctor_get(v_r_1001_, 4);
v___x_1019_ = lean_unsigned_to_nat(2u);
v___x_1020_ = lean_nat_mul(v___x_1019_, v_size_1013_);
v___x_1021_ = lean_nat_dec_lt(v_size_1014_, v___x_1020_);
lean_dec(v___x_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1050_; 
lean_inc(v_r_1018_);
lean_inc(v_l_1017_);
lean_inc(v_v_1016_);
lean_inc(v_k_1015_);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_r_1001_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; lean_object* v_unused_1052_; lean_object* v_unused_1053_; lean_object* v_unused_1054_; lean_object* v_unused_1055_; 
v_unused_1051_ = lean_ctor_get(v_r_1001_, 4);
lean_dec(v_unused_1051_);
v_unused_1052_ = lean_ctor_get(v_r_1001_, 3);
lean_dec(v_unused_1052_);
v_unused_1053_ = lean_ctor_get(v_r_1001_, 2);
lean_dec(v_unused_1053_);
v_unused_1054_ = lean_ctor_get(v_r_1001_, 1);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v_r_1001_, 0);
lean_dec(v_unused_1055_);
v___x_1023_ = v_r_1001_;
v_isShared_1024_ = v_isSharedCheck_1050_;
goto v_resetjp_1022_;
}
else
{
lean_dec(v_r_1001_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1050_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___x_1038_; lean_object* v___y_1040_; 
v___x_1025_ = lean_nat_add(v___x_995_, v_size_997_);
lean_dec(v_size_997_);
v___x_1026_ = lean_nat_add(v___x_1025_, v_size_996_);
lean_dec(v___x_1025_);
v___x_1038_ = lean_nat_add(v___x_995_, v_size_1013_);
if (lean_obj_tag(v_l_1017_) == 0)
{
lean_object* v_size_1048_; 
v_size_1048_ = lean_ctor_get(v_l_1017_, 0);
lean_inc(v_size_1048_);
v___y_1040_ = v_size_1048_;
goto v___jp_1039_;
}
else
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_unsigned_to_nat(0u);
v___y_1040_ = v___x_1049_;
goto v___jp_1039_;
}
v___jp_1027_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_nat_add(v___y_1028_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec(v___y_1028_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 4, v_impl_994_);
lean_ctor_set(v___x_1023_, 3, v_r_1018_);
lean_ctor_set(v___x_1023_, 2, v_v_502_);
lean_ctor_set(v___x_1023_, 1, v_k_501_);
lean_ctor_set(v___x_1023_, 0, v___x_1031_);
v___x_1033_ = v___x_1023_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_1037_, 3, v_r_1018_);
lean_ctor_set(v_reuseFailAlloc_1037_, 4, v_impl_994_);
v___x_1033_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 4, v___x_1033_);
lean_ctor_set(v___x_1011_, 3, v___y_1029_);
lean_ctor_set(v___x_1011_, 2, v_v_1016_);
lean_ctor_set(v___x_1011_, 1, v_k_1015_);
lean_ctor_set(v___x_1011_, 0, v___x_1026_);
v___x_1035_ = v___x_1011_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_k_1015_);
lean_ctor_set(v_reuseFailAlloc_1036_, 2, v_v_1016_);
lean_ctor_set(v_reuseFailAlloc_1036_, 3, v___y_1029_);
lean_ctor_set(v_reuseFailAlloc_1036_, 4, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
v___jp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1041_ = lean_nat_add(v___x_1038_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec(v___x_1038_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v_l_1017_);
lean_ctor_set(v___x_506_, 3, v_l_1000_);
lean_ctor_set(v___x_506_, 2, v_v_999_);
lean_ctor_set(v___x_506_, 1, v_k_998_);
lean_ctor_set(v___x_506_, 0, v___x_1041_);
v___x_1043_ = v___x_506_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_k_998_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_v_999_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_l_1000_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v_l_1017_);
v___x_1043_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_nat_add(v___x_995_, v_size_996_);
lean_dec(v_size_996_);
if (lean_obj_tag(v_r_1018_) == 0)
{
lean_object* v_size_1045_; 
v_size_1045_ = lean_ctor_get(v_r_1018_, 0);
lean_inc(v_size_1045_);
v___y_1028_ = v___x_1044_;
v___y_1029_ = v___x_1043_;
v___y_1030_ = v_size_1045_;
goto v___jp_1027_;
}
else
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_unsigned_to_nat(0u);
v___y_1028_ = v___x_1044_;
v___y_1029_ = v___x_1043_;
v___y_1030_ = v___x_1046_;
goto v___jp_1027_;
}
}
}
}
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_del_object(v___x_506_);
v___x_1056_ = lean_nat_add(v___x_995_, v_size_997_);
lean_dec(v_size_997_);
v___x_1057_ = lean_nat_add(v___x_1056_, v_size_996_);
lean_dec(v___x_1056_);
v___x_1058_ = lean_nat_add(v___x_995_, v_size_996_);
lean_dec(v_size_996_);
v___x_1059_ = lean_nat_add(v___x_1058_, v_size_1014_);
lean_dec(v___x_1058_);
lean_inc_ref(v_impl_994_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 4, v_impl_994_);
lean_ctor_set(v___x_1011_, 3, v_r_1001_);
lean_ctor_set(v___x_1011_, 2, v_v_502_);
lean_ctor_set(v___x_1011_, 1, v_k_501_);
lean_ctor_set(v___x_1011_, 0, v___x_1059_);
v___x_1061_ = v___x_1011_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_r_1001_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v_impl_994_);
v___x_1061_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
v_isSharedCheck_1068_ = !lean_is_exclusive(v_impl_994_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; lean_object* v_unused_1070_; lean_object* v_unused_1071_; lean_object* v_unused_1072_; lean_object* v_unused_1073_; 
v_unused_1069_ = lean_ctor_get(v_impl_994_, 4);
lean_dec(v_unused_1069_);
v_unused_1070_ = lean_ctor_get(v_impl_994_, 3);
lean_dec(v_unused_1070_);
v_unused_1071_ = lean_ctor_get(v_impl_994_, 2);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_impl_994_, 1);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_impl_994_, 0);
lean_dec(v_unused_1073_);
v___x_1063_ = v_impl_994_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_dec(v_impl_994_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 4, v___x_1061_);
lean_ctor_set(v___x_1063_, 3, v_l_1000_);
lean_ctor_set(v___x_1063_, 2, v_v_999_);
lean_ctor_set(v___x_1063_, 1, v_k_998_);
lean_ctor_set(v___x_1063_, 0, v___x_1057_);
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_k_998_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_v_999_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_l_1000_);
lean_ctor_set(v_reuseFailAlloc_1067_, 4, v___x_1061_);
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
}
}
}
else
{
lean_object* v_size_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v_size_1081_ = lean_ctor_get(v_impl_994_, 0);
lean_inc(v_size_1081_);
v___x_1082_ = lean_nat_add(v___x_995_, v_size_1081_);
lean_dec(v_size_1081_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v_impl_994_);
lean_ctor_set(v___x_506_, 0, v___x_1082_);
v___x_1084_ = v___x_506_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_l_503_);
lean_ctor_set(v_reuseFailAlloc_1085_, 4, v_impl_994_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
else
{
if (lean_obj_tag(v_l_503_) == 0)
{
lean_object* v_l_1086_; 
v_l_1086_ = lean_ctor_get(v_l_503_, 3);
if (lean_obj_tag(v_l_1086_) == 0)
{
lean_object* v_r_1087_; 
lean_inc_ref(v_l_1086_);
v_r_1087_ = lean_ctor_get(v_l_503_, 4);
lean_inc(v_r_1087_);
if (lean_obj_tag(v_r_1087_) == 0)
{
lean_object* v_size_1088_; lean_object* v_k_1089_; lean_object* v_v_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1103_; 
v_size_1088_ = lean_ctor_get(v_l_503_, 0);
v_k_1089_ = lean_ctor_get(v_l_503_, 1);
v_v_1090_ = lean_ctor_get(v_l_503_, 2);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_l_503_);
if (v_isSharedCheck_1103_ == 0)
{
lean_object* v_unused_1104_; lean_object* v_unused_1105_; 
v_unused_1104_ = lean_ctor_get(v_l_503_, 4);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_l_503_, 3);
lean_dec(v_unused_1105_);
v___x_1092_ = v_l_503_;
v_isShared_1093_ = v_isSharedCheck_1103_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_v_1090_);
lean_inc(v_k_1089_);
lean_inc(v_size_1088_);
lean_dec(v_l_503_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1103_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_size_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v_size_1094_ = lean_ctor_get(v_r_1087_, 0);
v___x_1095_ = lean_nat_add(v___x_995_, v_size_1088_);
lean_dec(v_size_1088_);
v___x_1096_ = lean_nat_add(v___x_995_, v_size_1094_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v_impl_994_);
lean_ctor_set(v___x_1092_, 3, v_r_1087_);
lean_ctor_set(v___x_1092_, 2, v_v_502_);
lean_ctor_set(v___x_1092_, 1, v_k_501_);
lean_ctor_set(v___x_1092_, 0, v___x_1096_);
v___x_1098_ = v___x_1092_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_1102_, 3, v_r_1087_);
lean_ctor_set(v_reuseFailAlloc_1102_, 4, v_impl_994_);
v___x_1098_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1100_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v___x_1098_);
lean_ctor_set(v___x_506_, 3, v_l_1086_);
lean_ctor_set(v___x_506_, 2, v_v_1090_);
lean_ctor_set(v___x_506_, 1, v_k_1089_);
lean_ctor_set(v___x_506_, 0, v___x_1095_);
v___x_1100_ = v___x_506_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1095_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1101_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1101_, 4, v___x_1098_);
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
else
{
lean_object* v_k_1106_; lean_object* v_v_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1118_; 
v_k_1106_ = lean_ctor_get(v_l_503_, 1);
v_v_1107_ = lean_ctor_get(v_l_503_, 2);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_l_503_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; lean_object* v_unused_1120_; lean_object* v_unused_1121_; 
v_unused_1119_ = lean_ctor_get(v_l_503_, 4);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_l_503_, 3);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_l_503_, 0);
lean_dec(v_unused_1121_);
v___x_1109_ = v_l_503_;
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_v_1107_);
lean_inc(v_k_1106_);
lean_dec(v_l_503_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = lean_unsigned_to_nat(3u);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 3, v_r_1087_);
lean_ctor_set(v___x_1109_, 2, v_v_502_);
lean_ctor_set(v___x_1109_, 1, v_k_501_);
lean_ctor_set(v___x_1109_, 0, v___x_995_);
v___x_1113_ = v___x_1109_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_r_1087_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v_r_1087_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1115_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v___x_1113_);
lean_ctor_set(v___x_506_, 3, v_l_1086_);
lean_ctor_set(v___x_506_, 2, v_v_1107_);
lean_ctor_set(v___x_506_, 1, v_k_1106_);
lean_ctor_set(v___x_506_, 0, v___x_1111_);
v___x_1115_ = v___x_506_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_k_1106_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_v_1107_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v___x_1113_);
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
else
{
lean_object* v_r_1122_; 
v_r_1122_ = lean_ctor_get(v_l_503_, 4);
lean_inc(v_r_1122_);
if (lean_obj_tag(v_r_1122_) == 0)
{
lean_object* v_k_1123_; lean_object* v_v_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1147_; 
lean_inc(v_l_1086_);
v_k_1123_ = lean_ctor_get(v_l_503_, 1);
v_v_1124_ = lean_ctor_get(v_l_503_, 2);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_l_503_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; lean_object* v_unused_1149_; lean_object* v_unused_1150_; 
v_unused_1148_ = lean_ctor_get(v_l_503_, 4);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_l_503_, 3);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_l_503_, 0);
lean_dec(v_unused_1150_);
v___x_1126_ = v_l_503_;
v_isShared_1127_ = v_isSharedCheck_1147_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_v_1124_);
lean_inc(v_k_1123_);
lean_dec(v_l_503_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1147_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_k_1128_; lean_object* v_v_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1143_; 
v_k_1128_ = lean_ctor_get(v_r_1122_, 1);
v_v_1129_ = lean_ctor_get(v_r_1122_, 2);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_r_1122_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; lean_object* v_unused_1145_; lean_object* v_unused_1146_; 
v_unused_1144_ = lean_ctor_get(v_r_1122_, 4);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_r_1122_, 3);
lean_dec(v_unused_1145_);
v_unused_1146_ = lean_ctor_get(v_r_1122_, 0);
lean_dec(v_unused_1146_);
v___x_1131_ = v_r_1122_;
v_isShared_1132_ = v_isSharedCheck_1143_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_v_1129_);
lean_inc(v_k_1128_);
lean_dec(v_r_1122_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1143_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_unsigned_to_nat(3u);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 4, v_l_1086_);
lean_ctor_set(v___x_1131_, 3, v_l_1086_);
lean_ctor_set(v___x_1131_, 2, v_v_1124_);
lean_ctor_set(v___x_1131_, 1, v_k_1123_);
lean_ctor_set(v___x_1131_, 0, v___x_995_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_k_1123_);
lean_ctor_set(v_reuseFailAlloc_1142_, 2, v_v_1124_);
lean_ctor_set(v_reuseFailAlloc_1142_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1142_, 4, v_l_1086_);
v___x_1135_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1137_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_l_1086_);
lean_ctor_set(v___x_1126_, 2, v_v_502_);
lean_ctor_set(v___x_1126_, 1, v_k_501_);
lean_ctor_set(v___x_1126_, 0, v___x_995_);
v___x_1137_ = v___x_1126_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_l_1086_);
v___x_1137_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1139_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v___x_1137_);
lean_ctor_set(v___x_506_, 3, v___x_1135_);
lean_ctor_set(v___x_506_, 2, v_v_1129_);
lean_ctor_set(v___x_506_, 1, v_k_1128_);
lean_ctor_set(v___x_506_, 0, v___x_1133_);
v___x_1139_ = v___x_506_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_k_1128_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_v_1129_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_unsigned_to_nat(2u);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v_r_1122_);
lean_ctor_set(v___x_506_, 0, v___x_1151_);
v___x_1153_ = v___x_506_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v_l_503_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v_r_1122_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_object* v___x_1156_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v_l_503_);
lean_ctor_set(v___x_506_, 0, v___x_995_);
v___x_1156_ = v___x_506_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_k_501_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_v_502_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_l_503_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_l_503_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
}
}
else
{
return v_t_500_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg___boxed(lean_object* v_k_1160_, lean_object* v_t_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1160_, v_t_1161_);
lean_dec(v_k_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString(lean_object* v_declName_1163_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1165_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1166_ = lean_st_ref_take(v___x_1165_);
v___x_1167_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_declName_1163_, v___x_1166_);
v___x_1168_ = lean_st_ref_set(v___x_1165_, v___x_1167_);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString___boxed(lean_object* v_declName_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_removeBuiltinDocString(v_declName_1170_);
lean_dec(v_declName_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(lean_object* v_00_u03b2_1173_, lean_object* v_k_1174_, lean_object* v_t_1175_, lean_object* v_h_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1174_, v_t_1175_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___boxed(lean_object* v_00_u03b2_1178_, lean_object* v_k_1179_, lean_object* v_t_1180_, lean_object* v_h_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(v_00_u03b2_1178_, v_k_1179_, v_t_1180_, v_h_1181_);
lean_dec(v_k_1179_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings(){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1185_ = lean_st_ref_get(v___x_1184_);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings___boxed(lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_getBuiltinVersoDocStrings();
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object* v_docString_1189_, lean_object* v_declName_1190_, lean_object* v_env_1191_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = l_Lean_docStringExt;
v___x_1193_ = l_String_removeLeadingSpaces(v_docString_1189_);
v___x_1194_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1192_, v_env_1191_, v_declName_1190_, v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_1195_, lean_object* v___f_1196_, lean_object* v_____r_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_apply_1(v_modifyEnv_1195_, v___f_1196_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__0));
v___x_1201_ = l_Lean_stringToMessageData(v___x_1200_);
return v___x_1201_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__2));
v___x_1204_ = l_Lean_stringToMessageData(v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2(lean_object* v_declName_1205_, lean_object* v_modifyEnv_1206_, lean_object* v___f_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_toBind_1210_, lean_object* v___f_1211_, lean_object* v_____do__lift_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1212_, v_declName_1205_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v___x_1214_; 
lean_dec(v___f_1211_);
lean_dec(v_toBind_1210_);
lean_dec_ref(v_inst_1209_);
lean_dec_ref(v_inst_1208_);
lean_dec(v_declName_1205_);
v___x_1214_ = lean_apply_1(v_modifyEnv_1206_, v___f_1207_);
return v___x_1214_;
}
else
{
uint8_t v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec_ref(v___x_1213_);
lean_dec_ref(v___f_1207_);
lean_dec(v_modifyEnv_1206_);
v___x_1215_ = 0;
v___x_1216_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1217_ = l_Lean_MessageData_ofConstName(v_declName_1205_, v___x_1215_);
v___x_1218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1218_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = l_Lean_throwError___redArg(v_inst_1208_, v_inst_1209_, v___x_1220_);
v___x_1222_ = lean_apply_4(v_toBind_1210_, lean_box(0), lean_box(0), v___x_1221_, v___f_1211_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1223_, lean_object* v_modifyEnv_1224_, lean_object* v___f_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_toBind_1228_, lean_object* v___f_1229_, lean_object* v_____do__lift_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_addDocStringCore___redArg___lam__2(v_declName_1223_, v_modifyEnv_1224_, v___f_1225_, v_inst_1226_, v_inst_1227_, v_toBind_1228_, v___f_1229_, v_____do__lift_1230_);
lean_dec_ref(v_____do__lift_1230_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg(lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_declName_1235_, lean_object* v_docString_1236_){
_start:
{
lean_object* v_toBind_1237_; lean_object* v_getEnv_1238_; lean_object* v_modifyEnv_1239_; lean_object* v___f_1240_; lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v___x_1243_; 
v_toBind_1237_ = lean_ctor_get(v_inst_1232_, 1);
lean_inc_n(v_toBind_1237_, 2);
v_getEnv_1238_ = lean_ctor_get(v_inst_1234_, 0);
lean_inc(v_getEnv_1238_);
v_modifyEnv_1239_ = lean_ctor_get(v_inst_1234_, 1);
lean_inc_n(v_modifyEnv_1239_, 2);
lean_dec_ref(v_inst_1234_);
lean_inc(v_declName_1235_);
v___f_1240_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1240_, 0, v_docString_1236_);
lean_closure_set(v___f_1240_, 1, v_declName_1235_);
lean_inc_ref(v___f_1240_);
v___f_1241_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1241_, 0, v_modifyEnv_1239_);
lean_closure_set(v___f_1241_, 1, v___f_1240_);
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1242_, 0, v_declName_1235_);
lean_closure_set(v___f_1242_, 1, v_modifyEnv_1239_);
lean_closure_set(v___f_1242_, 2, v___f_1240_);
lean_closure_set(v___f_1242_, 3, v_inst_1232_);
lean_closure_set(v___f_1242_, 4, v_inst_1233_);
lean_closure_set(v___f_1242_, 5, v_toBind_1237_);
lean_closure_set(v___f_1242_, 6, v___f_1241_);
v___x_1243_ = lean_apply_4(v_toBind_1237_, lean_box(0), lean_box(0), v_getEnv_1238_, v___f_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore(lean_object* v_m_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_declName_1249_, lean_object* v_docString_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_addDocStringCore___redArg(v_inst_1245_, v_inst_1246_, v_inst_1247_, v_declName_1249_, v_docString_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___boxed(lean_object* v_m_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_declName_1257_, lean_object* v_docString_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_addDocStringCore(v_m_1252_, v_inst_1253_, v_inst_1254_, v_inst_1255_, v_inst_1256_, v_declName_1257_, v_docString_1258_);
lean_dec(v_inst_1256_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__0(lean_object* v_declName_1261_, lean_object* v_x_1262_){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__0___closed__0));
v___x_1264_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_1263_, v_declName_1261_, v_x_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__1(lean_object* v___f_1265_, lean_object* v_env_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1267_ = l_Lean_docStringExt;
v___x_1268_ = lean_box(2);
v___x_1269_ = lean_box(0);
v___x_1270_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_1267_, v_env_1266_, v___f_1265_, v___x_1268_, v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__3___closed__0));
v___x_1273_ = l_Lean_stringToMessageData(v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3(lean_object* v_declName_1274_, lean_object* v_modifyEnv_1275_, lean_object* v___f_1276_, lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_toBind_1279_, lean_object* v___f_1280_, lean_object* v_____do__lift_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1281_, v_declName_1274_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1283_; 
lean_dec(v___f_1280_);
lean_dec(v_toBind_1279_);
lean_dec_ref(v_inst_1278_);
lean_dec_ref(v_inst_1277_);
lean_dec(v_declName_1274_);
v___x_1283_ = lean_apply_1(v_modifyEnv_1275_, v___f_1276_);
return v___x_1283_;
}
else
{
uint8_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec_ref(v___x_1282_);
lean_dec_ref(v___f_1276_);
lean_dec(v_modifyEnv_1275_);
v___x_1284_ = 0;
v___x_1285_ = lean_obj_once(&l_Lean_removeDocStringCore___redArg___lam__3___closed__1, &l_Lean_removeDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1);
v___x_1286_ = l_Lean_MessageData_ofConstName(v_declName_1274_, v___x_1284_);
v___x_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = l_Lean_throwError___redArg(v_inst_1277_, v_inst_1278_, v___x_1289_);
v___x_1291_ = lean_apply_4(v_toBind_1279_, lean_box(0), lean_box(0), v___x_1290_, v___f_1280_);
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_1292_, lean_object* v_modifyEnv_1293_, lean_object* v___f_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_toBind_1297_, lean_object* v___f_1298_, lean_object* v_____do__lift_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_removeDocStringCore___redArg___lam__3(v_declName_1292_, v_modifyEnv_1293_, v___f_1294_, v_inst_1295_, v_inst_1296_, v_toBind_1297_, v___f_1298_, v_____do__lift_1299_);
lean_dec_ref(v_____do__lift_1299_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg(lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_declName_1304_){
_start:
{
lean_object* v_toBind_1305_; lean_object* v_getEnv_1306_; lean_object* v_modifyEnv_1307_; lean_object* v___f_1308_; lean_object* v___f_1309_; lean_object* v___f_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; 
v_toBind_1305_ = lean_ctor_get(v_inst_1301_, 1);
lean_inc_n(v_toBind_1305_, 2);
v_getEnv_1306_ = lean_ctor_get(v_inst_1303_, 0);
lean_inc(v_getEnv_1306_);
v_modifyEnv_1307_ = lean_ctor_get(v_inst_1303_, 1);
lean_inc_n(v_modifyEnv_1307_, 2);
lean_dec_ref(v_inst_1303_);
lean_inc(v_declName_1304_);
v___f_1308_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1308_, 0, v_declName_1304_);
v___f_1309_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1309_, 0, v___f_1308_);
lean_inc_ref(v___f_1309_);
v___f_1310_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1310_, 0, v_modifyEnv_1307_);
lean_closure_set(v___f_1310_, 1, v___f_1309_);
v___f_1311_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1311_, 0, v_declName_1304_);
lean_closure_set(v___f_1311_, 1, v_modifyEnv_1307_);
lean_closure_set(v___f_1311_, 2, v___f_1309_);
lean_closure_set(v___f_1311_, 3, v_inst_1301_);
lean_closure_set(v___f_1311_, 4, v_inst_1302_);
lean_closure_set(v___f_1311_, 5, v_toBind_1305_);
lean_closure_set(v___f_1311_, 6, v___f_1310_);
v___x_1312_ = lean_apply_4(v_toBind_1305_, lean_box(0), lean_box(0), v_getEnv_1306_, v___f_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore(lean_object* v_m_1313_, lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_declName_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_removeDocStringCore___redArg(v_inst_1314_, v_inst_1315_, v_inst_1316_, v_declName_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___boxed(lean_object* v_m_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_declName_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_removeDocStringCore(v_m_1320_, v_inst_1321_, v_inst_1322_, v_inst_1323_, v_inst_1324_, v_declName_1325_);
lean_dec(v_inst_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___redArg(lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_declName_1330_, lean_object* v_docString_x3f_1331_){
_start:
{
if (lean_obj_tag(v_docString_x3f_1331_) == 0)
{
lean_object* v_toApplicative_1332_; lean_object* v_toPure_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_toApplicative_1332_ = lean_ctor_get(v_inst_1327_, 0);
lean_inc_ref(v_toApplicative_1332_);
lean_dec(v_declName_1330_);
lean_dec_ref(v_inst_1329_);
lean_dec_ref(v_inst_1328_);
lean_dec_ref(v_inst_1327_);
v_toPure_1333_ = lean_ctor_get(v_toApplicative_1332_, 1);
lean_inc(v_toPure_1333_);
lean_dec_ref(v_toApplicative_1332_);
v___x_1334_ = lean_box(0);
v___x_1335_ = lean_apply_2(v_toPure_1333_, lean_box(0), v___x_1334_);
return v___x_1335_;
}
else
{
lean_object* v_val_1336_; lean_object* v___x_1337_; 
v_val_1336_ = lean_ctor_get(v_docString_x3f_1331_, 0);
lean_inc(v_val_1336_);
lean_dec_ref(v_docString_x3f_1331_);
v___x_1337_ = l_Lean_addDocStringCore___redArg(v_inst_1327_, v_inst_1328_, v_inst_1329_, v_declName_1330_, v_val_1336_);
return v___x_1337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27(lean_object* v_m_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_declName_1343_, lean_object* v_docString_x3f_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_addDocStringCore_x27___redArg(v_inst_1339_, v_inst_1340_, v_inst_1341_, v_declName_1343_, v_docString_x3f_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___boxed(lean_object* v_m_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_declName_1351_, lean_object* v_docString_x3f_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_addDocStringCore_x27(v_m_1346_, v_inst_1347_, v_inst_1348_, v_inst_1349_, v_inst_1350_, v_declName_1351_, v_docString_x3f_1352_);
lean_dec(v_inst_1350_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object* v_declName_1354_, lean_object* v_target_1355_, lean_object* v_env_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1358_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1357_, v_env_1356_, v_declName_1354_, v_target_1355_);
return v___x_1358_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__2___closed__0));
v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object* v___x_1362_, lean_object* v_target_1363_, lean_object* v_declName_1364_, lean_object* v___x_1365_, lean_object* v_modifyEnv_1366_, lean_object* v___f_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_toBind_1370_, lean_object* v___f_1371_, lean_object* v_____do__lift_1372_){
_start:
{
lean_object* v___x_1373_; lean_object* v_toEnvExtension_1374_; lean_object* v_asyncMode_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1373_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1374_ = lean_ctor_get(v___x_1373_, 0);
v_asyncMode_1375_ = lean_ctor_get(v_toEnvExtension_1374_, 2);
v___x_1376_ = 1;
v___x_1377_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1362_, v___x_1373_, v_____do__lift_1372_, v_target_1363_, v_asyncMode_1375_, v___x_1376_);
v___x_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1378_, 0, v_declName_1364_);
v___x_1379_ = l_Option_instBEq_beq___redArg(v___x_1365_, v___x_1377_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_dec(v___f_1371_);
lean_dec(v_toBind_1370_);
lean_dec_ref(v_inst_1369_);
lean_dec_ref(v_inst_1368_);
v___x_1380_ = lean_apply_1(v_modifyEnv_1366_, v___f_1367_);
return v___x_1380_;
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec_ref(v___f_1367_);
lean_dec(v_modifyEnv_1366_);
v___x_1381_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__2___closed__1, &l_Lean_addInheritedDocString___redArg___lam__2___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1);
v___x_1382_ = l_Lean_throwError___redArg(v_inst_1368_, v_inst_1369_, v___x_1381_);
v___x_1383_ = lean_apply_4(v_toBind_1370_, lean_box(0), lean_box(0), v___x_1382_, v___f_1371_);
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object* v_toBind_1384_, lean_object* v_getEnv_1385_, lean_object* v___f_1386_, lean_object* v_____r_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_apply_4(v_toBind_1384_, lean_box(0), lean_box(0), v_getEnv_1385_, v___f_1386_);
return v___x_1388_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__0));
v___x_1391_ = l_Lean_stringToMessageData(v___x_1390_);
return v___x_1391_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__2));
v___x_1394_ = l_Lean_stringToMessageData(v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object* v___x_1395_, lean_object* v_declName_1396_, lean_object* v_toBind_1397_, lean_object* v_getEnv_1398_, lean_object* v___f_1399_, lean_object* v_inst_1400_, lean_object* v_inst_1401_, lean_object* v___f_1402_, lean_object* v_____do__lift_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v_toEnvExtension_1405_; lean_object* v_asyncMode_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1404_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1405_ = lean_ctor_get(v___x_1404_, 0);
v_asyncMode_1406_ = lean_ctor_get(v_toEnvExtension_1405_, 2);
v___x_1407_ = 1;
lean_inc(v_declName_1396_);
v___x_1408_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1395_, v___x_1404_, v_____do__lift_1403_, v_declName_1396_, v_asyncMode_1406_, v___x_1407_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v___x_1409_; 
lean_dec(v___f_1402_);
lean_dec_ref(v_inst_1401_);
lean_dec_ref(v_inst_1400_);
lean_dec(v_declName_1396_);
v___x_1409_ = lean_apply_4(v_toBind_1397_, lean_box(0), lean_box(0), v_getEnv_1398_, v___f_1399_);
return v___x_1409_;
}
else
{
lean_object* v___x_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_dec_ref(v___x_1408_);
lean_dec(v___f_1399_);
lean_dec(v_getEnv_1398_);
v___x_1410_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1411_ = 0;
v___x_1412_ = l_Lean_MessageData_ofConstName(v_declName_1396_, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1410_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__3, &l_Lean_addInheritedDocString___redArg___lam__3___closed__3_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = l_Lean_throwError___redArg(v_inst_1400_, v_inst_1401_, v___x_1415_);
v___x_1417_ = lean_apply_4(v_toBind_1397_, lean_box(0), lean_box(0), v___x_1416_, v___f_1402_);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object* v_declName_1418_, lean_object* v_toBind_1419_, lean_object* v_getEnv_1420_, lean_object* v___f_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v___f_1424_, lean_object* v_____do__lift_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1425_, v_declName_1418_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v___x_1427_; 
lean_dec(v___f_1424_);
lean_dec_ref(v_inst_1423_);
lean_dec_ref(v_inst_1422_);
lean_dec(v_declName_1418_);
v___x_1427_ = lean_apply_4(v_toBind_1419_, lean_box(0), lean_box(0), v_getEnv_1420_, v___f_1421_);
return v___x_1427_;
}
else
{
uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec_ref(v___x_1426_);
lean_dec(v___f_1421_);
lean_dec(v_getEnv_1420_);
v___x_1428_ = 0;
v___x_1429_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1430_ = l_Lean_MessageData_ofConstName(v_declName_1418_, v___x_1428_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = l_Lean_throwError___redArg(v_inst_1422_, v_inst_1423_, v___x_1433_);
v___x_1435_ = lean_apply_4(v_toBind_1419_, lean_box(0), lean_box(0), v___x_1434_, v___f_1424_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object* v_declName_1436_, lean_object* v_toBind_1437_, lean_object* v_getEnv_1438_, lean_object* v___f_1439_, lean_object* v_inst_1440_, lean_object* v_inst_1441_, lean_object* v___f_1442_, lean_object* v_____do__lift_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_addInheritedDocString___redArg___lam__5(v_declName_1436_, v_toBind_1437_, v_getEnv_1438_, v___f_1439_, v_inst_1440_, v_inst_1441_, v___f_1442_, v_____do__lift_1443_);
lean_dec_ref(v_____do__lift_1443_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v_declName_1449_, lean_object* v_target_1450_){
_start:
{
lean_object* v_toBind_1451_; lean_object* v_getEnv_1452_; lean_object* v_modifyEnv_1453_; lean_object* v___f_1454_; lean_object* v___f_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___f_1458_; lean_object* v___f_1459_; lean_object* v___f_1460_; lean_object* v___f_1461_; lean_object* v___f_1462_; lean_object* v___x_1463_; 
v_toBind_1451_ = lean_ctor_get(v_inst_1446_, 1);
lean_inc_n(v_toBind_1451_, 6);
v_getEnv_1452_ = lean_ctor_get(v_inst_1448_, 0);
lean_inc_n(v_getEnv_1452_, 5);
v_modifyEnv_1453_ = lean_ctor_get(v_inst_1448_, 1);
lean_inc_n(v_modifyEnv_1453_, 2);
lean_dec_ref(v_inst_1448_);
lean_inc(v_target_1450_);
lean_inc_n(v_declName_1449_, 3);
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1454_, 0, v_declName_1449_);
lean_closure_set(v___f_1454_, 1, v_target_1450_);
lean_inc_ref(v___f_1454_);
v___f_1455_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1455_, 0, v_modifyEnv_1453_);
lean_closure_set(v___f_1455_, 1, v___f_1454_);
v___x_1456_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___closed__0));
v___x_1457_ = lean_box(0);
lean_inc_ref_n(v_inst_1447_, 2);
lean_inc_ref_n(v_inst_1446_, 2);
v___f_1458_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__2), 11, 10);
lean_closure_set(v___f_1458_, 0, v___x_1457_);
lean_closure_set(v___f_1458_, 1, v_target_1450_);
lean_closure_set(v___f_1458_, 2, v_declName_1449_);
lean_closure_set(v___f_1458_, 3, v___x_1456_);
lean_closure_set(v___f_1458_, 4, v_modifyEnv_1453_);
lean_closure_set(v___f_1458_, 5, v___f_1454_);
lean_closure_set(v___f_1458_, 6, v_inst_1446_);
lean_closure_set(v___f_1458_, 7, v_inst_1447_);
lean_closure_set(v___f_1458_, 8, v_toBind_1451_);
lean_closure_set(v___f_1458_, 9, v___f_1455_);
lean_inc_ref(v___f_1458_);
v___f_1459_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1459_, 0, v_toBind_1451_);
lean_closure_set(v___f_1459_, 1, v_getEnv_1452_);
lean_closure_set(v___f_1459_, 2, v___f_1458_);
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__3), 9, 8);
lean_closure_set(v___f_1460_, 0, v___x_1457_);
lean_closure_set(v___f_1460_, 1, v_declName_1449_);
lean_closure_set(v___f_1460_, 2, v_toBind_1451_);
lean_closure_set(v___f_1460_, 3, v_getEnv_1452_);
lean_closure_set(v___f_1460_, 4, v___f_1458_);
lean_closure_set(v___f_1460_, 5, v_inst_1446_);
lean_closure_set(v___f_1460_, 6, v_inst_1447_);
lean_closure_set(v___f_1460_, 7, v___f_1459_);
lean_inc_ref(v___f_1460_);
v___f_1461_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1461_, 0, v_toBind_1451_);
lean_closure_set(v___f_1461_, 1, v_getEnv_1452_);
lean_closure_set(v___f_1461_, 2, v___f_1460_);
v___f_1462_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1462_, 0, v_declName_1449_);
lean_closure_set(v___f_1462_, 1, v_toBind_1451_);
lean_closure_set(v___f_1462_, 2, v_getEnv_1452_);
lean_closure_set(v___f_1462_, 3, v___f_1460_);
lean_closure_set(v___f_1462_, 4, v_inst_1446_);
lean_closure_set(v___f_1462_, 5, v_inst_1447_);
lean_closure_set(v___f_1462_, 6, v___f_1461_);
v___x_1463_ = lean_apply_4(v_toBind_1451_, lean_box(0), lean_box(0), v_getEnv_1452_, v___f_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object* v_m_1464_, lean_object* v_inst_1465_, lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_declName_1468_, lean_object* v_target_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_addInheritedDocString___redArg(v_inst_1465_, v_inst_1466_, v_inst_1467_, v_declName_1468_, v_target_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f(lean_object* v_env_1472_, lean_object* v_declName_1473_, uint8_t v_includeBuiltin_1474_){
_start:
{
lean_object* v___x_1479_; lean_object* v_toEnvExtension_1480_; lean_object* v_asyncMode_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1479_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1480_ = lean_ctor_get(v___x_1479_, 0);
v_asyncMode_1481_ = lean_ctor_get(v_toEnvExtension_1480_, 2);
v___x_1482_ = lean_box(0);
v___x_1483_ = 1;
lean_inc(v_declName_1473_);
lean_inc_ref(v_env_1472_);
v___x_1484_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1482_, v___x_1479_, v_env_1472_, v_declName_1473_, v_asyncMode_1481_, v___x_1483_);
if (lean_obj_tag(v___x_1484_) == 1)
{
lean_object* v_val_1485_; 
lean_dec(v_declName_1473_);
v_val_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_val_1485_);
lean_dec_ref(v___x_1484_);
v_declName_1473_ = v_val_1485_;
goto _start;
}
else
{
lean_object* v___x_1487_; lean_object* v_toEnvExtension_1488_; lean_object* v_asyncMode_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec(v___x_1484_);
v___x_1487_ = l_Lean_docStringExt;
v_toEnvExtension_1488_ = lean_ctor_get(v___x_1487_, 0);
v_asyncMode_1489_ = lean_ctor_get(v_toEnvExtension_1488_, 2);
v___x_1490_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
lean_inc(v_declName_1473_);
lean_inc_ref(v_env_1472_);
v___x_1491_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1490_, v___x_1487_, v_env_1472_, v_declName_1473_, v_asyncMode_1489_, v___x_1483_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v___x_1492_; lean_object* v_toEnvExtension_1493_; lean_object* v_asyncMode_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1492_ = l_Lean_versoDocStringExt;
v_toEnvExtension_1493_ = lean_ctor_get(v___x_1492_, 0);
v_asyncMode_1494_ = lean_ctor_get(v_toEnvExtension_1493_, 2);
v___x_1495_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default));
lean_inc(v_declName_1473_);
v___x_1496_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1495_, v___x_1492_, v_env_1472_, v_declName_1473_, v_asyncMode_1494_, v___x_1483_);
if (lean_obj_tag(v___x_1496_) == 0)
{
if (v_includeBuiltin_1474_ == 0)
{
lean_dec(v_declName_1473_);
goto v___jp_1476_;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1498_ = lean_st_ref_get(v___x_1497_);
v___x_1499_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1498_, v_declName_1473_);
lean_dec(v___x_1498_);
if (lean_obj_tag(v___x_1499_) == 1)
{
lean_object* v_val_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_declName_1473_);
v_val_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1509_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_val_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1509_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v_val_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1504_);
v___x_1506_ = v___x_1502_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
}
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec(v___x_1499_);
v___x_1510_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1511_ = lean_st_ref_get(v___x_1510_);
v___x_1512_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1511_, v_declName_1473_);
lean_dec(v_declName_1473_);
lean_dec(v___x_1511_);
if (lean_obj_tag(v___x_1512_) == 1)
{
lean_object* v_val_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1522_; 
v_val_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1522_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_val_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1522_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_val_1513_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v___x_1517_);
v___x_1519_ = v___x_1515_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
}
else
{
lean_dec(v___x_1512_);
goto v___jp_1476_;
}
}
}
}
else
{
lean_object* v_val_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_declName_1473_);
v_val_1523_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1525_ = v___x_1496_;
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_val_1523_);
lean_dec(v___x_1496_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_val_1523_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1527_);
v___x_1529_ = v___x_1525_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_val_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1542_; 
lean_dec(v_declName_1473_);
lean_dec_ref(v_env_1472_);
v_val_1533_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1535_ = v___x_1491_;
v_isShared_1536_ = v_isSharedCheck_1542_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_val_1533_);
lean_dec(v___x_1491_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1542_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_val_1533_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1537_);
v___x_1539_ = v___x_1535_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
return v___x_1540_;
}
}
}
}
v___jp_1476_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object* v_env_1543_, lean_object* v_declName_1544_, lean_object* v_includeBuiltin_1545_, lean_object* v_a_1546_){
_start:
{
uint8_t v_includeBuiltin_boxed_1547_; lean_object* v_res_1548_; 
v_includeBuiltin_boxed_1547_ = lean_unbox(v_includeBuiltin_1545_);
v_res_1548_ = l_Lean_findInternalDocString_x3f(v_env_1543_, v_declName_1544_, v_includeBuiltin_boxed_1547_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(lean_object* v_s_1549_, lean_object* v_replacement_1550_, lean_object* v_a_1551_, lean_object* v_b_1552_){
_start:
{
lean_object* v_it_1554_; lean_object* v_startPos_1555_; lean_object* v_endPos_1556_; lean_object* v_it_1565_; 
switch(lean_obj_tag(v_a_1551_))
{
case 0:
{
lean_object* v_pos_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1583_; 
v_pos_1571_ = lean_ctor_get(v_a_1551_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_a_1551_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1573_ = v_a_1551_;
v_isShared_1574_ = v_isSharedCheck_1583_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_pos_1571_);
lean_dec(v_a_1551_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1583_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_startInclusive_1575_; lean_object* v_endExclusive_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v_startInclusive_1575_ = lean_ctor_get(v_s_1549_, 1);
v_endExclusive_1576_ = lean_ctor_get(v_s_1549_, 2);
v___x_1577_ = lean_nat_sub(v_endExclusive_1576_, v_startInclusive_1575_);
v___x_1578_ = lean_nat_dec_eq(v_pos_1571_, v___x_1577_);
lean_dec(v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1580_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 1);
v___x_1580_ = v___x_1573_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_pos_1571_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
v_it_1565_ = v___x_1580_;
goto v___jp_1564_;
}
}
else
{
lean_object* v___x_1582_; 
lean_del_object(v___x_1573_);
lean_dec(v_pos_1571_);
v___x_1582_ = lean_box(3);
v_it_1565_ = v___x_1582_;
goto v___jp_1564_;
}
}
}
case 1:
{
lean_object* v_pos_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1596_; 
v_pos_1584_ = lean_ctor_get(v_a_1551_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_a_1551_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1586_ = v_a_1551_;
v_isShared_1587_ = v_isSharedCheck_1596_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_pos_1584_);
lean_dec(v_a_1551_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1596_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v_str_1588_; lean_object* v_startInclusive_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v_str_1588_ = lean_ctor_get(v_s_1549_, 0);
v_startInclusive_1589_ = lean_ctor_get(v_s_1549_, 1);
v___x_1590_ = lean_nat_add(v_startInclusive_1589_, v_pos_1584_);
v___x_1591_ = lean_string_utf8_next_fast(v_str_1588_, v___x_1590_);
lean_dec(v___x_1590_);
v___x_1592_ = lean_nat_sub(v___x_1591_, v_startInclusive_1589_);
lean_inc(v___x_1592_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set_tag(v___x_1586_, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1592_);
v___x_1594_ = v___x_1586_;
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
v_it_1554_ = v___x_1594_;
v_startPos_1555_ = v_pos_1584_;
v_endPos_1556_ = v___x_1592_;
goto v___jp_1553_;
}
}
}
case 2:
{
lean_object* v_needle_1597_; lean_object* v_table_1598_; lean_object* v_stackPos_1599_; lean_object* v_needlePos_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1659_; 
v_needle_1597_ = lean_ctor_get(v_a_1551_, 0);
v_table_1598_ = lean_ctor_get(v_a_1551_, 1);
v_stackPos_1599_ = lean_ctor_get(v_a_1551_, 2);
v_needlePos_1600_ = lean_ctor_get(v_a_1551_, 3);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_a_1551_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1602_ = v_a_1551_;
v_isShared_1603_ = v_isSharedCheck_1659_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_needlePos_1600_);
lean_inc(v_stackPos_1599_);
lean_inc(v_table_1598_);
lean_inc(v_needle_1597_);
lean_dec(v_a_1551_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1659_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v_str_1604_; lean_object* v_startInclusive_1605_; lean_object* v_endExclusive_1606_; lean_object* v_str_1607_; lean_object* v_startInclusive_1608_; lean_object* v_endExclusive_1609_; lean_object* v_basePos_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_str_1604_ = lean_ctor_get(v_needle_1597_, 0);
v_startInclusive_1605_ = lean_ctor_get(v_needle_1597_, 1);
v_endExclusive_1606_ = lean_ctor_get(v_needle_1597_, 2);
v_str_1607_ = lean_ctor_get(v_s_1549_, 0);
v_startInclusive_1608_ = lean_ctor_get(v_s_1549_, 1);
v_endExclusive_1609_ = lean_ctor_get(v_s_1549_, 2);
v_basePos_1610_ = lean_nat_sub(v_stackPos_1599_, v_needlePos_1600_);
v___x_1611_ = lean_nat_sub(v_endExclusive_1606_, v_startInclusive_1605_);
v___x_1612_ = lean_nat_add(v_basePos_1610_, v___x_1611_);
v___x_1613_ = lean_nat_sub(v_endExclusive_1609_, v_startInclusive_1608_);
v___x_1614_ = lean_nat_dec_le(v___x_1612_, v___x_1613_);
lean_dec(v___x_1612_);
if (v___x_1614_ == 0)
{
uint8_t v___x_1615_; 
lean_dec(v___x_1611_);
lean_del_object(v___x_1602_);
lean_dec(v_needlePos_1600_);
lean_dec(v_stackPos_1599_);
lean_dec_ref(v_table_1598_);
lean_dec_ref(v_needle_1597_);
v___x_1615_ = l_String_instDecidableLtRaw___aux__1(v_basePos_1610_, v___x_1613_);
if (v___x_1615_ == 0)
{
lean_dec(v___x_1613_);
lean_dec(v_basePos_1610_);
lean_dec_ref(v_s_1549_);
return v_b_1552_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = l_String_Slice_pos_x21(v_s_1549_, v_basePos_1610_);
lean_dec(v_basePos_1610_);
v___x_1617_ = lean_box(3);
v_it_1554_ = v___x_1617_;
v_startPos_1555_ = v___x_1616_;
v_endPos_1556_ = v___x_1613_;
goto v___jp_1553_;
}
}
else
{
lean_object* v___x_1618_; uint8_t v_stackByte_1619_; lean_object* v___x_1620_; uint8_t v_patByte_1621_; uint8_t v___x_1622_; 
lean_dec(v___x_1613_);
v___x_1618_ = lean_nat_add(v_startInclusive_1608_, v_stackPos_1599_);
v_stackByte_1619_ = lean_string_get_byte_fast(v_str_1607_, v___x_1618_);
v___x_1620_ = lean_nat_add(v_startInclusive_1605_, v_needlePos_1600_);
v_patByte_1621_ = lean_string_get_byte_fast(v_str_1604_, v___x_1620_);
v___x_1622_ = lean_uint8_dec_eq(v_stackByte_1619_, v_patByte_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; uint8_t v___x_1624_; 
lean_dec(v___x_1611_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_nat_dec_eq(v_needlePos_1600_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v_newNeedlePos_1627_; uint8_t v___x_1628_; 
v___x_1625_ = lean_unsigned_to_nat(1u);
v___x_1626_ = lean_nat_sub(v_needlePos_1600_, v___x_1625_);
lean_dec(v_needlePos_1600_);
v_newNeedlePos_1627_ = lean_array_fget_borrowed(v_table_1598_, v___x_1626_);
lean_dec(v___x_1626_);
v___x_1628_ = lean_nat_dec_eq(v_newNeedlePos_1627_, v___x_1623_);
if (v___x_1628_ == 0)
{
lean_object* v_oldBasePos_1629_; lean_object* v___x_1630_; lean_object* v_newBasePos_1631_; lean_object* v___x_1633_; 
lean_inc(v_newNeedlePos_1627_);
v_oldBasePos_1629_ = l_String_Slice_pos_x21(v_s_1549_, v_basePos_1610_);
lean_dec(v_basePos_1610_);
v___x_1630_ = lean_nat_sub(v_stackPos_1599_, v_newNeedlePos_1627_);
v_newBasePos_1631_ = l_String_Slice_pos_x21(v_s_1549_, v___x_1630_);
lean_dec(v___x_1630_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 3, v_newNeedlePos_1627_);
v___x_1633_ = v___x_1602_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_needle_1597_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_table_1598_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_stackPos_1599_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v_newNeedlePos_1627_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
v_it_1554_ = v___x_1633_;
v_startPos_1555_ = v_oldBasePos_1629_;
v_endPos_1556_ = v_newBasePos_1631_;
goto v___jp_1553_;
}
}
else
{
lean_object* v_basePos_1635_; lean_object* v_nextStackPos_1636_; lean_object* v___x_1638_; 
v_basePos_1635_ = l_String_Slice_pos_x21(v_s_1549_, v_basePos_1610_);
lean_dec(v_basePos_1610_);
v_nextStackPos_1636_ = l_String_Slice_posGE___redArg(v_s_1549_, v_stackPos_1599_);
lean_inc(v_nextStackPos_1636_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 3, v___x_1623_);
lean_ctor_set(v___x_1602_, 2, v_nextStackPos_1636_);
v___x_1638_ = v___x_1602_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_needle_1597_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_table_1598_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_nextStackPos_1636_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v___x_1623_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
v_it_1554_ = v___x_1638_;
v_startPos_1555_ = v_basePos_1635_;
v_endPos_1556_ = v_nextStackPos_1636_;
goto v___jp_1553_;
}
}
}
else
{
lean_object* v_basePos_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_nextStackPos_1643_; lean_object* v___x_1645_; 
lean_dec(v_basePos_1610_);
lean_dec(v_needlePos_1600_);
v_basePos_1640_ = l_String_Slice_pos_x21(v_s_1549_, v_stackPos_1599_);
v___x_1641_ = lean_unsigned_to_nat(1u);
v___x_1642_ = lean_nat_add(v_stackPos_1599_, v___x_1641_);
lean_dec(v_stackPos_1599_);
v_nextStackPos_1643_ = l_String_Slice_posGE___redArg(v_s_1549_, v___x_1642_);
lean_inc(v_nextStackPos_1643_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 3, v___x_1623_);
lean_ctor_set(v___x_1602_, 2, v_nextStackPos_1643_);
v___x_1645_ = v___x_1602_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_needle_1597_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_table_1598_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_nextStackPos_1643_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v___x_1623_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
v_it_1554_ = v___x_1645_;
v_startPos_1555_ = v_basePos_1640_;
v_endPos_1556_ = v_nextStackPos_1643_;
goto v___jp_1553_;
}
}
}
else
{
lean_object* v___x_1647_; lean_object* v_nextStackPos_1648_; lean_object* v_nextNeedlePos_1649_; uint8_t v___x_1650_; 
lean_dec(v_basePos_1610_);
v___x_1647_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1648_ = lean_nat_add(v_stackPos_1599_, v___x_1647_);
lean_dec(v_stackPos_1599_);
v_nextNeedlePos_1649_ = lean_nat_add(v_needlePos_1600_, v___x_1647_);
lean_dec(v_needlePos_1600_);
v___x_1650_ = lean_nat_dec_eq(v_nextNeedlePos_1649_, v___x_1611_);
lean_dec(v___x_1611_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1652_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 3, v_nextNeedlePos_1649_);
lean_ctor_set(v___x_1602_, 2, v_nextStackPos_1648_);
v___x_1652_ = v___x_1602_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_needle_1597_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_table_1598_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_nextStackPos_1648_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v_nextNeedlePos_1649_);
v___x_1652_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
v_a_1551_ = v___x_1652_;
goto _start;
}
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
lean_dec(v_nextNeedlePos_1649_);
v___x_1655_ = lean_unsigned_to_nat(0u);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 3, v___x_1655_);
lean_ctor_set(v___x_1602_, 2, v_nextStackPos_1648_);
v___x_1657_ = v___x_1602_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_needle_1597_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_table_1598_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_nextStackPos_1648_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
v_it_1565_ = v___x_1657_;
goto v___jp_1564_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1549_);
return v_b_1552_;
}
}
v___jp_1553_:
{
lean_object* v___x_1557_; lean_object* v_str_1558_; lean_object* v_startInclusive_1559_; lean_object* v_endExclusive_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_inc_ref(v_s_1549_);
v___x_1557_ = l_String_Slice_slice_x21(v_s_1549_, v_startPos_1555_, v_endPos_1556_);
lean_dec(v_endPos_1556_);
lean_dec(v_startPos_1555_);
v_str_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc_ref(v_str_1558_);
v_startInclusive_1559_ = lean_ctor_get(v___x_1557_, 1);
lean_inc(v_startInclusive_1559_);
v_endExclusive_1560_ = lean_ctor_get(v___x_1557_, 2);
lean_inc(v_endExclusive_1560_);
lean_dec_ref(v___x_1557_);
v___x_1561_ = lean_string_utf8_extract(v_str_1558_, v_startInclusive_1559_, v_endExclusive_1560_);
lean_dec(v_endExclusive_1560_);
lean_dec(v_startInclusive_1559_);
lean_dec_ref(v_str_1558_);
v___x_1562_ = lean_string_append(v_b_1552_, v___x_1561_);
lean_dec_ref(v___x_1561_);
v_a_1551_ = v_it_1554_;
v_b_1552_ = v___x_1562_;
goto _start;
}
v___jp_1564_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1566_ = lean_unsigned_to_nat(0u);
v___x_1567_ = lean_string_utf8_byte_size(v_replacement_1550_);
v___x_1568_ = lean_string_utf8_extract(v_replacement_1550_, v___x_1566_, v___x_1567_);
v___x_1569_ = lean_string_append(v_b_1552_, v___x_1568_);
lean_dec_ref(v___x_1568_);
v_a_1551_ = v_it_1565_;
v_b_1552_ = v___x_1569_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_s_1660_, lean_object* v_replacement_1661_, lean_object* v_a_1662_, lean_object* v_b_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1660_, v_replacement_1661_, v_a_1662_, v_b_1663_);
lean_dec_ref(v_replacement_1661_);
return v_res_1664_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1667_ = lean_string_utf8_byte_size(v___x_1666_);
return v___x_1667_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; 
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1670_ = lean_nat_dec_eq(v___x_1669_, v___x_1668_);
return v___x_1670_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1671_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1672_ = lean_unsigned_to_nat(0u);
v___x_1673_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v___x_1672_);
lean_ctor_set(v___x_1674_, 2, v___x_1671_);
return v___x_1674_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1676_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1675_);
return v___x_1676_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4);
v___x_1679_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1680_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v___x_1678_);
lean_ctor_set(v___x_1680_, 2, v___x_1677_);
lean_ctor_set(v___x_1680_, 3, v___x_1677_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(lean_object* v_s_1683_, lean_object* v_replacement_1684_){
_start:
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_1686_ = lean_uint8_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5);
v___x_1688_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1683_, v_replacement_1684_, v___x_1687_, v___x_1685_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__6));
v___x_1690_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1683_, v_replacement_1684_, v___x_1689_, v___x_1685_);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_s_1691_, lean_object* v_replacement_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v_s_1691_, v_replacement_1692_);
lean_dec_ref(v_replacement_1692_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(lean_object* v_as_1701_, size_t v_sz_1702_, size_t v_i_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = lean_usize_dec_lt(v_i_1703_, v_sz_1702_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v_b_1704_);
lean_ctor_set(v___x_1708_, 1, v___y_1706_);
return v___x_1708_;
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1710_; lean_object* v_snd_1711_; lean_object* v___x_1712_; size_t v___x_1713_; size_t v___x_1714_; 
v_a_1709_ = lean_array_uget_borrowed(v_as_1701_, v_i_1703_);
lean_inc(v_a_1709_);
v___x_1710_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_a_1709_, v___y_1705_, v___y_1706_);
v_snd_1711_ = lean_ctor_get(v___x_1710_, 1);
lean_inc(v_snd_1711_);
lean_dec_ref(v___x_1710_);
v___x_1712_ = lean_box(0);
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_add(v_i_1703_, v___x_1713_);
v_i_1703_ = v___x_1714_;
v_b_1704_ = v___x_1712_;
v___y_1706_ = v_snd_1711_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(lean_object* v_x_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
switch(lean_obj_tag(v_x_1729_))
{
case 0:
{
lean_object* v_string_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_string_1732_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_string_1732_);
lean_dec_ref(v_x_1729_);
v___x_1733_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1732_);
lean_dec_ref(v_string_1732_);
v___x_1734_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1733_, v_a_1731_);
lean_dec_ref(v___x_1733_);
return v___x_1734_;
}
case 1:
{
lean_object* v_content_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1776_; 
v_content_1735_ = lean_ctor_get(v_x_1729_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_x_1729_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1737_ = v_x_1729_;
v_isShared_1738_ = v_isSharedCheck_1776_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_content_1735_);
lean_dec(v_x_1729_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1776_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 9);
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_content_1735_);
v___x_1740_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; lean_object* v_snd_1742_; lean_object* v_fst_1743_; lean_object* v_fst_1744_; lean_object* v_snd_1745_; uint8_t v_inEmph_1747_; uint8_t v_inBold_1748_; uint8_t v_inLink_1749_; lean_object* v_linePrefix_1750_; lean_object* v___y_1751_; lean_object* v___x_1762_; uint8_t v_inEmph_1763_; 
v___x_1741_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1740_);
v_snd_1742_ = lean_ctor_get(v___x_1741_, 1);
lean_inc(v_snd_1742_);
v_fst_1743_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_fst_1743_);
lean_dec_ref(v___x_1741_);
v_fst_1744_ = lean_ctor_get(v_snd_1742_, 0);
lean_inc(v_fst_1744_);
v_snd_1745_ = lean_ctor_get(v_snd_1742_, 1);
lean_inc(v_snd_1745_);
lean_dec(v_snd_1742_);
v___x_1762_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_1743_, v_a_1731_);
lean_dec(v_fst_1743_);
v_inEmph_1763_ = lean_ctor_get_uint8(v_a_1730_, sizeof(void*)*1);
if (v_inEmph_1763_ == 0)
{
lean_object* v_snd_1764_; uint8_t v_inBold_1765_; uint8_t v_inLink_1766_; lean_object* v_linePrefix_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v_snd_1770_; 
v_snd_1764_ = lean_ctor_get(v___x_1762_, 1);
lean_inc(v_snd_1764_);
lean_dec_ref(v___x_1762_);
v_inBold_1765_ = lean_ctor_get_uint8(v_a_1730_, sizeof(void*)*1 + 1);
v_inLink_1766_ = lean_ctor_get_uint8(v_a_1730_, sizeof(void*)*1 + 2);
v_linePrefix_1767_ = lean_ctor_get(v_a_1730_, 0);
v___x_1768_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0));
v___x_1769_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1768_, v_snd_1764_);
v_snd_1770_ = lean_ctor_get(v___x_1769_, 1);
lean_inc(v_snd_1770_);
lean_dec_ref(v___x_1769_);
v_inEmph_1747_ = v_inEmph_1763_;
v_inBold_1748_ = v_inBold_1765_;
v_inLink_1749_ = v_inLink_1766_;
v_linePrefix_1750_ = v_linePrefix_1767_;
v___y_1751_ = v_snd_1770_;
goto v___jp_1746_;
}
else
{
lean_object* v_snd_1771_; uint8_t v_inBold_1772_; uint8_t v_inLink_1773_; lean_object* v_linePrefix_1774_; 
v_snd_1771_ = lean_ctor_get(v___x_1762_, 1);
lean_inc(v_snd_1771_);
lean_dec_ref(v___x_1762_);
v_inBold_1772_ = lean_ctor_get_uint8(v_a_1730_, sizeof(void*)*1 + 1);
v_inLink_1773_ = lean_ctor_get_uint8(v_a_1730_, sizeof(void*)*1 + 2);
v_linePrefix_1774_ = lean_ctor_get(v_a_1730_, 0);
v_inEmph_1747_ = v_inEmph_1763_;
v_inBold_1748_ = v_inBold_1772_;
v_inLink_1749_ = v_inLink_1773_;
v_linePrefix_1750_ = v_linePrefix_1774_;
v___y_1751_ = v_snd_1771_;
goto v___jp_1746_;
}
v___jp_1746_:
{
uint8_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = 1;
lean_inc_ref(v_linePrefix_1750_);
v___x_1753_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1753_, 0, v_linePrefix_1750_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*1, v___x_1752_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*1 + 1, v_inBold_1748_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*1 + 2, v_inLink_1749_);
v___x_1754_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_fst_1744_, v___x_1753_, v___y_1751_);
lean_dec_ref(v___x_1753_);
if (v_inEmph_1747_ == 0)
{
lean_object* v_snd_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v_snd_1758_; lean_object* v___x_1759_; 
v_snd_1755_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_snd_1755_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0));
v___x_1757_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1756_, v_snd_1755_);
v_snd_1758_ = lean_ctor_get(v___x_1757_, 1);
lean_inc(v_snd_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1745_, v_snd_1758_);
lean_dec(v_snd_1745_);
return v___x_1759_;
}
else
{
lean_object* v_snd_1760_; lean_object* v___x_1761_; 
v_snd_1760_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_snd_1760_);
lean_dec_ref(v___x_1754_);
v___x_1761_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1745_, v_snd_1760_);
lean_dec(v_snd_1745_);
return v___x_1761_;
}
}
}
}
}
case 2:
{
lean_object* v_content_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1815_; 
v_content_1777_ = lean_ctor_get(v_x_1729_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_x_1729_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1779_ = v_x_1729_;
v_isShared_1780_ = v_isSharedCheck_1815_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_content_1777_);
lean_dec(v_x_1729_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1815_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set_tag(v___x_1779_, 9);
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_content_1777_);
v___x_1782_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1783_; lean_object* v_snd_1784_; lean_object* v_fst_1785_; lean_object* v_fst_1786_; lean_object* v_snd_1787_; uint8_t v_inBold_1789_; uint8_t v_inLink_1790_; lean_object* v_linePrefix_1791_; lean_object* v___y_1792_; lean_object* v___x_1803_; uint8_t v_inBold_1804_; 
v___x_1783_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1782_);
v_snd_1784_ = lean_ctor_get(v___x_1783_, 1);
lean_inc(v_snd_1784_);
v_fst_1785_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_fst_1785_);
lean_dec_ref(v___x_1783_);
v_fst_1786_ = lean_ctor_get(v_snd_1784_, 0);
lean_inc(v_fst_1786_);
v_snd_1787_ = lean_ctor_get(v_snd_1784_, 1);
lean_inc(v_snd_1787_);
lean_dec(v_snd_1784_);
v___x_1803_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_1785_, v_a_1731_);
lean_dec(v_fst_1785_);
v_inBold_1804_ = lean_ctor_get_uint8(v_a_1730_, sizeof(void*)*1 + 1);
if (v_inBold_1804_ == 0)
{
lean_object* v_snd_1805_; uint8_t v_inLink_1806_; lean_object* v_linePrefix_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_snd_1810_; 
v_snd_1805_ = lean_ctor_get(v___x_1803_, 1);
lean_inc(v_snd_1805_);
lean_dec_ref(v___x_1803_);
v_inLink_1806_ = lean_ctor_get_uint8(v_a_1730_, sizeof(void*)*1 + 2);
v_linePrefix_1807_ = lean_ctor_get(v_a_1730_, 0);
v___x_1808_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1));
v___x_1809_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1808_, v_snd_1805_);
v_snd_1810_ = lean_ctor_get(v___x_1809_, 1);
lean_inc(v_snd_1810_);
lean_dec_ref(v___x_1809_);
v_inBold_1789_ = v_inBold_1804_;
v_inLink_1790_ = v_inLink_1806_;
v_linePrefix_1791_ = v_linePrefix_1807_;
v___y_1792_ = v_snd_1810_;
goto v___jp_1788_;
}
else
{
lean_object* v_snd_1811_; uint8_t v_inLink_1812_; lean_object* v_linePrefix_1813_; 
v_snd_1811_ = lean_ctor_get(v___x_1803_, 1);
lean_inc(v_snd_1811_);
lean_dec_ref(v___x_1803_);
v_inLink_1812_ = lean_ctor_get_uint8(v_a_1730_, sizeof(void*)*1 + 2);
v_linePrefix_1813_ = lean_ctor_get(v_a_1730_, 0);
v_inBold_1789_ = v_inBold_1804_;
v_inLink_1790_ = v_inLink_1812_;
v_linePrefix_1791_ = v_linePrefix_1813_;
v___y_1792_ = v_snd_1811_;
goto v___jp_1788_;
}
v___jp_1788_:
{
uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = 1;
lean_inc_ref(v_linePrefix_1791_);
v___x_1794_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1794_, 0, v_linePrefix_1791_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*1, v___x_1793_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*1 + 1, v_inBold_1789_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*1 + 2, v_inLink_1790_);
v___x_1795_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_fst_1786_, v___x_1794_, v___y_1792_);
lean_dec_ref(v___x_1794_);
if (v_inBold_1789_ == 0)
{
lean_object* v_snd_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v_snd_1799_; lean_object* v___x_1800_; 
v_snd_1796_ = lean_ctor_get(v___x_1795_, 1);
lean_inc(v_snd_1796_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1));
v___x_1798_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1797_, v_snd_1796_);
v_snd_1799_ = lean_ctor_get(v___x_1798_, 1);
lean_inc(v_snd_1799_);
lean_dec_ref(v___x_1798_);
v___x_1800_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1787_, v_snd_1799_);
lean_dec(v_snd_1787_);
return v___x_1800_;
}
else
{
lean_object* v_snd_1801_; lean_object* v___x_1802_; 
v_snd_1801_ = lean_ctor_get(v___x_1795_, 1);
lean_inc(v_snd_1801_);
lean_dec_ref(v___x_1795_);
v___x_1802_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1787_, v_snd_1801_);
lean_dec(v_snd_1787_);
return v___x_1802_;
}
}
}
}
}
case 3:
{
lean_object* v_string_1816_; lean_object* v___y_1818_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v_fst_1823_; uint8_t v___x_1824_; 
v_string_1816_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_string_1816_);
lean_dec_ref(v_x_1729_);
v___x_1821_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__2));
v___x_1822_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v___x_1821_, v_a_1731_);
v_fst_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_fst_1823_);
v___x_1824_ = lean_unbox(v_fst_1823_);
lean_dec(v_fst_1823_);
if (v___x_1824_ == 0)
{
lean_object* v_snd_1825_; 
v_snd_1825_ = lean_ctor_get(v___x_1822_, 1);
lean_inc(v_snd_1825_);
lean_dec_ref(v___x_1822_);
v___y_1818_ = v_snd_1825_;
goto v___jp_1817_;
}
else
{
lean_object* v_snd_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_snd_1829_; 
v_snd_1826_ = lean_ctor_get(v___x_1822_, 1);
lean_inc(v_snd_1826_);
lean_dec_ref(v___x_1822_);
v___x_1827_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__3));
v___x_1828_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1827_, v_snd_1826_);
v_snd_1829_ = lean_ctor_get(v___x_1828_, 1);
lean_inc(v_snd_1829_);
lean_dec_ref(v___x_1828_);
v___y_1818_ = v_snd_1829_;
goto v___jp_1817_;
}
v___jp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1816_);
v___x_1820_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1819_, v___y_1818_);
lean_dec_ref(v___x_1819_);
return v___x_1820_;
}
}
case 4:
{
uint8_t v_mode_1830_; 
v_mode_1830_ = lean_ctor_get_uint8(v_x_1729_, sizeof(void*)*1);
if (v_mode_1830_ == 0)
{
lean_object* v_string_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_string_1831_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_string_1831_);
lean_dec_ref(v_x_1729_);
v___x_1832_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__4));
v___x_1833_ = lean_string_append(v___x_1832_, v_string_1831_);
lean_dec_ref(v_string_1831_);
v___x_1834_ = lean_string_append(v___x_1833_, v___x_1832_);
v___x_1835_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1834_, v_a_1731_);
lean_dec_ref(v___x_1834_);
return v___x_1835_;
}
else
{
lean_object* v_string_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v_string_1836_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_string_1836_);
lean_dec_ref(v_x_1729_);
v___x_1837_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__5));
v___x_1838_ = lean_string_append(v___x_1837_, v_string_1836_);
lean_dec_ref(v_string_1836_);
v___x_1839_ = lean_string_append(v___x_1838_, v___x_1837_);
v___x_1840_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1839_, v_a_1731_);
lean_dec_ref(v___x_1839_);
return v___x_1840_;
}
}
case 5:
{
lean_object* v_string_1841_; lean_object* v_linePrefix_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v_string_1841_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_string_1841_);
lean_dec_ref(v_x_1729_);
v_linePrefix_1842_ = lean_ctor_get(v_a_1730_, 0);
v___x_1843_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1844_ = lean_string_append(v___x_1843_, v_linePrefix_1842_);
v___x_1845_ = lean_unsigned_to_nat(0u);
v___x_1846_ = lean_string_utf8_byte_size(v_string_1841_);
v___x_1847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1847_, 0, v_string_1841_);
lean_ctor_set(v___x_1847_, 1, v___x_1845_);
lean_ctor_set(v___x_1847_, 2, v___x_1846_);
v___x_1848_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v___x_1847_, v___x_1844_);
lean_dec_ref(v___x_1844_);
v___x_1849_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1848_, v_a_1731_);
lean_dec_ref(v___x_1848_);
return v___x_1849_;
}
case 6:
{
uint8_t v_inLink_1850_; 
v_inLink_1850_ = lean_ctor_get_uint8(v_a_1730_, sizeof(void*)*1 + 2);
if (v_inLink_1850_ == 0)
{
lean_object* v_content_1851_; lean_object* v_url_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v_snd_1855_; lean_object* v___x_1856_; size_t v_sz_1857_; size_t v___x_1858_; lean_object* v___x_1859_; lean_object* v_snd_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v_snd_1863_; lean_object* v___x_1864_; lean_object* v_snd_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_content_1851_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_content_1851_);
v_url_1852_ = lean_ctor_get(v_x_1729_, 1);
lean_inc_ref(v_url_1852_);
lean_dec_ref(v_x_1729_);
v___x_1853_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__6));
v___x_1854_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1853_, v_a_1731_);
v_snd_1855_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_snd_1855_);
lean_dec_ref(v___x_1854_);
v___x_1856_ = lean_box(0);
v_sz_1857_ = lean_array_size(v_content_1851_);
v___x_1858_ = ((size_t)0ULL);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1851_, v_sz_1857_, v___x_1858_, v___x_1856_, v_a_1730_, v_snd_1855_);
lean_dec_ref(v_content_1851_);
v_snd_1860_ = lean_ctor_get(v___x_1859_, 1);
lean_inc(v_snd_1860_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7));
v___x_1862_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1861_, v_snd_1860_);
v_snd_1863_ = lean_ctor_get(v___x_1862_, 1);
lean_inc(v_snd_1863_);
lean_dec_ref(v___x_1862_);
v___x_1864_ = l_Lean_Doc_MarkdownM_push___redArg(v_url_1852_, v_snd_1863_);
lean_dec_ref(v_url_1852_);
v_snd_1865_ = lean_ctor_get(v___x_1864_, 1);
lean_inc(v_snd_1865_);
lean_dec_ref(v___x_1864_);
v___x_1866_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_1867_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1866_, v_snd_1865_);
return v___x_1867_;
}
else
{
lean_object* v_content_1868_; lean_object* v___x_1869_; size_t v_sz_1870_; size_t v___x_1871_; lean_object* v___x_1872_; lean_object* v_snd_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_content_1868_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_content_1868_);
lean_dec_ref(v_x_1729_);
v___x_1869_ = lean_box(0);
v_sz_1870_ = lean_array_size(v_content_1868_);
v___x_1871_ = ((size_t)0ULL);
v___x_1872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1868_, v_sz_1870_, v___x_1871_, v___x_1869_, v_a_1730_, v_a_1731_);
lean_dec_ref(v_content_1868_);
v_snd_1873_ = lean_ctor_get(v___x_1872_, 1);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v___x_1872_, 0);
lean_dec(v_unused_1881_);
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_snd_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1869_);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_snd_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
case 7:
{
lean_object* v_name_1882_; lean_object* v_content_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v_snd_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1928_; 
v_name_1882_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_name_1882_);
v_content_1883_ = lean_ctor_get(v_x_1729_, 1);
lean_inc_ref(v_content_1883_);
lean_dec_ref(v_x_1729_);
v___x_1884_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__9));
v___x_1885_ = lean_string_append(v___x_1884_, v_name_1882_);
v___x_1886_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10));
v___x_1887_ = lean_string_append(v___x_1885_, v___x_1886_);
v___x_1888_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1887_, v_a_1731_);
lean_dec_ref(v___x_1887_);
v_snd_1889_ = lean_ctor_get(v___x_1888_, 1);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; 
v_unused_1929_ = lean_ctor_get(v___x_1888_, 0);
lean_dec(v_unused_1929_);
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1928_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snd_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1928_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_snd_1894_; lean_object* v___y_1913_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = lean_array_get_size(v_content_1883_);
v___x_1917_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11));
v___x_1918_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13));
v___x_1919_ = lean_nat_dec_lt(v___x_1915_, v___x_1916_);
if (v___x_1919_ == 0)
{
lean_dec_ref(v_content_1883_);
v_snd_1894_ = v___x_1918_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_nat_dec_le(v___x_1916_, v___x_1916_);
if (v___x_1921_ == 0)
{
if (v___x_1919_ == 0)
{
lean_dec_ref(v_content_1883_);
v_snd_1894_ = v___x_1918_;
goto v___jp_1893_;
}
else
{
size_t v___x_1922_; size_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = ((size_t)0ULL);
v___x_1923_ = lean_usize_of_nat(v___x_1916_);
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1883_, v___x_1922_, v___x_1923_, v___x_1920_, v___x_1917_, v___x_1918_);
lean_dec_ref(v_content_1883_);
v___y_1913_ = v___x_1924_;
goto v___jp_1912_;
}
}
else
{
size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = ((size_t)0ULL);
v___x_1926_ = lean_usize_of_nat(v___x_1916_);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1883_, v___x_1925_, v___x_1926_, v___x_1920_, v___x_1917_, v___x_1918_);
lean_dec_ref(v_content_1883_);
v___y_1913_ = v___x_1927_;
goto v___jp_1912_;
}
}
v___jp_1893_:
{
lean_object* v_priorBlocks_1895_; lean_object* v_currentBlock_1896_; lean_object* v_footnotes_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1911_; 
v_priorBlocks_1895_ = lean_ctor_get(v_snd_1889_, 0);
v_currentBlock_1896_ = lean_ctor_get(v_snd_1889_, 1);
v_footnotes_1897_ = lean_ctor_get(v_snd_1889_, 2);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_snd_1889_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1899_ = v_snd_1889_;
v_isShared_1900_ = v_isSharedCheck_1911_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_footnotes_1897_);
lean_inc(v_currentBlock_1896_);
lean_inc(v_priorBlocks_1895_);
lean_dec(v_snd_1889_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1911_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1901_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(v_snd_1894_);
v___x_1902_ = lean_box(0);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 1, v___x_1901_);
lean_ctor_set(v___x_1891_, 0, v_name_1882_);
v___x_1904_ = v___x_1891_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_name_1882_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v___x_1901_);
v___x_1904_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_array_push(v_footnotes_1897_, v___x_1904_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 2, v___x_1905_);
v___x_1907_ = v___x_1899_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_priorBlocks_1895_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_currentBlock_1896_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1902_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
return v___x_1908_;
}
}
}
}
v___jp_1912_:
{
lean_object* v_snd_1914_; 
v_snd_1914_ = lean_ctor_get(v___y_1913_, 1);
lean_inc(v_snd_1914_);
lean_dec_ref(v___y_1913_);
v_snd_1894_ = v_snd_1914_;
goto v___jp_1893_;
}
}
}
case 8:
{
lean_object* v_alt_1930_; lean_object* v_url_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v_alt_1930_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_alt_1930_);
v_url_1931_ = lean_ctor_get(v_x_1729_, 1);
lean_inc_ref(v_url_1931_);
lean_dec_ref(v_x_1729_);
v___x_1932_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__14));
v___x_1933_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1930_);
lean_dec_ref(v_alt_1930_);
v___x_1934_ = lean_string_append(v___x_1932_, v___x_1933_);
lean_dec_ref(v___x_1933_);
v___x_1935_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7));
v___x_1936_ = lean_string_append(v___x_1934_, v___x_1935_);
v___x_1937_ = lean_string_append(v___x_1936_, v_url_1931_);
lean_dec_ref(v_url_1931_);
v___x_1938_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_1939_ = lean_string_append(v___x_1937_, v___x_1938_);
v___x_1940_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1939_, v_a_1731_);
lean_dec_ref(v___x_1939_);
return v___x_1940_;
}
case 9:
{
lean_object* v_content_1941_; lean_object* v___x_1942_; size_t v_sz_1943_; size_t v___x_1944_; lean_object* v___x_1945_; lean_object* v_snd_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_content_1941_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_content_1941_);
lean_dec_ref(v_x_1729_);
v___x_1942_ = lean_box(0);
v_sz_1943_ = lean_array_size(v_content_1941_);
v___x_1944_ = ((size_t)0ULL);
v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1941_, v_sz_1943_, v___x_1944_, v___x_1942_, v_a_1730_, v_a_1731_);
lean_dec_ref(v_content_1941_);
v_snd_1946_ = lean_ctor_get(v___x_1945_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; 
v_unused_1954_ = lean_ctor_get(v___x_1945_, 0);
lean_dec(v_unused_1954_);
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_snd_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1942_);
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_snd_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
default: 
{
lean_object* v_content_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_content_1955_ = lean_ctor_get(v_x_1729_, 1);
lean_inc_ref(v_content_1955_);
lean_dec_ref(v_x_1729_);
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = lean_array_get_size(v_content_1955_);
v___x_1958_ = lean_box(0);
v___x_1959_ = lean_nat_dec_lt(v___x_1956_, v___x_1957_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; 
lean_dec_ref(v_content_1955_);
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set(v___x_1960_, 1, v_a_1731_);
return v___x_1960_;
}
else
{
uint8_t v___x_1961_; 
v___x_1961_ = lean_nat_dec_le(v___x_1957_, v___x_1957_);
if (v___x_1961_ == 0)
{
if (v___x_1959_ == 0)
{
lean_object* v___x_1962_; 
lean_dec_ref(v_content_1955_);
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1958_);
lean_ctor_set(v___x_1962_, 1, v_a_1731_);
return v___x_1962_;
}
else
{
size_t v___x_1963_; size_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = lean_usize_of_nat(v___x_1957_);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1955_, v___x_1963_, v___x_1964_, v___x_1958_, v_a_1730_, v_a_1731_);
lean_dec_ref(v_content_1955_);
return v___x_1965_;
}
}
else
{
size_t v___x_1966_; size_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = ((size_t)0ULL);
v___x_1967_ = lean_usize_of_nat(v___x_1957_);
v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1955_, v___x_1966_, v___x_1967_, v___x_1958_, v_a_1730_, v_a_1731_);
lean_dec_ref(v_content_1955_);
return v___x_1968_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(lean_object* v_as_1969_, size_t v_i_1970_, size_t v_stop_1971_, lean_object* v_b_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_usize_dec_eq(v_i_1970_, v_stop_1971_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v_fst_1978_; lean_object* v_snd_1979_; size_t v___x_1980_; size_t v___x_1981_; 
v___x_1976_ = lean_array_uget_borrowed(v_as_1969_, v_i_1970_);
lean_inc(v___x_1976_);
v___x_1977_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_1976_, v___y_1973_, v___y_1974_);
v_fst_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_fst_1978_);
v_snd_1979_ = lean_ctor_get(v___x_1977_, 1);
lean_inc(v_snd_1979_);
lean_dec_ref(v___x_1977_);
v___x_1980_ = ((size_t)1ULL);
v___x_1981_ = lean_usize_add(v_i_1970_, v___x_1980_);
v_i_1970_ = v___x_1981_;
v_b_1972_ = v_fst_1978_;
v___y_1974_ = v_snd_1979_;
goto _start;
}
else
{
lean_object* v___x_1983_; 
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v_b_1972_);
lean_ctor_set(v___x_1983_, 1, v___y_1974_);
return v___x_1983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1984_, lean_object* v_i_1985_, lean_object* v_stop_1986_, lean_object* v_b_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
size_t v_i_boxed_1990_; size_t v_stop_boxed_1991_; lean_object* v_res_1992_; 
v_i_boxed_1990_ = lean_unbox_usize(v_i_1985_);
lean_dec(v_i_1985_);
v_stop_boxed_1991_ = lean_unbox_usize(v_stop_1986_);
lean_dec(v_stop_1986_);
v_res_1992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_as_1984_, v_i_boxed_1990_, v_stop_boxed_1991_, v_b_1987_, v___y_1988_, v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec_ref(v_as_1984_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2___boxed(lean_object* v_as_1993_, lean_object* v_sz_1994_, lean_object* v_i_1995_, lean_object* v_b_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
size_t v_sz_boxed_1999_; size_t v_i_boxed_2000_; lean_object* v_res_2001_; 
v_sz_boxed_1999_ = lean_unbox_usize(v_sz_1994_);
lean_dec(v_sz_1994_);
v_i_boxed_2000_ = lean_unbox_usize(v_i_1995_);
lean_dec(v_i_1995_);
v_res_2001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_as_1993_, v_sz_boxed_1999_, v_i_boxed_2000_, v_b_1996_, v___y_1997_, v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec_ref(v_as_1993_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___boxed(lean_object* v_x_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_x_2002_, v_a_2003_, v_a_2004_);
lean_dec_ref(v_a_2003_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(lean_object* v_as_2008_, size_t v_sz_2009_, size_t v_i_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_usize_dec_lt(v_i_2010_, v_sz_2009_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v_b_2011_);
lean_ctor_set(v___x_2015_, 1, v___y_2013_);
return v___x_2015_;
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2017_; lean_object* v_snd_2018_; lean_object* v___x_2019_; size_t v___x_2020_; size_t v___x_2021_; 
v_a_2016_ = lean_array_uget_borrowed(v_as_2008_, v_i_2010_);
lean_inc(v_a_2016_);
v___x_2017_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v_a_2016_, v___y_2012_, v___y_2013_);
v_snd_2018_ = lean_ctor_get(v___x_2017_, 1);
lean_inc(v_snd_2018_);
lean_dec_ref(v___x_2017_);
v___x_2019_ = lean_box(0);
v___x_2020_ = ((size_t)1ULL);
v___x_2021_ = lean_usize_add(v_i_2010_, v___x_2020_);
v_i_2010_ = v___x_2021_;
v_b_2011_ = v___x_2019_;
v___y_2013_ = v_snd_2018_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(lean_object* v_as_2023_, size_t v_sz_2024_, size_t v_i_2025_, lean_object* v_b_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_usize_dec_lt(v_i_2025_, v_sz_2024_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v_b_2026_);
lean_ctor_set(v___x_2030_, 1, v___y_2028_);
return v___x_2030_;
}
else
{
uint8_t v_inEmph_2031_; uint8_t v_inBold_2032_; uint8_t v_inLink_2033_; lean_object* v_linePrefix_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v_snd_2038_; lean_object* v___x_2039_; lean_object* v_a_2040_; size_t v_sz_2041_; size_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v_snd_2047_; size_t v___x_2048_; size_t v___x_2049_; 
v_inEmph_2031_ = lean_ctor_get_uint8(v___y_2027_, sizeof(void*)*1);
v_inBold_2032_ = lean_ctor_get_uint8(v___y_2027_, sizeof(void*)*1 + 1);
v_inLink_2033_ = lean_ctor_get_uint8(v___y_2027_, sizeof(void*)*1 + 2);
v_linePrefix_2034_ = lean_ctor_get(v___y_2027_, 0);
v___x_2035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0));
lean_inc_ref_n(v_linePrefix_2034_, 2);
v___x_2036_ = lean_string_append(v_linePrefix_2034_, v___x_2035_);
v___x_2037_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2036_, v___y_2028_);
lean_dec_ref(v___x_2036_);
v_snd_2038_ = lean_ctor_get(v___x_2037_, 1);
lean_inc(v_snd_2038_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = lean_box(0);
v_a_2040_ = lean_array_uget_borrowed(v_as_2023_, v_i_2025_);
v_sz_2041_ = lean_array_size(v_a_2040_);
v___x_2042_ = ((size_t)0ULL);
v___x_2043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
v___x_2044_ = lean_string_append(v_linePrefix_2034_, v___x_2043_);
v___x_2045_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*1, v_inEmph_2031_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*1 + 1, v_inBold_2032_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*1 + 2, v_inLink_2033_);
v___x_2046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_a_2040_, v_sz_2041_, v___x_2042_, v___x_2039_, v___x_2045_, v_snd_2038_);
lean_dec_ref(v___x_2045_);
v_snd_2047_ = lean_ctor_get(v___x_2046_, 1);
lean_inc(v_snd_2047_);
lean_dec_ref(v___x_2046_);
v___x_2048_ = ((size_t)1ULL);
v___x_2049_ = lean_usize_add(v_i_2025_, v___x_2048_);
v_i_2025_ = v___x_2049_;
v_b_2026_ = v___x_2039_;
v___y_2028_ = v_snd_2047_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(lean_object* v_as_2052_, size_t v_sz_2053_, size_t v_i_2054_, lean_object* v_b_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
uint8_t v___x_2058_; 
v___x_2058_ = lean_usize_dec_lt(v_i_2054_, v_sz_2053_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v_b_2055_);
lean_ctor_set(v___x_2059_, 1, v___y_2057_);
return v___x_2059_;
}
else
{
uint8_t v_inEmph_2060_; uint8_t v_inBold_2061_; uint8_t v_inLink_2062_; lean_object* v_linePrefix_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v_snd_2069_; lean_object* v_a_2070_; lean_object* v___x_2071_; size_t v_sz_2072_; size_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v_snd_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; size_t v___x_2081_; size_t v___x_2082_; 
v_inEmph_2060_ = lean_ctor_get_uint8(v___y_2056_, sizeof(void*)*1);
v_inBold_2061_ = lean_ctor_get_uint8(v___y_2056_, sizeof(void*)*1 + 1);
v_inLink_2062_ = lean_ctor_get_uint8(v___y_2056_, sizeof(void*)*1 + 2);
v_linePrefix_2063_ = lean_ctor_get(v___y_2056_, 0);
lean_inc(v_b_2055_);
v___x_2064_ = l_Nat_reprFast(v_b_2055_);
v___x_2065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0));
v___x_2066_ = lean_string_append(v___x_2064_, v___x_2065_);
lean_inc_ref_n(v_linePrefix_2063_, 2);
v___x_2067_ = lean_string_append(v_linePrefix_2063_, v___x_2066_);
lean_dec_ref(v___x_2066_);
v___x_2068_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2067_, v___y_2057_);
lean_dec_ref(v___x_2067_);
v_snd_2069_ = lean_ctor_get(v___x_2068_, 1);
lean_inc(v_snd_2069_);
lean_dec_ref(v___x_2068_);
v_a_2070_ = lean_array_uget_borrowed(v_as_2052_, v_i_2054_);
v___x_2071_ = lean_box(0);
v_sz_2072_ = lean_array_size(v_a_2070_);
v___x_2073_ = ((size_t)0ULL);
v___x_2074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
v___x_2075_ = lean_string_append(v_linePrefix_2063_, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*1, v_inEmph_2060_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*1 + 1, v_inBold_2061_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*1 + 2, v_inLink_2062_);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_a_2070_, v_sz_2072_, v___x_2073_, v___x_2071_, v___x_2076_, v_snd_2069_);
lean_dec_ref(v___x_2076_);
v_snd_2078_ = lean_ctor_get(v___x_2077_, 1);
lean_inc(v_snd_2078_);
lean_dec_ref(v___x_2077_);
v___x_2079_ = lean_unsigned_to_nat(1u);
v___x_2080_ = lean_nat_add(v_b_2055_, v___x_2079_);
lean_dec(v_b_2055_);
v___x_2081_ = ((size_t)1ULL);
v___x_2082_ = lean_usize_add(v_i_2054_, v___x_2081_);
v_i_2054_ = v___x_2082_;
v_b_2055_ = v___x_2080_;
v___y_2057_ = v_snd_2078_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(lean_object* v_as_2087_, size_t v_sz_2088_, size_t v_i_2089_, lean_object* v_b_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
uint8_t v___x_2093_; 
v___x_2093_ = lean_usize_dec_lt(v_i_2089_, v_sz_2088_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v_b_2090_);
lean_ctor_set(v___x_2094_, 1, v___y_2092_);
return v___x_2094_;
}
else
{
uint8_t v_inEmph_2095_; uint8_t v_inBold_2096_; uint8_t v_inLink_2097_; lean_object* v_linePrefix_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v_snd_2102_; lean_object* v_a_2103_; lean_object* v_term_2104_; lean_object* v_desc_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v_snd_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_snd_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v_snd_2117_; lean_object* v___x_2118_; lean_object* v_snd_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v_snd_2122_; lean_object* v___x_2123_; size_t v___x_2124_; size_t v___x_2125_; 
v_inEmph_2095_ = lean_ctor_get_uint8(v___y_2091_, sizeof(void*)*1);
v_inBold_2096_ = lean_ctor_get_uint8(v___y_2091_, sizeof(void*)*1 + 1);
v_inLink_2097_ = lean_ctor_get_uint8(v___y_2091_, sizeof(void*)*1 + 2);
v_linePrefix_2098_ = lean_ctor_get(v___y_2091_, 0);
v___x_2099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0));
lean_inc_ref_n(v_linePrefix_2098_, 2);
v___x_2100_ = lean_string_append(v_linePrefix_2098_, v___x_2099_);
v___x_2101_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2100_, v___y_2092_);
lean_dec_ref(v___x_2100_);
v_snd_2102_ = lean_ctor_get(v___x_2101_, 1);
lean_inc(v_snd_2102_);
lean_dec_ref(v___x_2101_);
v_a_2103_ = lean_array_uget_borrowed(v_as_2087_, v_i_2089_);
v_term_2104_ = lean_ctor_get(v_a_2103_, 0);
v_desc_2105_ = lean_ctor_get(v_a_2103_, 1);
lean_inc_ref(v_term_2104_);
v___x_2106_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_term_2104_);
v___x_2107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
v___x_2108_ = lean_string_append(v_linePrefix_2098_, v___x_2107_);
lean_inc_ref(v___x_2108_);
v___x_2109_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set_uint8(v___x_2109_, sizeof(void*)*1, v_inEmph_2095_);
lean_ctor_set_uint8(v___x_2109_, sizeof(void*)*1 + 1, v_inBold_2096_);
lean_ctor_set_uint8(v___x_2109_, sizeof(void*)*1 + 2, v_inLink_2097_);
v___x_2110_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_2106_, v___x_2109_, v_snd_2102_);
v_snd_2111_ = lean_ctor_get(v___x_2110_, 1);
lean_inc(v_snd_2111_);
lean_dec_ref(v___x_2110_);
v___x_2112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__1));
v___x_2113_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_2112_, v___x_2109_, v_snd_2111_);
v_snd_2114_ = lean_ctor_get(v___x_2113_, 1);
lean_inc(v_snd_2114_);
lean_dec_ref(v___x_2113_);
v___x_2115_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2116_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2115_, v_snd_2114_);
v_snd_2117_ = lean_ctor_get(v___x_2116_, 1);
lean_inc(v_snd_2117_);
lean_dec_ref(v___x_2116_);
v___x_2118_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2108_, v_snd_2117_);
lean_dec_ref(v___x_2108_);
v_snd_2119_ = lean_ctor_get(v___x_2118_, 1);
lean_inc(v_snd_2119_);
lean_dec_ref(v___x_2118_);
lean_inc_ref(v_desc_2105_);
v___x_2120_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2120_, 0, v_desc_2105_);
v___x_2121_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v___x_2120_, v___x_2109_, v_snd_2119_);
lean_dec_ref(v___x_2109_);
v_snd_2122_ = lean_ctor_get(v___x_2121_, 1);
lean_inc(v_snd_2122_);
lean_dec_ref(v___x_2121_);
v___x_2123_ = lean_box(0);
v___x_2124_ = ((size_t)1ULL);
v___x_2125_ = lean_usize_add(v_i_2089_, v___x_2124_);
v_i_2089_ = v___x_2125_;
v_b_2090_ = v___x_2123_;
v___y_2092_ = v_snd_2122_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(lean_object* v_x_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
switch(lean_obj_tag(v_x_2128_))
{
case 0:
{
lean_object* v_contents_2131_; lean_object* v___x_2132_; size_t v_sz_2133_; size_t v___x_2134_; lean_object* v___x_2135_; lean_object* v_snd_2136_; lean_object* v___x_2137_; 
v_contents_2131_ = lean_ctor_get(v_x_2128_, 0);
lean_inc_ref(v_contents_2131_);
lean_dec_ref(v_x_2128_);
v___x_2132_ = lean_box(0);
v_sz_2133_ = lean_array_size(v_contents_2131_);
v___x_2134_ = ((size_t)0ULL);
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_contents_2131_, v_sz_2133_, v___x_2134_, v___x_2132_, v_a_2129_, v_a_2130_);
lean_dec_ref(v_contents_2131_);
v_snd_2136_ = lean_ctor_get(v___x_2135_, 1);
lean_inc(v_snd_2136_);
lean_dec_ref(v___x_2135_);
v___x_2137_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2136_);
return v___x_2137_;
}
case 1:
{
lean_object* v_content_2138_; lean_object* v___y_2140_; lean_object* v___y_2141_; uint8_t v___y_2149_; lean_object* v_currentBlock_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v_content_2138_ = lean_ctor_get(v_x_2128_, 0);
lean_inc_ref(v_content_2138_);
lean_dec_ref(v_x_2128_);
v_currentBlock_2153_ = lean_ctor_get(v_a_2130_, 1);
v___x_2154_ = lean_string_utf8_byte_size(v_currentBlock_2153_);
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = lean_nat_dec_eq(v___x_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2157_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2158_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_2159_ = lean_nat_dec_le(v___x_2158_, v___x_2154_);
if (v___x_2159_ == 0)
{
v___y_2149_ = v___x_2156_;
goto v___jp_2148_;
}
else
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = lean_nat_sub(v___x_2154_, v___x_2158_);
v___x_2161_ = lean_string_memcmp(v_currentBlock_2153_, v___x_2157_, v___x_2160_, v___x_2155_, v___x_2158_);
lean_dec(v___x_2160_);
v___y_2149_ = v___x_2161_;
goto v___jp_2148_;
}
}
else
{
v___y_2149_ = v___x_2156_;
goto v___jp_2148_;
}
v___jp_2139_:
{
lean_object* v_linePrefix_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v_snd_2146_; lean_object* v___x_2147_; 
v_linePrefix_2142_ = lean_ctor_get(v___y_2140_, 0);
v___x_2143_ = lean_string_length(v_linePrefix_2142_);
v___x_2144_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v___x_2143_, v_content_2138_);
lean_dec_ref(v_content_2138_);
v___x_2145_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2144_, v___y_2141_);
lean_dec_ref(v___x_2144_);
v_snd_2146_ = lean_ctor_get(v___x_2145_, 1);
lean_inc(v_snd_2146_);
lean_dec_ref(v___x_2145_);
v___x_2147_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2146_);
return v___x_2147_;
}
v___jp_2148_:
{
if (v___y_2149_ == 0)
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v_snd_2152_; 
v___x_2150_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2151_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2150_, v_a_2130_);
v_snd_2152_ = lean_ctor_get(v___x_2151_, 1);
lean_inc(v_snd_2152_);
lean_dec_ref(v___x_2151_);
v___y_2140_ = v_a_2129_;
v___y_2141_ = v_snd_2152_;
goto v___jp_2139_;
}
else
{
v___y_2140_ = v_a_2129_;
v___y_2141_ = v_a_2130_;
goto v___jp_2139_;
}
}
}
case 2:
{
lean_object* v_items_2162_; lean_object* v___x_2163_; size_t v_sz_2164_; size_t v___x_2165_; lean_object* v___x_2166_; lean_object* v_snd_2167_; lean_object* v___x_2168_; 
v_items_2162_ = lean_ctor_get(v_x_2128_, 0);
lean_inc_ref(v_items_2162_);
lean_dec_ref(v_x_2128_);
v___x_2163_ = lean_box(0);
v_sz_2164_ = lean_array_size(v_items_2162_);
v___x_2165_ = ((size_t)0ULL);
v___x_2166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_items_2162_, v_sz_2164_, v___x_2165_, v___x_2163_, v_a_2129_, v_a_2130_);
lean_dec_ref(v_items_2162_);
v_snd_2167_ = lean_ctor_get(v___x_2166_, 1);
lean_inc(v_snd_2167_);
lean_dec_ref(v___x_2166_);
v___x_2168_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2167_);
return v___x_2168_;
}
case 3:
{
lean_object* v_start_2169_; lean_object* v_items_2170_; lean_object* v___y_2172_; lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v_start_2169_ = lean_ctor_get(v_x_2128_, 0);
lean_inc(v_start_2169_);
v_items_2170_ = lean_ctor_get(v_x_2128_, 1);
lean_inc_ref(v_items_2170_);
lean_dec_ref(v_x_2128_);
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = l_Int_toNat(v_start_2169_);
lean_dec(v_start_2169_);
v___x_2180_ = lean_nat_dec_le(v___x_2178_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_dec(v___x_2179_);
v___y_2172_ = v___x_2178_;
goto v___jp_2171_;
}
else
{
v___y_2172_ = v___x_2179_;
goto v___jp_2171_;
}
v___jp_2171_:
{
size_t v_sz_2173_; size_t v___x_2174_; lean_object* v___x_2175_; lean_object* v_snd_2176_; lean_object* v___x_2177_; 
v_sz_2173_ = lean_array_size(v_items_2170_);
v___x_2174_ = ((size_t)0ULL);
v___x_2175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_items_2170_, v_sz_2173_, v___x_2174_, v___y_2172_, v_a_2129_, v_a_2130_);
lean_dec_ref(v_items_2170_);
v_snd_2176_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_snd_2176_);
lean_dec_ref(v___x_2175_);
v___x_2177_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2176_);
return v___x_2177_;
}
}
case 4:
{
lean_object* v_items_2181_; lean_object* v___x_2182_; size_t v_sz_2183_; size_t v___x_2184_; lean_object* v___x_2185_; lean_object* v_snd_2186_; lean_object* v___x_2187_; 
v_items_2181_ = lean_ctor_get(v_x_2128_, 0);
lean_inc_ref(v_items_2181_);
lean_dec_ref(v_x_2128_);
v___x_2182_ = lean_box(0);
v_sz_2183_ = lean_array_size(v_items_2181_);
v___x_2184_ = ((size_t)0ULL);
v___x_2185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_items_2181_, v_sz_2183_, v___x_2184_, v___x_2182_, v_a_2129_, v_a_2130_);
lean_dec_ref(v_items_2181_);
v_snd_2186_ = lean_ctor_get(v___x_2185_, 1);
lean_inc(v_snd_2186_);
lean_dec_ref(v___x_2185_);
v___x_2187_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2186_);
return v___x_2187_;
}
case 5:
{
lean_object* v_items_2188_; uint8_t v_inEmph_2189_; uint8_t v_inBold_2190_; uint8_t v_inLink_2191_; lean_object* v_linePrefix_2192_; lean_object* v___x_2193_; size_t v_sz_2194_; size_t v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v_snd_2200_; lean_object* v___x_2201_; 
v_items_2188_ = lean_ctor_get(v_x_2128_, 0);
lean_inc_ref(v_items_2188_);
lean_dec_ref(v_x_2128_);
v_inEmph_2189_ = lean_ctor_get_uint8(v_a_2129_, sizeof(void*)*1);
v_inBold_2190_ = lean_ctor_get_uint8(v_a_2129_, sizeof(void*)*1 + 1);
v_inLink_2191_ = lean_ctor_get_uint8(v_a_2129_, sizeof(void*)*1 + 2);
v_linePrefix_2192_ = lean_ctor_get(v_a_2129_, 0);
v___x_2193_ = lean_box(0);
v_sz_2194_ = lean_array_size(v_items_2188_);
v___x_2195_ = ((size_t)0ULL);
v___x_2196_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0));
lean_inc_ref(v_linePrefix_2192_);
v___x_2197_ = lean_string_append(v_linePrefix_2192_, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
lean_ctor_set_uint8(v___x_2198_, sizeof(void*)*1, v_inEmph_2189_);
lean_ctor_set_uint8(v___x_2198_, sizeof(void*)*1 + 1, v_inBold_2190_);
lean_ctor_set_uint8(v___x_2198_, sizeof(void*)*1 + 2, v_inLink_2191_);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_items_2188_, v_sz_2194_, v___x_2195_, v___x_2193_, v___x_2198_, v_a_2130_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v_items_2188_);
v_snd_2200_ = lean_ctor_get(v___x_2199_, 1);
lean_inc(v_snd_2200_);
lean_dec_ref(v___x_2199_);
v___x_2201_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2200_);
return v___x_2201_;
}
case 6:
{
lean_object* v_content_2202_; lean_object* v___x_2203_; size_t v_sz_2204_; size_t v___x_2205_; lean_object* v___x_2206_; lean_object* v_snd_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
v_content_2202_ = lean_ctor_get(v_x_2128_, 0);
lean_inc_ref(v_content_2202_);
lean_dec_ref(v_x_2128_);
v___x_2203_ = lean_box(0);
v_sz_2204_ = lean_array_size(v_content_2202_);
v___x_2205_ = ((size_t)0ULL);
v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_content_2202_, v_sz_2204_, v___x_2205_, v___x_2203_, v_a_2129_, v_a_2130_);
lean_dec_ref(v_content_2202_);
v_snd_2207_ = lean_ctor_get(v___x_2206_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v___x_2206_, 0);
lean_dec(v_unused_2215_);
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_snd_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2203_);
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_snd_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
default: 
{
lean_object* v_content_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2237_; 
v_content_2216_ = lean_ctor_get(v_x_2128_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_x_2128_);
if (v_isSharedCheck_2237_ == 0)
{
lean_object* v_unused_2238_; 
v_unused_2238_ = lean_ctor_get(v_x_2128_, 0);
lean_dec(v_unused_2238_);
v___x_2218_ = v_x_2128_;
v_isShared_2219_ = v_isSharedCheck_2237_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_content_2216_);
lean_dec(v_x_2128_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2237_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2220_ = lean_unsigned_to_nat(0u);
v___x_2221_ = lean_array_get_size(v_content_2216_);
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_nat_dec_lt(v___x_2220_, v___x_2221_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2225_; 
lean_dec_ref(v_content_2216_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set_tag(v___x_2218_, 0);
lean_ctor_set(v___x_2218_, 1, v_a_2130_);
lean_ctor_set(v___x_2218_, 0, v___x_2222_);
v___x_2225_ = v___x_2218_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_a_2130_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
else
{
uint8_t v___x_2227_; 
v___x_2227_ = lean_nat_dec_le(v___x_2221_, v___x_2221_);
if (v___x_2227_ == 0)
{
if (v___x_2223_ == 0)
{
lean_object* v___x_2229_; 
lean_dec_ref(v_content_2216_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set_tag(v___x_2218_, 0);
lean_ctor_set(v___x_2218_, 1, v_a_2130_);
lean_ctor_set(v___x_2218_, 0, v___x_2222_);
v___x_2229_ = v___x_2218_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_a_2130_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
else
{
size_t v___x_2231_; size_t v___x_2232_; lean_object* v___x_2233_; 
lean_del_object(v___x_2218_);
v___x_2231_ = ((size_t)0ULL);
v___x_2232_ = lean_usize_of_nat(v___x_2221_);
v___x_2233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_content_2216_, v___x_2231_, v___x_2232_, v___x_2222_, v_a_2129_, v_a_2130_);
lean_dec_ref(v_content_2216_);
return v___x_2233_;
}
}
else
{
size_t v___x_2234_; size_t v___x_2235_; lean_object* v___x_2236_; 
lean_del_object(v___x_2218_);
v___x_2234_ = ((size_t)0ULL);
v___x_2235_ = lean_usize_of_nat(v___x_2221_);
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_content_2216_, v___x_2234_, v___x_2235_, v___x_2222_, v_a_2129_, v_a_2130_);
lean_dec_ref(v_content_2216_);
return v___x_2236_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(lean_object* v_as_2239_, size_t v_i_2240_, size_t v_stop_2241_, lean_object* v_b_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
uint8_t v___x_2245_; 
v___x_2245_ = lean_usize_dec_eq(v_i_2240_, v_stop_2241_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v_fst_2248_; lean_object* v_snd_2249_; size_t v___x_2250_; size_t v___x_2251_; 
v___x_2246_ = lean_array_uget_borrowed(v_as_2239_, v_i_2240_);
lean_inc(v___x_2246_);
v___x_2247_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v___x_2246_, v___y_2243_, v___y_2244_);
v_fst_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_fst_2248_);
v_snd_2249_ = lean_ctor_get(v___x_2247_, 1);
lean_inc(v_snd_2249_);
lean_dec_ref(v___x_2247_);
v___x_2250_ = ((size_t)1ULL);
v___x_2251_ = lean_usize_add(v_i_2240_, v___x_2250_);
v_i_2240_ = v___x_2251_;
v_b_2242_ = v_fst_2248_;
v___y_2244_ = v_snd_2249_;
goto _start;
}
else
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2253_, 0, v_b_2242_);
lean_ctor_set(v___x_2253_, 1, v___y_2244_);
return v___x_2253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___boxed(lean_object* v_as_2254_, lean_object* v_i_2255_, lean_object* v_stop_2256_, lean_object* v_b_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
size_t v_i_boxed_2260_; size_t v_stop_boxed_2261_; lean_object* v_res_2262_; 
v_i_boxed_2260_ = lean_unbox_usize(v_i_2255_);
lean_dec(v_i_2255_);
v_stop_boxed_2261_ = lean_unbox_usize(v_stop_2256_);
lean_dec(v_stop_2256_);
v_res_2262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_as_2254_, v_i_boxed_2260_, v_stop_boxed_2261_, v_b_2257_, v___y_2258_, v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v_as_2254_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2___boxed(lean_object* v_as_2263_, lean_object* v_sz_2264_, lean_object* v_i_2265_, lean_object* v_b_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
size_t v_sz_boxed_2269_; size_t v_i_boxed_2270_; lean_object* v_res_2271_; 
v_sz_boxed_2269_ = lean_unbox_usize(v_sz_2264_);
lean_dec(v_sz_2264_);
v_i_boxed_2270_ = lean_unbox_usize(v_i_2265_);
lean_dec(v_i_2265_);
v_res_2271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_as_2263_, v_sz_boxed_2269_, v_i_boxed_2270_, v_b_2266_, v___y_2267_, v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec_ref(v_as_2263_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___boxed(lean_object* v_as_2272_, lean_object* v_sz_2273_, lean_object* v_i_2274_, lean_object* v_b_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
size_t v_sz_boxed_2278_; size_t v_i_boxed_2279_; lean_object* v_res_2280_; 
v_sz_boxed_2278_ = lean_unbox_usize(v_sz_2273_);
lean_dec(v_sz_2273_);
v_i_boxed_2279_ = lean_unbox_usize(v_i_2274_);
lean_dec(v_i_2274_);
v_res_2280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_as_2272_, v_sz_boxed_2278_, v_i_boxed_2279_, v_b_2275_, v___y_2276_, v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec_ref(v_as_2272_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___boxed(lean_object* v_as_2281_, lean_object* v_sz_2282_, lean_object* v_i_2283_, lean_object* v_b_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
size_t v_sz_boxed_2287_; size_t v_i_boxed_2288_; lean_object* v_res_2289_; 
v_sz_boxed_2287_ = lean_unbox_usize(v_sz_2282_);
lean_dec(v_sz_2282_);
v_i_boxed_2288_ = lean_unbox_usize(v_i_2283_);
lean_dec(v_i_2283_);
v_res_2289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_as_2281_, v_sz_boxed_2287_, v_i_boxed_2288_, v_b_2284_, v___y_2285_, v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec_ref(v_as_2281_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___boxed(lean_object* v_as_2290_, lean_object* v_sz_2291_, lean_object* v_i_2292_, lean_object* v_b_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
size_t v_sz_boxed_2296_; size_t v_i_boxed_2297_; lean_object* v_res_2298_; 
v_sz_boxed_2296_ = lean_unbox_usize(v_sz_2291_);
lean_dec(v_sz_2291_);
v_i_boxed_2297_ = lean_unbox_usize(v_i_2292_);
lean_dec(v_i_2292_);
v_res_2298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_as_2290_, v_sz_boxed_2296_, v_i_boxed_2297_, v_b_2293_, v___y_2294_, v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec_ref(v_as_2290_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___boxed(lean_object* v_x_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v_x_2299_, v_a_2300_, v_a_2301_);
lean_dec_ref(v_a_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(lean_object* v_x_2303_, lean_object* v_x_2304_){
_start:
{
lean_object* v_zero_2305_; uint8_t v_isZero_2306_; 
v_zero_2305_ = lean_unsigned_to_nat(0u);
v_isZero_2306_ = lean_nat_dec_eq(v_x_2303_, v_zero_2305_);
if (v_isZero_2306_ == 1)
{
lean_dec(v_x_2303_);
return v_x_2304_;
}
else
{
uint32_t v___x_2307_; lean_object* v_one_2308_; lean_object* v_n_2309_; lean_object* v___x_2310_; 
v___x_2307_ = 35;
v_one_2308_ = lean_unsigned_to_nat(1u);
v_n_2309_ = lean_nat_sub(v_x_2303_, v_one_2308_);
lean_dec(v_x_2303_);
v___x_2310_ = lean_string_push(v_x_2304_, v___x_2307_);
v_x_2303_ = v_n_2309_;
v_x_2304_ = v___x_2310_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(lean_object* v_level_2313_, lean_object* v_part_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v_snd_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v_snd_2325_; lean_object* v_title_2326_; lean_object* v_content_2327_; lean_object* v_subParts_2328_; lean_object* v___x_2329_; size_t v_sz_2330_; size_t v___x_2331_; lean_object* v___x_2332_; lean_object* v_snd_2333_; lean_object* v___x_2334_; lean_object* v_snd_2335_; size_t v_sz_2336_; lean_object* v___x_2337_; lean_object* v_snd_2338_; lean_object* v___x_2339_; lean_object* v_snd_2340_; size_t v_sz_2341_; lean_object* v___x_2342_; lean_object* v_snd_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
v___x_2317_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_2318_ = lean_unsigned_to_nat(1u);
v___x_2319_ = lean_nat_add(v_level_2313_, v___x_2318_);
lean_inc(v___x_2319_);
v___x_2320_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v___x_2319_, v___x_2317_);
v___x_2321_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2320_, v_a_2316_);
lean_dec_ref(v___x_2320_);
v_snd_2322_ = lean_ctor_get(v___x_2321_, 1);
lean_inc(v_snd_2322_);
lean_dec_ref(v___x_2321_);
v___x_2323_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0));
v___x_2324_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2323_, v_snd_2322_);
v_snd_2325_ = lean_ctor_get(v___x_2324_, 1);
lean_inc(v_snd_2325_);
lean_dec_ref(v___x_2324_);
v_title_2326_ = lean_ctor_get(v_part_2314_, 0);
v_content_2327_ = lean_ctor_get(v_part_2314_, 3);
v_subParts_2328_ = lean_ctor_get(v_part_2314_, 4);
v___x_2329_ = lean_box(0);
v_sz_2330_ = lean_array_size(v_title_2326_);
v___x_2331_ = ((size_t)0ULL);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_title_2326_, v_sz_2330_, v___x_2331_, v___x_2329_, v_a_2315_, v_snd_2325_);
v_snd_2333_ = lean_ctor_get(v___x_2332_, 1);
lean_inc(v_snd_2333_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2333_);
v_snd_2335_ = lean_ctor_get(v___x_2334_, 1);
lean_inc(v_snd_2335_);
lean_dec_ref(v___x_2334_);
v_sz_2336_ = lean_array_size(v_content_2327_);
v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_content_2327_, v_sz_2336_, v___x_2331_, v___x_2329_, v_a_2315_, v_snd_2335_);
v_snd_2338_ = lean_ctor_get(v___x_2337_, 1);
lean_inc(v_snd_2338_);
lean_dec_ref(v___x_2337_);
v___x_2339_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2338_);
v_snd_2340_ = lean_ctor_get(v___x_2339_, 1);
lean_inc(v_snd_2340_);
lean_dec_ref(v___x_2339_);
v_sz_2341_ = lean_array_size(v_subParts_2328_);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2319_, v_subParts_2328_, v_sz_2341_, v___x_2331_, v___x_2329_, v_a_2315_, v_snd_2340_);
lean_dec(v___x_2319_);
v_snd_2343_ = lean_ctor_get(v___x_2342_, 1);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2350_ == 0)
{
lean_object* v_unused_2351_; 
v_unused_2351_ = lean_ctor_get(v___x_2342_, 0);
lean_dec(v_unused_2351_);
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_snd_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2329_);
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_snd_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(lean_object* v___x_2352_, lean_object* v_as_2353_, size_t v_sz_2354_, size_t v_i_2355_, lean_object* v_b_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
uint8_t v___x_2359_; 
v___x_2359_ = lean_usize_dec_lt(v_i_2355_, v_sz_2354_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2360_, 0, v_b_2356_);
lean_ctor_set(v___x_2360_, 1, v___y_2358_);
return v___x_2360_;
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2362_; lean_object* v_snd_2363_; lean_object* v___x_2364_; size_t v___x_2365_; size_t v___x_2366_; 
v_a_2361_ = lean_array_uget_borrowed(v_as_2353_, v_i_2355_);
v___x_2362_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v___x_2352_, v_a_2361_, v___y_2357_, v___y_2358_);
v_snd_2363_ = lean_ctor_get(v___x_2362_, 1);
lean_inc(v_snd_2363_);
lean_dec_ref(v___x_2362_);
v___x_2364_ = lean_box(0);
v___x_2365_ = ((size_t)1ULL);
v___x_2366_ = lean_usize_add(v_i_2355_, v___x_2365_);
v_i_2355_ = v___x_2366_;
v_b_2356_ = v___x_2364_;
v___y_2358_ = v_snd_2363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg___boxed(lean_object* v___x_2368_, lean_object* v_as_2369_, lean_object* v_sz_2370_, lean_object* v_i_2371_, lean_object* v_b_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
size_t v_sz_boxed_2375_; size_t v_i_boxed_2376_; lean_object* v_res_2377_; 
v_sz_boxed_2375_ = lean_unbox_usize(v_sz_2370_);
lean_dec(v_sz_2370_);
v_i_boxed_2376_ = lean_unbox_usize(v_i_2371_);
lean_dec(v_i_2371_);
v_res_2377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2368_, v_as_2369_, v_sz_boxed_2375_, v_i_boxed_2376_, v_b_2372_, v___y_2373_, v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec_ref(v_as_2369_);
lean_dec(v___x_2368_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___boxed(lean_object* v_level_2378_, lean_object* v_part_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_level_2378_, v_part_2379_, v_a_2380_, v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec_ref(v_part_2379_);
lean_dec(v_level_2378_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(lean_object* v_as_2383_, size_t v_sz_2384_, size_t v_i_2385_, lean_object* v_b_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
uint8_t v___x_2389_; 
v___x_2389_ = lean_usize_dec_lt(v_i_2385_, v_sz_2384_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; 
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v_b_2386_);
lean_ctor_set(v___x_2390_, 1, v___y_2388_);
return v___x_2390_;
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v_snd_2394_; lean_object* v___x_2395_; size_t v___x_2396_; size_t v___x_2397_; 
v_a_2391_ = lean_array_uget_borrowed(v_as_2383_, v_i_2385_);
v___x_2392_ = lean_unsigned_to_nat(0u);
v___x_2393_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v___x_2392_, v_a_2391_, v___y_2387_, v___y_2388_);
v_snd_2394_ = lean_ctor_get(v___x_2393_, 1);
lean_inc(v_snd_2394_);
lean_dec_ref(v___x_2393_);
v___x_2395_ = lean_box(0);
v___x_2396_ = ((size_t)1ULL);
v___x_2397_ = lean_usize_add(v_i_2385_, v___x_2396_);
v_i_2385_ = v___x_2397_;
v_b_2386_ = v___x_2395_;
v___y_2388_ = v_snd_2394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3___boxed(lean_object* v_as_2399_, lean_object* v_sz_2400_, lean_object* v_i_2401_, lean_object* v_b_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
size_t v_sz_boxed_2405_; size_t v_i_boxed_2406_; lean_object* v_res_2407_; 
v_sz_boxed_2405_ = lean_unbox_usize(v_sz_2400_);
lean_dec(v_sz_2400_);
v_i_boxed_2406_ = lean_unbox_usize(v_i_2401_);
lean_dec(v_i_2401_);
v_res_2407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(v_as_2399_, v_sz_boxed_2405_, v_i_boxed_2406_, v_b_2402_, v___y_2403_, v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec_ref(v_as_2399_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(lean_object* v_text_2408_, size_t v_sz_2409_, size_t v___x_2410_, lean_object* v___x_2411_, lean_object* v_subsections_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2415_; lean_object* v_snd_2416_; size_t v_sz_2417_; lean_object* v___x_2418_; lean_object* v_snd_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
v___x_2415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_text_2408_, v_sz_2409_, v___x_2410_, v___x_2411_, v___y_2413_, v___y_2414_);
v_snd_2416_ = lean_ctor_get(v___x_2415_, 1);
lean_inc(v_snd_2416_);
lean_dec_ref(v___x_2415_);
v_sz_2417_ = lean_array_size(v_subsections_2412_);
v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(v_subsections_2412_, v_sz_2417_, v___x_2410_, v___x_2411_, v___y_2413_, v_snd_2416_);
v_snd_2419_ = lean_ctor_get(v___x_2418_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; 
v_unused_2427_ = lean_ctor_get(v___x_2418_, 0);
lean_dec(v_unused_2427_);
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_snd_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2411_);
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_snd_2419_);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed(lean_object* v_text_2428_, lean_object* v_sz_2429_, lean_object* v___x_2430_, lean_object* v___x_2431_, lean_object* v_subsections_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
size_t v_sz_boxed_2435_; size_t v___x_10664__boxed_2436_; lean_object* v_res_2437_; 
v_sz_boxed_2435_ = lean_unbox_usize(v_sz_2429_);
lean_dec(v_sz_2429_);
v___x_10664__boxed_2436_ = lean_unbox_usize(v___x_2430_);
lean_dec(v___x_2430_);
v_res_2437_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(v_text_2428_, v_sz_boxed_2435_, v___x_10664__boxed_2436_, v___x_2431_, v_subsections_2432_, v___y_2433_, v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec_ref(v_subsections_2432_);
lean_dec_ref(v_text_2428_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(lean_object* v_a_2440_){
_start:
{
lean_object* v_text_2441_; lean_object* v_subsections_2442_; lean_object* v___x_2443_; size_t v_sz_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___f_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v_text_2441_ = lean_ctor_get(v_a_2440_, 0);
lean_inc_ref(v_text_2441_);
v_subsections_2442_ = lean_ctor_get(v_a_2440_, 1);
lean_inc_ref(v_subsections_2442_);
lean_dec_ref(v_a_2440_);
v___x_2443_ = lean_box(0);
v_sz_2444_ = lean_array_size(v_text_2441_);
v___x_2445_ = lean_box_usize(v_sz_2444_);
v___x_2446_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1));
v___f_2447_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2447_, 0, v_text_2441_);
lean_closure_set(v___f_2447_, 1, v___x_2445_);
lean_closure_set(v___f_2447_, 2, v___x_2446_);
lean_closure_set(v___f_2447_, 3, v___x_2443_);
lean_closure_set(v___f_2447_, 4, v_subsections_2442_);
v___x_2448_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11));
v___x_2449_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13));
v___x_2450_ = l_Lean_Doc_MarkdownM_run_x27(v___f_2447_, v___x_2448_, v___x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(lean_object* v_p_2451_, lean_object* v_level_2452_, lean_object* v_part_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_level_2452_, v_part_2453_, v_a_2454_, v_a_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___boxed(lean_object* v_p_2457_, lean_object* v_level_2458_, lean_object* v_part_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(v_p_2457_, v_level_2458_, v_part_2459_, v_a_2460_, v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec_ref(v_part_2459_);
lean_dec(v_level_2458_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(lean_object* v_p_2463_, lean_object* v___x_2464_, lean_object* v_as_2465_, size_t v_sz_2466_, size_t v_i_2467_, lean_object* v_b_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2464_, v_as_2465_, v_sz_2466_, v_i_2467_, v_b_2468_, v___y_2469_, v___y_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___boxed(lean_object* v_p_2472_, lean_object* v___x_2473_, lean_object* v_as_2474_, lean_object* v_sz_2475_, lean_object* v_i_2476_, lean_object* v_b_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
size_t v_sz_boxed_2480_; size_t v_i_boxed_2481_; lean_object* v_res_2482_; 
v_sz_boxed_2480_ = lean_unbox_usize(v_sz_2475_);
lean_dec(v_sz_2475_);
v_i_boxed_2481_ = lean_unbox_usize(v_i_2476_);
lean_dec(v_i_2476_);
v_res_2482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(v_p_2472_, v___x_2473_, v_as_2474_, v_sz_boxed_2480_, v_i_boxed_2481_, v_b_2477_, v___y_2478_, v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec_ref(v_as_2474_);
lean_dec(v___x_2473_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2(lean_object* v_s_2483_, lean_object* v_pattern_2484_, lean_object* v_replacement_2485_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v_s_2483_, v_replacement_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___boxed(lean_object* v_s_2487_, lean_object* v_pattern_2488_, lean_object* v_replacement_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2(v_s_2487_, v_pattern_2488_, v_replacement_2489_);
lean_dec_ref(v_replacement_2489_);
lean_dec_ref(v_pattern_2488_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6(lean_object* v_s_2491_, lean_object* v_replacement_2492_, lean_object* v_inst_2493_, lean_object* v_R_2494_, lean_object* v_a_2495_, lean_object* v_b_2496_, lean_object* v_c_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_2491_, v_replacement_2492_, v_a_2495_, v_b_2496_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___boxed(lean_object* v_s_2499_, lean_object* v_replacement_2500_, lean_object* v_inst_2501_, lean_object* v_R_2502_, lean_object* v_a_2503_, lean_object* v_b_2504_, lean_object* v_c_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6(v_s_2499_, v_replacement_2500_, v_inst_2501_, v_R_2502_, v_a_2503_, v_b_2504_, v_c_2505_);
lean_dec_ref(v_replacement_2500_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_2507_, lean_object* v_declName_2508_, uint8_t v_includeBuiltin_2509_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_findInternalDocString_x3f(v_env_2507_, v_declName_2508_, v_includeBuiltin_2509_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2540_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2540_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2540_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
if (lean_obj_tag(v_a_2512_) == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = lean_box(0);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2516_);
v___x_2518_ = v___x_2514_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
else
{
lean_object* v_val_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2539_; 
v_val_2520_ = lean_ctor_get(v_a_2512_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_a_2512_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2522_ = v_a_2512_;
v_isShared_2523_ = v_isSharedCheck_2539_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_val_2520_);
lean_dec(v_a_2512_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2539_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
if (lean_obj_tag(v_val_2520_) == 0)
{
lean_object* v_val_2524_; lean_object* v___x_2526_; 
v_val_2524_ = lean_ctor_get(v_val_2520_, 0);
lean_inc(v_val_2524_);
lean_dec_ref(v_val_2520_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 0, v_val_2524_);
v___x_2526_ = v___x_2522_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_val_2524_);
v___x_2526_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2528_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2526_);
v___x_2528_ = v___x_2514_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
else
{
lean_object* v_val_2531_; lean_object* v___x_2532_; lean_object* v___x_2534_; 
v_val_2531_ = lean_ctor_get(v_val_2520_, 0);
lean_inc(v_val_2531_);
lean_dec_ref(v_val_2520_);
v___x_2532_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(v_val_2531_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 0, v___x_2532_);
v___x_2534_ = v___x_2522_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2536_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2534_);
v___x_2536_ = v___x_2514_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
v_a_2541_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2511_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2511_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_2549_, lean_object* v_declName_2550_, lean_object* v_includeBuiltin_2551_, lean_object* v_a_2552_){
_start:
{
uint8_t v_includeBuiltin_boxed_2553_; lean_object* v_res_2554_; 
v_includeBuiltin_boxed_2553_ = lean_unbox(v_includeBuiltin_2551_);
v_res_2554_ = l_Lean_findSimpleDocString_x3f(v_env_2549_, v_declName_2550_, v_includeBuiltin_boxed_2553_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_es_2555_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_array_mk(v_es_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_x_2559_, lean_object* v_x_2560_, lean_object* v_es_2561_){
_start:
{
lean_object* v_ents_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v_ents_2562_ = lean_array_mk(v_es_2561_);
v___x_2563_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
lean_inc_ref(v_ents_2562_);
v___x_2564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
lean_ctor_set(v___x_2564_, 1, v_ents_2562_);
lean_ctor_set(v___x_2564_, 2, v_ents_2562_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_x_2565_, lean_object* v_x_2566_, lean_object* v_es_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v_x_2565_, v_x_2566_, v_es_2567_);
lean_dec_ref(v_x_2566_);
lean_dec_ref(v_x_2565_);
return v_res_2568_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = lean_unsigned_to_nat(32u);
v___x_2570_ = lean_mk_empty_array_with_capacity(v___x_2569_);
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v___x_2572_, lean_object* v_x_2573_){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2574_ = lean_unsigned_to_nat(32u);
v___x_2575_ = lean_mk_empty_array_with_capacity(v___x_2574_);
v___x_2576_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_);
v___x_2577_ = ((size_t)5ULL);
lean_inc(v___x_2572_);
v___x_2578_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v___x_2575_);
lean_ctor_set(v___x_2578_, 2, v___x_2572_);
lean_ctor_set(v___x_2578_, 3, v___x_2572_);
lean_ctor_set_usize(v___x_2578_, 4, v___x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v___x_2579_, lean_object* v_x_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v___x_2579_, v_x_2580_);
lean_dec_ref(v_x_2580_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
v___x_2603_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object* v_env_2606_, lean_object* v_doc_2607_){
_start:
{
lean_object* v___x_2608_; lean_object* v_toEnvExtension_2609_; lean_object* v_asyncMode_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2608_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2609_ = lean_ctor_get(v___x_2608_, 0);
v_asyncMode_2610_ = lean_ctor_get(v_toEnvExtension_2609_, 2);
v___x_2611_ = lean_box(0);
v___x_2612_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2608_, v_env_2606_, v_doc_2607_, v_asyncMode_2610_, v___x_2611_);
return v___x_2612_;
}
}
static lean_object* _init_l_Lean_getMainModuleDoc___closed__0(void){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object* v_env_2614_){
_start:
{
lean_object* v___x_2615_; lean_object* v_toEnvExtension_2616_; lean_object* v_asyncMode_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2615_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2616_ = lean_ctor_get(v___x_2615_, 0);
v_asyncMode_2617_ = lean_ctor_get(v_toEnvExtension_2616_, 2);
v___x_2618_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2619_ = lean_box(0);
v___x_2620_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2618_, v___x_2615_, v_env_2614_, v_asyncMode_2617_, v___x_2619_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_getModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2622_ = lean_box(0);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v___x_2621_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object* v_env_2624_, lean_object* v_moduleName_2625_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_Environment_getModuleIdx_x3f(v_env_2624_, v_moduleName_2625_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_box(0);
return v___x_2627_;
}
else
{
lean_object* v_val_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2639_; 
v_val_2628_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2630_ = v___x_2626_;
v_isShared_2631_ = v_isSharedCheck_2639_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_val_2628_);
lean_dec(v___x_2626_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2639_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
v___x_2632_ = lean_obj_once(&l_Lean_getModuleDoc_x3f___closed__0, &l_Lean_getModuleDoc_x3f___closed__0_once, _init_l_Lean_getModuleDoc_x3f___closed__0);
v___x_2633_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v___x_2634_ = 1;
v___x_2635_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2632_, v___x_2633_, v_env_2624_, v_val_2628_, v___x_2634_);
lean_dec(v_val_2628_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2635_);
v___x_2637_ = v___x_2630_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object* v_env_2640_, lean_object* v_moduleName_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_getModuleDoc_x3f(v_env_2640_, v_moduleName_2641_);
lean_dec(v_moduleName_2641_);
lean_dec_ref(v_env_2640_);
return v_res_2642_;
}
}
static lean_object* _init_l_Lean_getDocStringText___redArg___closed__1(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__0));
v___x_2645_ = l_Lean_stringToMessageData(v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object* v_inst_2649_, lean_object* v_inst_2650_, lean_object* v_stx_2651_){
_start:
{
lean_object* v_toApplicative_2658_; lean_object* v_toPure_2659_; lean_object* v_val_2661_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_toApplicative_2658_ = lean_ctor_get(v_inst_2649_, 0);
v_toPure_2659_ = lean_ctor_get(v_toApplicative_2658_, 1);
v___x_2668_ = lean_unsigned_to_nat(1u);
v___x_2669_ = l_Lean_Syntax_getArg(v_stx_2651_, v___x_2668_);
switch(lean_obj_tag(v___x_2669_))
{
case 2:
{
lean_object* v_val_2670_; 
lean_inc(v_toPure_2659_);
lean_dec(v_stx_2651_);
lean_dec_ref(v_inst_2650_);
lean_dec_ref(v_inst_2649_);
v_val_2670_ = lean_ctor_get(v___x_2669_, 1);
lean_inc_ref(v_val_2670_);
lean_dec_ref(v___x_2669_);
v_val_2661_ = v_val_2670_;
goto v___jp_2660_;
}
case 1:
{
lean_object* v_kind_2671_; 
v_kind_2671_ = lean_ctor_get(v___x_2669_, 1);
lean_inc(v_kind_2671_);
if (lean_obj_tag(v_kind_2671_) == 1)
{
lean_object* v_pre_2672_; 
v_pre_2672_ = lean_ctor_get(v_kind_2671_, 0);
lean_inc(v_pre_2672_);
if (lean_obj_tag(v_pre_2672_) == 1)
{
lean_object* v_pre_2673_; 
v_pre_2673_ = lean_ctor_get(v_pre_2672_, 0);
lean_inc(v_pre_2673_);
if (lean_obj_tag(v_pre_2673_) == 1)
{
lean_object* v_pre_2674_; 
v_pre_2674_ = lean_ctor_get(v_pre_2673_, 0);
lean_inc(v_pre_2674_);
if (lean_obj_tag(v_pre_2674_) == 1)
{
lean_object* v_pre_2675_; 
v_pre_2675_ = lean_ctor_get(v_pre_2674_, 0);
if (lean_obj_tag(v_pre_2675_) == 0)
{
lean_object* v_str_2676_; lean_object* v_str_2677_; lean_object* v_str_2678_; lean_object* v_str_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
v_str_2676_ = lean_ctor_get(v_kind_2671_, 1);
lean_inc_ref(v_str_2676_);
lean_dec_ref(v_kind_2671_);
v_str_2677_ = lean_ctor_get(v_pre_2672_, 1);
lean_inc_ref(v_str_2677_);
lean_dec_ref(v_pre_2672_);
v_str_2678_ = lean_ctor_get(v_pre_2673_, 1);
lean_inc_ref(v_str_2678_);
lean_dec_ref(v_pre_2673_);
v_str_2679_ = lean_ctor_get(v_pre_2674_, 1);
lean_inc_ref(v_str_2679_);
lean_dec_ref(v_pre_2674_);
v___x_2680_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_2681_ = lean_string_dec_eq(v_str_2679_, v___x_2680_);
lean_dec_ref(v_str_2679_);
if (v___x_2681_ == 0)
{
lean_dec_ref(v_str_2678_);
lean_dec_ref(v_str_2677_);
lean_dec_ref(v_str_2676_);
lean_dec_ref(v___x_2669_);
goto v___jp_2652_;
}
else
{
lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2682_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__2));
v___x_2683_ = lean_string_dec_eq(v_str_2678_, v___x_2682_);
lean_dec_ref(v_str_2678_);
if (v___x_2683_ == 0)
{
lean_dec_ref(v_str_2677_);
lean_dec_ref(v_str_2676_);
lean_dec_ref(v___x_2669_);
goto v___jp_2652_;
}
else
{
lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__3));
v___x_2685_ = lean_string_dec_eq(v_str_2677_, v___x_2684_);
lean_dec_ref(v_str_2677_);
if (v___x_2685_ == 0)
{
lean_dec_ref(v_str_2676_);
lean_dec_ref(v___x_2669_);
goto v___jp_2652_;
}
else
{
lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2686_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__4));
v___x_2687_ = lean_string_dec_eq(v_str_2676_, v___x_2686_);
lean_dec_ref(v_str_2676_);
if (v___x_2687_ == 0)
{
lean_dec_ref(v___x_2669_);
goto v___jp_2652_;
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_unsigned_to_nat(0u);
v___x_2689_ = l_Lean_Syntax_getArg(v___x_2669_, v___x_2688_);
lean_dec_ref(v___x_2669_);
if (lean_obj_tag(v___x_2689_) == 2)
{
lean_object* v_val_2690_; 
lean_inc(v_toPure_2659_);
lean_dec(v_stx_2651_);
lean_dec_ref(v_inst_2650_);
lean_dec_ref(v_inst_2649_);
v_val_2690_ = lean_ctor_get(v___x_2689_, 1);
lean_inc_ref(v_val_2690_);
lean_dec_ref(v___x_2689_);
v_val_2661_ = v_val_2690_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_dec(v___x_2689_);
v___x_2691_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2651_);
v___x_2692_ = l_Lean_MessageData_ofSyntax(v_stx_2651_);
v___x_2693_ = l_Lean_indentD(v___x_2692_);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2691_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = l_Lean_throwErrorAt___redArg(v_inst_2649_, v_inst_2650_, v_stx_2651_, v___x_2694_);
return v___x_2695_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2674_);
lean_dec_ref(v_pre_2673_);
lean_dec_ref(v_pre_2672_);
lean_dec_ref(v_kind_2671_);
lean_dec_ref(v___x_2669_);
goto v___jp_2652_;
}
}
else
{
lean_dec(v_pre_2674_);
lean_dec_ref(v_pre_2673_);
lean_dec_ref(v_pre_2672_);
lean_dec_ref(v_kind_2671_);
lean_dec_ref(v___x_2669_);
goto v___jp_2652_;
}
}
else
{
lean_dec(v_pre_2673_);
lean_dec_ref(v_pre_2672_);
lean_dec_ref(v_kind_2671_);
lean_dec_ref(v___x_2669_);
goto v___jp_2652_;
}
}
else
{
lean_dec(v_pre_2672_);
lean_dec_ref(v_kind_2671_);
lean_dec_ref(v___x_2669_);
goto v___jp_2652_;
}
}
else
{
lean_dec_ref(v___x_2669_);
lean_dec(v_kind_2671_);
goto v___jp_2652_;
}
}
default: 
{
lean_dec(v___x_2669_);
goto v___jp_2652_;
}
}
v___jp_2652_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2653_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2651_);
v___x_2654_ = l_Lean_MessageData_ofSyntax(v_stx_2651_);
v___x_2655_ = l_Lean_indentD(v___x_2654_);
v___x_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2653_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = l_Lean_throwErrorAt___redArg(v_inst_2649_, v_inst_2650_, v_stx_2651_, v___x_2656_);
return v___x_2657_;
}
v___jp_2660_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = lean_string_utf8_byte_size(v_val_2661_);
v___x_2664_ = lean_unsigned_to_nat(2u);
v___x_2665_ = lean_nat_sub(v___x_2663_, v___x_2664_);
v___x_2666_ = lean_string_utf8_extract(v_val_2661_, v___x_2662_, v___x_2665_);
lean_dec(v___x_2665_);
lean_dec_ref(v_val_2661_);
v___x_2667_ = lean_apply_2(v_toPure_2659_, lean_box(0), v___x_2666_);
return v___x_2667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object* v_m_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_stx_2699_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_getDocStringText___redArg(v_inst_2697_, v_inst_2698_, v_stx_2699_);
return v___x_2700_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_2702_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default___closed__0));
v___x_2703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
lean_ctor_set(v___x_2703_, 2, v___x_2701_);
return v___x_2703_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default(void){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = lean_obj_once(&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0, &l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_once, _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet(void){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object* v_a_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_nat_to_int(v_a_2706_);
return v___x_2707_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = lean_unsigned_to_nat(2u);
v___x_2715_ = lean_nat_to_int(v___x_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = lean_unsigned_to_nat(1u);
v___x_2717_ = lean_nat_to_int(v___x_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object* v_x_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_){
_start:
{
if (lean_obj_tag(v_x_2732_) == 0)
{
lean_dec(v_x_2730_);
return v_x_2731_;
}
else
{
lean_object* v_head_2733_; lean_object* v_tail_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2745_; 
v_head_2733_ = lean_ctor_get(v_x_2732_, 0);
v_tail_2734_ = lean_ctor_get(v_x_2732_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_x_2732_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2736_ = v_x_2732_;
v_isShared_2737_ = v_isSharedCheck_2745_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_tail_2734_);
lean_inc(v_head_2733_);
lean_dec(v_x_2732_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2745_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
lean_inc(v_x_2730_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set_tag(v___x_2736_, 5);
lean_ctor_set(v___x_2736_, 1, v_x_2730_);
lean_ctor_set(v___x_2736_, 0, v_x_2731_);
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_x_2731_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_x_2730_);
v___x_2739_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2740_ = lean_unsigned_to_nat(0u);
v___x_2741_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2733_, v___x_2740_);
v___x_2742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2739_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v_x_2731_ = v___x_2742_;
v_x_2732_ = v_tail_2734_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object* v_x_2746_, lean_object* v_x_2747_, lean_object* v_x_2748_){
_start:
{
if (lean_obj_tag(v_x_2748_) == 0)
{
lean_dec(v_x_2746_);
return v_x_2747_;
}
else
{
lean_object* v_head_2749_; lean_object* v_tail_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2761_; 
v_head_2749_ = lean_ctor_get(v_x_2748_, 0);
v_tail_2750_ = lean_ctor_get(v_x_2748_, 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_x_2748_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2752_ = v_x_2748_;
v_isShared_2753_ = v_isSharedCheck_2761_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_tail_2750_);
lean_inc(v_head_2749_);
lean_dec(v_x_2748_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2761_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
lean_inc(v_x_2746_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set_tag(v___x_2752_, 5);
lean_ctor_set(v___x_2752_, 1, v_x_2746_);
lean_ctor_set(v___x_2752_, 0, v_x_2747_);
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_x_2747_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v_x_2746_);
v___x_2755_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2756_ = lean_unsigned_to_nat(0u);
v___x_2757_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2749_, v___x_2756_);
v___x_2758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2755_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(v_x_2746_, v___x_2758_, v_tail_2750_);
return v___x_2759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2762_, lean_object* v_x_2763_){
_start:
{
if (lean_obj_tag(v_x_2762_) == 0)
{
lean_object* v___x_2764_; 
lean_dec(v_x_2763_);
v___x_2764_ = lean_box(0);
return v___x_2764_;
}
else
{
lean_object* v_tail_2765_; 
v_tail_2765_ = lean_ctor_get(v_x_2762_, 1);
if (lean_obj_tag(v_tail_2765_) == 0)
{
lean_object* v_head_2766_; lean_object* v___x_2767_; 
lean_dec(v_x_2763_);
v_head_2766_ = lean_ctor_get(v_x_2762_, 0);
lean_inc(v_head_2766_);
lean_dec_ref(v_x_2762_);
v___x_2767_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2766_);
return v___x_2767_;
}
else
{
lean_object* v_head_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_inc(v_tail_2765_);
v_head_2768_ = lean_ctor_get(v_x_2762_, 0);
lean_inc(v_head_2768_);
lean_dec_ref(v_x_2762_);
v___x_2769_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2768_);
v___x_2770_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(v_x_2763_, v___x_2769_, v_tail_2765_);
return v___x_2770_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0));
v___x_2773_ = lean_string_length(v___x_2772_);
return v___x_2773_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4);
v___x_2775_ = lean_nat_to_int(v___x_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_xs_2783_){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2784_ = lean_array_get_size(v_xs_2783_);
v___x_2785_ = lean_unsigned_to_nat(0u);
v___x_2786_ = lean_nat_dec_eq(v___x_2784_, v___x_2785_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2787_ = lean_array_to_list(v_xs_2783_);
v___x_2788_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2789_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_2787_, v___x_2788_);
v___x_2790_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_2791_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_2792_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v___x_2789_);
v___x_2793_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2790_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = l_Std_Format_fill(v___x_2795_);
return v___x_2796_;
}
else
{
lean_object* v___x_2797_; 
lean_dec_ref(v_xs_2783_);
v___x_2797_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_2797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_2852_, lean_object* v_prec_2853_){
_start:
{
switch(lean_obj_tag(v_x_2852_))
{
case 0:
{
lean_object* v_string_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2874_; 
v_string_2854_ = lean_ctor_get(v_x_2852_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2856_ = v_x_2852_;
v_isShared_2857_ = v_isSharedCheck_2874_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_string_2854_);
lean_dec(v_x_2852_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2874_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___y_2859_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2870_ = lean_unsigned_to_nat(1024u);
v___x_2871_ = lean_nat_dec_le(v___x_2870_, v_prec_2853_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2859_ = v___x_2872_;
goto v___jp_2858_;
}
else
{
lean_object* v___x_2873_; 
v___x_2873_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2859_ = v___x_2873_;
goto v___jp_2858_;
}
v___jp_2858_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2860_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_2861_ = l_String_quote(v_string_2854_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set_tag(v___x_2856_, 3);
lean_ctor_set(v___x_2856_, 0, v___x_2861_);
v___x_2863_ = v___x_2856_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2860_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
lean_inc(v___y_2859_);
v___x_2865_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___y_2859_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = 0;
v___x_2867_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2867_, 0, v___x_2865_);
lean_ctor_set_uint8(v___x_2867_, sizeof(void*)*1, v___x_2866_);
v___x_2868_ = l_Repr_addAppParen(v___x_2867_, v_prec_2853_);
return v___x_2868_;
}
}
}
}
case 1:
{
lean_object* v_content_2875_; lean_object* v___y_2877_; lean_object* v___x_2885_; uint8_t v___x_2886_; 
v_content_2875_ = lean_ctor_get(v_x_2852_, 0);
lean_inc_ref(v_content_2875_);
lean_dec_ref(v_x_2852_);
v___x_2885_ = lean_unsigned_to_nat(1024u);
v___x_2886_ = lean_nat_dec_le(v___x_2885_, v_prec_2853_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; 
v___x_2887_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2877_ = v___x_2887_;
goto v___jp_2876_;
}
else
{
lean_object* v___x_2888_; 
v___x_2888_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2877_ = v___x_2888_;
goto v___jp_2876_;
}
v___jp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2878_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7));
v___x_2879_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2875_);
v___x_2880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2878_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
lean_inc(v___y_2877_);
v___x_2881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___y_2877_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = 0;
v___x_2883_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set_uint8(v___x_2883_, sizeof(void*)*1, v___x_2882_);
v___x_2884_ = l_Repr_addAppParen(v___x_2883_, v_prec_2853_);
return v___x_2884_;
}
}
case 2:
{
lean_object* v_content_2889_; lean_object* v___y_2891_; lean_object* v___x_2899_; uint8_t v___x_2900_; 
v_content_2889_ = lean_ctor_get(v_x_2852_, 0);
lean_inc_ref(v_content_2889_);
lean_dec_ref(v_x_2852_);
v___x_2899_ = lean_unsigned_to_nat(1024u);
v___x_2900_ = lean_nat_dec_le(v___x_2899_, v_prec_2853_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; 
v___x_2901_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2891_ = v___x_2901_;
goto v___jp_2890_;
}
else
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2891_ = v___x_2902_;
goto v___jp_2890_;
}
v___jp_2890_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2892_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10));
v___x_2893_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2889_);
v___x_2894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
lean_inc(v___y_2891_);
v___x_2895_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___y_2891_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = 0;
v___x_2897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set_uint8(v___x_2897_, sizeof(void*)*1, v___x_2896_);
v___x_2898_ = l_Repr_addAppParen(v___x_2897_, v_prec_2853_);
return v___x_2898_;
}
}
case 3:
{
lean_object* v_string_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2923_; 
v_string_2903_ = lean_ctor_get(v_x_2852_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2905_ = v_x_2852_;
v_isShared_2906_ = v_isSharedCheck_2923_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_string_2903_);
lean_dec(v_x_2852_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2923_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___y_2908_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = lean_unsigned_to_nat(1024u);
v___x_2920_ = lean_nat_dec_le(v___x_2919_, v_prec_2853_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2908_ = v___x_2921_;
goto v___jp_2907_;
}
else
{
lean_object* v___x_2922_; 
v___x_2922_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2908_ = v___x_2922_;
goto v___jp_2907_;
}
v___jp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2909_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13));
v___x_2910_ = l_String_quote(v_string_2903_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2910_);
v___x_2912_ = v___x_2905_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2909_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
lean_inc(v___y_2908_);
v___x_2914_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___y_2908_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = 0;
v___x_2916_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*1, v___x_2915_);
v___x_2917_ = l_Repr_addAppParen(v___x_2916_, v_prec_2853_);
return v___x_2917_;
}
}
}
}
case 4:
{
uint8_t v_mode_2924_; lean_object* v_string_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2950_; 
v_mode_2924_ = lean_ctor_get_uint8(v_x_2852_, sizeof(void*)*1);
v_string_2925_ = lean_ctor_get(v_x_2852_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2927_ = v_x_2852_;
v_isShared_2928_ = v_isSharedCheck_2950_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_string_2925_);
lean_dec(v_x_2852_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2950_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___y_2930_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2946_ = lean_unsigned_to_nat(1024u);
v___x_2947_ = lean_nat_dec_le(v___x_2946_, v_prec_2853_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; 
v___x_2948_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2930_ = v___x_2948_;
goto v___jp_2929_;
}
else
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2930_ = v___x_2949_;
goto v___jp_2929_;
}
v___jp_2929_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; lean_object* v___x_2943_; 
v___x_2931_ = lean_box(1);
v___x_2932_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16));
v___x_2933_ = lean_unsigned_to_nat(1024u);
v___x_2934_ = l_Lean_Doc_instReprMathMode_repr(v_mode_2924_, v___x_2933_);
v___x_2935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2932_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
v___x_2936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
lean_ctor_set(v___x_2936_, 1, v___x_2931_);
v___x_2937_ = l_String_quote(v_string_2925_);
v___x_2938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
v___x_2939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2936_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
lean_inc(v___y_2930_);
v___x_2940_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___y_2930_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = 0;
if (v_isShared_2928_ == 0)
{
lean_ctor_set_tag(v___x_2927_, 6);
lean_ctor_set(v___x_2927_, 0, v___x_2940_);
v___x_2943_ = v___x_2927_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2940_);
v___x_2943_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2944_; 
lean_ctor_set_uint8(v___x_2943_, sizeof(void*)*1, v___x_2941_);
v___x_2944_ = l_Repr_addAppParen(v___x_2943_, v_prec_2853_);
return v___x_2944_;
}
}
}
}
case 5:
{
lean_object* v_string_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2971_; 
v_string_2951_ = lean_ctor_get(v_x_2852_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2953_ = v_x_2852_;
v_isShared_2954_ = v_isSharedCheck_2971_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_string_2951_);
lean_dec(v_x_2852_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2971_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___y_2956_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v___x_2967_ = lean_unsigned_to_nat(1024u);
v___x_2968_ = lean_nat_dec_le(v___x_2967_, v_prec_2853_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; 
v___x_2969_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2956_ = v___x_2969_;
goto v___jp_2955_;
}
else
{
lean_object* v___x_2970_; 
v___x_2970_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2956_ = v___x_2970_;
goto v___jp_2955_;
}
v___jp_2955_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2957_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19));
v___x_2958_ = l_String_quote(v_string_2951_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set_tag(v___x_2953_, 3);
lean_ctor_set(v___x_2953_, 0, v___x_2958_);
v___x_2960_ = v___x_2953_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2957_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
lean_inc(v___y_2956_);
v___x_2962_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___y_2956_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = 0;
v___x_2964_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2964_, 0, v___x_2962_);
lean_ctor_set_uint8(v___x_2964_, sizeof(void*)*1, v___x_2963_);
v___x_2965_ = l_Repr_addAppParen(v___x_2964_, v_prec_2853_);
return v___x_2965_;
}
}
}
}
case 6:
{
lean_object* v_content_2972_; lean_object* v_url_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2997_; 
v_content_2972_ = lean_ctor_get(v_x_2852_, 0);
v_url_2973_ = lean_ctor_get(v_x_2852_, 1);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2975_ = v_x_2852_;
v_isShared_2976_ = v_isSharedCheck_2997_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_url_2973_);
lean_inc(v_content_2972_);
lean_dec(v_x_2852_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2997_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___y_2978_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v___x_2993_ = lean_unsigned_to_nat(1024u);
v___x_2994_ = lean_nat_dec_le(v___x_2993_, v_prec_2853_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2978_ = v___x_2995_;
goto v___jp_2977_;
}
else
{
lean_object* v___x_2996_; 
v___x_2996_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2978_ = v___x_2996_;
goto v___jp_2977_;
}
v___jp_2977_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
v___x_2979_ = lean_box(1);
v___x_2980_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22));
v___x_2981_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2972_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set_tag(v___x_2975_, 5);
lean_ctor_set(v___x_2975_, 1, v___x_2981_);
lean_ctor_set(v___x_2975_, 0, v___x_2980_);
v___x_2983_ = v___x_2975_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
lean_ctor_set(v___x_2984_, 1, v___x_2979_);
v___x_2985_ = l_String_quote(v_url_2973_);
v___x_2986_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
v___x_2987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2984_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
lean_inc(v___y_2978_);
v___x_2988_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___y_2978_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = 0;
v___x_2990_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2990_, 0, v___x_2988_);
lean_ctor_set_uint8(v___x_2990_, sizeof(void*)*1, v___x_2989_);
v___x_2991_ = l_Repr_addAppParen(v___x_2990_, v_prec_2853_);
return v___x_2991_;
}
}
}
}
case 7:
{
lean_object* v_name_2998_; lean_object* v_content_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3023_; 
v_name_2998_ = lean_ctor_get(v_x_2852_, 0);
v_content_2999_ = lean_ctor_get(v_x_2852_, 1);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3001_ = v_x_2852_;
v_isShared_3002_ = v_isSharedCheck_3023_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_content_2999_);
lean_inc(v_name_2998_);
lean_dec(v_x_2852_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3023_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___y_3004_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3019_ = lean_unsigned_to_nat(1024u);
v___x_3020_ = lean_nat_dec_le(v___x_3019_, v_prec_2853_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3004_ = v___x_3021_;
goto v___jp_3003_;
}
else
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3004_ = v___x_3022_;
goto v___jp_3003_;
}
v___jp_3003_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3010_; 
v___x_3005_ = lean_box(1);
v___x_3006_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25));
v___x_3007_ = l_String_quote(v_name_2998_);
v___x_3008_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set_tag(v___x_3001_, 5);
lean_ctor_set(v___x_3001_, 1, v___x_3008_);
lean_ctor_set(v___x_3001_, 0, v___x_3006_);
v___x_3010_ = v___x_3001_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3006_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v___x_3005_);
v___x_3012_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2999_);
v___x_3013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3011_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
lean_inc(v___y_3004_);
v___x_3014_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___y_3004_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v___x_3015_ = 0;
v___x_3016_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3016_, 0, v___x_3014_);
lean_ctor_set_uint8(v___x_3016_, sizeof(void*)*1, v___x_3015_);
v___x_3017_ = l_Repr_addAppParen(v___x_3016_, v_prec_2853_);
return v___x_3017_;
}
}
}
}
case 8:
{
lean_object* v_alt_3024_; lean_object* v_url_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3050_; 
v_alt_3024_ = lean_ctor_get(v_x_2852_, 0);
v_url_3025_ = lean_ctor_get(v_x_2852_, 1);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3027_ = v_x_2852_;
v_isShared_3028_ = v_isSharedCheck_3050_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_url_3025_);
lean_inc(v_alt_3024_);
lean_dec(v_x_2852_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3050_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___y_3030_; lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = lean_unsigned_to_nat(1024u);
v___x_3047_ = lean_nat_dec_le(v___x_3046_, v_prec_2853_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3030_ = v___x_3048_;
goto v___jp_3029_;
}
else
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3030_ = v___x_3049_;
goto v___jp_3029_;
}
v___jp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3036_; 
v___x_3031_ = lean_box(1);
v___x_3032_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28));
v___x_3033_ = l_String_quote(v_alt_3024_);
v___x_3034_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set_tag(v___x_3027_, 5);
lean_ctor_set(v___x_3027_, 1, v___x_3034_);
lean_ctor_set(v___x_3027_, 0, v___x_3032_);
v___x_3036_ = v___x_3027_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3031_);
v___x_3038_ = l_String_quote(v_url_3025_);
v___x_3039_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3037_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
lean_inc(v___y_3030_);
v___x_3041_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___y_3030_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = 0;
v___x_3043_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3043_, 0, v___x_3041_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*1, v___x_3042_);
v___x_3044_ = l_Repr_addAppParen(v___x_3043_, v_prec_2853_);
return v___x_3044_;
}
}
}
}
case 9:
{
lean_object* v_content_3051_; lean_object* v___y_3053_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v_content_3051_ = lean_ctor_get(v_x_2852_, 0);
lean_inc_ref(v_content_3051_);
lean_dec_ref(v_x_2852_);
v___x_3061_ = lean_unsigned_to_nat(1024u);
v___x_3062_ = lean_nat_dec_le(v___x_3061_, v_prec_2853_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3053_ = v___x_3063_;
goto v___jp_3052_;
}
else
{
lean_object* v___x_3064_; 
v___x_3064_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3053_ = v___x_3064_;
goto v___jp_3052_;
}
v___jp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3054_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31));
v___x_3055_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3051_);
v___x_3056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3054_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
lean_inc(v___y_3053_);
v___x_3057_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___y_3053_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = 0;
v___x_3059_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3059_, 0, v___x_3057_);
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*1, v___x_3058_);
v___x_3060_ = l_Repr_addAppParen(v___x_3059_, v_prec_2853_);
return v___x_3060_;
}
}
default: 
{
lean_object* v_container_3065_; lean_object* v_content_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3114_; 
v_container_3065_ = lean_ctor_get(v_x_2852_, 0);
v_content_3066_ = lean_ctor_get(v_x_2852_, 1);
v_isSharedCheck_3114_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3068_ = v_x_2852_;
v_isShared_3069_ = v_isSharedCheck_3114_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_content_3066_);
lean_inc(v_container_3065_);
lean_dec(v_x_2852_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3114_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___y_3071_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = lean_unsigned_to_nat(1024u);
v___x_3111_ = lean_nat_dec_le(v___x_3110_, v_prec_2853_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; 
v___x_3112_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3071_ = v___x_3112_;
goto v___jp_3070_;
}
else
{
lean_object* v___x_3113_; 
v___x_3113_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3071_ = v___x_3113_;
goto v___jp_3070_;
}
v___jp_3070_:
{
lean_object* v_name_3072_; lean_object* v_val_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3109_; 
v_name_3072_ = lean_ctor_get(v_container_3065_, 0);
v_val_3073_ = lean_ctor_get(v_container_3065_, 1);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_container_3065_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3075_ = v_container_3065_;
v_isShared_3076_ = v_isSharedCheck_3109_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_val_3073_);
lean_inc(v_name_3072_);
lean_dec(v_container_3065_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3109_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3083_; 
v___x_3077_ = lean_box(1);
v___x_3078_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34));
v___x_3079_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3080_ = lean_unsigned_to_nat(0u);
v___x_3081_ = l_Lean_Name_reprPrec(v_name_3072_, v___x_3080_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set_tag(v___x_3075_, 5);
lean_ctor_set(v___x_3075_, 1, v___x_3081_);
lean_ctor_set(v___x_3075_, 0, v___x_3079_);
v___x_3083_ = v___x_3075_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v___x_3081_);
v___x_3083_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
lean_object* v___x_3084_; uint8_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3084_ = l_Std_Format_nestD(v___x_3083_);
v___x_3085_ = 0;
v___x_3086_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3086_, 0, v___x_3084_);
lean_ctor_set_uint8(v___x_3086_, sizeof(void*)*1, v___x_3085_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set_tag(v___x_3068_, 5);
lean_ctor_set(v___x_3068_, 1, v___x_3077_);
lean_ctor_set(v___x_3068_, 0, v___x_3086_);
v___x_3088_ = v___x_3068_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v___x_3077_);
v___x_3088_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3089_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3090_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3073_);
lean_dec(v_val_3073_);
v___x_3091_ = l_Lean_Name_reprPrec(v___x_3090_, v___x_3080_);
v___x_3092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3089_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
v___x_3093_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3092_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
v___x_3095_ = l_Std_Format_nestD(v___x_3094_);
v___x_3096_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
lean_ctor_set_uint8(v___x_3096_, sizeof(void*)*1, v___x_3085_);
v___x_3097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3088_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___x_3098_ = l_Std_Format_nestD(v___x_3097_);
v___x_3099_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*1, v___x_3085_);
v___x_3100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3078_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
lean_ctor_set(v___x_3101_, 1, v___x_3077_);
v___x_3102_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3066_);
v___x_3103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3101_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
lean_inc(v___y_3071_);
v___x_3104_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___y_3071_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
lean_ctor_set_uint8(v___x_3105_, sizeof(void*)*1, v___x_3085_);
v___x_3106_ = l_Repr_addAppParen(v___x_3105_, v_prec_2853_);
return v___x_3106_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v___y_3115_, v___x_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_3118_, lean_object* v_prec_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_x_3118_, v_prec_3119_);
lean_dec(v_prec_3119_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object* v_xs_3121_){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; 
v___x_3122_ = lean_array_get_size(v_xs_3121_);
v___x_3123_ = lean_unsigned_to_nat(0u);
v___x_3124_ = lean_nat_dec_eq(v___x_3122_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3125_ = lean_array_to_list(v_xs_3121_);
v___x_3126_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3127_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_3125_, v___x_3126_);
v___x_3128_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3129_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
lean_ctor_set(v___x_3130_, 1, v___x_3127_);
v___x_3131_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3130_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3128_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
v___x_3134_ = l_Std_Format_fill(v___x_3133_);
return v___x_3134_;
}
else
{
lean_object* v___x_3135_; 
lean_dec_ref(v_xs_3121_);
v___x_3135_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3135_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = lean_unsigned_to_nat(12u);
v___x_3167_ = lean_nat_to_int(v___x_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object* v_x_3168_, lean_object* v_x_3169_, lean_object* v_x_3170_){
_start:
{
if (lean_obj_tag(v_x_3170_) == 0)
{
lean_dec(v_x_3168_);
return v_x_3169_;
}
else
{
lean_object* v_head_3171_; lean_object* v_tail_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3183_; 
v_head_3171_ = lean_ctor_get(v_x_3170_, 0);
v_tail_3172_ = lean_ctor_get(v_x_3170_, 1);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_x_3170_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3174_ = v_x_3170_;
v_isShared_3175_ = v_isSharedCheck_3183_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_tail_3172_);
lean_inc(v_head_3171_);
lean_dec(v_x_3170_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3183_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
lean_inc(v_x_3168_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 5);
lean_ctor_set(v___x_3174_, 1, v_x_3168_);
lean_ctor_set(v___x_3174_, 0, v_x_3169_);
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_x_3169_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_x_3168_);
v___x_3177_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = lean_unsigned_to_nat(0u);
v___x_3179_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_3171_, v___x_3178_);
v___x_3180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3177_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v_x_3169_ = v___x_3180_;
v_x_3170_ = v_tail_3172_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object* v_x_3184_, lean_object* v_x_3185_, lean_object* v_x_3186_){
_start:
{
if (lean_obj_tag(v_x_3186_) == 0)
{
lean_dec(v_x_3184_);
return v_x_3185_;
}
else
{
lean_object* v_head_3187_; lean_object* v_tail_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3199_; 
v_head_3187_ = lean_ctor_get(v_x_3186_, 0);
v_tail_3188_ = lean_ctor_get(v_x_3186_, 1);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_x_3186_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3190_ = v_x_3186_;
v_isShared_3191_ = v_isSharedCheck_3199_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_tail_3188_);
lean_inc(v_head_3187_);
lean_dec(v_x_3186_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3199_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
lean_inc(v_x_3184_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set_tag(v___x_3190_, 5);
lean_ctor_set(v___x_3190_, 1, v_x_3184_);
lean_ctor_set(v___x_3190_, 0, v_x_3185_);
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_x_3185_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_x_3184_);
v___x_3193_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3194_ = lean_unsigned_to_nat(0u);
v___x_3195_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_3187_, v___x_3194_);
v___x_3196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3193_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(v_x_3184_, v___x_3196_, v_tail_3188_);
return v___x_3197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object* v_x_3200_, lean_object* v_x_3201_){
_start:
{
if (lean_obj_tag(v_x_3200_) == 0)
{
lean_object* v___x_3202_; 
lean_dec(v_x_3201_);
v___x_3202_ = lean_box(0);
return v___x_3202_;
}
else
{
lean_object* v_tail_3203_; 
v_tail_3203_ = lean_ctor_get(v_x_3200_, 1);
if (lean_obj_tag(v_tail_3203_) == 0)
{
lean_object* v_head_3204_; lean_object* v___x_3205_; 
lean_dec(v_x_3201_);
v_head_3204_ = lean_ctor_get(v_x_3200_, 0);
lean_inc(v_head_3204_);
lean_dec_ref(v_x_3200_);
v___x_3205_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3204_);
return v___x_3205_;
}
else
{
lean_object* v_head_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_inc(v_tail_3203_);
v_head_3206_ = lean_ctor_get(v_x_3200_, 0);
lean_inc(v_head_3206_);
lean_dec_ref(v_x_3200_);
v___x_3207_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3206_);
v___x_3208_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(v_x_3201_, v___x_3207_, v_tail_3203_);
return v___x_3208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object* v_xs_3209_){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; uint8_t v___x_3212_; 
v___x_3210_ = lean_array_get_size(v_xs_3209_);
v___x_3211_ = lean_unsigned_to_nat(0u);
v___x_3212_ = lean_nat_dec_eq(v___x_3210_, v___x_3211_);
if (v___x_3212_ == 0)
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3213_ = lean_array_to_list(v_xs_3209_);
v___x_3214_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3215_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3213_, v___x_3214_);
v___x_3216_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3217_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
lean_ctor_set(v___x_3218_, 1, v___x_3215_);
v___x_3219_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3216_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = l_Std_Format_fill(v___x_3221_);
return v___x_3222_;
}
else
{
lean_object* v___x_3223_; 
lean_dec_ref(v_xs_3209_);
v___x_3223_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3223_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_3226_ = lean_string_length(v___x_3225_);
return v___x_3226_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9);
v___x_3228_ = lean_nat_to_int(v___x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_x_3234_){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3235_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6));
v___x_3236_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3237_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_x_3234_);
v___x_3238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___x_3239_ = 0;
v___x_3240_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3240_, 0, v___x_3238_);
lean_ctor_set_uint8(v___x_3240_, sizeof(void*)*1, v___x_3239_);
v___x_3241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3235_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
v___x_3242_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3243_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
lean_ctor_set(v___x_3244_, 1, v___x_3241_);
v___x_3245_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3242_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3248_, 0, v___x_3247_);
lean_ctor_set_uint8(v___x_3248_, sizeof(void*)*1, v___x_3239_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object* v_x_3249_, lean_object* v_x_3250_, lean_object* v_x_3251_){
_start:
{
if (lean_obj_tag(v_x_3251_) == 0)
{
lean_dec(v_x_3249_);
return v_x_3250_;
}
else
{
lean_object* v_head_3252_; lean_object* v_tail_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3263_; 
v_head_3252_ = lean_ctor_get(v_x_3251_, 0);
v_tail_3253_ = lean_ctor_get(v_x_3251_, 1);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_x_3251_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3255_ = v_x_3251_;
v_isShared_3256_ = v_isSharedCheck_3263_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_tail_3253_);
lean_inc(v_head_3252_);
lean_dec(v_x_3251_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3263_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
lean_inc(v_x_3249_);
if (v_isShared_3256_ == 0)
{
lean_ctor_set_tag(v___x_3255_, 5);
lean_ctor_set(v___x_3255_, 1, v_x_3249_);
lean_ctor_set(v___x_3255_, 0, v_x_3250_);
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_x_3250_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_x_3249_);
v___x_3258_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3252_);
v___x_3260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v_x_3250_ = v___x_3260_;
v_x_3251_ = v_tail_3253_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object* v_x_3264_, lean_object* v_x_3265_, lean_object* v_x_3266_){
_start:
{
if (lean_obj_tag(v_x_3266_) == 0)
{
lean_dec(v_x_3264_);
return v_x_3265_;
}
else
{
lean_object* v_head_3267_; lean_object* v_tail_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3278_; 
v_head_3267_ = lean_ctor_get(v_x_3266_, 0);
v_tail_3268_ = lean_ctor_get(v_x_3266_, 1);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_x_3266_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3270_ = v_x_3266_;
v_isShared_3271_ = v_isSharedCheck_3278_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_tail_3268_);
lean_inc(v_head_3267_);
lean_dec(v_x_3266_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3278_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
lean_inc(v_x_3264_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set_tag(v___x_3270_, 5);
lean_ctor_set(v___x_3270_, 1, v_x_3264_);
lean_ctor_set(v___x_3270_, 0, v_x_3265_);
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_x_3265_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_x_3264_);
v___x_3273_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3274_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3267_);
v___x_3275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3273_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(v_x_3264_, v___x_3275_, v_tail_3268_);
return v___x_3276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object* v_x_3279_, lean_object* v_x_3280_){
_start:
{
if (lean_obj_tag(v_x_3279_) == 0)
{
lean_object* v___x_3281_; 
lean_dec(v_x_3280_);
v___x_3281_ = lean_box(0);
return v___x_3281_;
}
else
{
lean_object* v_tail_3282_; 
v_tail_3282_ = lean_ctor_get(v_x_3279_, 1);
if (lean_obj_tag(v_tail_3282_) == 0)
{
lean_object* v_head_3283_; lean_object* v___x_3284_; 
lean_dec(v_x_3280_);
v_head_3283_ = lean_ctor_get(v_x_3279_, 0);
lean_inc(v_head_3283_);
lean_dec_ref(v_x_3279_);
v___x_3284_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3283_);
return v___x_3284_;
}
else
{
lean_object* v_head_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
lean_inc(v_tail_3282_);
v_head_3285_ = lean_ctor_get(v_x_3279_, 0);
lean_inc(v_head_3285_);
lean_dec_ref(v_x_3279_);
v___x_3286_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3285_);
v___x_3287_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(v_x_3280_, v___x_3286_, v_tail_3282_);
return v___x_3287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object* v_xs_3288_){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3289_ = lean_array_get_size(v_xs_3288_);
v___x_3290_ = lean_unsigned_to_nat(0u);
v___x_3291_ = lean_nat_dec_eq(v___x_3289_, v___x_3290_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3292_ = lean_array_to_list(v_xs_3288_);
v___x_3293_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3294_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(v___x_3292_, v___x_3293_);
v___x_3295_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3296_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
lean_ctor_set(v___x_3297_, 1, v___x_3294_);
v___x_3298_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3295_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = l_Std_Format_fill(v___x_3300_);
return v___x_3301_;
}
else
{
lean_object* v___x_3302_; 
lean_dec_ref(v_xs_3288_);
v___x_3302_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3302_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = lean_unsigned_to_nat(0u);
v___x_3310_ = lean_nat_to_int(v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = lean_unsigned_to_nat(8u);
v___x_3327_ = lean_nat_to_int(v___x_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_x_3331_){
_start:
{
lean_object* v_term_3332_; lean_object* v_desc_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3365_; 
v_term_3332_ = lean_ctor_get(v_x_3331_, 0);
v_desc_3333_ = lean_ctor_get(v_x_3331_, 1);
v_isSharedCheck_3365_ = !lean_is_exclusive(v_x_3331_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3335_ = v_x_3331_;
v_isShared_3336_ = v_isSharedCheck_3365_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_desc_3333_);
lean_inc(v_term_3332_);
lean_dec(v_x_3331_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3365_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3337_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3338_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3));
v___x_3339_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3340_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_term_3332_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set_tag(v___x_3335_, 4);
lean_ctor_set(v___x_3335_, 1, v___x_3340_);
lean_ctor_set(v___x_3335_, 0, v___x_3339_);
v___x_3342_ = v___x_3335_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
uint8_t v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3343_ = 0;
v___x_3344_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*1, v___x_3343_);
v___x_3345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3338_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3345_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = lean_box(1);
v___x_3349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3347_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6));
v___x_3351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
lean_ctor_set(v___x_3352_, 1, v___x_3337_);
v___x_3353_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_desc_3333_);
v___x_3354_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3339_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
lean_ctor_set_uint8(v___x_3355_, sizeof(void*)*1, v___x_3343_);
v___x_3356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3352_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3358_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
lean_ctor_set(v___x_3359_, 1, v___x_3356_);
v___x_3360_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3359_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3357_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*1, v___x_3343_);
return v___x_3363_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object* v_x_3366_, lean_object* v_x_3367_, lean_object* v_x_3368_){
_start:
{
if (lean_obj_tag(v_x_3368_) == 0)
{
lean_dec(v_x_3366_);
return v_x_3367_;
}
else
{
lean_object* v_head_3369_; lean_object* v_tail_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3380_; 
v_head_3369_ = lean_ctor_get(v_x_3368_, 0);
v_tail_3370_ = lean_ctor_get(v_x_3368_, 1);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_x_3368_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3372_ = v_x_3368_;
v_isShared_3373_ = v_isSharedCheck_3380_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_tail_3370_);
lean_inc(v_head_3369_);
lean_dec(v_x_3368_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3380_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
lean_inc(v_x_3366_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set_tag(v___x_3372_, 5);
lean_ctor_set(v___x_3372_, 1, v_x_3366_);
lean_ctor_set(v___x_3372_, 0, v_x_3367_);
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_x_3367_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_x_3366_);
v___x_3375_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3369_);
v___x_3377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3375_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v_x_3367_ = v___x_3377_;
v_x_3368_ = v_tail_3370_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object* v_x_3381_, lean_object* v_x_3382_, lean_object* v_x_3383_){
_start:
{
if (lean_obj_tag(v_x_3383_) == 0)
{
lean_dec(v_x_3381_);
return v_x_3382_;
}
else
{
lean_object* v_head_3384_; lean_object* v_tail_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3395_; 
v_head_3384_ = lean_ctor_get(v_x_3383_, 0);
v_tail_3385_ = lean_ctor_get(v_x_3383_, 1);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_x_3383_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3387_ = v_x_3383_;
v_isShared_3388_ = v_isSharedCheck_3395_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_tail_3385_);
lean_inc(v_head_3384_);
lean_dec(v_x_3383_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3395_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
lean_inc(v_x_3381_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set_tag(v___x_3387_, 5);
lean_ctor_set(v___x_3387_, 1, v_x_3381_);
lean_ctor_set(v___x_3387_, 0, v_x_3382_);
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_x_3382_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_x_3381_);
v___x_3390_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3384_);
v___x_3392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3390_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(v_x_3381_, v___x_3392_, v_tail_3385_);
return v___x_3393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object* v_x_3396_, lean_object* v_x_3397_){
_start:
{
if (lean_obj_tag(v_x_3396_) == 0)
{
lean_object* v___x_3398_; 
lean_dec(v_x_3397_);
v___x_3398_ = lean_box(0);
return v___x_3398_;
}
else
{
lean_object* v_tail_3399_; 
v_tail_3399_ = lean_ctor_get(v_x_3396_, 1);
if (lean_obj_tag(v_tail_3399_) == 0)
{
lean_object* v_head_3400_; lean_object* v___x_3401_; 
lean_dec(v_x_3397_);
v_head_3400_ = lean_ctor_get(v_x_3396_, 0);
lean_inc(v_head_3400_);
lean_dec_ref(v_x_3396_);
v___x_3401_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3400_);
return v___x_3401_;
}
else
{
lean_object* v_head_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
lean_inc(v_tail_3399_);
v_head_3402_ = lean_ctor_get(v_x_3396_, 0);
lean_inc(v_head_3402_);
lean_dec_ref(v_x_3396_);
v___x_3403_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3402_);
v___x_3404_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(v_x_3397_, v___x_3403_, v_tail_3399_);
return v___x_3404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object* v_xs_3405_){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3406_ = lean_array_get_size(v_xs_3405_);
v___x_3407_ = lean_unsigned_to_nat(0u);
v___x_3408_ = lean_nat_dec_eq(v___x_3406_, v___x_3407_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3409_ = lean_array_to_list(v_xs_3405_);
v___x_3410_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3411_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(v___x_3409_, v___x_3410_);
v___x_3412_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3413_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3414_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
lean_ctor_set(v___x_3414_, 1, v___x_3411_);
v___x_3415_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3416_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3414_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3412_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v___x_3418_ = l_Std_Format_fill(v___x_3417_);
return v___x_3418_;
}
else
{
lean_object* v___x_3419_; 
lean_dec_ref(v_xs_3405_);
v___x_3419_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object* v_x_3438_, lean_object* v_prec_3439_){
_start:
{
switch(lean_obj_tag(v_x_3438_))
{
case 0:
{
lean_object* v_contents_3440_; lean_object* v___y_3442_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
v_contents_3440_ = lean_ctor_get(v_x_3438_, 0);
lean_inc_ref(v_contents_3440_);
lean_dec_ref(v_x_3438_);
v___x_3450_ = lean_unsigned_to_nat(1024u);
v___x_3451_ = lean_nat_dec_le(v___x_3450_, v_prec_3439_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3442_ = v___x_3452_;
goto v___jp_3441_;
}
else
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3442_ = v___x_3453_;
goto v___jp_3441_;
}
v___jp_3441_:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3443_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2));
v___x_3444_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_contents_3440_);
v___x_3445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3443_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
lean_inc(v___y_3442_);
v___x_3446_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___y_3442_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___x_3447_ = 0;
v___x_3448_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3448_, 0, v___x_3446_);
lean_ctor_set_uint8(v___x_3448_, sizeof(void*)*1, v___x_3447_);
v___x_3449_ = l_Repr_addAppParen(v___x_3448_, v_prec_3439_);
return v___x_3449_;
}
}
case 1:
{
lean_object* v_content_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3474_; 
v_content_3454_ = lean_ctor_get(v_x_3438_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_x_3438_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3456_ = v_x_3438_;
v_isShared_3457_ = v_isSharedCheck_3474_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_content_3454_);
lean_dec(v_x_3438_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3474_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___y_3459_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
v___x_3470_ = lean_unsigned_to_nat(1024u);
v___x_3471_ = lean_nat_dec_le(v___x_3470_, v_prec_3439_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; 
v___x_3472_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3459_ = v___x_3472_;
goto v___jp_3458_;
}
else
{
lean_object* v___x_3473_; 
v___x_3473_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3459_ = v___x_3473_;
goto v___jp_3458_;
}
v___jp_3458_:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3460_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5));
v___x_3461_ = l_String_quote(v_content_3454_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set_tag(v___x_3456_, 3);
lean_ctor_set(v___x_3456_, 0, v___x_3461_);
v___x_3463_ = v___x_3456_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; uint8_t v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3460_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
lean_inc(v___y_3459_);
v___x_3465_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___y_3459_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = 0;
v___x_3467_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3467_, 0, v___x_3465_);
lean_ctor_set_uint8(v___x_3467_, sizeof(void*)*1, v___x_3466_);
v___x_3468_ = l_Repr_addAppParen(v___x_3467_, v_prec_3439_);
return v___x_3468_;
}
}
}
}
case 2:
{
lean_object* v_items_3475_; lean_object* v___y_3477_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v_items_3475_ = lean_ctor_get(v_x_3438_, 0);
lean_inc_ref(v_items_3475_);
lean_dec_ref(v_x_3438_);
v___x_3485_ = lean_unsigned_to_nat(1024u);
v___x_3486_ = lean_nat_dec_le(v___x_3485_, v_prec_3439_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3477_ = v___x_3487_;
goto v___jp_3476_;
}
else
{
lean_object* v___x_3488_; 
v___x_3488_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3477_ = v___x_3488_;
goto v___jp_3476_;
}
v___jp_3476_:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3478_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8));
v___x_3479_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3475_);
v___x_3480_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3478_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
lean_inc(v___y_3477_);
v___x_3481_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___y_3477_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = 0;
v___x_3483_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*1, v___x_3482_);
v___x_3484_ = l_Repr_addAppParen(v___x_3483_, v_prec_3439_);
return v___x_3484_;
}
}
case 3:
{
lean_object* v_start_3489_; lean_object* v_items_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3525_; 
v_start_3489_ = lean_ctor_get(v_x_3438_, 0);
v_items_3490_ = lean_ctor_get(v_x_3438_, 1);
v_isSharedCheck_3525_ = !lean_is_exclusive(v_x_3438_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3492_ = v_x_3438_;
v_isShared_3493_ = v_isSharedCheck_3525_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_items_3490_);
lean_inc(v_start_3489_);
lean_dec(v_x_3438_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3525_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3510_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_3521_ = lean_unsigned_to_nat(1024u);
v___x_3522_ = lean_nat_dec_le(v___x_3521_, v_prec_3439_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; 
v___x_3523_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3510_ = v___x_3523_;
goto v___jp_3509_;
}
else
{
lean_object* v___x_3524_; 
v___x_3524_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3510_ = v___x_3524_;
goto v___jp_3509_;
}
v___jp_3494_:
{
lean_object* v___x_3500_; 
lean_inc(v___y_3497_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set_tag(v___x_3492_, 5);
lean_ctor_set(v___x_3492_, 1, v___y_3498_);
lean_ctor_set(v___x_3492_, 0, v___y_3497_);
v___x_3500_ = v___x_3492_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___y_3497_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v___y_3498_);
v___x_3500_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
lean_inc(v___y_3496_);
v___x_3501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
lean_ctor_set(v___x_3501_, 1, v___y_3496_);
v___x_3502_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3490_);
v___x_3503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3501_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
lean_inc(v___y_3495_);
v___x_3504_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___y_3495_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
v___x_3505_ = 0;
v___x_3506_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3506_, 0, v___x_3504_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*1, v___x_3505_);
v___x_3507_ = l_Repr_addAppParen(v___x_3506_, v_prec_3439_);
return v___x_3507_;
}
}
v___jp_3509_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
v___x_3511_ = lean_box(1);
v___x_3512_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11));
v___x_3513_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12, &l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12);
v___x_3514_ = lean_int_dec_lt(v_start_3489_, v___x_3513_);
if (v___x_3514_ == 0)
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = l_Int_repr(v_start_3489_);
lean_dec(v_start_3489_);
v___x_3516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
v___y_3495_ = v___y_3510_;
v___y_3496_ = v___x_3511_;
v___y_3497_ = v___x_3512_;
v___y_3498_ = v___x_3516_;
goto v___jp_3494_;
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3517_ = lean_unsigned_to_nat(1024u);
v___x_3518_ = l_Int_repr(v_start_3489_);
lean_dec(v_start_3489_);
v___x_3519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
v___x_3520_ = l_Repr_addAppParen(v___x_3519_, v___x_3517_);
v___y_3495_ = v___y_3510_;
v___y_3496_ = v___x_3511_;
v___y_3497_ = v___x_3512_;
v___y_3498_ = v___x_3520_;
goto v___jp_3494_;
}
}
}
}
case 4:
{
lean_object* v_items_3526_; lean_object* v___y_3528_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v_items_3526_ = lean_ctor_get(v_x_3438_, 0);
lean_inc_ref(v_items_3526_);
lean_dec_ref(v_x_3438_);
v___x_3536_ = lean_unsigned_to_nat(1024u);
v___x_3537_ = lean_nat_dec_le(v___x_3536_, v_prec_3439_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; 
v___x_3538_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3528_ = v___x_3538_;
goto v___jp_3527_;
}
else
{
lean_object* v___x_3539_; 
v___x_3539_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3528_ = v___x_3539_;
goto v___jp_3527_;
}
v___jp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3529_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15));
v___x_3530_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(v_items_3526_);
v___x_3531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3529_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
lean_inc(v___y_3528_);
v___x_3532_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___y_3528_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = 0;
v___x_3534_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3534_, 0, v___x_3532_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*1, v___x_3533_);
v___x_3535_ = l_Repr_addAppParen(v___x_3534_, v_prec_3439_);
return v___x_3535_;
}
}
case 5:
{
lean_object* v_items_3540_; lean_object* v___y_3542_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v_items_3540_ = lean_ctor_get(v_x_3438_, 0);
lean_inc_ref(v_items_3540_);
lean_dec_ref(v_x_3438_);
v___x_3550_ = lean_unsigned_to_nat(1024u);
v___x_3551_ = lean_nat_dec_le(v___x_3550_, v_prec_3439_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; 
v___x_3552_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3542_ = v___x_3552_;
goto v___jp_3541_;
}
else
{
lean_object* v___x_3553_; 
v___x_3553_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3542_ = v___x_3553_;
goto v___jp_3541_;
}
v___jp_3541_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3543_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18));
v___x_3544_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_items_3540_);
v___x_3545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3543_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
lean_inc(v___y_3542_);
v___x_3546_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___y_3542_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = 0;
v___x_3548_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3548_, 0, v___x_3546_);
lean_ctor_set_uint8(v___x_3548_, sizeof(void*)*1, v___x_3547_);
v___x_3549_ = l_Repr_addAppParen(v___x_3548_, v_prec_3439_);
return v___x_3549_;
}
}
case 6:
{
lean_object* v_content_3554_; lean_object* v___y_3556_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v_content_3554_ = lean_ctor_get(v_x_3438_, 0);
lean_inc_ref(v_content_3554_);
lean_dec_ref(v_x_3438_);
v___x_3564_ = lean_unsigned_to_nat(1024u);
v___x_3565_ = lean_nat_dec_le(v___x_3564_, v_prec_3439_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3556_ = v___x_3566_;
goto v___jp_3555_;
}
else
{
lean_object* v___x_3567_; 
v___x_3567_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3556_ = v___x_3567_;
goto v___jp_3555_;
}
v___jp_3555_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3557_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21));
v___x_3558_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3554_);
v___x_3559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3557_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
lean_inc(v___y_3556_);
v___x_3560_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___y_3556_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = 0;
v___x_3562_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set_uint8(v___x_3562_, sizeof(void*)*1, v___x_3561_);
v___x_3563_ = l_Repr_addAppParen(v___x_3562_, v_prec_3439_);
return v___x_3563_;
}
}
default: 
{
lean_object* v_container_3568_; lean_object* v_content_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3617_; 
v_container_3568_ = lean_ctor_get(v_x_3438_, 0);
v_content_3569_ = lean_ctor_get(v_x_3438_, 1);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_x_3438_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3571_ = v_x_3438_;
v_isShared_3572_ = v_isSharedCheck_3617_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_content_3569_);
lean_inc(v_container_3568_);
lean_dec(v_x_3438_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3617_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___y_3574_; lean_object* v___x_3613_; uint8_t v___x_3614_; 
v___x_3613_ = lean_unsigned_to_nat(1024u);
v___x_3614_ = lean_nat_dec_le(v___x_3613_, v_prec_3439_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; 
v___x_3615_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3574_ = v___x_3615_;
goto v___jp_3573_;
}
else
{
lean_object* v___x_3616_; 
v___x_3616_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3574_ = v___x_3616_;
goto v___jp_3573_;
}
v___jp_3573_:
{
lean_object* v_name_3575_; lean_object* v_val_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3612_; 
v_name_3575_ = lean_ctor_get(v_container_3568_, 0);
v_val_3576_ = lean_ctor_get(v_container_3568_, 1);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_container_3568_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3578_ = v_container_3568_;
v_isShared_3579_ = v_isSharedCheck_3612_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_val_3576_);
lean_inc(v_name_3575_);
lean_dec(v_container_3568_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3612_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3580_ = lean_box(1);
v___x_3581_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24));
v___x_3582_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = l_Lean_Name_reprPrec(v_name_3575_, v___x_3583_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set_tag(v___x_3578_, 5);
lean_ctor_set(v___x_3578_, 1, v___x_3584_);
lean_ctor_set(v___x_3578_, 0, v___x_3582_);
v___x_3586_ = v___x_3578_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v___x_3584_);
v___x_3586_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3587_; uint8_t v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3591_; 
v___x_3587_ = l_Std_Format_nestD(v___x_3586_);
v___x_3588_ = 0;
v___x_3589_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3589_, 0, v___x_3587_);
lean_ctor_set_uint8(v___x_3589_, sizeof(void*)*1, v___x_3588_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set_tag(v___x_3571_, 5);
lean_ctor_set(v___x_3571_, 1, v___x_3580_);
lean_ctor_set(v___x_3571_, 0, v___x_3589_);
v___x_3591_ = v___x_3571_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3589_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v___x_3580_);
v___x_3591_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3592_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3593_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3576_);
lean_dec(v_val_3576_);
v___x_3594_ = l_Lean_Name_reprPrec(v___x_3593_, v___x_3583_);
v___x_3595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3592_);
lean_ctor_set(v___x_3595_, 1, v___x_3594_);
v___x_3596_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3595_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = l_Std_Format_nestD(v___x_3597_);
v___x_3599_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*1, v___x_3588_);
v___x_3600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3591_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = l_Std_Format_nestD(v___x_3600_);
v___x_3602_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
lean_ctor_set_uint8(v___x_3602_, sizeof(void*)*1, v___x_3588_);
v___x_3603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3581_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3603_);
lean_ctor_set(v___x_3604_, 1, v___x_3580_);
v___x_3605_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3569_);
v___x_3606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3604_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
lean_inc(v___y_3574_);
v___x_3607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___y_3574_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set_uint8(v___x_3608_, sizeof(void*)*1, v___x_3588_);
v___x_3609_ = l_Repr_addAppParen(v___x_3608_, v_prec_3439_);
return v___x_3609_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object* v___y_3618_){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = lean_unsigned_to_nat(0u);
v___x_3620_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v___y_3618_, v___x_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object* v_x_3621_, lean_object* v_prec_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_x_3621_, v_prec_3622_);
lean_dec(v_prec_3622_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object* v_xs_3624_){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; uint8_t v___x_3627_; 
v___x_3625_ = lean_array_get_size(v_xs_3624_);
v___x_3626_ = lean_unsigned_to_nat(0u);
v___x_3627_ = lean_nat_dec_eq(v___x_3625_, v___x_3626_);
if (v___x_3627_ == 0)
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3628_ = lean_array_to_list(v_xs_3624_);
v___x_3629_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3630_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3628_, v___x_3629_);
v___x_3631_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3632_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
lean_ctor_set(v___x_3633_, 1, v___x_3630_);
v___x_3634_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3633_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3631_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
v___x_3637_ = l_Std_Format_fill(v___x_3636_);
return v___x_3637_;
}
else
{
lean_object* v___x_3638_; 
lean_dec_ref(v_xs_3624_);
v___x_3638_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object* v_x_3642_){
_start:
{
lean_object* v___x_3643_; 
v___x_3643_ = ((lean_object*)(l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1));
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object* v_x_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3644_);
lean_dec(v_x_3644_);
return v_res_3645_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = lean_unsigned_to_nat(9u);
v___x_3656_ = lean_nat_to_int(v___x_3655_);
return v___x_3656_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = lean_unsigned_to_nat(15u);
v___x_3661_ = lean_nat_to_int(v___x_3660_);
return v___x_3661_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12(void){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = lean_unsigned_to_nat(11u);
v___x_3669_ = lean_nat_to_int(v___x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object* v_x_3673_, lean_object* v_x_3674_, lean_object* v_x_3675_){
_start:
{
if (lean_obj_tag(v_x_3675_) == 0)
{
lean_dec(v_x_3673_);
return v_x_3674_;
}
else
{
lean_object* v_head_3676_; lean_object* v_tail_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3687_; 
v_head_3676_ = lean_ctor_get(v_x_3675_, 0);
v_tail_3677_ = lean_ctor_get(v_x_3675_, 1);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_x_3675_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3679_ = v_x_3675_;
v_isShared_3680_ = v_isSharedCheck_3687_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_tail_3677_);
lean_inc(v_head_3676_);
lean_dec(v_x_3675_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3687_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
lean_inc(v_x_3673_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set_tag(v___x_3679_, 5);
lean_ctor_set(v___x_3679_, 1, v_x_3673_);
lean_ctor_set(v___x_3679_, 0, v_x_3674_);
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_x_3674_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_x_3673_);
v___x_3682_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3683_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3676_);
v___x_3684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3682_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
v___x_3685_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(v_x_3673_, v___x_3684_, v_tail_3677_);
return v___x_3685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object* v_x_3688_, lean_object* v_x_3689_){
_start:
{
if (lean_obj_tag(v_x_3688_) == 0)
{
lean_object* v___x_3690_; 
lean_dec(v_x_3689_);
v___x_3690_ = lean_box(0);
return v___x_3690_;
}
else
{
lean_object* v_tail_3691_; 
v_tail_3691_ = lean_ctor_get(v_x_3688_, 1);
if (lean_obj_tag(v_tail_3691_) == 0)
{
lean_object* v_head_3692_; lean_object* v___x_3693_; 
lean_dec(v_x_3689_);
v_head_3692_ = lean_ctor_get(v_x_3688_, 0);
lean_inc(v_head_3692_);
lean_dec_ref(v_x_3688_);
v___x_3693_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3692_);
return v___x_3693_;
}
else
{
lean_object* v_head_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
lean_inc(v_tail_3691_);
v_head_3694_ = lean_ctor_get(v_x_3688_, 0);
lean_inc(v_head_3694_);
lean_dec_ref(v_x_3688_);
v___x_3695_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3694_);
v___x_3696_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(v_x_3689_, v___x_3695_, v_tail_3691_);
return v___x_3696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object* v_xs_3697_){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; uint8_t v___x_3700_; 
v___x_3698_ = lean_array_get_size(v_xs_3697_);
v___x_3699_ = lean_unsigned_to_nat(0u);
v___x_3700_ = lean_nat_dec_eq(v___x_3698_, v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3701_ = lean_array_to_list(v_xs_3697_);
v___x_3702_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3703_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(v___x_3701_, v___x_3702_);
v___x_3704_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3705_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3705_);
lean_ctor_set(v___x_3706_, 1, v___x_3703_);
v___x_3707_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3706_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
v___x_3709_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3704_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = l_Std_Format_fill(v___x_3709_);
return v___x_3710_;
}
else
{
lean_object* v___x_3711_; 
lean_dec_ref(v_xs_3697_);
v___x_3711_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object* v_x_3712_){
_start:
{
lean_object* v_title_3713_; lean_object* v_titleString_3714_; lean_object* v_metadata_3715_; lean_object* v_content_3716_; lean_object* v_subParts_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v_title_3713_ = lean_ctor_get(v_x_3712_, 0);
lean_inc_ref(v_title_3713_);
v_titleString_3714_ = lean_ctor_get(v_x_3712_, 1);
lean_inc_ref(v_titleString_3714_);
v_metadata_3715_ = lean_ctor_get(v_x_3712_, 2);
lean_inc(v_metadata_3715_);
v_content_3716_ = lean_ctor_get(v_x_3712_, 3);
lean_inc_ref(v_content_3716_);
v_subParts_3717_ = lean_ctor_get(v_x_3712_, 4);
lean_inc_ref(v_subParts_3717_);
lean_dec_ref(v_x_3712_);
v___x_3718_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3719_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3));
v___x_3720_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4);
v___x_3721_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_title_3713_);
v___x_3722_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3720_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = 0;
v___x_3724_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3724_, 0, v___x_3722_);
lean_ctor_set_uint8(v___x_3724_, sizeof(void*)*1, v___x_3723_);
v___x_3725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3719_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = lean_box(1);
v___x_3729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6));
v___x_3731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3729_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
lean_ctor_set(v___x_3732_, 1, v___x_3718_);
v___x_3733_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7);
v___x_3734_ = l_String_quote(v_titleString_3714_);
v___x_3735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3733_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set_uint8(v___x_3737_, sizeof(void*)*1, v___x_3723_);
v___x_3738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3732_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
lean_ctor_set(v___x_3739_, 1, v___x_3726_);
v___x_3740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
lean_ctor_set(v___x_3740_, 1, v___x_3728_);
v___x_3741_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9));
v___x_3742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3740_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
v___x_3743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
lean_ctor_set(v___x_3743_, 1, v___x_3718_);
v___x_3744_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3745_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_metadata_3715_);
lean_dec(v_metadata_3715_);
v___x_3746_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3744_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*1, v___x_3723_);
v___x_3748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3743_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
lean_ctor_set(v___x_3749_, 1, v___x_3726_);
v___x_3750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
lean_ctor_set(v___x_3750_, 1, v___x_3728_);
v___x_3751_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11));
v___x_3752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
lean_ctor_set(v___x_3753_, 1, v___x_3718_);
v___x_3754_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12);
v___x_3755_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_content_3716_);
v___x_3756_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3754_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set_uint8(v___x_3757_, sizeof(void*)*1, v___x_3723_);
v___x_3758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3753_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
v___x_3759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
lean_ctor_set(v___x_3759_, 1, v___x_3726_);
v___x_3760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
lean_ctor_set(v___x_3760_, 1, v___x_3728_);
v___x_3761_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14));
v___x_3762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
lean_ctor_set(v___x_3763_, 1, v___x_3718_);
v___x_3764_ = l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(v_subParts_3717_);
v___x_3765_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3744_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
lean_ctor_set_uint8(v___x_3766_, sizeof(void*)*1, v___x_3723_);
v___x_3767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3763_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3769_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
lean_ctor_set(v___x_3770_, 1, v___x_3767_);
v___x_3771_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3770_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3768_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
lean_ctor_set_uint8(v___x_3774_, sizeof(void*)*1, v___x_3723_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object* v_x_3775_, lean_object* v_x_3776_, lean_object* v_x_3777_){
_start:
{
if (lean_obj_tag(v_x_3777_) == 0)
{
lean_dec(v_x_3775_);
return v_x_3776_;
}
else
{
lean_object* v_head_3778_; lean_object* v_tail_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3789_; 
v_head_3778_ = lean_ctor_get(v_x_3777_, 0);
v_tail_3779_ = lean_ctor_get(v_x_3777_, 1);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_x_3777_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3781_ = v_x_3777_;
v_isShared_3782_ = v_isSharedCheck_3789_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_tail_3779_);
lean_inc(v_head_3778_);
lean_dec(v_x_3777_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3789_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
lean_inc(v_x_3775_);
if (v_isShared_3782_ == 0)
{
lean_ctor_set_tag(v___x_3781_, 5);
lean_ctor_set(v___x_3781_, 1, v_x_3775_);
lean_ctor_set(v___x_3781_, 0, v_x_3776_);
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_x_3776_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v_x_3775_);
v___x_3784_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3778_);
v___x_3786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3784_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v_x_3776_ = v___x_3786_;
v_x_3777_ = v_tail_3779_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object* v_x_3790_, lean_object* v_x_3791_){
_start:
{
lean_object* v_fst_3792_; lean_object* v_snd_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3803_; 
v_fst_3792_ = lean_ctor_get(v_x_3790_, 0);
v_snd_3793_ = lean_ctor_get(v_x_3790_, 1);
v_isSharedCheck_3803_ = !lean_is_exclusive(v_x_3790_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3795_ = v_x_3790_;
v_isShared_3796_ = v_isSharedCheck_3803_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_snd_3793_);
lean_inc(v_fst_3792_);
lean_dec(v_x_3790_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3803_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3797_; lean_object* v___x_3799_; 
v___x_3797_ = l_Lean_instReprDeclarationRange_repr___redArg(v_fst_3792_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set_tag(v___x_3795_, 1);
lean_ctor_set(v___x_3795_, 1, v_x_3791_);
lean_ctor_set(v___x_3795_, 0, v___x_3797_);
v___x_3799_ = v___x_3795_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3797_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_x_3791_);
v___x_3799_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_snd_3793_);
v___x_3801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
lean_ctor_set(v___x_3801_, 1, v___x_3799_);
return v___x_3801_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object* v_x_3804_, lean_object* v_x_3805_, lean_object* v_x_3806_){
_start:
{
if (lean_obj_tag(v_x_3806_) == 0)
{
lean_dec(v_x_3804_);
return v_x_3805_;
}
else
{
lean_object* v_head_3807_; lean_object* v_tail_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3817_; 
v_head_3807_ = lean_ctor_get(v_x_3806_, 0);
v_tail_3808_ = lean_ctor_get(v_x_3806_, 1);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_x_3806_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3810_ = v_x_3806_;
v_isShared_3811_ = v_isSharedCheck_3817_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_tail_3808_);
lean_inc(v_head_3807_);
lean_dec(v_x_3806_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3817_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
lean_inc(v_x_3804_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set_tag(v___x_3810_, 5);
lean_ctor_set(v___x_3810_, 1, v_x_3804_);
lean_ctor_set(v___x_3810_, 0, v_x_3805_);
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_x_3805_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_x_3804_);
v___x_3813_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
lean_object* v___x_3814_; 
v___x_3814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set(v___x_3814_, 1, v_head_3807_);
v_x_3805_ = v___x_3814_;
v_x_3806_ = v_tail_3808_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object* v_x_3818_, lean_object* v_x_3819_){
_start:
{
if (lean_obj_tag(v_x_3818_) == 0)
{
lean_object* v___x_3820_; 
lean_dec(v_x_3819_);
v___x_3820_ = lean_box(0);
return v___x_3820_;
}
else
{
lean_object* v_tail_3821_; 
v_tail_3821_ = lean_ctor_get(v_x_3818_, 1);
if (lean_obj_tag(v_tail_3821_) == 0)
{
lean_object* v_head_3822_; 
lean_dec(v_x_3819_);
v_head_3822_ = lean_ctor_get(v_x_3818_, 0);
lean_inc(v_head_3822_);
lean_dec_ref(v_x_3818_);
return v_head_3822_;
}
else
{
lean_object* v_head_3823_; lean_object* v___x_3824_; 
lean_inc(v_tail_3821_);
v_head_3823_ = lean_ctor_get(v_x_3818_, 0);
lean_inc(v_head_3823_);
lean_dec_ref(v_x_3818_);
v___x_3824_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(v_x_3819_, v_head_3823_, v_tail_3821_);
return v___x_3824_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3826_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0));
v___x_3827_ = lean_string_length(v___x_3826_);
return v___x_3827_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3828_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1);
v___x_3829_ = lean_nat_to_int(v___x_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object* v_x_3834_){
_start:
{
lean_object* v_fst_3835_; lean_object* v_snd_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3858_; 
v_fst_3835_ = lean_ctor_get(v_x_3834_, 0);
v_snd_3836_ = lean_ctor_get(v_x_3834_, 1);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_x_3834_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3838_ = v_x_3834_;
v_isShared_3839_ = v_isSharedCheck_3858_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_snd_3836_);
lean_inc(v_fst_3835_);
lean_dec(v_x_3834_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3858_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
v___x_3840_ = l_Nat_reprFast(v_fst_3835_);
v___x_3841_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
v___x_3842_ = lean_box(0);
if (v_isShared_3839_ == 0)
{
lean_ctor_set_tag(v___x_3838_, 1);
lean_ctor_set(v___x_3838_, 1, v___x_3842_);
lean_ctor_set(v___x_3838_, 0, v___x_3841_);
v___x_3844_ = v___x_3838_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3841_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; lean_object* v___x_3856_; 
v___x_3845_ = l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(v_snd_3836_, v___x_3844_);
v___x_3846_ = l_List_reverse___redArg(v___x_3845_);
v___x_3847_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3848_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(v___x_3846_, v___x_3847_);
v___x_3849_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2);
v___x_3850_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3));
v___x_3851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
lean_ctor_set(v___x_3851_, 1, v___x_3848_);
v___x_3852_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4));
v___x_3853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3851_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v___x_3854_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3849_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = 0;
v___x_3856_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3856_, 0, v___x_3854_);
lean_ctor_set_uint8(v___x_3856_, sizeof(void*)*1, v___x_3855_);
return v___x_3856_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object* v_x_3859_, lean_object* v_x_3860_, lean_object* v_x_3861_){
_start:
{
if (lean_obj_tag(v_x_3861_) == 0)
{
lean_dec(v_x_3859_);
return v_x_3860_;
}
else
{
lean_object* v_head_3862_; lean_object* v_tail_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3873_; 
v_head_3862_ = lean_ctor_get(v_x_3861_, 0);
v_tail_3863_ = lean_ctor_get(v_x_3861_, 1);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_x_3861_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3865_ = v_x_3861_;
v_isShared_3866_ = v_isSharedCheck_3873_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_tail_3863_);
lean_inc(v_head_3862_);
lean_dec(v_x_3861_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3873_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
lean_inc(v_x_3859_);
if (v_isShared_3866_ == 0)
{
lean_ctor_set_tag(v___x_3865_, 5);
lean_ctor_set(v___x_3865_, 1, v_x_3859_);
lean_ctor_set(v___x_3865_, 0, v_x_3860_);
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_x_3860_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_x_3859_);
v___x_3868_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3862_);
v___x_3870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3868_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
v_x_3860_ = v___x_3870_;
v_x_3861_ = v_tail_3863_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object* v_x_3874_, lean_object* v_x_3875_, lean_object* v_x_3876_){
_start:
{
if (lean_obj_tag(v_x_3876_) == 0)
{
lean_dec(v_x_3874_);
return v_x_3875_;
}
else
{
lean_object* v_head_3877_; lean_object* v_tail_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3888_; 
v_head_3877_ = lean_ctor_get(v_x_3876_, 0);
v_tail_3878_ = lean_ctor_get(v_x_3876_, 1);
v_isSharedCheck_3888_ = !lean_is_exclusive(v_x_3876_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3880_ = v_x_3876_;
v_isShared_3881_ = v_isSharedCheck_3888_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_tail_3878_);
lean_inc(v_head_3877_);
lean_dec(v_x_3876_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3888_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
lean_inc(v_x_3874_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set_tag(v___x_3880_, 5);
lean_ctor_set(v___x_3880_, 1, v_x_3874_);
lean_ctor_set(v___x_3880_, 0, v_x_3875_);
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_x_3875_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v_x_3874_);
v___x_3883_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3884_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3877_);
v___x_3885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3883_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
v___x_3886_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(v_x_3874_, v___x_3885_, v_tail_3878_);
return v___x_3886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object* v_x_3889_, lean_object* v_x_3890_){
_start:
{
if (lean_obj_tag(v_x_3889_) == 0)
{
lean_object* v___x_3891_; 
lean_dec(v_x_3890_);
v___x_3891_ = lean_box(0);
return v___x_3891_;
}
else
{
lean_object* v_tail_3892_; 
v_tail_3892_ = lean_ctor_get(v_x_3889_, 1);
if (lean_obj_tag(v_tail_3892_) == 0)
{
lean_object* v_head_3893_; lean_object* v___x_3894_; 
lean_dec(v_x_3890_);
v_head_3893_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_head_3893_);
lean_dec_ref(v_x_3889_);
v___x_3894_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3893_);
return v___x_3894_;
}
else
{
lean_object* v_head_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
lean_inc(v_tail_3892_);
v_head_3895_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_head_3895_);
lean_dec_ref(v_x_3889_);
v___x_3896_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3895_);
v___x_3897_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(v_x_3890_, v___x_3896_, v_tail_3892_);
return v___x_3897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object* v_xs_3898_){
_start:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; 
v___x_3899_ = lean_array_get_size(v_xs_3898_);
v___x_3900_ = lean_unsigned_to_nat(0u);
v___x_3901_ = lean_nat_dec_eq(v___x_3899_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3902_ = lean_array_to_list(v_xs_3898_);
v___x_3903_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3904_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(v___x_3902_, v___x_3903_);
v___x_3905_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3906_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
lean_ctor_set(v___x_3907_, 1, v___x_3904_);
v___x_3908_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3907_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3905_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
v___x_3911_ = l_Std_Format_fill(v___x_3910_);
return v___x_3911_;
}
else
{
lean_object* v___x_3912_; 
lean_dec_ref(v_xs_3898_);
v___x_3912_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3912_;
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3928_ = lean_unsigned_to_nat(20u);
v___x_3929_ = lean_nat_to_int(v___x_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object* v_x_3930_){
_start:
{
lean_object* v_text_3931_; lean_object* v_sections_3932_; lean_object* v_declarationRange_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v_text_3931_ = lean_ctor_get(v_x_3930_, 0);
lean_inc_ref(v_text_3931_);
v_sections_3932_ = lean_ctor_get(v_x_3930_, 1);
lean_inc_ref(v_sections_3932_);
v_declarationRange_3933_ = lean_ctor_get(v_x_3930_, 2);
lean_inc_ref(v_declarationRange_3933_);
lean_dec_ref(v_x_3930_);
v___x_3934_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3935_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3));
v___x_3936_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3937_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_text_3931_);
v___x_3938_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3936_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
v___x_3939_ = 0;
v___x_3940_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3940_, 0, v___x_3938_);
lean_ctor_set_uint8(v___x_3940_, sizeof(void*)*1, v___x_3939_);
v___x_3941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3935_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
v___x_3942_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3941_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = lean_box(1);
v___x_3945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3943_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5));
v___x_3947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3945_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
v___x_3948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3947_);
lean_ctor_set(v___x_3948_, 1, v___x_3934_);
v___x_3949_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3950_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(v_sections_3932_);
v___x_3951_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3949_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
v___x_3952_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
lean_ctor_set_uint8(v___x_3952_, sizeof(void*)*1, v___x_3939_);
v___x_3953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3948_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___x_3954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
lean_ctor_set(v___x_3954_, 1, v___x_3942_);
v___x_3955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
lean_ctor_set(v___x_3955_, 1, v___x_3944_);
v___x_3956_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7));
v___x_3957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3955_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
lean_ctor_set(v___x_3958_, 1, v___x_3934_);
v___x_3959_ = lean_obj_once(&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8, &l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once, _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8);
v___x_3960_ = l_Lean_instReprDeclarationRange_repr___redArg(v_declarationRange_3933_);
v___x_3961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3959_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set_uint8(v___x_3962_, sizeof(void*)*1, v___x_3939_);
v___x_3963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3958_);
lean_ctor_set(v___x_3963_, 1, v___x_3962_);
v___x_3964_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3965_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
lean_ctor_set(v___x_3966_, 1, v___x_3963_);
v___x_3967_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3966_);
lean_ctor_set(v___x_3968_, 1, v___x_3967_);
v___x_3969_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3964_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
lean_ctor_set_uint8(v___x_3970_, sizeof(void*)*1, v___x_3939_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object* v_x_3971_, lean_object* v_prec_3972_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(v_x_3971_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object* v_x_3974_, lean_object* v_prec_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lean_VersoModuleDocs_instReprSnippet_repr(v_x_3974_, v_prec_3975_);
lean_dec(v_prec_3975_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object* v_x_3977_, lean_object* v_x_3978_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_x_3977_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object* v_x_3980_, lean_object* v_x_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(v_x_3980_, v_x_3981_);
lean_dec(v_x_3981_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_3983_, lean_object* v_prec_3984_){
_start:
{
lean_object* v___x_3985_; 
v___x_3985_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_x_3983_);
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_x_3986_, lean_object* v_prec_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(v_x_3986_, v_prec_3987_);
lean_dec(v_prec_3987_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object* v_x_3989_, lean_object* v_prec_3990_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_x_3989_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_x_3992_, lean_object* v_prec_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(v_x_3992_, v_prec_3993_);
lean_dec(v_prec_3993_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object* v_x_3995_, lean_object* v_x_3996_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3995_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object* v_x_3998_, lean_object* v_x_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(v_x_3998_, v_x_3999_);
lean_dec(v_x_3999_);
lean_dec(v_x_3998_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object* v_x_4001_, lean_object* v_prec_4002_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_x_4001_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object* v_x_4004_, lean_object* v_prec_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(v_x_4004_, v_prec_4005_);
lean_dec(v_prec_4005_);
return v_res_4006_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object* v_level_4009_, lean_object* v_snippet_4010_){
_start:
{
lean_object* v_sections_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; 
v_sections_4011_ = lean_ctor_get(v_snippet_4010_, 1);
v___x_4012_ = lean_unsigned_to_nat(0u);
v___x_4013_ = lean_array_get_size(v_sections_4011_);
v___x_4014_ = lean_nat_dec_lt(v___x_4012_, v___x_4013_);
if (v___x_4014_ == 0)
{
uint8_t v___x_4015_; 
v___x_4015_ = 1;
return v___x_4015_;
}
else
{
lean_object* v___x_4016_; lean_object* v_fst_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; uint8_t v___x_4020_; 
v___x_4016_ = lean_array_fget_borrowed(v_sections_4011_, v___x_4012_);
v_fst_4017_ = lean_ctor_get(v___x_4016_, 0);
v___x_4018_ = lean_unsigned_to_nat(1u);
v___x_4019_ = lean_nat_add(v_level_4009_, v___x_4018_);
v___x_4020_ = lean_nat_dec_le(v_fst_4017_, v___x_4019_);
lean_dec(v___x_4019_);
return v___x_4020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object* v_level_4021_, lean_object* v_snippet_4022_){
_start:
{
uint8_t v_res_4023_; lean_object* v_r_4024_; 
v_res_4023_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_level_4021_, v_snippet_4022_);
lean_dec_ref(v_snippet_4022_);
lean_dec(v_level_4021_);
v_r_4024_ = lean_box(v_res_4023_);
return v_r_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object* v_snippet_4025_){
_start:
{
lean_object* v_sections_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; uint8_t v___x_4030_; 
v_sections_4026_ = lean_ctor_get(v_snippet_4025_, 1);
v___x_4027_ = lean_array_get_size(v_sections_4026_);
v___x_4028_ = lean_unsigned_to_nat(1u);
v___x_4029_ = lean_nat_sub(v___x_4027_, v___x_4028_);
v___x_4030_ = lean_nat_dec_lt(v___x_4029_, v___x_4027_);
if (v___x_4030_ == 0)
{
lean_object* v___x_4031_; 
lean_dec(v___x_4029_);
v___x_4031_ = lean_box(0);
return v___x_4031_;
}
else
{
lean_object* v___x_4032_; lean_object* v_fst_4033_; lean_object* v___x_4034_; 
v___x_4032_ = lean_array_fget_borrowed(v_sections_4026_, v___x_4029_);
lean_dec(v___x_4029_);
v_fst_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_fst_4033_);
v___x_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4034_, 0, v_fst_4033_);
return v___x_4034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object* v_snippet_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4035_);
lean_dec_ref(v_snippet_4035_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object* v_snippet_4037_, lean_object* v_block_4038_){
_start:
{
lean_object* v_text_4039_; lean_object* v_sections_4040_; lean_object* v_declarationRange_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; uint8_t v___x_4044_; 
v_text_4039_ = lean_ctor_get(v_snippet_4037_, 0);
v_sections_4040_ = lean_ctor_get(v_snippet_4037_, 1);
v_declarationRange_4041_ = lean_ctor_get(v_snippet_4037_, 2);
v___x_4042_ = lean_array_get_size(v_sections_4040_);
v___x_4043_ = lean_unsigned_to_nat(0u);
v___x_4044_ = lean_nat_dec_eq(v___x_4042_, v___x_4043_);
if (v___x_4044_ == 0)
{
lean_object* v___x_4045_; lean_object* v___x_4046_; uint8_t v___x_4047_; 
v___x_4045_ = lean_unsigned_to_nat(1u);
v___x_4046_ = lean_nat_sub(v___x_4042_, v___x_4045_);
v___x_4047_ = lean_nat_dec_lt(v___x_4046_, v___x_4042_);
if (v___x_4047_ == 0)
{
lean_dec(v___x_4046_);
lean_dec_ref(v_block_4038_);
return v_snippet_4037_;
}
else
{
lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4091_; 
lean_inc_ref(v_declarationRange_4041_);
lean_inc_ref(v_sections_4040_);
lean_inc_ref(v_text_4039_);
v_isSharedCheck_4091_ = !lean_is_exclusive(v_snippet_4037_);
if (v_isSharedCheck_4091_ == 0)
{
lean_object* v_unused_4092_; lean_object* v_unused_4093_; lean_object* v_unused_4094_; 
v_unused_4092_ = lean_ctor_get(v_snippet_4037_, 2);
lean_dec(v_unused_4092_);
v_unused_4093_ = lean_ctor_get(v_snippet_4037_, 1);
lean_dec(v_unused_4093_);
v_unused_4094_ = lean_ctor_get(v_snippet_4037_, 0);
lean_dec(v_unused_4094_);
v___x_4049_ = v_snippet_4037_;
v_isShared_4050_ = v_isSharedCheck_4091_;
goto v_resetjp_4048_;
}
else
{
lean_dec(v_snippet_4037_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4091_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v_v_4051_; lean_object* v_snd_4052_; lean_object* v_snd_4053_; lean_object* v_fst_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4089_; 
v_v_4051_ = lean_array_fget(v_sections_4040_, v___x_4046_);
v_snd_4052_ = lean_ctor_get(v_v_4051_, 1);
lean_inc(v_snd_4052_);
v_snd_4053_ = lean_ctor_get(v_snd_4052_, 1);
lean_inc(v_snd_4053_);
v_fst_4054_ = lean_ctor_get(v_v_4051_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_v_4051_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; 
v_unused_4090_ = lean_ctor_get(v_v_4051_, 1);
lean_dec(v_unused_4090_);
v___x_4056_ = v_v_4051_;
v_isShared_4057_ = v_isSharedCheck_4089_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_fst_4054_);
lean_dec(v_v_4051_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4089_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v_fst_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4087_; 
v_fst_4058_ = lean_ctor_get(v_snd_4052_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_snd_4052_);
if (v_isSharedCheck_4087_ == 0)
{
lean_object* v_unused_4088_; 
v_unused_4088_ = lean_ctor_get(v_snd_4052_, 1);
lean_dec(v_unused_4088_);
v___x_4060_ = v_snd_4052_;
v_isShared_4061_ = v_isSharedCheck_4087_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_fst_4058_);
lean_dec(v_snd_4052_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4087_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v_title_4062_; lean_object* v_titleString_4063_; lean_object* v_metadata_4064_; lean_object* v_content_4065_; lean_object* v_subParts_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4086_; 
v_title_4062_ = lean_ctor_get(v_snd_4053_, 0);
v_titleString_4063_ = lean_ctor_get(v_snd_4053_, 1);
v_metadata_4064_ = lean_ctor_get(v_snd_4053_, 2);
v_content_4065_ = lean_ctor_get(v_snd_4053_, 3);
v_subParts_4066_ = lean_ctor_get(v_snd_4053_, 4);
v_isSharedCheck_4086_ = !lean_is_exclusive(v_snd_4053_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4068_ = v_snd_4053_;
v_isShared_4069_ = v_isSharedCheck_4086_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_subParts_4066_);
lean_inc(v_content_4065_);
lean_inc(v_metadata_4064_);
lean_inc(v_titleString_4063_);
lean_inc(v_title_4062_);
lean_dec(v_snd_4053_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4086_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4070_; lean_object* v_xs_x27_4071_; lean_object* v___x_4072_; lean_object* v___x_4074_; 
v___x_4070_ = lean_box(0);
v_xs_x27_4071_ = lean_array_fset(v_sections_4040_, v___x_4046_, v___x_4070_);
v___x_4072_ = lean_array_push(v_content_4065_, v_block_4038_);
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 3, v___x_4072_);
v___x_4074_ = v___x_4068_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_title_4062_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v_titleString_4063_);
lean_ctor_set(v_reuseFailAlloc_4085_, 2, v_metadata_4064_);
lean_ctor_set(v_reuseFailAlloc_4085_, 3, v___x_4072_);
lean_ctor_set(v_reuseFailAlloc_4085_, 4, v_subParts_4066_);
v___x_4074_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4076_; 
if (v_isShared_4061_ == 0)
{
lean_ctor_set(v___x_4060_, 1, v___x_4074_);
v___x_4076_ = v___x_4060_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_fst_4058_);
lean_ctor_set(v_reuseFailAlloc_4084_, 1, v___x_4074_);
v___x_4076_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4078_; 
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 1, v___x_4076_);
v___x_4078_ = v___x_4056_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_fst_4054_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v___x_4076_);
v___x_4078_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
lean_object* v___x_4079_; lean_object* v___x_4081_; 
v___x_4079_ = lean_array_fset(v_xs_x27_4071_, v___x_4046_, v___x_4078_);
lean_dec(v___x_4046_);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 1, v___x_4079_);
v___x_4081_ = v___x_4049_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_text_4039_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v___x_4079_);
lean_ctor_set(v_reuseFailAlloc_4082_, 2, v_declarationRange_4041_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
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
lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4102_; 
lean_inc_ref(v_declarationRange_4041_);
lean_inc_ref(v_sections_4040_);
lean_inc_ref(v_text_4039_);
v_isSharedCheck_4102_ = !lean_is_exclusive(v_snippet_4037_);
if (v_isSharedCheck_4102_ == 0)
{
lean_object* v_unused_4103_; lean_object* v_unused_4104_; lean_object* v_unused_4105_; 
v_unused_4103_ = lean_ctor_get(v_snippet_4037_, 2);
lean_dec(v_unused_4103_);
v_unused_4104_ = lean_ctor_get(v_snippet_4037_, 1);
lean_dec(v_unused_4104_);
v_unused_4105_ = lean_ctor_get(v_snippet_4037_, 0);
lean_dec(v_unused_4105_);
v___x_4096_ = v_snippet_4037_;
v_isShared_4097_ = v_isSharedCheck_4102_;
goto v_resetjp_4095_;
}
else
{
lean_dec(v_snippet_4037_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4102_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4098_; lean_object* v___x_4100_; 
v___x_4098_ = lean_array_push(v_text_4039_, v_block_4038_);
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 0, v___x_4098_);
v___x_4100_ = v___x_4096_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v___x_4098_);
lean_ctor_set(v_reuseFailAlloc_4101_, 1, v_sections_4040_);
lean_ctor_set(v_reuseFailAlloc_4101_, 2, v_declarationRange_4041_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object* v_snippet_4106_, lean_object* v_level_4107_, lean_object* v_range_4108_, lean_object* v_part_4109_){
_start:
{
lean_object* v_text_4110_; lean_object* v_sections_4111_; lean_object* v_declarationRange_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4122_; 
v_text_4110_ = lean_ctor_get(v_snippet_4106_, 0);
v_sections_4111_ = lean_ctor_get(v_snippet_4106_, 1);
v_declarationRange_4112_ = lean_ctor_get(v_snippet_4106_, 2);
v_isSharedCheck_4122_ = !lean_is_exclusive(v_snippet_4106_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4114_ = v_snippet_4106_;
v_isShared_4115_ = v_isSharedCheck_4122_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_declarationRange_4112_);
lean_inc(v_sections_4111_);
lean_inc(v_text_4110_);
lean_dec(v_snippet_4106_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4122_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4120_; 
v___x_4116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4116_, 0, v_range_4108_);
lean_ctor_set(v___x_4116_, 1, v_part_4109_);
v___x_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4117_, 0, v_level_4107_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = lean_array_push(v_sections_4111_, v___x_4117_);
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 1, v___x_4118_);
v___x_4120_ = v___x_4114_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_text_4110_);
lean_ctor_set(v_reuseFailAlloc_4121_, 1, v___x_4118_);
lean_ctor_set(v_reuseFailAlloc_4121_, 2, v_declarationRange_4112_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0(lean_object* v___x_4123_, lean_object* v___x_4124_, lean_object* v_x_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v___x_4123_, v___x_4124_, v___y_4126_, v___y_4127_, v___y_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_4130_, lean_object* v___x_4131_, lean_object* v_x_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean_instToMarkdownSnippet___lam__0(v___x_4130_, v___x_4131_, v_x_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec_ref(v___y_4134_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1(lean_object* v___x_4137_, lean_object* v___x_4138_, lean_object* v___x_4139_, lean_object* v_a_4140_, lean_object* v_x_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4145_; lean_object* v_snd_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4154_; 
v___x_4145_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v___x_4137_, v___x_4138_, v_a_4140_, v___y_4143_, v___y_4144_);
v_snd_4146_ = lean_ctor_get(v___x_4145_, 1);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4154_ == 0)
{
lean_object* v_unused_4155_; 
v_unused_4155_ = lean_ctor_get(v___x_4145_, 0);
lean_dec(v_unused_4155_);
v___x_4148_ = v___x_4145_;
v_isShared_4149_ = v_isSharedCheck_4154_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_snd_4146_);
lean_dec(v___x_4145_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4154_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4150_; lean_object* v___x_4152_; 
v___x_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4139_);
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 0, v___x_4150_);
v___x_4152_ = v___x_4148_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4150_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_snd_4146_);
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
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_4156_, lean_object* v___x_4157_, lean_object* v___x_4158_, lean_object* v_a_4159_, lean_object* v_x_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_instToMarkdownSnippet___lam__1(v___x_4156_, v___x_4157_, v___x_4158_, v_a_4159_, v_x_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
lean_dec_ref(v___y_4162_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2(lean_object* v___x_4165_, lean_object* v___x_4166_, lean_object* v_a_4167_, lean_object* v_x_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4172_; lean_object* v_snd_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4181_; 
v___x_4172_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_box(0), v___x_4165_, v_a_4167_, v___y_4170_, v___y_4171_);
v_snd_4173_ = lean_ctor_get(v___x_4172_, 1);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4181_ == 0)
{
lean_object* v_unused_4182_; 
v_unused_4182_ = lean_ctor_get(v___x_4172_, 0);
lean_dec(v_unused_4182_);
v___x_4175_ = v___x_4172_;
v_isShared_4176_ = v_isSharedCheck_4181_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_snd_4173_);
lean_dec(v___x_4172_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4181_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4177_; lean_object* v___x_4179_; 
v___x_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4166_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v___x_4177_);
v___x_4179_ = v___x_4175_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v_snd_4173_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2___boxed(lean_object* v___x_4183_, lean_object* v___x_4184_, lean_object* v_a_4185_, lean_object* v_x_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_instToMarkdownSnippet___lam__2(v___x_4183_, v___x_4184_, v_a_4185_, v_x_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec_ref(v___y_4188_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3(uint32_t v___x_4191_, lean_object* v_s_4192_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = lean_string_push(v_s_4192_, v___x_4191_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3___boxed(lean_object* v___x_4194_, lean_object* v_s_4195_){
_start:
{
uint32_t v___x_5743__boxed_4196_; lean_object* v_res_4197_; 
v___x_5743__boxed_4196_ = lean_unbox_uint32(v___x_4194_);
lean_dec(v___x_4194_);
v_res_4197_ = l_Lean_instToMarkdownSnippet___lam__3(v___x_5743__boxed_4196_, v_s_4195_);
return v_res_4197_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = 35;
v___x_4199_ = lean_box_uint32(v___x_4198_);
return v___x_4199_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0(void){
_start:
{
lean_object* v___x_4200_; lean_object* v___f_4201_; 
v___x_4200_ = l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1;
v___f_4201_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__3___boxed), 2, 1);
lean_closure_set(v___f_4201_, 0, v___x_4200_);
return v___f_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4(lean_object* v___x_4202_, lean_object* v___f_4203_, lean_object* v___x_4204_, lean_object* v___f_4205_, lean_object* v_a_4206_, lean_object* v_x_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_snd_4211_; lean_object* v_fst_4212_; lean_object* v_snd_4213_; lean_object* v___x_4214_; lean_object* v___f_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v_snd_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v_snd_4223_; lean_object* v_title_4224_; lean_object* v_content_4225_; size_t v_sz_4226_; size_t v___x_4227_; lean_object* v___x_5585__overap_4228_; lean_object* v___x_4229_; lean_object* v_snd_4230_; lean_object* v___x_4231_; lean_object* v_snd_4232_; size_t v_sz_4233_; lean_object* v___x_5591__overap_4234_; lean_object* v___x_4235_; lean_object* v_snd_4236_; lean_object* v___x_4237_; lean_object* v_snd_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4246_; 
v_snd_4211_ = lean_ctor_get(v_a_4206_, 1);
lean_inc(v_snd_4211_);
v_fst_4212_ = lean_ctor_get(v_a_4206_, 0);
lean_inc(v_fst_4212_);
lean_dec_ref(v_a_4206_);
v_snd_4213_ = lean_ctor_get(v_snd_4211_, 1);
lean_inc(v_snd_4213_);
lean_dec(v_snd_4211_);
v___x_4214_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___f_4215_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___lam__4___closed__0, &l_Lean_instToMarkdownSnippet___lam__4___closed__0_once, _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0);
v___x_4216_ = lean_unsigned_to_nat(1u);
v___x_4217_ = lean_nat_add(v_fst_4212_, v___x_4216_);
lean_dec(v_fst_4212_);
v___x_4218_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_4215_, v___x_4217_, v___x_4214_);
v___x_4219_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_4218_, v___y_4210_);
lean_dec(v___x_4218_);
v_snd_4220_ = lean_ctor_get(v___x_4219_, 1);
lean_inc(v_snd_4220_);
lean_dec_ref(v___x_4219_);
v___x_4221_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0));
v___x_4222_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_4221_, v_snd_4220_);
v_snd_4223_ = lean_ctor_get(v___x_4222_, 1);
lean_inc(v_snd_4223_);
lean_dec_ref(v___x_4222_);
v_title_4224_ = lean_ctor_get(v_snd_4213_, 0);
lean_inc_ref(v_title_4224_);
v_content_4225_ = lean_ctor_get(v_snd_4213_, 3);
lean_inc_ref(v_content_4225_);
lean_dec(v_snd_4213_);
v_sz_4226_ = lean_array_size(v_title_4224_);
v___x_4227_ = ((size_t)0ULL);
lean_inc_ref(v___x_4202_);
v___x_5585__overap_4228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4202_, v_title_4224_, v___f_4203_, v_sz_4226_, v___x_4227_, v___x_4204_);
lean_inc_ref_n(v___y_4209_, 2);
v___x_4229_ = lean_apply_2(v___x_5585__overap_4228_, v___y_4209_, v_snd_4223_);
v_snd_4230_ = lean_ctor_get(v___x_4229_, 1);
lean_inc(v_snd_4230_);
lean_dec_ref(v___x_4229_);
v___x_4231_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4230_);
v_snd_4232_ = lean_ctor_get(v___x_4231_, 1);
lean_inc(v_snd_4232_);
lean_dec_ref(v___x_4231_);
v_sz_4233_ = lean_array_size(v_content_4225_);
v___x_5591__overap_4234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4202_, v_content_4225_, v___f_4205_, v_sz_4233_, v___x_4227_, v___x_4204_);
v___x_4235_ = lean_apply_2(v___x_5591__overap_4234_, v___y_4209_, v_snd_4232_);
v_snd_4236_ = lean_ctor_get(v___x_4235_, 1);
lean_inc(v_snd_4236_);
lean_dec_ref(v___x_4235_);
v___x_4237_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4236_);
v_snd_4238_ = lean_ctor_get(v___x_4237_, 1);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4246_ == 0)
{
lean_object* v_unused_4247_; 
v_unused_4247_ = lean_ctor_get(v___x_4237_, 0);
lean_dec(v_unused_4247_);
v___x_4240_ = v___x_4237_;
v_isShared_4241_ = v_isSharedCheck_4246_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_snd_4238_);
lean_dec(v___x_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4246_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4242_; lean_object* v___x_4244_; 
v___x_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4204_);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v___x_4242_);
v___x_4244_ = v___x_4240_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v___x_4242_);
lean_ctor_set(v_reuseFailAlloc_4245_, 1, v_snd_4238_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4___boxed(lean_object* v___x_4248_, lean_object* v___f_4249_, lean_object* v___x_4250_, lean_object* v___f_4251_, lean_object* v_a_4252_, lean_object* v_x_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_Lean_instToMarkdownSnippet___lam__4(v___x_4248_, v___f_4249_, v___x_4250_, v___f_4251_, v_a_4252_, v_x_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
lean_dec_ref(v___y_4255_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5(lean_object* v___x_4258_, lean_object* v___x_4259_, lean_object* v___x_4260_, lean_object* v___f_4261_, lean_object* v_x_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v_text_4265_; lean_object* v_sections_4266_; lean_object* v_snd_4268_; lean_object* v___y_4289_; lean_object* v___x_4291_; lean_object* v___x_4292_; uint8_t v___x_4293_; 
v_text_4265_ = lean_ctor_get(v_x_4262_, 0);
lean_inc_ref(v_text_4265_);
v_sections_4266_ = lean_ctor_get(v_x_4262_, 1);
lean_inc_ref(v_sections_4266_);
lean_dec_ref(v_x_4262_);
v___x_4291_ = lean_unsigned_to_nat(0u);
v___x_4292_ = lean_array_get_size(v_text_4265_);
v___x_4293_ = lean_nat_dec_lt(v___x_4291_, v___x_4292_);
if (v___x_4293_ == 0)
{
lean_dec_ref(v_text_4265_);
lean_dec_ref(v___f_4261_);
v_snd_4268_ = v___y_4264_;
goto v___jp_4267_;
}
else
{
lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4294_ = lean_box(0);
v___x_4295_ = lean_nat_dec_le(v___x_4292_, v___x_4292_);
if (v___x_4295_ == 0)
{
if (v___x_4293_ == 0)
{
lean_dec_ref(v_text_4265_);
lean_dec_ref(v___f_4261_);
v_snd_4268_ = v___y_4264_;
goto v___jp_4267_;
}
else
{
size_t v___x_4296_; size_t v___x_4297_; lean_object* v___x_5634__overap_4298_; lean_object* v___x_4299_; 
v___x_4296_ = ((size_t)0ULL);
v___x_4297_ = lean_usize_of_nat(v___x_4292_);
lean_inc_ref(v___x_4260_);
v___x_5634__overap_4298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4260_, v___f_4261_, v_text_4265_, v___x_4296_, v___x_4297_, v___x_4294_);
lean_inc_ref(v___y_4263_);
v___x_4299_ = lean_apply_2(v___x_5634__overap_4298_, v___y_4263_, v___y_4264_);
v___y_4289_ = v___x_4299_;
goto v___jp_4288_;
}
}
else
{
size_t v___x_4300_; size_t v___x_4301_; lean_object* v___x_5637__overap_4302_; lean_object* v___x_4303_; 
v___x_4300_ = ((size_t)0ULL);
v___x_4301_ = lean_usize_of_nat(v___x_4292_);
lean_inc_ref(v___x_4260_);
v___x_5637__overap_4302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4260_, v___f_4261_, v_text_4265_, v___x_4300_, v___x_4301_, v___x_4294_);
lean_inc_ref(v___y_4263_);
v___x_4303_ = lean_apply_2(v___x_5637__overap_4302_, v___y_4263_, v___y_4264_);
v___y_4289_ = v___x_4303_;
goto v___jp_4288_;
}
}
v___jp_4267_:
{
lean_object* v___x_4269_; lean_object* v_snd_4270_; lean_object* v___x_4271_; lean_object* v___f_4272_; lean_object* v___f_4273_; lean_object* v___f_4274_; size_t v_sz_4275_; size_t v___x_4276_; lean_object* v___x_5619__overap_4277_; lean_object* v___x_4278_; lean_object* v_snd_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
v___x_4269_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4268_);
v_snd_4270_ = lean_ctor_get(v___x_4269_, 1);
lean_inc(v_snd_4270_);
lean_dec_ref(v___x_4269_);
v___x_4271_ = lean_box(0);
lean_inc_ref(v___x_4258_);
v___f_4272_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__1___boxed), 8, 3);
lean_closure_set(v___f_4272_, 0, v___x_4258_);
lean_closure_set(v___f_4272_, 1, v___x_4259_);
lean_closure_set(v___f_4272_, 2, v___x_4271_);
v___f_4273_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_4273_, 0, v___x_4258_);
lean_closure_set(v___f_4273_, 1, v___x_4271_);
lean_inc_ref(v___x_4260_);
v___f_4274_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__4___boxed), 9, 4);
lean_closure_set(v___f_4274_, 0, v___x_4260_);
lean_closure_set(v___f_4274_, 1, v___f_4273_);
lean_closure_set(v___f_4274_, 2, v___x_4271_);
lean_closure_set(v___f_4274_, 3, v___f_4272_);
v_sz_4275_ = lean_array_size(v_sections_4266_);
v___x_4276_ = ((size_t)0ULL);
v___x_5619__overap_4277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4260_, v_sections_4266_, v___f_4274_, v_sz_4275_, v___x_4276_, v___x_4271_);
lean_inc_ref(v___y_4263_);
v___x_4278_ = lean_apply_2(v___x_5619__overap_4277_, v___y_4263_, v_snd_4270_);
v_snd_4279_ = lean_ctor_get(v___x_4278_, 1);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4286_ == 0)
{
lean_object* v_unused_4287_; 
v_unused_4287_ = lean_ctor_get(v___x_4278_, 0);
lean_dec(v_unused_4287_);
v___x_4281_ = v___x_4278_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_snd_4279_);
lean_dec(v___x_4278_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 0, v___x_4271_);
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v___x_4271_);
lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_snd_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
v___jp_4288_:
{
lean_object* v_snd_4290_; 
v_snd_4290_ = lean_ctor_get(v___y_4289_, 1);
lean_inc(v_snd_4290_);
lean_dec_ref(v___y_4289_);
v_snd_4268_ = v_snd_4290_;
goto v___jp_4267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5___boxed(lean_object* v___x_4304_, lean_object* v___x_4305_, lean_object* v___x_4306_, lean_object* v___f_4307_, lean_object* v_x_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Lean_instToMarkdownSnippet___lam__5(v___x_4304_, v___x_4305_, v___x_4306_, v___f_4307_, v_x_4308_, v___y_4309_, v___y_4310_);
lean_dec_ref(v___y_4309_);
return v_res_4311_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___f_4314_; 
v___x_4312_ = l_Lean_instMarkdownBlockElabInlineElabBlock;
v___x_4313_ = l_Lean_instMarkdownInlineElabInline;
v___f_4314_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__0___boxed), 6, 2);
lean_closure_set(v___f_4314_, 0, v___x_4313_);
lean_closure_set(v___f_4314_, 1, v___x_4312_);
return v___f_4314_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___closed__1(void){
_start:
{
lean_object* v___f_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___f_4319_; 
v___f_4315_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___closed__0, &l_Lean_instToMarkdownSnippet___closed__0_once, _init_l_Lean_instToMarkdownSnippet___closed__0);
v___x_4316_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__20, &l_Lean_instMarkdownInlineElabInline___closed__20_once, _init_l_Lean_instMarkdownInlineElabInline___closed__20);
v___x_4317_ = l_Lean_instMarkdownBlockElabInlineElabBlock;
v___x_4318_ = l_Lean_instMarkdownInlineElabInline;
v___f_4319_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__5___boxed), 7, 4);
lean_closure_set(v___f_4319_, 0, v___x_4318_);
lean_closure_set(v___f_4319_, 1, v___x_4317_);
lean_closure_set(v___f_4319_, 2, v___x_4316_);
lean_closure_set(v___f_4319_, 3, v___f_4315_);
return v___f_4319_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet(void){
_start:
{
lean_object* v___f_4320_; 
v___f_4320_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___closed__1, &l_Lean_instToMarkdownSnippet___closed__1_once, _init_l_Lean_instToMarkdownSnippet___closed__1);
return v___f_4320_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0(void){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_4321_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1(void){
_start:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4322_ = lean_box(0);
v___x_4323_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_4324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4323_);
lean_ctor_set(v___x_4324_, 1, v___x_4322_);
return v___x_4324_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default(void){
_start:
{
lean_object* v___x_4325_; 
v___x_4325_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__1, &l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1);
return v___x_4325_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs(void){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_Lean_instInhabitedVersoModuleDocs_default;
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object* v___x_4333_, lean_object* v_v_4334_, lean_object* v_x_4335_){
_start:
{
lean_object* v_snippets_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4359_; 
v_snippets_4336_ = lean_ctor_get(v_v_4334_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v_v_4334_);
if (v_isSharedCheck_4359_ == 0)
{
lean_object* v_unused_4360_; 
v_unused_4360_ = lean_ctor_get(v_v_4334_, 1);
lean_dec(v_unused_4360_);
v___x_4338_ = v_v_4334_;
v_isShared_4339_ = v_isSharedCheck_4359_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_snippets_4336_);
lean_dec(v_v_4334_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4359_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4347_; 
v___x_4340_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___x_4341_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_4342_ = lean_box(1);
v___x_4343_ = ((lean_object*)(l_Lean_instReprVersoModuleDocs___lam__0___closed__2));
v___x_4344_ = l_Lean_PersistentArray_toArray___redArg(v_snippets_4336_);
lean_dec_ref(v_snippets_4336_);
v___x_4345_ = l_Array_repr___redArg(v___x_4333_, v___x_4344_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set_tag(v___x_4338_, 5);
lean_ctor_set(v___x_4338_, 1, v___x_4345_);
lean_ctor_set(v___x_4338_, 0, v___x_4343_);
v___x_4347_ = v___x_4338_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4343_);
lean_ctor_set(v_reuseFailAlloc_4358_, 1, v___x_4345_);
v___x_4347_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
lean_object* v___x_4348_; uint8_t v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4348_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4340_);
lean_ctor_set(v___x_4348_, 1, v___x_4347_);
v___x_4349_ = 0;
v___x_4350_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4350_, 0, v___x_4348_);
lean_ctor_set_uint8(v___x_4350_, sizeof(void*)*1, v___x_4349_);
lean_inc_ref(v___x_4350_);
v___x_4351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4341_);
lean_ctor_set(v___x_4351_, 1, v___x_4350_);
v___x_4352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
lean_ctor_set(v___x_4352_, 1, v___x_4342_);
v___x_4353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4352_);
lean_ctor_set(v___x_4353_, 1, v___x_4350_);
v___x_4354_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_4355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4353_);
lean_ctor_set(v___x_4355_, 1, v___x_4354_);
v___x_4356_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4340_);
lean_ctor_set(v___x_4356_, 1, v___x_4355_);
v___x_4357_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4357_, 0, v___x_4356_);
lean_ctor_set_uint8(v___x_4357_, sizeof(void*)*1, v___x_4349_);
return v___x_4357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object* v___x_4361_, lean_object* v_v_4362_, lean_object* v_x_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l_Lean_instReprVersoModuleDocs___lam__0(v___x_4361_, v_v_4362_, v_x_4363_);
lean_dec(v_x_4363_);
return v_res_4364_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object* v_docs_4368_){
_start:
{
lean_object* v_snippets_4369_; uint8_t v___x_4370_; 
v_snippets_4369_ = lean_ctor_get(v_docs_4368_, 0);
v___x_4370_ = l_Lean_PersistentArray_isEmpty___redArg(v_snippets_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object* v_docs_4371_){
_start:
{
uint8_t v_res_4372_; lean_object* v_r_4373_; 
v_res_4372_ = l_Lean_VersoModuleDocs_isEmpty(v_docs_4371_);
lean_dec_ref(v_docs_4371_);
v_r_4373_ = lean_box(v_res_4372_);
return v_r_4373_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object* v_docs_4374_, lean_object* v_snippet_4375_){
_start:
{
lean_object* v_terminalNesting_4376_; 
v_terminalNesting_4376_ = lean_ctor_get(v_docs_4374_, 1);
if (lean_obj_tag(v_terminalNesting_4376_) == 1)
{
lean_object* v_val_4377_; uint8_t v___x_4378_; 
v_val_4377_ = lean_ctor_get(v_terminalNesting_4376_, 0);
v___x_4378_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4377_, v_snippet_4375_);
return v___x_4378_;
}
else
{
uint8_t v___x_4379_; 
v___x_4379_ = 1;
return v___x_4379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object* v_docs_4380_, lean_object* v_snippet_4381_){
_start:
{
uint8_t v_res_4382_; lean_object* v_r_4383_; 
v_res_4382_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4380_, v_snippet_4381_);
lean_dec_ref(v_snippet_4381_);
lean_dec_ref(v_docs_4380_);
v_r_4383_ = lean_box(v_res_4382_);
return v_r_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object* v_docs_4387_, lean_object* v_snippet_4388_){
_start:
{
uint8_t v___x_4389_; 
v___x_4389_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4387_, v_snippet_4388_);
if (v___x_4389_ == 0)
{
lean_object* v___x_4390_; 
lean_dec_ref(v_snippet_4388_);
lean_dec_ref(v_docs_4387_);
v___x_4390_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__1));
return v___x_4390_;
}
else
{
lean_object* v_snippets_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4401_; 
v_snippets_4391_ = lean_ctor_get(v_docs_4387_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v_docs_4387_);
if (v_isSharedCheck_4401_ == 0)
{
lean_object* v_unused_4402_; 
v_unused_4402_ = lean_ctor_get(v_docs_4387_, 1);
lean_dec(v_unused_4402_);
v___x_4393_ = v_docs_4387_;
v_isShared_4394_ = v_isSharedCheck_4401_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_snippets_4391_);
lean_dec(v_docs_4387_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4401_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4398_; 
lean_inc_ref(v_snippet_4388_);
v___x_4395_ = l_Lean_PersistentArray_push___redArg(v_snippets_4391_, v_snippet_4388_);
v___x_4396_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4388_);
lean_dec_ref(v_snippet_4388_);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 1, v___x_4396_);
lean_ctor_set(v___x_4393_, 0, v___x_4395_);
v___x_4398_ = v___x_4393_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4395_);
lean_ctor_set(v_reuseFailAlloc_4400_, 1, v___x_4396_);
v___x_4398_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
lean_object* v___x_4399_; 
v___x_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4398_);
return v___x_4399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object* v_msg_4403_){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4404_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_4405_ = lean_panic_fn_borrowed(v___x_4404_, v_msg_4403_);
return v___x_4405_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_add_x21___closed__2(void){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4408_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__0));
v___x_4409_ = lean_unsigned_to_nat(4u);
v___x_4410_ = lean_unsigned_to_nat(328u);
v___x_4411_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__1));
v___x_4412_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__0));
v___x_4413_ = l_mkPanicMessageWithDecl(v___x_4412_, v___x_4411_, v___x_4410_, v___x_4409_, v___x_4408_);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object* v_docs_4414_, lean_object* v_snippet_4415_){
_start:
{
lean_object* v_snippets_4416_; lean_object* v_terminalNesting_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4431_; 
v_snippets_4416_ = lean_ctor_get(v_docs_4414_, 0);
v_terminalNesting_4417_ = lean_ctor_get(v_docs_4414_, 1);
v_isSharedCheck_4431_ = !lean_is_exclusive(v_docs_4414_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4419_ = v_docs_4414_;
v_isShared_4420_ = v_isSharedCheck_4431_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_terminalNesting_4417_);
lean_inc(v_snippets_4416_);
lean_dec(v_docs_4414_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4431_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
if (lean_obj_tag(v_terminalNesting_4417_) == 1)
{
lean_object* v_val_4427_; uint8_t v___x_4428_; 
v_val_4427_ = lean_ctor_get(v_terminalNesting_4417_, 0);
lean_inc(v_val_4427_);
lean_dec_ref(v_terminalNesting_4417_);
v___x_4428_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4427_, v_snippet_4415_);
lean_dec(v_val_4427_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
lean_del_object(v___x_4419_);
lean_dec_ref(v_snippets_4416_);
lean_dec_ref(v_snippet_4415_);
v___x_4429_ = lean_obj_once(&l_Lean_VersoModuleDocs_add_x21___closed__2, &l_Lean_VersoModuleDocs_add_x21___closed__2_once, _init_l_Lean_VersoModuleDocs_add_x21___closed__2);
v___x_4430_ = l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(v___x_4429_);
return v___x_4430_;
}
else
{
goto v___jp_4421_;
}
}
else
{
lean_dec(v_terminalNesting_4417_);
goto v___jp_4421_;
}
v___jp_4421_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4425_; 
lean_inc_ref(v_snippet_4415_);
v___x_4422_ = l_Lean_PersistentArray_push___redArg(v_snippets_4416_, v_snippet_4415_);
v___x_4423_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4415_);
lean_dec_ref(v_snippet_4415_);
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 1, v___x_4423_);
lean_ctor_set(v___x_4419_, 0, v___x_4422_);
v___x_4425_ = v___x_4419_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4422_);
lean_ctor_set(v_reuseFailAlloc_4426_, 1, v___x_4423_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object* v_ctx_4432_){
_start:
{
lean_object* v_context_4433_; lean_object* v___x_4434_; 
v_context_4433_ = lean_ctor_get(v_ctx_4432_, 2);
v___x_4434_ = lean_array_get_size(v_context_4433_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object* v_ctx_4435_){
_start:
{
lean_object* v_res_4436_; 
v_res_4436_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4435_);
lean_dec_ref(v_ctx_4435_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object* v_ctx_4440_){
_start:
{
lean_object* v_content_4441_; lean_object* v_priorParts_4442_; lean_object* v_context_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4466_; 
v_content_4441_ = lean_ctor_get(v_ctx_4440_, 0);
v_priorParts_4442_ = lean_ctor_get(v_ctx_4440_, 1);
v_context_4443_ = lean_ctor_get(v_ctx_4440_, 2);
v_isSharedCheck_4466_ = !lean_is_exclusive(v_ctx_4440_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4445_ = v_ctx_4440_;
v_isShared_4446_ = v_isSharedCheck_4466_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_context_4443_);
lean_inc(v_priorParts_4442_);
lean_inc(v_content_4441_);
lean_dec(v_ctx_4440_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4466_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; uint8_t v___x_4449_; 
v___x_4447_ = lean_array_get_size(v_context_4443_);
v___x_4448_ = lean_unsigned_to_nat(0u);
v___x_4449_ = lean_nat_dec_eq(v___x_4447_, v___x_4448_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v_last_4452_; lean_object* v_content_4453_; lean_object* v_priorParts_4454_; lean_object* v_titleString_4455_; lean_object* v_title_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4450_ = lean_unsigned_to_nat(1u);
v___x_4451_ = lean_nat_sub(v___x_4447_, v___x_4450_);
v_last_4452_ = lean_array_fget_borrowed(v_context_4443_, v___x_4451_);
lean_dec(v___x_4451_);
v_content_4453_ = lean_ctor_get(v_last_4452_, 0);
lean_inc_ref(v_content_4453_);
v_priorParts_4454_ = lean_ctor_get(v_last_4452_, 1);
v_titleString_4455_ = lean_ctor_get(v_last_4452_, 2);
v_title_4456_ = lean_ctor_get(v_last_4452_, 3);
v___x_4457_ = lean_box(0);
lean_inc_ref(v_titleString_4455_);
lean_inc_ref(v_title_4456_);
v___x_4458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4458_, 0, v_title_4456_);
lean_ctor_set(v___x_4458_, 1, v_titleString_4455_);
lean_ctor_set(v___x_4458_, 2, v___x_4457_);
lean_ctor_set(v___x_4458_, 3, v_content_4441_);
lean_ctor_set(v___x_4458_, 4, v_priorParts_4442_);
lean_inc_ref(v_priorParts_4454_);
v___x_4459_ = lean_array_push(v_priorParts_4454_, v___x_4458_);
v___x_4460_ = lean_array_pop(v_context_4443_);
if (v_isShared_4446_ == 0)
{
lean_ctor_set(v___x_4445_, 2, v___x_4460_);
lean_ctor_set(v___x_4445_, 1, v___x_4459_);
lean_ctor_set(v___x_4445_, 0, v_content_4453_);
v___x_4462_ = v___x_4445_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_content_4453_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v___x_4459_);
lean_ctor_set(v_reuseFailAlloc_4464_, 2, v___x_4460_);
v___x_4462_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
lean_object* v___x_4463_; 
v___x_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4462_);
return v___x_4463_;
}
}
else
{
lean_object* v___x_4465_; 
lean_del_object(v___x_4445_);
lean_dec_ref(v_context_4443_);
lean_dec_ref(v_priorParts_4442_);
lean_dec_ref(v_content_4441_);
v___x_4465_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1));
return v___x_4465_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object* v_ctx_4467_){
_start:
{
lean_object* v_context_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; uint8_t v___x_4471_; 
v_context_4468_ = lean_ctor_get(v_ctx_4467_, 2);
v___x_4469_ = lean_array_get_size(v_context_4468_);
v___x_4470_ = lean_unsigned_to_nat(0u);
v___x_4471_ = lean_nat_dec_eq(v___x_4469_, v___x_4470_);
if (v___x_4471_ == 0)
{
lean_object* v___x_4472_; 
v___x_4472_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4467_);
if (lean_obj_tag(v___x_4472_) == 0)
{
return v___x_4472_;
}
else
{
lean_object* v_a_4473_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_a_4473_);
lean_dec_ref(v___x_4472_);
v_ctx_4467_ = v_a_4473_;
goto _start;
}
}
else
{
lean_object* v___x_4475_; 
v___x_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4475_, 0, v_ctx_4467_);
return v___x_4475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object* v_ctx_4478_, lean_object* v_partLevel_4479_, lean_object* v_part_4480_){
_start:
{
lean_object* v___x_4481_; uint8_t v___x_4482_; 
v___x_4481_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4478_);
v___x_4482_ = lean_nat_dec_lt(v___x_4481_, v_partLevel_4479_);
if (v___x_4482_ == 0)
{
uint8_t v___x_4483_; 
v___x_4483_ = lean_nat_dec_eq(v_partLevel_4479_, v___x_4481_);
lean_dec(v___x_4481_);
if (v___x_4483_ == 0)
{
lean_object* v___x_4484_; 
v___x_4484_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4478_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_dec_ref(v_part_4480_);
lean_dec(v_partLevel_4479_);
return v___x_4484_;
}
else
{
lean_object* v_a_4485_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4485_);
lean_dec_ref(v___x_4484_);
v_ctx_4478_ = v_a_4485_;
goto _start;
}
}
else
{
lean_object* v_content_4487_; lean_object* v_priorParts_4488_; lean_object* v_context_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4498_; 
lean_dec(v_partLevel_4479_);
v_content_4487_ = lean_ctor_get(v_ctx_4478_, 0);
v_priorParts_4488_ = lean_ctor_get(v_ctx_4478_, 1);
v_context_4489_ = lean_ctor_get(v_ctx_4478_, 2);
v_isSharedCheck_4498_ = !lean_is_exclusive(v_ctx_4478_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4491_ = v_ctx_4478_;
v_isShared_4492_ = v_isSharedCheck_4498_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_context_4489_);
lean_inc(v_priorParts_4488_);
lean_inc(v_content_4487_);
lean_dec(v_ctx_4478_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4498_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4493_; lean_object* v___x_4495_; 
v___x_4493_ = lean_array_push(v_priorParts_4488_, v_part_4480_);
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 1, v___x_4493_);
v___x_4495_ = v___x_4491_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_content_4487_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v___x_4493_);
lean_ctor_set(v_reuseFailAlloc_4497_, 2, v_context_4489_);
v___x_4495_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
lean_object* v___x_4496_; 
v___x_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
return v___x_4496_;
}
}
}
}
else
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
lean_dec_ref(v_part_4480_);
lean_dec_ref(v_ctx_4478_);
v___x_4499_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0));
v___x_4500_ = l_Nat_reprFast(v___x_4481_);
v___x_4501_ = lean_string_append(v___x_4499_, v___x_4500_);
lean_dec_ref(v___x_4500_);
v___x_4502_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1));
v___x_4503_ = lean_string_append(v___x_4501_, v___x_4502_);
v___x_4504_ = l_Nat_reprFast(v_partLevel_4479_);
v___x_4505_ = lean_string_append(v___x_4503_, v___x_4504_);
lean_dec_ref(v___x_4504_);
v___x_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
return v___x_4506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object* v_ctx_4510_, lean_object* v_blocks_4511_){
_start:
{
lean_object* v_content_4512_; lean_object* v_priorParts_4513_; lean_object* v_context_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4527_; 
v_content_4512_ = lean_ctor_get(v_ctx_4510_, 0);
v_priorParts_4513_ = lean_ctor_get(v_ctx_4510_, 1);
v_context_4514_ = lean_ctor_get(v_ctx_4510_, 2);
v_isSharedCheck_4527_ = !lean_is_exclusive(v_ctx_4510_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4516_ = v_ctx_4510_;
v_isShared_4517_ = v_isSharedCheck_4527_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_context_4514_);
lean_inc(v_priorParts_4513_);
lean_inc(v_content_4512_);
lean_dec(v_ctx_4510_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4527_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; uint8_t v___x_4520_; 
v___x_4518_ = lean_array_get_size(v_priorParts_4513_);
v___x_4519_ = lean_unsigned_to_nat(0u);
v___x_4520_ = lean_nat_dec_eq(v___x_4518_, v___x_4519_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; 
lean_del_object(v___x_4516_);
lean_dec_ref(v_context_4514_);
lean_dec_ref(v_priorParts_4513_);
lean_dec_ref(v_content_4512_);
v___x_4521_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1));
return v___x_4521_;
}
else
{
lean_object* v___x_4522_; lean_object* v___x_4524_; 
v___x_4522_ = l_Array_append___redArg(v_content_4512_, v_blocks_4511_);
if (v_isShared_4517_ == 0)
{
lean_ctor_set(v___x_4516_, 0, v___x_4522_);
v___x_4524_ = v___x_4516_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4522_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_priorParts_4513_);
lean_ctor_set(v_reuseFailAlloc_4526_, 2, v_context_4514_);
v___x_4524_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
lean_object* v___x_4525_; 
v___x_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4524_);
return v___x_4525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object* v_ctx_4528_, lean_object* v_blocks_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4528_, v_blocks_4529_);
lean_dec_ref(v_blocks_4529_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object* v_as_4531_, size_t v_sz_4532_, size_t v_i_4533_, lean_object* v_b_4534_){
_start:
{
uint8_t v___x_4535_; 
v___x_4535_ = lean_usize_dec_lt(v_i_4533_, v_sz_4532_);
if (v___x_4535_ == 0)
{
lean_object* v___x_4536_; 
v___x_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4536_, 0, v_b_4534_);
return v___x_4536_;
}
else
{
lean_object* v_a_4537_; lean_object* v_snd_4538_; lean_object* v_fst_4539_; lean_object* v_snd_4540_; lean_object* v___x_4541_; 
v_a_4537_ = lean_array_uget_borrowed(v_as_4531_, v_i_4533_);
v_snd_4538_ = lean_ctor_get(v_a_4537_, 1);
v_fst_4539_ = lean_ctor_get(v_a_4537_, 0);
v_snd_4540_ = lean_ctor_get(v_snd_4538_, 1);
lean_inc(v_snd_4540_);
lean_inc(v_fst_4539_);
v___x_4541_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(v_b_4534_, v_fst_4539_, v_snd_4540_);
if (lean_obj_tag(v___x_4541_) == 0)
{
return v___x_4541_;
}
else
{
lean_object* v_a_4542_; size_t v___x_4543_; size_t v___x_4544_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_a_4542_);
lean_dec_ref(v___x_4541_);
v___x_4543_ = ((size_t)1ULL);
v___x_4544_ = lean_usize_add(v_i_4533_, v___x_4543_);
v_i_4533_ = v___x_4544_;
v_b_4534_ = v_a_4542_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object* v_as_4546_, lean_object* v_sz_4547_, lean_object* v_i_4548_, lean_object* v_b_4549_){
_start:
{
size_t v_sz_boxed_4550_; size_t v_i_boxed_4551_; lean_object* v_res_4552_; 
v_sz_boxed_4550_ = lean_unbox_usize(v_sz_4547_);
lean_dec(v_sz_4547_);
v_i_boxed_4551_ = lean_unbox_usize(v_i_4548_);
lean_dec(v_i_4548_);
v_res_4552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_as_4546_, v_sz_boxed_4550_, v_i_boxed_4551_, v_b_4549_);
lean_dec_ref(v_as_4546_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object* v_ctx_4553_, lean_object* v_snippet_4554_){
_start:
{
lean_object* v_text_4555_; lean_object* v_sections_4556_; lean_object* v___x_4557_; 
v_text_4555_ = lean_ctor_get(v_snippet_4554_, 0);
v_sections_4556_ = lean_ctor_get(v_snippet_4554_, 1);
v___x_4557_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4553_, v_text_4555_);
if (lean_obj_tag(v___x_4557_) == 0)
{
return v___x_4557_;
}
else
{
lean_object* v_a_4558_; size_t v_sz_4559_; size_t v___x_4560_; lean_object* v___x_4561_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
lean_inc(v_a_4558_);
lean_dec_ref(v___x_4557_);
v_sz_4559_ = lean_array_size(v_sections_4556_);
v___x_4560_ = ((size_t)0ULL);
v___x_4561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_sections_4556_, v_sz_4559_, v___x_4560_, v_a_4558_);
return v___x_4561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object* v_ctx_4562_, lean_object* v_snippet_4563_){
_start:
{
lean_object* v_res_4564_; 
v_res_4564_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_ctx_4562_, v_snippet_4563_);
lean_dec_ref(v_snippet_4563_);
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object* v_as_4565_, size_t v_sz_4566_, size_t v_i_4567_, lean_object* v_b_4568_){
_start:
{
uint8_t v___x_4569_; 
v___x_4569_ = lean_usize_dec_lt(v_i_4567_, v_sz_4566_);
if (v___x_4569_ == 0)
{
lean_object* v___x_4570_; 
v___x_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4570_, 0, v_b_4568_);
return v___x_4570_;
}
else
{
lean_object* v_snd_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4593_; 
v_snd_4571_ = lean_ctor_get(v_b_4568_, 1);
v_isSharedCheck_4593_ = !lean_is_exclusive(v_b_4568_);
if (v_isSharedCheck_4593_ == 0)
{
lean_object* v_unused_4594_; 
v_unused_4594_ = lean_ctor_get(v_b_4568_, 0);
lean_dec(v_unused_4594_);
v___x_4573_ = v_b_4568_;
v_isShared_4574_ = v_isSharedCheck_4593_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_snd_4571_);
lean_dec(v_b_4568_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4593_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v_a_4575_; lean_object* v___x_4576_; 
v_a_4575_ = lean_array_uget_borrowed(v_as_4565_, v_i_4567_);
v___x_4576_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4571_, v_a_4575_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_del_object(v___x_4573_);
v_a_4577_ = lean_ctor_get(v___x_4576_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4576_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4576_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4586_; lean_object* v___x_4588_; 
v_a_4585_ = lean_ctor_get(v___x_4576_, 0);
lean_inc(v_a_4585_);
lean_dec_ref(v___x_4576_);
v___x_4586_ = lean_box(0);
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 1, v_a_4585_);
lean_ctor_set(v___x_4573_, 0, v___x_4586_);
v___x_4588_ = v___x_4573_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4586_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v_a_4585_);
v___x_4588_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
size_t v___x_4589_; size_t v___x_4590_; 
v___x_4589_ = ((size_t)1ULL);
v___x_4590_ = lean_usize_add(v_i_4567_, v___x_4589_);
v_i_4567_ = v___x_4590_;
v_b_4568_ = v___x_4588_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4595_, lean_object* v_sz_4596_, lean_object* v_i_4597_, lean_object* v_b_4598_){
_start:
{
size_t v_sz_boxed_4599_; size_t v_i_boxed_4600_; lean_object* v_res_4601_; 
v_sz_boxed_4599_ = lean_unbox_usize(v_sz_4596_);
lean_dec(v_sz_4596_);
v_i_boxed_4600_ = lean_unbox_usize(v_i_4597_);
lean_dec(v_i_4597_);
v_res_4601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4595_, v_sz_boxed_4599_, v_i_boxed_4600_, v_b_4598_);
lean_dec_ref(v_as_4595_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object* v_as_4602_, size_t v_sz_4603_, size_t v_i_4604_, lean_object* v_b_4605_){
_start:
{
uint8_t v___x_4606_; 
v___x_4606_ = lean_usize_dec_lt(v_i_4604_, v_sz_4603_);
if (v___x_4606_ == 0)
{
lean_object* v___x_4607_; 
v___x_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4607_, 0, v_b_4605_);
return v___x_4607_;
}
else
{
lean_object* v_snd_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4630_; 
v_snd_4608_ = lean_ctor_get(v_b_4605_, 1);
v_isSharedCheck_4630_ = !lean_is_exclusive(v_b_4605_);
if (v_isSharedCheck_4630_ == 0)
{
lean_object* v_unused_4631_; 
v_unused_4631_ = lean_ctor_get(v_b_4605_, 0);
lean_dec(v_unused_4631_);
v___x_4610_ = v_b_4605_;
v_isShared_4611_ = v_isSharedCheck_4630_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_snd_4608_);
lean_dec(v_b_4605_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4630_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v_a_4612_; lean_object* v___x_4613_; 
v_a_4612_ = lean_array_uget_borrowed(v_as_4602_, v_i_4604_);
v___x_4613_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4608_, v_a_4612_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4621_; 
lean_del_object(v___x_4610_);
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4616_ = v___x_4613_;
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4613_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4623_; lean_object* v___x_4625_; 
v_a_4622_ = lean_ctor_get(v___x_4613_, 0);
lean_inc(v_a_4622_);
lean_dec_ref(v___x_4613_);
v___x_4623_ = lean_box(0);
if (v_isShared_4611_ == 0)
{
lean_ctor_set(v___x_4610_, 1, v_a_4622_);
lean_ctor_set(v___x_4610_, 0, v___x_4623_);
v___x_4625_ = v___x_4610_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4623_);
lean_ctor_set(v_reuseFailAlloc_4629_, 1, v_a_4622_);
v___x_4625_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
size_t v___x_4626_; size_t v___x_4627_; lean_object* v___x_4628_; 
v___x_4626_ = ((size_t)1ULL);
v___x_4627_ = lean_usize_add(v_i_4604_, v___x_4626_);
v___x_4628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4602_, v_sz_4603_, v___x_4627_, v___x_4625_);
return v___x_4628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object* v_as_4632_, lean_object* v_sz_4633_, lean_object* v_i_4634_, lean_object* v_b_4635_){
_start:
{
size_t v_sz_boxed_4636_; size_t v_i_boxed_4637_; lean_object* v_res_4638_; 
v_sz_boxed_4636_ = lean_unbox_usize(v_sz_4633_);
lean_dec(v_sz_4633_);
v_i_boxed_4637_ = lean_unbox_usize(v_i_4634_);
lean_dec(v_i_4634_);
v_res_4638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_as_4632_, v_sz_boxed_4636_, v_i_boxed_4637_, v_b_4635_);
lean_dec_ref(v_as_4632_);
return v_res_4638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_4639_, size_t v_sz_4640_, size_t v_i_4641_, lean_object* v_b_4642_){
_start:
{
uint8_t v___x_4643_; 
v___x_4643_ = lean_usize_dec_lt(v_i_4641_, v_sz_4640_);
if (v___x_4643_ == 0)
{
lean_object* v___x_4644_; 
v___x_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4644_, 0, v_b_4642_);
return v___x_4644_;
}
else
{
lean_object* v_snd_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4667_; 
v_snd_4645_ = lean_ctor_get(v_b_4642_, 1);
v_isSharedCheck_4667_ = !lean_is_exclusive(v_b_4642_);
if (v_isSharedCheck_4667_ == 0)
{
lean_object* v_unused_4668_; 
v_unused_4668_ = lean_ctor_get(v_b_4642_, 0);
lean_dec(v_unused_4668_);
v___x_4647_ = v_b_4642_;
v_isShared_4648_ = v_isSharedCheck_4667_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_snd_4645_);
lean_dec(v_b_4642_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4667_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v_a_4649_; lean_object* v___x_4650_; 
v_a_4649_ = lean_array_uget_borrowed(v_as_4639_, v_i_4641_);
v___x_4650_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4645_, v_a_4649_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4658_; 
lean_del_object(v___x_4647_);
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4653_ = v___x_4650_;
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4650_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4656_; 
if (v_isShared_4654_ == 0)
{
v___x_4656_ = v___x_4653_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4651_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
else
{
lean_object* v_a_4659_; lean_object* v___x_4660_; lean_object* v___x_4662_; 
v_a_4659_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4659_);
lean_dec_ref(v___x_4650_);
v___x_4660_ = lean_box(0);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 1, v_a_4659_);
lean_ctor_set(v___x_4647_, 0, v___x_4660_);
v___x_4662_ = v___x_4647_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4660_);
lean_ctor_set(v_reuseFailAlloc_4666_, 1, v_a_4659_);
v___x_4662_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
size_t v___x_4663_; size_t v___x_4664_; 
v___x_4663_ = ((size_t)1ULL);
v___x_4664_ = lean_usize_add(v_i_4641_, v___x_4663_);
v_i_4641_ = v___x_4664_;
v_b_4642_ = v___x_4662_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_4669_, lean_object* v_sz_4670_, lean_object* v_i_4671_, lean_object* v_b_4672_){
_start:
{
size_t v_sz_boxed_4673_; size_t v_i_boxed_4674_; lean_object* v_res_4675_; 
v_sz_boxed_4673_ = lean_unbox_usize(v_sz_4670_);
lean_dec(v_sz_4670_);
v_i_boxed_4674_ = lean_unbox_usize(v_i_4671_);
lean_dec(v_i_4671_);
v_res_4675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4669_, v_sz_boxed_4673_, v_i_boxed_4674_, v_b_4672_);
lean_dec_ref(v_as_4669_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object* v_as_4676_, size_t v_sz_4677_, size_t v_i_4678_, lean_object* v_b_4679_){
_start:
{
uint8_t v___x_4680_; 
v___x_4680_ = lean_usize_dec_lt(v_i_4678_, v_sz_4677_);
if (v___x_4680_ == 0)
{
lean_object* v___x_4681_; 
v___x_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4681_, 0, v_b_4679_);
return v___x_4681_;
}
else
{
lean_object* v_snd_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4704_; 
v_snd_4682_ = lean_ctor_get(v_b_4679_, 1);
v_isSharedCheck_4704_ = !lean_is_exclusive(v_b_4679_);
if (v_isSharedCheck_4704_ == 0)
{
lean_object* v_unused_4705_; 
v_unused_4705_ = lean_ctor_get(v_b_4679_, 0);
lean_dec(v_unused_4705_);
v___x_4684_ = v_b_4679_;
v_isShared_4685_ = v_isSharedCheck_4704_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_snd_4682_);
lean_dec(v_b_4679_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4704_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v_a_4686_; lean_object* v___x_4687_; 
v_a_4686_ = lean_array_uget_borrowed(v_as_4676_, v_i_4678_);
v___x_4687_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4682_, v_a_4686_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4695_; 
lean_del_object(v___x_4684_);
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4690_ = v___x_4687_;
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4687_);
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
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4696_; lean_object* v___x_4697_; lean_object* v___x_4699_; 
v_a_4696_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4696_);
lean_dec_ref(v___x_4687_);
v___x_4697_ = lean_box(0);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 1, v_a_4696_);
lean_ctor_set(v___x_4684_, 0, v___x_4697_);
v___x_4699_ = v___x_4684_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4697_);
lean_ctor_set(v_reuseFailAlloc_4703_, 1, v_a_4696_);
v___x_4699_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
size_t v___x_4700_; size_t v___x_4701_; lean_object* v___x_4702_; 
v___x_4700_ = ((size_t)1ULL);
v___x_4701_ = lean_usize_add(v_i_4678_, v___x_4700_);
v___x_4702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4676_, v_sz_4677_, v___x_4701_, v___x_4699_);
return v___x_4702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4706_, lean_object* v_sz_4707_, lean_object* v_i_4708_, lean_object* v_b_4709_){
_start:
{
size_t v_sz_boxed_4710_; size_t v_i_boxed_4711_; lean_object* v_res_4712_; 
v_sz_boxed_4710_ = lean_unbox_usize(v_sz_4707_);
lean_dec(v_sz_4707_);
v_i_boxed_4711_ = lean_unbox_usize(v_i_4708_);
lean_dec(v_i_4708_);
v_res_4712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_as_4706_, v_sz_boxed_4710_, v_i_boxed_4711_, v_b_4709_);
lean_dec_ref(v_as_4706_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object* v_init_4713_, lean_object* v_n_4714_, lean_object* v_b_4715_){
_start:
{
if (lean_obj_tag(v_n_4714_) == 0)
{
lean_object* v_cs_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4750_; 
v_cs_4716_ = lean_ctor_get(v_n_4714_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v_n_4714_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4718_ = v_n_4714_;
v_isShared_4719_ = v_isSharedCheck_4750_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_cs_4716_);
lean_dec(v_n_4714_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4750_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; size_t v_sz_4722_; size_t v___x_4723_; lean_object* v___x_4724_; 
v___x_4720_ = lean_box(0);
v___x_4721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
lean_ctor_set(v___x_4721_, 1, v_b_4715_);
v_sz_4722_ = lean_array_size(v_cs_4716_);
v___x_4723_ = ((size_t)0ULL);
v___x_4724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_4713_, v_cs_4716_, v_sz_4722_, v___x_4723_, v___x_4721_);
lean_dec_ref(v_cs_4716_);
if (lean_obj_tag(v___x_4724_) == 0)
{
lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4732_; 
lean_del_object(v___x_4718_);
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4732_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4727_ = v___x_4724_;
v_isShared_4728_ = v_isSharedCheck_4732_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4724_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4732_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v___x_4730_; 
if (v_isShared_4728_ == 0)
{
v___x_4730_ = v___x_4727_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_a_4725_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
else
{
lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4749_; 
v_a_4733_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4735_ = v___x_4724_;
v_isShared_4736_ = v_isSharedCheck_4749_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4724_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4749_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v_fst_4737_; 
v_fst_4737_ = lean_ctor_get(v_a_4733_, 0);
if (lean_obj_tag(v_fst_4737_) == 0)
{
lean_object* v_snd_4738_; lean_object* v___x_4740_; 
v_snd_4738_ = lean_ctor_get(v_a_4733_, 1);
lean_inc(v_snd_4738_);
lean_dec(v_a_4733_);
if (v_isShared_4719_ == 0)
{
lean_ctor_set_tag(v___x_4718_, 1);
lean_ctor_set(v___x_4718_, 0, v_snd_4738_);
v___x_4740_ = v___x_4718_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_snd_4738_);
v___x_4740_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
lean_object* v___x_4742_; 
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 0, v___x_4740_);
v___x_4742_ = v___x_4735_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4740_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
else
{
lean_object* v_val_4745_; lean_object* v___x_4747_; 
lean_inc_ref(v_fst_4737_);
lean_dec(v_a_4733_);
lean_del_object(v___x_4718_);
v_val_4745_ = lean_ctor_get(v_fst_4737_, 0);
lean_inc(v_val_4745_);
lean_dec_ref(v_fst_4737_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 0, v_val_4745_);
v___x_4747_ = v___x_4735_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_val_4745_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
}
}
else
{
lean_object* v_vs_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4785_; 
v_vs_4751_ = lean_ctor_get(v_n_4714_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v_n_4714_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4753_ = v_n_4714_;
v_isShared_4754_ = v_isSharedCheck_4785_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_vs_4751_);
lean_dec(v_n_4714_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4785_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; size_t v_sz_4757_; size_t v___x_4758_; lean_object* v___x_4759_; 
v___x_4755_ = lean_box(0);
v___x_4756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4755_);
lean_ctor_set(v___x_4756_, 1, v_b_4715_);
v_sz_4757_ = lean_array_size(v_vs_4751_);
v___x_4758_ = ((size_t)0ULL);
v___x_4759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_vs_4751_, v_sz_4757_, v___x_4758_, v___x_4756_);
lean_dec_ref(v_vs_4751_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
lean_del_object(v___x_4753_);
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4759_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4759_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
else
{
lean_object* v_a_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4784_; 
v_a_4768_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4770_ = v___x_4759_;
v_isShared_4771_ = v_isSharedCheck_4784_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_a_4768_);
lean_dec(v___x_4759_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4784_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v_fst_4772_; 
v_fst_4772_ = lean_ctor_get(v_a_4768_, 0);
if (lean_obj_tag(v_fst_4772_) == 0)
{
lean_object* v_snd_4773_; lean_object* v___x_4775_; 
v_snd_4773_ = lean_ctor_get(v_a_4768_, 1);
lean_inc(v_snd_4773_);
lean_dec(v_a_4768_);
if (v_isShared_4754_ == 0)
{
lean_ctor_set(v___x_4753_, 0, v_snd_4773_);
v___x_4775_ = v___x_4753_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_snd_4773_);
v___x_4775_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
lean_object* v___x_4777_; 
if (v_isShared_4771_ == 0)
{
lean_ctor_set(v___x_4770_, 0, v___x_4775_);
v___x_4777_ = v___x_4770_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4775_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
return v___x_4777_;
}
}
}
else
{
lean_object* v_val_4780_; lean_object* v___x_4782_; 
lean_inc_ref(v_fst_4772_);
lean_dec(v_a_4768_);
lean_del_object(v___x_4753_);
v_val_4780_ = lean_ctor_get(v_fst_4772_, 0);
lean_inc(v_val_4780_);
lean_dec_ref(v_fst_4772_);
if (v_isShared_4771_ == 0)
{
lean_ctor_set(v___x_4770_, 0, v_val_4780_);
v___x_4782_ = v___x_4770_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_val_4780_);
v___x_4782_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
return v___x_4782_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object* v_init_4786_, lean_object* v_as_4787_, size_t v_sz_4788_, size_t v_i_4789_, lean_object* v_b_4790_){
_start:
{
uint8_t v___x_4791_; 
v___x_4791_ = lean_usize_dec_lt(v_i_4789_, v_sz_4788_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4792_; 
v___x_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4792_, 0, v_b_4790_);
return v___x_4792_;
}
else
{
lean_object* v_snd_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4827_; 
v_snd_4793_ = lean_ctor_get(v_b_4790_, 1);
v_isSharedCheck_4827_ = !lean_is_exclusive(v_b_4790_);
if (v_isSharedCheck_4827_ == 0)
{
lean_object* v_unused_4828_; 
v_unused_4828_ = lean_ctor_get(v_b_4790_, 0);
lean_dec(v_unused_4828_);
v___x_4795_ = v_b_4790_;
v_isShared_4796_ = v_isSharedCheck_4827_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_snd_4793_);
lean_dec(v_b_4790_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4827_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v_a_4797_; lean_object* v___x_4798_; 
v_a_4797_ = lean_array_uget_borrowed(v_as_4787_, v_i_4789_);
lean_inc(v_snd_4793_);
lean_inc(v_a_4797_);
v___x_4798_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4786_, v_a_4797_, v_snd_4793_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4806_; 
lean_del_object(v___x_4795_);
lean_dec(v_snd_4793_);
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4801_ = v___x_4798_;
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4798_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___x_4804_; 
if (v_isShared_4802_ == 0)
{
v___x_4804_ = v___x_4801_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4826_; 
v_a_4807_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4809_ = v___x_4798_;
v_isShared_4810_ = v_isSharedCheck_4826_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4798_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4826_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
if (lean_obj_tag(v_a_4807_) == 0)
{
lean_object* v___x_4811_; lean_object* v___x_4813_; 
v___x_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4811_, 0, v_a_4807_);
if (v_isShared_4796_ == 0)
{
lean_ctor_set(v___x_4795_, 0, v___x_4811_);
v___x_4813_ = v___x_4795_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4811_);
lean_ctor_set(v_reuseFailAlloc_4817_, 1, v_snd_4793_);
v___x_4813_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
lean_object* v___x_4815_; 
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4813_);
v___x_4815_ = v___x_4809_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4813_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
else
{
lean_object* v_a_4818_; lean_object* v___x_4819_; lean_object* v___x_4821_; 
lean_del_object(v___x_4809_);
lean_dec(v_snd_4793_);
v_a_4818_ = lean_ctor_get(v_a_4807_, 0);
lean_inc(v_a_4818_);
lean_dec_ref(v_a_4807_);
v___x_4819_ = lean_box(0);
if (v_isShared_4796_ == 0)
{
lean_ctor_set(v___x_4795_, 1, v_a_4818_);
lean_ctor_set(v___x_4795_, 0, v___x_4819_);
v___x_4821_ = v___x_4795_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v___x_4819_);
lean_ctor_set(v_reuseFailAlloc_4825_, 1, v_a_4818_);
v___x_4821_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
size_t v___x_4822_; size_t v___x_4823_; 
v___x_4822_ = ((size_t)1ULL);
v___x_4823_ = lean_usize_add(v_i_4789_, v___x_4822_);
v_i_4789_ = v___x_4823_;
v_b_4790_ = v___x_4821_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4829_, lean_object* v_as_4830_, lean_object* v_sz_4831_, lean_object* v_i_4832_, lean_object* v_b_4833_){
_start:
{
size_t v_sz_boxed_4834_; size_t v_i_boxed_4835_; lean_object* v_res_4836_; 
v_sz_boxed_4834_ = lean_unbox_usize(v_sz_4831_);
lean_dec(v_sz_4831_);
v_i_boxed_4835_ = lean_unbox_usize(v_i_4832_);
lean_dec(v_i_4832_);
v_res_4836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_4829_, v_as_4830_, v_sz_boxed_4834_, v_i_boxed_4835_, v_b_4833_);
lean_dec_ref(v_as_4830_);
lean_dec_ref(v_init_4829_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object* v_init_4837_, lean_object* v_n_4838_, lean_object* v_b_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4837_, v_n_4838_, v_b_4839_);
lean_dec_ref(v_init_4837_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object* v_t_4841_, lean_object* v_init_4842_){
_start:
{
lean_object* v_root_4843_; lean_object* v_tail_4844_; lean_object* v___x_4845_; 
v_root_4843_ = lean_ctor_get(v_t_4841_, 0);
lean_inc_ref(v_root_4843_);
v_tail_4844_ = lean_ctor_get(v_t_4841_, 1);
lean_inc_ref(v_tail_4844_);
lean_dec_ref(v_t_4841_);
lean_inc_ref(v_init_4842_);
v___x_4845_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4842_, v_root_4843_, v_init_4842_);
lean_dec_ref(v_init_4842_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4853_; 
lean_dec_ref(v_tail_4844_);
v_a_4846_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4848_ = v___x_4845_;
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4845_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4846_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4890_; 
v_a_4854_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4856_ = v___x_4845_;
v_isShared_4857_ = v_isSharedCheck_4890_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4845_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4890_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
if (lean_obj_tag(v_a_4854_) == 0)
{
lean_object* v_a_4858_; lean_object* v___x_4860_; 
lean_dec_ref(v_tail_4844_);
v_a_4858_ = lean_ctor_get(v_a_4854_, 0);
lean_inc(v_a_4858_);
lean_dec_ref(v_a_4854_);
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 0, v_a_4858_);
v___x_4860_ = v___x_4856_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_a_4858_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
else
{
lean_object* v_a_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; size_t v_sz_4865_; size_t v___x_4866_; lean_object* v___x_4867_; 
lean_del_object(v___x_4856_);
v_a_4862_ = lean_ctor_get(v_a_4854_, 0);
lean_inc(v_a_4862_);
lean_dec_ref(v_a_4854_);
v___x_4863_ = lean_box(0);
v___x_4864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4863_);
lean_ctor_set(v___x_4864_, 1, v_a_4862_);
v_sz_4865_ = lean_array_size(v_tail_4844_);
v___x_4866_ = ((size_t)0ULL);
v___x_4867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_tail_4844_, v_sz_4865_, v___x_4866_, v___x_4864_);
lean_dec_ref(v_tail_4844_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4867_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4867_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4873_; 
if (v_isShared_4871_ == 0)
{
v___x_4873_ = v___x_4870_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4868_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4889_; 
v_a_4876_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4878_ = v___x_4867_;
v_isShared_4879_ = v_isSharedCheck_4889_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4867_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4889_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v_fst_4880_; 
v_fst_4880_ = lean_ctor_get(v_a_4876_, 0);
if (lean_obj_tag(v_fst_4880_) == 0)
{
lean_object* v_snd_4881_; lean_object* v___x_4883_; 
v_snd_4881_ = lean_ctor_get(v_a_4876_, 1);
lean_inc(v_snd_4881_);
lean_dec(v_a_4876_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v_snd_4881_);
v___x_4883_ = v___x_4878_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_snd_4881_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
else
{
lean_object* v_val_4885_; lean_object* v___x_4887_; 
lean_inc_ref(v_fst_4880_);
lean_dec(v_a_4876_);
v_val_4885_ = lean_ctor_get(v_fst_4880_, 0);
lean_inc(v_val_4885_);
lean_dec_ref(v_fst_4880_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v_val_4885_);
v___x_4887_ = v___x_4878_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_val_4885_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object* v_docs_4895_){
_start:
{
lean_object* v_snippets_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4933_; 
v_snippets_4896_ = lean_ctor_get(v_docs_4895_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v_docs_4895_);
if (v_isSharedCheck_4933_ == 0)
{
lean_object* v_unused_4934_; 
v_unused_4934_ = lean_ctor_get(v_docs_4895_, 1);
lean_dec(v_unused_4934_);
v___x_4898_ = v_docs_4895_;
v_isShared_4899_ = v_isSharedCheck_4933_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_snippets_4896_);
lean_dec(v_docs_4895_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4933_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v_ctx_4900_; lean_object* v___x_4901_; 
v_ctx_4900_ = ((lean_object*)(l_Lean_VersoModuleDocs_assemble___closed__1));
v___x_4901_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_snippets_4896_, v_ctx_4900_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4909_; 
lean_del_object(v___x_4898_);
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4904_ = v___x_4901_;
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4901_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4902_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
else
{
lean_object* v_a_4910_; lean_object* v___x_4911_; 
v_a_4910_ = lean_ctor_get(v___x_4901_, 0);
lean_inc(v_a_4910_);
lean_dec_ref(v___x_4901_);
v___x_4911_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(v_a_4910_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4919_; 
lean_del_object(v___x_4898_);
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4914_ = v___x_4911_;
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4911_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4917_; 
if (v_isShared_4915_ == 0)
{
v___x_4917_ = v___x_4914_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_a_4912_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
else
{
lean_object* v_a_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4932_; 
v_a_4920_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4922_ = v___x_4911_;
v_isShared_4923_ = v_isSharedCheck_4932_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_a_4920_);
lean_dec(v___x_4911_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4932_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v_content_4924_; lean_object* v_priorParts_4925_; lean_object* v___x_4927_; 
v_content_4924_ = lean_ctor_get(v_a_4920_, 0);
lean_inc_ref(v_content_4924_);
v_priorParts_4925_ = lean_ctor_get(v_a_4920_, 1);
lean_inc_ref(v_priorParts_4925_);
lean_dec(v_a_4920_);
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 1, v_priorParts_4925_);
lean_ctor_set(v___x_4898_, 0, v_content_4924_);
v___x_4927_ = v___x_4898_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_content_4924_);
lean_ctor_set(v_reuseFailAlloc_4931_, 1, v_priorParts_4925_);
v___x_4927_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
lean_object* v___x_4929_; 
if (v_isShared_4923_ == 0)
{
lean_ctor_set(v___x_4922_, 0, v___x_4927_);
v___x_4929_ = v___x_4922_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4927_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_es_4935_){
_start:
{
lean_object* v___x_4936_; 
v___x_4936_ = lean_array_mk(v_es_4935_);
return v___x_4936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_x_4939_, lean_object* v_x_4940_, lean_object* v_es_4941_){
_start:
{
lean_object* v_ents_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v_ents_4942_ = lean_array_mk(v_es_4941_);
v___x_4943_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
lean_inc_ref(v_ents_4942_);
v___x_4944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4943_);
lean_ctor_set(v___x_4944_, 1, v_ents_4942_);
lean_ctor_set(v___x_4944_, 2, v_ents_4942_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_x_4945_, lean_object* v_x_4946_, lean_object* v_es_4947_){
_start:
{
lean_object* v_res_4948_; 
v_res_4948_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v_x_4945_, v_x_4946_, v_es_4947_);
lean_dec_ref(v_x_4946_);
lean_dec_ref(v_x_4945_);
return v_res_4948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_4949_, lean_object* v_i_4950_){
_start:
{
lean_object* v_zero_4951_; uint8_t v_isZero_4952_; 
v_zero_4951_ = lean_unsigned_to_nat(0u);
v_isZero_4952_ = lean_nat_dec_eq(v_i_4950_, v_zero_4951_);
if (v_isZero_4952_ == 1)
{
lean_object* v___x_4953_; 
lean_dec(v_i_4950_);
v___x_4953_ = lean_box(0);
return v___x_4953_;
}
else
{
lean_object* v_one_4954_; lean_object* v_n_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; 
v_one_4954_ = lean_unsigned_to_nat(1u);
v_n_4955_ = lean_nat_sub(v_i_4950_, v_one_4954_);
lean_dec(v_i_4950_);
v___x_4956_ = lean_array_fget_borrowed(v_as_4949_, v_n_4955_);
v___x_4957_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v___x_4956_);
if (lean_obj_tag(v___x_4957_) == 0)
{
v_i_4950_ = v_n_4955_;
goto _start;
}
else
{
lean_dec(v_n_4955_);
return v___x_4957_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_4959_, lean_object* v_i_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_4959_, v_i_4960_);
lean_dec_ref(v_as_4959_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_as_4962_, lean_object* v_i_4963_){
_start:
{
lean_object* v_zero_4964_; uint8_t v_isZero_4965_; 
v_zero_4964_ = lean_unsigned_to_nat(0u);
v_isZero_4965_ = lean_nat_dec_eq(v_i_4963_, v_zero_4964_);
if (v_isZero_4965_ == 1)
{
lean_object* v___x_4966_; 
lean_dec(v_i_4963_);
v___x_4966_ = lean_box(0);
return v___x_4966_;
}
else
{
lean_object* v_one_4967_; lean_object* v_n_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v_one_4967_ = lean_unsigned_to_nat(1u);
v_n_4968_ = lean_nat_sub(v_i_4963_, v_one_4967_);
lean_dec(v_i_4963_);
v___x_4969_ = lean_array_fget_borrowed(v_as_4962_, v_n_4968_);
v___x_4970_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1(v___x_4969_);
if (lean_obj_tag(v___x_4970_) == 0)
{
v_i_4963_ = v_n_4968_;
goto _start;
}
else
{
lean_dec(v_n_4968_);
return v___x_4970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_x_4972_){
_start:
{
if (lean_obj_tag(v_x_4972_) == 0)
{
lean_object* v_cs_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v_cs_4973_ = lean_ctor_get(v_x_4972_, 0);
v___x_4974_ = lean_array_get_size(v_cs_4973_);
v___x_4975_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_cs_4973_, v___x_4974_);
return v___x_4975_;
}
else
{
lean_object* v_vs_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; 
v_vs_4976_ = lean_ctor_get(v_x_4972_, 0);
v___x_4977_ = lean_array_get_size(v_vs_4976_);
v___x_4978_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0___redArg(v_vs_4976_, v___x_4977_);
return v___x_4978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_x_4979_){
_start:
{
lean_object* v_res_4980_; 
v_res_4980_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1(v_x_4979_);
lean_dec_ref(v_x_4979_);
return v_res_4980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_4981_, lean_object* v_i_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_as_4981_, v_i_4982_);
lean_dec_ref(v_as_4981_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0(lean_object* v_t_4984_){
_start:
{
lean_object* v_root_4985_; lean_object* v_tail_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v_root_4985_ = lean_ctor_get(v_t_4984_, 0);
v_tail_4986_ = lean_ctor_get(v_t_4984_, 1);
v___x_4987_ = lean_array_get_size(v_tail_4986_);
v___x_4988_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0___redArg(v_tail_4986_, v___x_4987_);
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v___x_4989_; 
v___x_4989_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1(v_root_4985_);
return v___x_4989_;
}
else
{
return v___x_4988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0___boxed(lean_object* v_t_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0(v_t_4990_);
lean_dec_ref(v_t_4990_);
return v_res_4991_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4992_ = lean_unsigned_to_nat(32u);
v___x_4993_ = lean_mk_empty_array_with_capacity(v___x_4992_);
v___x_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v___x_4995_, lean_object* v_x_4996_){
_start:
{
lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; size_t v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_4997_ = lean_unsigned_to_nat(32u);
v___x_4998_ = lean_mk_empty_array_with_capacity(v___x_4997_);
v___x_4999_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_);
v___x_5000_ = ((size_t)5ULL);
lean_inc(v___x_4995_);
v___x_5001_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5001_, 0, v___x_4999_);
lean_ctor_set(v___x_5001_, 1, v___x_4998_);
lean_ctor_set(v___x_5001_, 2, v___x_4995_);
lean_ctor_set(v___x_5001_, 3, v___x_4995_);
lean_ctor_set_usize(v___x_5001_, 4, v___x_5000_);
v___x_5002_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0(v___x_5001_);
v___x_5003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5003_, 0, v___x_5001_);
lean_ctor_set(v___x_5003_, 1, v___x_5002_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v___x_5004_, lean_object* v_x_5005_){
_start:
{
lean_object* v_res_5006_; 
v_res_5006_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v___x_5004_, v_x_5005_);
lean_dec_ref(v_x_5005_);
return v_res_5006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5027_; lean_object* v___x_5028_; 
v___x_5027_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
v___x_5028_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5027_);
return v___x_5028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_a_5029_){
_start:
{
lean_object* v_res_5030_; 
v_res_5030_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
return v_res_5030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_5031_, lean_object* v_i_5032_, lean_object* v_a_5033_){
_start:
{
lean_object* v___x_5034_; 
v___x_5034_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_5031_, v_i_5032_);
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_5035_, lean_object* v_i_5036_, lean_object* v_a_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__0(v_as_5035_, v_i_5036_, v_a_5037_);
lean_dec_ref(v_as_5035_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_as_5039_, lean_object* v_i_5040_, lean_object* v_a_5041_){
_start:
{
lean_object* v___x_5042_; 
v___x_5042_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_as_5039_, v_i_5040_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1_spec__2___boxed(lean_object* v_as_5043_, lean_object* v_i_5044_, lean_object* v_a_5045_){
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__spec__0_spec__1_spec__2(v_as_5043_, v_i_5044_, v_a_5045_);
lean_dec_ref(v_as_5043_);
return v_res_5046_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object* v_env_5047_){
_start:
{
lean_object* v___x_5048_; lean_object* v_toEnvExtension_5049_; lean_object* v_asyncMode_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5048_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_5049_ = lean_ctor_get(v___x_5048_, 0);
v_asyncMode_5050_ = lean_ctor_get(v_toEnvExtension_5049_, 2);
v___x_5051_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_5052_ = lean_box(0);
v___x_5053_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5051_, v___x_5048_, v_env_5047_, v_asyncMode_5050_, v___x_5052_);
return v___x_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object* v_env_5054_){
_start:
{
lean_object* v___x_5055_; 
v___x_5055_ = l_Lean_getMainVersoModuleDocs(v_env_5054_);
return v___x_5055_;
}
}
static lean_object* _init_l_Lean_getVersoModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
v___x_5056_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_5057_ = lean_box(0);
v___x_5058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5058_, 0, v___x_5057_);
lean_ctor_set(v___x_5058_, 1, v___x_5056_);
return v___x_5058_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object* v_env_5059_, lean_object* v_moduleName_5060_){
_start:
{
lean_object* v___x_5061_; 
v___x_5061_ = l_Lean_Environment_getModuleIdx_x3f(v_env_5059_, v_moduleName_5060_);
if (lean_obj_tag(v___x_5061_) == 0)
{
lean_object* v___x_5062_; 
v___x_5062_ = lean_box(0);
return v___x_5062_;
}
else
{
lean_object* v_val_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5074_; 
v_val_5063_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5065_ = v___x_5061_;
v_isShared_5066_ = v_isSharedCheck_5074_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_val_5063_);
lean_dec(v___x_5061_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5074_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; uint8_t v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5072_; 
v___x_5067_ = lean_obj_once(&l_Lean_getVersoModuleDoc_x3f___closed__0, &l_Lean_getVersoModuleDoc_x3f___closed__0_once, _init_l_Lean_getVersoModuleDoc_x3f___closed__0);
v___x_5068_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v___x_5069_ = 1;
v___x_5070_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_5067_, v___x_5068_, v_env_5059_, v_val_5063_, v___x_5069_);
lean_dec(v_val_5063_);
if (v_isShared_5066_ == 0)
{
lean_ctor_set(v___x_5065_, 0, v___x_5070_);
v___x_5072_ = v___x_5065_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v___x_5070_);
v___x_5072_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
return v___x_5072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object* v_env_5075_, lean_object* v_moduleName_5076_){
_start:
{
lean_object* v_res_5077_; 
v_res_5077_ = l_Lean_getVersoModuleDoc_x3f(v_env_5075_, v_moduleName_5076_);
lean_dec(v_moduleName_5076_);
lean_dec_ref(v_env_5075_);
return v_res_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object* v_env_5080_, lean_object* v_snippet_5081_){
_start:
{
lean_object* v_docs_5082_; uint8_t v___x_5083_; 
lean_inc_ref(v_env_5080_);
v_docs_5082_ = l_Lean_getMainVersoModuleDocs(v_env_5080_);
v___x_5083_ = l_Lean_VersoModuleDocs_canAdd(v_docs_5082_, v_snippet_5081_);
if (v___x_5083_ == 0)
{
lean_object* v_terminalNesting_5084_; lean_object* v___x_5085_; lean_object* v___y_5087_; 
lean_dec_ref(v_snippet_5081_);
lean_dec_ref(v_env_5080_);
v_terminalNesting_5084_ = lean_ctor_get(v_docs_5082_, 1);
lean_inc(v_terminalNesting_5084_);
lean_dec_ref(v_docs_5082_);
v___x_5085_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__0));
if (lean_obj_tag(v_terminalNesting_5084_) == 0)
{
lean_object* v___x_5092_; 
v___x_5092_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___y_5087_ = v___x_5092_;
goto v___jp_5086_;
}
else
{
lean_object* v_val_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; 
v_val_5093_ = lean_ctor_get(v_terminalNesting_5084_, 0);
lean_inc(v_val_5093_);
lean_dec_ref(v_terminalNesting_5084_);
v___x_5094_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__1));
v___x_5095_ = l_Nat_reprFast(v_val_5093_);
v___x_5096_ = lean_string_append(v___x_5094_, v___x_5095_);
lean_dec_ref(v___x_5095_);
v___x_5097_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_5098_ = lean_string_append(v___x_5096_, v___x_5097_);
v___y_5087_ = v___x_5098_;
goto v___jp_5086_;
}
v___jp_5086_:
{
lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___x_5088_ = lean_string_append(v___x_5085_, v___y_5087_);
lean_dec_ref(v___y_5087_);
v___x_5089_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_5090_ = lean_string_append(v___x_5088_, v___x_5089_);
v___x_5091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5090_);
return v___x_5091_;
}
}
else
{
lean_object* v___x_5099_; lean_object* v_toEnvExtension_5100_; lean_object* v_asyncMode_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
lean_dec_ref(v_docs_5082_);
v___x_5099_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_5100_ = lean_ctor_get(v___x_5099_, 0);
v_asyncMode_5101_ = lean_ctor_get(v_toEnvExtension_5100_, 2);
v___x_5102_ = lean_box(0);
v___x_5103_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5099_, v_env_5080_, v_snippet_5081_, v_asyncMode_5101_, v___x_5102_);
v___x_5104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5104_, 0, v___x_5103_);
return v___x_5104_;
}
}
}
lean_object* runtime_initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Markdown(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Markdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instMarkdownInlineElabInline = _init_l_Lean_instMarkdownInlineElabInline();
lean_mark_persistent(l_Lean_instMarkdownInlineElabInline);
l_Lean_instMarkdownBlockElabInlineElabBlock = _init_l_Lean_instMarkdownBlockElabInlineElabBlock();
lean_mark_persistent(l_Lean_instMarkdownBlockElabInlineElabBlock);
res = l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_doc_verso = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_doc_verso);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_doc_verso_module = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_doc_verso_module);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_docStringExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_docStringExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_versoDocStringExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_versoDocStringExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_moduleDocExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_moduleDocExt);
lean_dec_ref(res);
l_Lean_VersoModuleDocs_instInhabitedSnippet_default = _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default();
lean_mark_persistent(l_Lean_VersoModuleDocs_instInhabitedSnippet_default);
l_Lean_VersoModuleDocs_instInhabitedSnippet = _init_l_Lean_VersoModuleDocs_instInhabitedSnippet();
lean_mark_persistent(l_Lean_VersoModuleDocs_instInhabitedSnippet);
l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1 = _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1();
lean_mark_persistent(l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1);
l_Lean_instToMarkdownSnippet = _init_l_Lean_instToMarkdownSnippet();
lean_mark_persistent(l_Lean_instToMarkdownSnippet);
l_Lean_instInhabitedVersoModuleDocs_default = _init_l_Lean_instInhabitedVersoModuleDocs_default();
lean_mark_persistent(l_Lean_instInhabitedVersoModuleDocs_default);
l_Lean_instInhabitedVersoModuleDocs = _init_l_Lean_instInhabitedVersoModuleDocs();
lean_mark_persistent(l_Lean_instInhabitedVersoModuleDocs);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Extension(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* initialize_Lean_DocString_Markdown(uint8_t builtin);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Extension(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Markdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Extension(builtin);
}
#ifdef __cplusplus
}
#endif
