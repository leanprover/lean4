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
lean_object* lean_array_mk(lean_object*);
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
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_instInhabitedVersoDocString_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoDocString_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoDocString_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoDocString;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "docStringExt"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(220, 176, 252, 112, 223, 70, 141, 135)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_docStringExt;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DocString"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 151, 103, 225, 164, 122, 118, 127)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Extension"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 24, 255, 250, 40, 109, 111, 101)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(90, 73, 37, 46, 133, 14, 26, 13)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(251, 17, 71, 28, 211, 27, 155, 40)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inheritDocStringExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__10_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 170, 221, 64, 52, 198, 31, 56)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "versoDocStringExt"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 29, 13, 95, 132, 33, 43, 178)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13;
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
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentArray_push___redArg, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "moduleDocExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 198, 210, 20, 250, 243, 120, 74)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object*);
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
static lean_once_cell_t l_Lean_VersoModuleDocs_assemble___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_VersoModuleDocs_assemble___closed__1;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_VersoModuleDocs_add_x21, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "versoModuleDocExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 74, 101, 232, 220, 166, 152, 230)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_instInhabitedVersoDocString_default___closed__1(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default___closed__0));
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoDocString_default(void){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Lean_instInhabitedVersoDocString_default___closed__1, &l_Lean_instInhabitedVersoDocString_default___closed__1_once, _init_l_Lean_instInhabitedVersoDocString_default___closed__1);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoDocString(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_instInhabitedVersoDocString_default;
return v___x_234_;
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
lean_inc(v_name_235_);
v___x_246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_246_, 0, v_name_235_);
lean_ctor_set(v___x_246_, 1, v_ref_237_);
lean_ctor_set(v___x_246_, 2, v___x_244_);
lean_ctor_set(v___x_246_, 3, v_descr_240_);
lean_inc(v_name_235_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v_k_325_; lean_object* v_v_326_; lean_object* v_l_327_; lean_object* v_r_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_k_325_ = lean_ctor_get(v_x_324_, 1);
v_v_326_ = lean_ctor_get(v_x_324_, 2);
v_l_327_ = lean_ctor_get(v_x_324_, 3);
v_r_328_ = lean_ctor_get(v_x_324_, 4);
v___x_329_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(v_init_323_, v_l_327_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_333_, lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(v_init_333_, v_x_334_);
lean_dec(v_x_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_(lean_object* v_x_338_, lean_object* v_s_339_, uint8_t v_level_340_){
_start:
{
uint8_t v___x_341_; uint8_t v___x_342_; 
v___x_341_ = 1;
v___x_342_ = l_Lean_instOrdOLeanLevel_ord(v_level_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
v___x_343_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_345_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(v___x_344_, v_s_339_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2____boxed(lean_object* v_x_346_, lean_object* v_s_347_, lean_object* v_level_348_){
_start:
{
uint8_t v_level_boxed_349_; lean_object* v_res_350_; 
v_level_boxed_349_ = lean_unbox(v_level_348_);
v_res_350_ = l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_(v_x_346_, v_s_347_, v_level_boxed_349_);
lean_dec(v_s_347_);
lean_dec_ref(v_x_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___f_359_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_360_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_361_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_362_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_360_, v___x_361_, v___f_359_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2____boxed(lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_();
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0(lean_object* v_init_365_, lean_object* v_t_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(v_init_365_, v_t_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_368_, lean_object* v_t_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0(v_init_368_, v_t_369_);
lean_dec(v_t_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_371_, lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
lean_object* v_k_373_; lean_object* v_v_374_; lean_object* v_l_375_; lean_object* v_r_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_k_373_ = lean_ctor_get(v_x_372_, 1);
v_v_374_ = lean_ctor_get(v_x_372_, 2);
v_l_375_ = lean_ctor_get(v_x_372_, 3);
v_r_376_ = lean_ctor_get(v_x_372_, 4);
v___x_377_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(v_init_371_, v_l_375_);
lean_inc(v_v_374_);
lean_inc(v_k_373_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_k_373_);
lean_ctor_set(v___x_378_, 1, v_v_374_);
v___x_379_ = lean_array_push(v___x_377_, v___x_378_);
v_init_371_ = v___x_379_;
v_x_372_ = v_r_376_;
goto _start;
}
else
{
return v_init_371_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_381_, lean_object* v_x_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(v_init_381_, v_x_382_);
lean_dec(v_x_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_(lean_object* v_x_386_, lean_object* v_s_387_, uint8_t v_level_388_){
_start:
{
uint8_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 1;
v___x_390_ = l_Lean_instOrdOLeanLevel_ord(v_level_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
v___x_393_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(v___x_392_, v_s_387_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2____boxed(lean_object* v_x_394_, lean_object* v_s_395_, lean_object* v_level_396_){
_start:
{
uint8_t v_level_boxed_397_; lean_object* v_res_398_; 
v_level_boxed_397_ = lean_unbox(v_level_396_);
v_res_398_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_(v_x_394_, v_s_395_, v_level_boxed_397_);
lean_dec(v_s_395_);
lean_dec_ref(v_x_394_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___f_428_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
v___x_429_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
v___x_430_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
v___x_431_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_429_, v___x_430_, v___f_428_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2____boxed(lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_();
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0(lean_object* v_init_434_, lean_object* v_t_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(v_init_434_, v_t_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_437_, lean_object* v_t_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0(v_init_437_, v_t_438_);
lean_dec(v_t_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_box(1);
v___x_442_ = lean_st_mk_ref(v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_object* v_k_448_; lean_object* v_v_449_; lean_object* v_l_450_; lean_object* v_r_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_k_448_ = lean_ctor_get(v_x_447_, 1);
v_v_449_ = lean_ctor_get(v_x_447_, 2);
v_l_450_ = lean_ctor_get(v_x_447_, 3);
v_r_451_ = lean_ctor_get(v_x_447_, 4);
v___x_452_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(v_init_446_, v_l_450_);
lean_inc(v_v_449_);
lean_inc(v_k_448_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_k_448_);
lean_ctor_set(v___x_453_, 1, v_v_449_);
v___x_454_ = lean_array_push(v___x_452_, v___x_453_);
v_init_446_ = v___x_454_;
v_x_447_ = v_r_451_;
goto _start;
}
else
{
return v_init_446_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_456_, lean_object* v_x_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(v_init_456_, v_x_457_);
lean_dec(v_x_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_(lean_object* v_x_461_, lean_object* v_s_462_, uint8_t v_level_463_){
_start:
{
uint8_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = 1;
v___x_465_ = l_Lean_instOrdOLeanLevel_ord(v_level_463_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
v___x_466_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_));
return v___x_466_;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_));
v___x_468_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(v___x_467_, v_s_462_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2____boxed(lean_object* v_x_469_, lean_object* v_s_470_, lean_object* v_level_471_){
_start:
{
uint8_t v_level_boxed_472_; lean_object* v_res_473_; 
v_level_boxed_472_ = lean_unbox(v_level_471_);
v_res_473_ = l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_(v_x_469_, v_s_470_, v_level_boxed_472_);
lean_dec(v_s_470_);
lean_dec_ref(v_x_469_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___f_480_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_));
v___x_481_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_));
v___x_482_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_483_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_481_, v___x_482_, v___f_480_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2____boxed(lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_();
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0(lean_object* v_init_486_, lean_object* v_t_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(v_init_486_, v_t_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_489_, lean_object* v_t_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0(v_init_489_, v_t_490_);
lean_dec(v_t_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString(lean_object* v_declName_492_, lean_object* v_docString_493_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_495_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_496_ = lean_st_ref_take(v___x_495_);
v___x_497_ = l_String_removeLeadingSpaces(v_docString_493_);
v___x_498_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_492_, v___x_497_, v___x_496_);
v___x_499_ = lean_st_ref_set(v___x_495_, v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString___boxed(lean_object* v_declName_501_, lean_object* v_docString_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_addBuiltinDocString(v_declName_501_, v_docString_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object* v_k_505_, lean_object* v_t_506_){
_start:
{
if (lean_obj_tag(v_t_506_) == 0)
{
lean_object* v_k_507_; lean_object* v_v_508_; lean_object* v_l_509_; lean_object* v_r_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_1164_; 
v_k_507_ = lean_ctor_get(v_t_506_, 1);
v_v_508_ = lean_ctor_get(v_t_506_, 2);
v_l_509_ = lean_ctor_get(v_t_506_, 3);
v_r_510_ = lean_ctor_get(v_t_506_, 4);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_t_506_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v_t_506_, 0);
lean_dec(v_unused_1165_);
v___x_512_ = v_t_506_;
v_isShared_513_ = v_isSharedCheck_1164_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_r_510_);
lean_inc(v_l_509_);
lean_inc(v_v_508_);
lean_inc(v_k_507_);
lean_dec(v_t_506_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_1164_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint8_t v___x_514_; 
v___x_514_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_505_, v_k_507_);
switch(v___x_514_)
{
case 0:
{
lean_object* v_impl_515_; lean_object* v___x_516_; 
v_impl_515_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_505_, v_l_509_);
v___x_516_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_515_) == 0)
{
if (lean_obj_tag(v_r_510_) == 0)
{
lean_object* v_size_517_; lean_object* v_size_518_; lean_object* v_k_519_; lean_object* v_v_520_; lean_object* v_l_521_; lean_object* v_r_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_size_517_ = lean_ctor_get(v_impl_515_, 0);
lean_inc(v_size_517_);
v_size_518_ = lean_ctor_get(v_r_510_, 0);
v_k_519_ = lean_ctor_get(v_r_510_, 1);
v_v_520_ = lean_ctor_get(v_r_510_, 2);
v_l_521_ = lean_ctor_get(v_r_510_, 3);
lean_inc(v_l_521_);
v_r_522_ = lean_ctor_get(v_r_510_, 4);
v___x_523_ = lean_unsigned_to_nat(3u);
v___x_524_ = lean_nat_mul(v___x_523_, v_size_517_);
v___x_525_ = lean_nat_dec_lt(v___x_524_, v_size_518_);
lean_dec(v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
lean_dec(v_l_521_);
v___x_526_ = lean_nat_add(v___x_516_, v_size_517_);
lean_dec(v_size_517_);
v___x_527_ = lean_nat_add(v___x_526_, v_size_518_);
lean_dec(v___x_526_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 3, v_impl_515_);
lean_ctor_set(v___x_512_, 0, v___x_527_);
v___x_529_ = v___x_512_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_530_, 3, v_impl_515_);
lean_ctor_set(v_reuseFailAlloc_530_, 4, v_r_510_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
else
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_594_; 
lean_inc(v_r_522_);
lean_inc(v_v_520_);
lean_inc(v_k_519_);
lean_inc(v_size_518_);
v_isSharedCheck_594_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; lean_object* v_unused_596_; lean_object* v_unused_597_; lean_object* v_unused_598_; lean_object* v_unused_599_; 
v_unused_595_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_595_);
v_unused_596_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_596_);
v_unused_597_ = lean_ctor_get(v_r_510_, 2);
lean_dec(v_unused_597_);
v_unused_598_ = lean_ctor_get(v_r_510_, 1);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v_r_510_, 0);
lean_dec(v_unused_599_);
v___x_532_ = v_r_510_;
v_isShared_533_ = v_isSharedCheck_594_;
goto v_resetjp_531_;
}
else
{
lean_dec(v_r_510_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_594_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_size_534_; lean_object* v_k_535_; lean_object* v_v_536_; lean_object* v_l_537_; lean_object* v_r_538_; lean_object* v_size_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_size_534_ = lean_ctor_get(v_l_521_, 0);
v_k_535_ = lean_ctor_get(v_l_521_, 1);
v_v_536_ = lean_ctor_get(v_l_521_, 2);
v_l_537_ = lean_ctor_get(v_l_521_, 3);
v_r_538_ = lean_ctor_get(v_l_521_, 4);
v_size_539_ = lean_ctor_get(v_r_522_, 0);
v___x_540_ = lean_unsigned_to_nat(2u);
v___x_541_ = lean_nat_mul(v___x_540_, v_size_539_);
v___x_542_ = lean_nat_dec_lt(v_size_534_, v___x_541_);
lean_dec(v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_570_; 
lean_inc(v_r_538_);
lean_inc(v_l_537_);
lean_inc(v_v_536_);
lean_inc(v_k_535_);
v_isSharedCheck_570_ = !lean_is_exclusive(v_l_521_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_571_ = lean_ctor_get(v_l_521_, 4);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_l_521_, 3);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_l_521_, 2);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_l_521_, 1);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_l_521_, 0);
lean_dec(v_unused_575_);
v___x_544_ = v_l_521_;
v_isShared_545_ = v_isSharedCheck_570_;
goto v_resetjp_543_;
}
else
{
lean_dec(v_l_521_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_570_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_560_; 
v___x_546_ = lean_nat_add(v___x_516_, v_size_517_);
lean_dec(v_size_517_);
v___x_547_ = lean_nat_add(v___x_546_, v_size_518_);
lean_dec(v_size_518_);
if (lean_obj_tag(v_l_537_) == 0)
{
lean_object* v_size_568_; 
v_size_568_ = lean_ctor_get(v_l_537_, 0);
lean_inc(v_size_568_);
v___y_560_ = v_size_568_;
goto v___jp_559_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = lean_unsigned_to_nat(0u);
v___y_560_ = v___x_569_;
goto v___jp_559_;
}
v___jp_548_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_nat_add(v___y_549_, v___y_551_);
lean_dec(v___y_551_);
lean_dec(v___y_549_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 4, v_r_522_);
lean_ctor_set(v___x_544_, 3, v_r_538_);
lean_ctor_set(v___x_544_, 2, v_v_520_);
lean_ctor_set(v___x_544_, 1, v_k_519_);
lean_ctor_set(v___x_544_, 0, v___x_552_);
v___x_554_ = v___x_544_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_k_519_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_v_520_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_r_538_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_r_522_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 4, v___x_554_);
lean_ctor_set(v___x_532_, 3, v___y_550_);
lean_ctor_set(v___x_532_, 2, v_v_536_);
lean_ctor_set(v___x_532_, 1, v_k_535_);
lean_ctor_set(v___x_532_, 0, v___x_547_);
v___x_556_ = v___x_532_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_k_535_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_v_536_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v___y_550_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
v___jp_559_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_nat_add(v___x_546_, v___y_560_);
lean_dec(v___y_560_);
lean_dec(v___x_546_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_l_537_);
lean_ctor_set(v___x_512_, 3, v_impl_515_);
lean_ctor_set(v___x_512_, 0, v___x_561_);
v___x_563_ = v___x_512_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v_impl_515_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_l_537_);
v___x_563_ = v_reuseFailAlloc_567_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_nat_add(v___x_516_, v_size_539_);
if (lean_obj_tag(v_r_538_) == 0)
{
lean_object* v_size_565_; 
v_size_565_ = lean_ctor_get(v_r_538_, 0);
lean_inc(v_size_565_);
v___y_549_ = v___x_564_;
v___y_550_ = v___x_563_;
v___y_551_ = v_size_565_;
goto v___jp_548_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___y_549_ = v___x_564_;
v___y_550_ = v___x_563_;
v___y_551_ = v___x_566_;
goto v___jp_548_;
}
}
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
lean_del_object(v___x_512_);
v___x_576_ = lean_nat_add(v___x_516_, v_size_517_);
lean_dec(v_size_517_);
v___x_577_ = lean_nat_add(v___x_576_, v_size_518_);
lean_dec(v_size_518_);
v___x_578_ = lean_nat_add(v___x_576_, v_size_534_);
lean_dec(v___x_576_);
lean_inc_ref(v_impl_515_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 4, v_l_521_);
lean_ctor_set(v___x_532_, 3, v_impl_515_);
lean_ctor_set(v___x_532_, 2, v_v_508_);
lean_ctor_set(v___x_532_, 1, v_k_507_);
lean_ctor_set(v___x_532_, 0, v___x_578_);
v___x_580_ = v___x_532_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_impl_515_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_l_521_);
v___x_580_ = v_reuseFailAlloc_593_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v_impl_515_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; lean_object* v_unused_589_; lean_object* v_unused_590_; lean_object* v_unused_591_; lean_object* v_unused_592_; 
v_unused_588_ = lean_ctor_get(v_impl_515_, 4);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_impl_515_, 3);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_impl_515_, 2);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_impl_515_, 1);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_impl_515_, 0);
lean_dec(v_unused_592_);
v___x_582_ = v_impl_515_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_dec(v_impl_515_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 4, v_r_522_);
lean_ctor_set(v___x_582_, 3, v___x_580_);
lean_ctor_set(v___x_582_, 2, v_v_520_);
lean_ctor_set(v___x_582_, 1, v_k_519_);
lean_ctor_set(v___x_582_, 0, v___x_577_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_k_519_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_v_520_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v_r_522_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v_size_600_ = lean_ctor_get(v_impl_515_, 0);
lean_inc(v_size_600_);
v___x_601_ = lean_nat_add(v___x_516_, v_size_600_);
lean_dec(v_size_600_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 3, v_impl_515_);
lean_ctor_set(v___x_512_, 0, v___x_601_);
v___x_603_ = v___x_512_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_impl_515_);
lean_ctor_set(v_reuseFailAlloc_604_, 4, v_r_510_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
if (lean_obj_tag(v_r_510_) == 0)
{
lean_object* v_l_605_; 
v_l_605_ = lean_ctor_get(v_r_510_, 3);
lean_inc(v_l_605_);
if (lean_obj_tag(v_l_605_) == 0)
{
lean_object* v_r_606_; 
v_r_606_ = lean_ctor_get(v_r_510_, 4);
lean_inc(v_r_606_);
if (lean_obj_tag(v_r_606_) == 0)
{
lean_object* v_size_607_; lean_object* v_k_608_; lean_object* v_v_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_622_; 
v_size_607_ = lean_ctor_get(v_r_510_, 0);
v_k_608_ = lean_ctor_get(v_r_510_, 1);
v_v_609_ = lean_ctor_get(v_r_510_, 2);
v_isSharedCheck_622_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; lean_object* v_unused_624_; 
v_unused_623_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_624_);
v___x_611_ = v_r_510_;
v_isShared_612_ = v_isSharedCheck_622_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_v_609_);
lean_inc(v_k_608_);
lean_inc(v_size_607_);
lean_dec(v_r_510_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_622_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_size_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v_size_613_ = lean_ctor_get(v_l_605_, 0);
v___x_614_ = lean_nat_add(v___x_516_, v_size_607_);
lean_dec(v_size_607_);
v___x_615_ = lean_nat_add(v___x_516_, v_size_613_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 4, v_l_605_);
lean_ctor_set(v___x_611_, 3, v_impl_515_);
lean_ctor_set(v___x_611_, 2, v_v_508_);
lean_ctor_set(v___x_611_, 1, v_k_507_);
lean_ctor_set(v___x_611_, 0, v___x_615_);
v___x_617_ = v___x_611_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_impl_515_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_l_605_);
v___x_617_ = v_reuseFailAlloc_621_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_r_606_);
lean_ctor_set(v___x_512_, 3, v___x_617_);
lean_ctor_set(v___x_512_, 2, v_v_609_);
lean_ctor_set(v___x_512_, 1, v_k_608_);
lean_ctor_set(v___x_512_, 0, v___x_614_);
v___x_619_ = v___x_512_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_k_608_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_v_609_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_r_606_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_k_625_; lean_object* v_v_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_649_; 
v_k_625_ = lean_ctor_get(v_r_510_, 1);
v_v_626_ = lean_ctor_get(v_r_510_, 2);
v_isSharedCheck_649_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; 
v_unused_650_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_r_510_, 0);
lean_dec(v_unused_652_);
v___x_628_ = v_r_510_;
v_isShared_629_ = v_isSharedCheck_649_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_v_626_);
lean_inc(v_k_625_);
lean_dec(v_r_510_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_649_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v_k_630_; lean_object* v_v_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_645_; 
v_k_630_ = lean_ctor_get(v_l_605_, 1);
v_v_631_ = lean_ctor_get(v_l_605_, 2);
v_isSharedCheck_645_ = !lean_is_exclusive(v_l_605_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; lean_object* v_unused_647_; lean_object* v_unused_648_; 
v_unused_646_ = lean_ctor_get(v_l_605_, 4);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_l_605_, 3);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_l_605_, 0);
lean_dec(v_unused_648_);
v___x_633_ = v_l_605_;
v_isShared_634_ = v_isSharedCheck_645_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_v_631_);
lean_inc(v_k_630_);
lean_dec(v_l_605_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_645_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_unsigned_to_nat(3u);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_r_606_);
lean_ctor_set(v___x_633_, 3, v_r_606_);
lean_ctor_set(v___x_633_, 2, v_v_508_);
lean_ctor_set(v___x_633_, 1, v_k_507_);
lean_ctor_set(v___x_633_, 0, v___x_516_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_r_606_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v_r_606_);
v___x_637_ = v_reuseFailAlloc_644_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 3, v_r_606_);
lean_ctor_set(v___x_628_, 0, v___x_516_);
v___x_639_ = v___x_628_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_k_625_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_v_626_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_r_606_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v_r_606_);
v___x_639_ = v_reuseFailAlloc_643_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_641_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___x_639_);
lean_ctor_set(v___x_512_, 3, v___x_637_);
lean_ctor_set(v___x_512_, 2, v_v_631_);
lean_ctor_set(v___x_512_, 1, v_k_630_);
lean_ctor_set(v___x_512_, 0, v___x_635_);
v___x_641_ = v___x_512_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_k_630_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_v_631_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_653_; 
v_r_653_ = lean_ctor_get(v_r_510_, 4);
lean_inc(v_r_653_);
if (lean_obj_tag(v_r_653_) == 0)
{
lean_object* v_k_654_; lean_object* v_v_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_666_; 
v_k_654_ = lean_ctor_get(v_r_510_, 1);
v_v_655_ = lean_ctor_get(v_r_510_, 2);
v_isSharedCheck_666_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; lean_object* v_unused_668_; lean_object* v_unused_669_; 
v_unused_667_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v_r_510_, 0);
lean_dec(v_unused_669_);
v___x_657_ = v_r_510_;
v_isShared_658_ = v_isSharedCheck_666_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_v_655_);
lean_inc(v_k_654_);
lean_dec(v_r_510_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_666_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_unsigned_to_nat(3u);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 4, v_l_605_);
lean_ctor_set(v___x_657_, 2, v_v_508_);
lean_ctor_set(v___x_657_, 1, v_k_507_);
lean_ctor_set(v___x_657_, 0, v___x_516_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v_l_605_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v_l_605_);
v___x_661_ = v_reuseFailAlloc_665_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_r_653_);
lean_ctor_set(v___x_512_, 3, v___x_661_);
lean_ctor_set(v___x_512_, 2, v_v_655_);
lean_ctor_set(v___x_512_, 1, v_k_654_);
lean_ctor_set(v___x_512_, 0, v___x_659_);
v___x_663_ = v___x_512_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_664_, 4, v_r_653_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v_size_670_; lean_object* v_k_671_; lean_object* v_v_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_683_; 
v_size_670_ = lean_ctor_get(v_r_510_, 0);
v_k_671_ = lean_ctor_get(v_r_510_, 1);
v_v_672_ = lean_ctor_get(v_r_510_, 2);
v_isSharedCheck_683_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; lean_object* v_unused_685_; 
v_unused_684_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_685_);
v___x_674_ = v_r_510_;
v_isShared_675_ = v_isSharedCheck_683_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_v_672_);
lean_inc(v_k_671_);
lean_inc(v_size_670_);
lean_dec(v_r_510_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_683_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 3, v_r_653_);
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_size_670_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_k_671_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_v_672_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_r_653_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_r_653_);
v___x_677_ = v_reuseFailAlloc_682_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_unsigned_to_nat(2u);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___x_677_);
lean_ctor_set(v___x_512_, 3, v_r_653_);
lean_ctor_set(v___x_512_, 0, v___x_678_);
v___x_680_ = v___x_512_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_r_653_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v___x_677_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
}
else
{
lean_object* v___x_687_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 3, v_r_510_);
lean_ctor_set(v___x_512_, 0, v___x_516_);
v___x_687_ = v___x_512_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_r_510_);
lean_ctor_set(v_reuseFailAlloc_688_, 4, v_r_510_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
case 1:
{
lean_del_object(v___x_512_);
lean_dec(v_v_508_);
lean_dec(v_k_507_);
if (lean_obj_tag(v_l_509_) == 0)
{
if (lean_obj_tag(v_r_510_) == 0)
{
lean_object* v_size_689_; lean_object* v_k_690_; lean_object* v_v_691_; lean_object* v_l_692_; lean_object* v_r_693_; lean_object* v_size_694_; lean_object* v_k_695_; lean_object* v_v_696_; lean_object* v_l_697_; lean_object* v_r_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_size_689_ = lean_ctor_get(v_l_509_, 0);
v_k_690_ = lean_ctor_get(v_l_509_, 1);
v_v_691_ = lean_ctor_get(v_l_509_, 2);
v_l_692_ = lean_ctor_get(v_l_509_, 3);
v_r_693_ = lean_ctor_get(v_l_509_, 4);
lean_inc(v_r_693_);
v_size_694_ = lean_ctor_get(v_r_510_, 0);
v_k_695_ = lean_ctor_get(v_r_510_, 1);
v_v_696_ = lean_ctor_get(v_r_510_, 2);
v_l_697_ = lean_ctor_get(v_r_510_, 3);
lean_inc(v_l_697_);
v_r_698_ = lean_ctor_get(v_r_510_, 4);
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_nat_dec_lt(v_size_689_, v_size_694_);
if (v___x_700_ == 0)
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_836_; 
lean_inc(v_l_692_);
lean_inc(v_v_691_);
lean_inc(v_k_690_);
v_isSharedCheck_836_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; 
v_unused_837_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_l_509_, 2);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_l_509_, 1);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_841_);
v___x_702_ = v_l_509_;
v_isShared_703_ = v_isSharedCheck_836_;
goto v_resetjp_701_;
}
else
{
lean_dec(v_l_509_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_836_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v_tree_705_; 
v___x_704_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_690_, v_v_691_, v_l_692_, v_r_693_);
v_tree_705_ = lean_ctor_get(v___x_704_, 2);
lean_inc(v_tree_705_);
if (lean_obj_tag(v_tree_705_) == 0)
{
lean_object* v_k_706_; lean_object* v_v_707_; lean_object* v_size_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_k_706_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_k_706_);
v_v_707_ = lean_ctor_get(v___x_704_, 1);
lean_inc(v_v_707_);
lean_dec_ref(v___x_704_);
v_size_708_ = lean_ctor_get(v_tree_705_, 0);
v___x_709_ = lean_unsigned_to_nat(3u);
v___x_710_ = lean_nat_mul(v___x_709_, v_size_708_);
v___x_711_ = lean_nat_dec_lt(v___x_710_, v_size_694_);
lean_dec(v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
lean_dec(v_l_697_);
v___x_712_ = lean_nat_add(v___x_699_, v_size_708_);
v___x_713_ = lean_nat_add(v___x_712_, v_size_694_);
lean_dec(v___x_712_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v_r_510_);
lean_ctor_set(v___x_702_, 3, v_tree_705_);
lean_ctor_set(v___x_702_, 2, v_v_707_);
lean_ctor_set(v___x_702_, 1, v_k_706_);
lean_ctor_set(v___x_702_, 0, v___x_713_);
v___x_715_ = v___x_702_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_k_706_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_v_707_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_tree_705_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v_r_510_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
else
{
lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_771_; 
lean_inc(v_r_698_);
lean_inc(v_v_696_);
lean_inc(v_k_695_);
lean_inc(v_size_694_);
v_isSharedCheck_771_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; lean_object* v_unused_776_; 
v_unused_772_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_772_);
v_unused_773_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_r_510_, 2);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_r_510_, 1);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_r_510_, 0);
lean_dec(v_unused_776_);
v___x_718_ = v_r_510_;
v_isShared_719_ = v_isSharedCheck_771_;
goto v_resetjp_717_;
}
else
{
lean_dec(v_r_510_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_771_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_size_720_; lean_object* v_k_721_; lean_object* v_v_722_; lean_object* v_l_723_; lean_object* v_r_724_; lean_object* v_size_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_size_720_ = lean_ctor_get(v_l_697_, 0);
v_k_721_ = lean_ctor_get(v_l_697_, 1);
v_v_722_ = lean_ctor_get(v_l_697_, 2);
v_l_723_ = lean_ctor_get(v_l_697_, 3);
v_r_724_ = lean_ctor_get(v_l_697_, 4);
v_size_725_ = lean_ctor_get(v_r_698_, 0);
v___x_726_ = lean_unsigned_to_nat(2u);
v___x_727_ = lean_nat_mul(v___x_726_, v_size_725_);
v___x_728_ = lean_nat_dec_lt(v_size_720_, v___x_727_);
lean_dec(v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_756_; 
lean_inc(v_r_724_);
lean_inc(v_l_723_);
lean_inc(v_v_722_);
lean_inc(v_k_721_);
v_isSharedCheck_756_ = !lean_is_exclusive(v_l_697_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; lean_object* v_unused_758_; lean_object* v_unused_759_; lean_object* v_unused_760_; lean_object* v_unused_761_; 
v_unused_757_ = lean_ctor_get(v_l_697_, 4);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_l_697_, 3);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_l_697_, 2);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_l_697_, 1);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_l_697_, 0);
lean_dec(v_unused_761_);
v___x_730_ = v_l_697_;
v_isShared_731_ = v_isSharedCheck_756_;
goto v_resetjp_729_;
}
else
{
lean_dec(v_l_697_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_756_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_746_; 
v___x_732_ = lean_nat_add(v___x_699_, v_size_708_);
v___x_733_ = lean_nat_add(v___x_732_, v_size_694_);
lean_dec(v_size_694_);
if (lean_obj_tag(v_l_723_) == 0)
{
lean_object* v_size_754_; 
v_size_754_ = lean_ctor_get(v_l_723_, 0);
lean_inc(v_size_754_);
v___y_746_ = v_size_754_;
goto v___jp_745_;
}
else
{
lean_object* v___x_755_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___y_746_ = v___x_755_;
goto v___jp_745_;
}
v___jp_734_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_738_ = lean_nat_add(v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec(v___y_736_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 4, v_r_698_);
lean_ctor_set(v___x_730_, 3, v_r_724_);
lean_ctor_set(v___x_730_, 2, v_v_696_);
lean_ctor_set(v___x_730_, 1, v_k_695_);
lean_ctor_set(v___x_730_, 0, v___x_738_);
v___x_740_ = v___x_730_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v_r_724_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v_r_698_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_742_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 4, v___x_740_);
lean_ctor_set(v___x_718_, 3, v___y_735_);
lean_ctor_set(v___x_718_, 2, v_v_722_);
lean_ctor_set(v___x_718_, 1, v_k_721_);
lean_ctor_set(v___x_718_, 0, v___x_733_);
v___x_742_ = v___x_718_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_k_721_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_v_722_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v___y_735_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
v___jp_745_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = lean_nat_add(v___x_732_, v___y_746_);
lean_dec(v___y_746_);
lean_dec(v___x_732_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v_l_723_);
lean_ctor_set(v___x_702_, 3, v_tree_705_);
lean_ctor_set(v___x_702_, 2, v_v_707_);
lean_ctor_set(v___x_702_, 1, v_k_706_);
lean_ctor_set(v___x_702_, 0, v___x_747_);
v___x_749_ = v___x_702_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_k_706_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_v_707_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_tree_705_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v_l_723_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; 
v___x_750_ = lean_nat_add(v___x_699_, v_size_725_);
if (lean_obj_tag(v_r_724_) == 0)
{
lean_object* v_size_751_; 
v_size_751_ = lean_ctor_get(v_r_724_, 0);
lean_inc(v_size_751_);
v___y_735_ = v___x_749_;
v___y_736_ = v___x_750_;
v___y_737_ = v_size_751_;
goto v___jp_734_;
}
else
{
lean_object* v___x_752_; 
v___x_752_ = lean_unsigned_to_nat(0u);
v___y_735_ = v___x_749_;
v___y_736_ = v___x_750_;
v___y_737_ = v___x_752_;
goto v___jp_734_;
}
}
}
}
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_762_ = lean_nat_add(v___x_699_, v_size_708_);
v___x_763_ = lean_nat_add(v___x_762_, v_size_694_);
lean_dec(v_size_694_);
v___x_764_ = lean_nat_add(v___x_762_, v_size_720_);
lean_dec(v___x_762_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 4, v_l_697_);
lean_ctor_set(v___x_718_, 3, v_tree_705_);
lean_ctor_set(v___x_718_, 2, v_v_707_);
lean_ctor_set(v___x_718_, 1, v_k_706_);
lean_ctor_set(v___x_718_, 0, v___x_764_);
v___x_766_ = v___x_718_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_706_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_707_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_tree_705_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_l_697_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v_r_698_);
lean_ctor_set(v___x_702_, 3, v___x_766_);
lean_ctor_set(v___x_702_, 2, v_v_696_);
lean_ctor_set(v___x_702_, 1, v_k_695_);
lean_ctor_set(v___x_702_, 0, v___x_763_);
v___x_768_ = v___x_702_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v_r_698_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
else
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_830_; 
lean_inc(v_r_698_);
lean_inc(v_v_696_);
lean_inc(v_k_695_);
lean_inc(v_size_694_);
v_isSharedCheck_830_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; 
v_unused_831_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_831_);
v_unused_832_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_r_510_, 2);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_r_510_, 1);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_r_510_, 0);
lean_dec(v_unused_835_);
v___x_778_ = v_r_510_;
v_isShared_779_ = v_isSharedCheck_830_;
goto v_resetjp_777_;
}
else
{
lean_dec(v_r_510_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_830_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
if (lean_obj_tag(v_l_697_) == 0)
{
if (lean_obj_tag(v_r_698_) == 0)
{
lean_object* v_k_780_; lean_object* v_v_781_; lean_object* v_size_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v_k_780_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_k_780_);
v_v_781_ = lean_ctor_get(v___x_704_, 1);
lean_inc(v_v_781_);
lean_dec_ref(v___x_704_);
v_size_782_ = lean_ctor_get(v_l_697_, 0);
v___x_783_ = lean_nat_add(v___x_699_, v_size_694_);
lean_dec(v_size_694_);
v___x_784_ = lean_nat_add(v___x_699_, v_size_782_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 4, v_l_697_);
lean_ctor_set(v___x_778_, 3, v_tree_705_);
lean_ctor_set(v___x_778_, 2, v_v_781_);
lean_ctor_set(v___x_778_, 1, v_k_780_);
lean_ctor_set(v___x_778_, 0, v___x_784_);
v___x_786_ = v___x_778_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_k_780_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_v_781_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v_tree_705_);
lean_ctor_set(v_reuseFailAlloc_790_, 4, v_l_697_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v_r_698_);
lean_ctor_set(v___x_702_, 3, v___x_786_);
lean_ctor_set(v___x_702_, 2, v_v_696_);
lean_ctor_set(v___x_702_, 1, v_k_695_);
lean_ctor_set(v___x_702_, 0, v___x_783_);
v___x_788_ = v___x_702_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_789_, 4, v_r_698_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
lean_object* v_k_791_; lean_object* v_v_792_; lean_object* v_k_793_; lean_object* v_v_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_808_; 
lean_dec(v_size_694_);
v_k_791_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_k_791_);
v_v_792_ = lean_ctor_get(v___x_704_, 1);
lean_inc(v_v_792_);
lean_dec_ref(v___x_704_);
v_k_793_ = lean_ctor_get(v_l_697_, 1);
v_v_794_ = lean_ctor_get(v_l_697_, 2);
v_isSharedCheck_808_ = !lean_is_exclusive(v_l_697_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; lean_object* v_unused_810_; lean_object* v_unused_811_; 
v_unused_809_ = lean_ctor_get(v_l_697_, 4);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_l_697_, 3);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_l_697_, 0);
lean_dec(v_unused_811_);
v___x_796_ = v_l_697_;
v_isShared_797_ = v_isSharedCheck_808_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_v_794_);
lean_inc(v_k_793_);
lean_dec(v_l_697_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_808_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_unsigned_to_nat(3u);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 4, v_r_698_);
lean_ctor_set(v___x_796_, 3, v_r_698_);
lean_ctor_set(v___x_796_, 2, v_v_792_);
lean_ctor_set(v___x_796_, 1, v_k_791_);
lean_ctor_set(v___x_796_, 0, v___x_699_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_k_791_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_v_792_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v_r_698_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v_r_698_);
v___x_800_ = v_reuseFailAlloc_807_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 3, v_r_698_);
lean_ctor_set(v___x_778_, 0, v___x_699_);
v___x_802_ = v___x_778_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_r_698_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_r_698_);
v___x_802_ = v_reuseFailAlloc_806_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_804_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v___x_802_);
lean_ctor_set(v___x_702_, 3, v___x_800_);
lean_ctor_set(v___x_702_, 2, v_v_794_);
lean_ctor_set(v___x_702_, 1, v_k_793_);
lean_ctor_set(v___x_702_, 0, v___x_798_);
v___x_804_ = v___x_702_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_k_793_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_v_794_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_698_) == 0)
{
lean_object* v_k_812_; lean_object* v_v_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec(v_size_694_);
v_k_812_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_k_812_);
v_v_813_ = lean_ctor_get(v___x_704_, 1);
lean_inc(v_v_813_);
lean_dec_ref(v___x_704_);
v___x_814_ = lean_unsigned_to_nat(3u);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 4, v_l_697_);
lean_ctor_set(v___x_778_, 2, v_v_813_);
lean_ctor_set(v___x_778_, 1, v_k_812_);
lean_ctor_set(v___x_778_, 0, v___x_699_);
v___x_816_ = v___x_778_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_k_812_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_v_813_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v_l_697_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_l_697_);
v___x_816_ = v_reuseFailAlloc_820_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v_r_698_);
lean_ctor_set(v___x_702_, 3, v___x_816_);
lean_ctor_set(v___x_702_, 2, v_v_696_);
lean_ctor_set(v___x_702_, 1, v_k_695_);
lean_ctor_set(v___x_702_, 0, v___x_814_);
v___x_818_ = v___x_702_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_r_698_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v_k_821_; lean_object* v_v_822_; lean_object* v___x_824_; 
v_k_821_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_k_821_);
v_v_822_ = lean_ctor_get(v___x_704_, 1);
lean_inc(v_v_822_);
lean_dec_ref(v___x_704_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 3, v_r_698_);
v___x_824_ = v___x_778_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_size_694_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_k_695_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_v_696_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v_r_698_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v_r_698_);
v___x_824_ = v_reuseFailAlloc_829_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_unsigned_to_nat(2u);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v___x_824_);
lean_ctor_set(v___x_702_, 3, v_r_698_);
lean_ctor_set(v___x_702_, 2, v_v_822_);
lean_ctor_set(v___x_702_, 1, v_k_821_);
lean_ctor_set(v___x_702_, 0, v___x_825_);
v___x_827_ = v___x_702_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_821_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_822_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_r_698_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v___x_824_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
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
lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_994_; 
lean_inc(v_r_698_);
lean_inc(v_v_696_);
lean_inc(v_k_695_);
v_isSharedCheck_994_ = !lean_is_exclusive(v_r_510_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; 
v_unused_995_ = lean_ctor_get(v_r_510_, 4);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_r_510_, 3);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_r_510_, 2);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_r_510_, 1);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_r_510_, 0);
lean_dec(v_unused_999_);
v___x_843_ = v_r_510_;
v_isShared_844_ = v_isSharedCheck_994_;
goto v_resetjp_842_;
}
else
{
lean_dec(v_r_510_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_994_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v_tree_846_; 
v___x_845_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_695_, v_v_696_, v_l_697_, v_r_698_);
v_tree_846_ = lean_ctor_get(v___x_845_, 2);
lean_inc(v_tree_846_);
if (lean_obj_tag(v_tree_846_) == 0)
{
lean_object* v_k_847_; lean_object* v_v_848_; lean_object* v_size_849_; lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_k_847_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_k_847_);
v_v_848_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_v_848_);
lean_dec_ref(v___x_845_);
v_size_849_ = lean_ctor_get(v_tree_846_, 0);
v___x_850_ = lean_unsigned_to_nat(3u);
v___x_851_ = lean_nat_mul(v___x_850_, v_size_849_);
v___x_852_ = lean_nat_dec_lt(v___x_851_, v_size_689_);
lean_dec(v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec(v_r_693_);
v___x_853_ = lean_nat_add(v___x_699_, v_size_689_);
v___x_854_ = lean_nat_add(v___x_853_, v_size_849_);
lean_dec(v___x_853_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_tree_846_);
lean_ctor_set(v___x_843_, 3, v_l_509_);
lean_ctor_set(v___x_843_, 2, v_v_848_);
lean_ctor_set(v___x_843_, 1, v_k_847_);
lean_ctor_set(v___x_843_, 0, v___x_854_);
v___x_856_ = v___x_843_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_k_847_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_v_848_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_857_, 4, v_tree_846_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
else
{
lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_923_; 
lean_inc(v_l_692_);
lean_inc(v_v_691_);
lean_inc(v_k_690_);
lean_inc(v_size_689_);
v_isSharedCheck_923_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; lean_object* v_unused_925_; lean_object* v_unused_926_; lean_object* v_unused_927_; lean_object* v_unused_928_; 
v_unused_924_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_924_);
v_unused_925_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_l_509_, 2);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v_l_509_, 1);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_928_);
v___x_859_ = v_l_509_;
v_isShared_860_ = v_isSharedCheck_923_;
goto v_resetjp_858_;
}
else
{
lean_dec(v_l_509_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_923_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v_size_861_; lean_object* v_size_862_; lean_object* v_k_863_; lean_object* v_v_864_; lean_object* v_l_865_; lean_object* v_r_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_size_861_ = lean_ctor_get(v_l_692_, 0);
v_size_862_ = lean_ctor_get(v_r_693_, 0);
v_k_863_ = lean_ctor_get(v_r_693_, 1);
v_v_864_ = lean_ctor_get(v_r_693_, 2);
v_l_865_ = lean_ctor_get(v_r_693_, 3);
v_r_866_ = lean_ctor_get(v_r_693_, 4);
v___x_867_ = lean_unsigned_to_nat(2u);
v___x_868_ = lean_nat_mul(v___x_867_, v_size_861_);
v___x_869_ = lean_nat_dec_lt(v_size_862_, v___x_868_);
lean_dec(v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_907_; 
lean_inc(v_r_866_);
lean_inc(v_l_865_);
lean_inc(v_v_864_);
lean_inc(v_k_863_);
lean_del_object(v___x_859_);
v_isSharedCheck_907_ = !lean_is_exclusive(v_r_693_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; lean_object* v_unused_909_; lean_object* v_unused_910_; lean_object* v_unused_911_; lean_object* v_unused_912_; 
v_unused_908_ = lean_ctor_get(v_r_693_, 4);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_r_693_, 3);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_r_693_, 2);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_r_693_, 1);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_r_693_, 0);
lean_dec(v_unused_912_);
v___x_871_ = v_r_693_;
v_isShared_872_ = v_isSharedCheck_907_;
goto v_resetjp_870_;
}
else
{
lean_dec(v_r_693_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_907_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___x_895_; lean_object* v___y_897_; 
v___x_873_ = lean_nat_add(v___x_699_, v_size_689_);
lean_dec(v_size_689_);
v___x_874_ = lean_nat_add(v___x_873_, v_size_849_);
lean_dec(v___x_873_);
v___x_895_ = lean_nat_add(v___x_699_, v_size_861_);
if (lean_obj_tag(v_l_865_) == 0)
{
lean_object* v_size_905_; 
v_size_905_ = lean_ctor_get(v_l_865_, 0);
lean_inc(v_size_905_);
v___y_897_ = v_size_905_;
goto v___jp_896_;
}
else
{
lean_object* v___x_906_; 
v___x_906_ = lean_unsigned_to_nat(0u);
v___y_897_ = v___x_906_;
goto v___jp_896_;
}
v___jp_875_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_nat_add(v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec(v___y_877_);
lean_inc_ref(v_tree_846_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 4, v_tree_846_);
lean_ctor_set(v___x_871_, 3, v_r_866_);
lean_ctor_set(v___x_871_, 2, v_v_848_);
lean_ctor_set(v___x_871_, 1, v_k_847_);
lean_ctor_set(v___x_871_, 0, v___x_879_);
v___x_881_ = v___x_871_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_k_847_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_v_848_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_r_866_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_tree_846_);
v___x_881_ = v_reuseFailAlloc_894_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_isSharedCheck_888_ = !lean_is_exclusive(v_tree_846_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; lean_object* v_unused_890_; lean_object* v_unused_891_; lean_object* v_unused_892_; lean_object* v_unused_893_; 
v_unused_889_ = lean_ctor_get(v_tree_846_, 4);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_tree_846_, 3);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_tree_846_, 2);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_tree_846_, 1);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_tree_846_, 0);
lean_dec(v_unused_893_);
v___x_883_ = v_tree_846_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_dec(v_tree_846_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 4, v___x_881_);
lean_ctor_set(v___x_883_, 3, v___y_876_);
lean_ctor_set(v___x_883_, 2, v_v_864_);
lean_ctor_set(v___x_883_, 1, v_k_863_);
lean_ctor_set(v___x_883_, 0, v___x_874_);
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_k_863_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_v_864_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v___y_876_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v___x_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
v___jp_896_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_nat_add(v___x_895_, v___y_897_);
lean_dec(v___y_897_);
lean_dec(v___x_895_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_l_865_);
lean_ctor_set(v___x_843_, 3, v_l_692_);
lean_ctor_set(v___x_843_, 2, v_v_691_);
lean_ctor_set(v___x_843_, 1, v_k_690_);
lean_ctor_set(v___x_843_, 0, v___x_898_);
v___x_900_ = v___x_843_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_k_690_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_v_691_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v_l_865_);
v___x_900_ = v_reuseFailAlloc_904_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; 
v___x_901_ = lean_nat_add(v___x_699_, v_size_849_);
if (lean_obj_tag(v_r_866_) == 0)
{
lean_object* v_size_902_; 
v_size_902_ = lean_ctor_get(v_r_866_, 0);
lean_inc(v_size_902_);
v___y_876_ = v___x_900_;
v___y_877_ = v___x_901_;
v___y_878_ = v_size_902_;
goto v___jp_875_;
}
else
{
lean_object* v___x_903_; 
v___x_903_ = lean_unsigned_to_nat(0u);
v___y_876_ = v___x_900_;
v___y_877_ = v___x_901_;
v___y_878_ = v___x_903_;
goto v___jp_875_;
}
}
}
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_913_ = lean_nat_add(v___x_699_, v_size_689_);
lean_dec(v_size_689_);
v___x_914_ = lean_nat_add(v___x_913_, v_size_849_);
lean_dec(v___x_913_);
v___x_915_ = lean_nat_add(v___x_699_, v_size_849_);
v___x_916_ = lean_nat_add(v___x_915_, v_size_862_);
lean_dec(v___x_915_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_tree_846_);
lean_ctor_set(v___x_843_, 3, v_r_693_);
lean_ctor_set(v___x_843_, 2, v_v_848_);
lean_ctor_set(v___x_843_, 1, v_k_847_);
lean_ctor_set(v___x_843_, 0, v___x_916_);
v___x_918_ = v___x_843_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_k_847_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_v_848_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_r_693_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_tree_846_);
v___x_918_ = v_reuseFailAlloc_922_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_920_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 4, v___x_918_);
lean_ctor_set(v___x_859_, 0, v___x_914_);
v___x_920_ = v___x_859_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_690_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_v_691_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_692_) == 0)
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_952_; 
lean_inc_ref(v_l_692_);
lean_inc(v_v_691_);
lean_inc(v_k_690_);
lean_inc(v_size_689_);
v_isSharedCheck_952_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; lean_object* v_unused_957_; 
v_unused_953_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_l_509_, 2);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_l_509_, 1);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_957_);
v___x_930_ = v_l_509_;
v_isShared_931_ = v_isSharedCheck_952_;
goto v_resetjp_929_;
}
else
{
lean_dec(v_l_509_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_952_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
if (lean_obj_tag(v_r_693_) == 0)
{
lean_object* v_k_932_; lean_object* v_v_933_; lean_object* v_size_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v_k_932_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_k_932_);
v_v_933_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_v_933_);
lean_dec_ref(v___x_845_);
v_size_934_ = lean_ctor_get(v_r_693_, 0);
v___x_935_ = lean_nat_add(v___x_699_, v_size_689_);
lean_dec(v_size_689_);
v___x_936_ = lean_nat_add(v___x_699_, v_size_934_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_tree_846_);
lean_ctor_set(v___x_843_, 3, v_r_693_);
lean_ctor_set(v___x_843_, 2, v_v_933_);
lean_ctor_set(v___x_843_, 1, v_k_932_);
lean_ctor_set(v___x_843_, 0, v___x_936_);
v___x_938_ = v___x_843_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_r_693_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_tree_846_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 4, v___x_938_);
lean_ctor_set(v___x_930_, 0, v___x_935_);
v___x_940_ = v___x_930_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_690_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_691_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
else
{
lean_object* v_k_943_; lean_object* v_v_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
lean_dec(v_size_689_);
v_k_943_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_k_943_);
v_v_944_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_v_944_);
lean_dec_ref(v___x_845_);
v___x_945_ = lean_unsigned_to_nat(3u);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_r_693_);
lean_ctor_set(v___x_843_, 3, v_r_693_);
lean_ctor_set(v___x_843_, 2, v_v_944_);
lean_ctor_set(v___x_843_, 1, v_k_943_);
lean_ctor_set(v___x_843_, 0, v___x_699_);
v___x_947_ = v___x_843_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_k_943_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_v_944_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_r_693_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_r_693_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 4, v___x_947_);
lean_ctor_set(v___x_930_, 0, v___x_945_);
v___x_949_ = v___x_930_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_k_690_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_v_691_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_693_) == 0)
{
lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_982_; 
lean_inc(v_l_692_);
lean_inc(v_v_691_);
lean_inc(v_k_690_);
v_isSharedCheck_982_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; lean_object* v_unused_984_; lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; 
v_unused_983_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_l_509_, 2);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_l_509_, 1);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_987_);
v___x_959_ = v_l_509_;
v_isShared_960_ = v_isSharedCheck_982_;
goto v_resetjp_958_;
}
else
{
lean_dec(v_l_509_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_982_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_k_961_; lean_object* v_v_962_; lean_object* v_k_963_; lean_object* v_v_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_978_; 
v_k_961_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_k_961_);
v_v_962_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_v_962_);
lean_dec_ref(v___x_845_);
v_k_963_ = lean_ctor_get(v_r_693_, 1);
v_v_964_ = lean_ctor_get(v_r_693_, 2);
v_isSharedCheck_978_ = !lean_is_exclusive(v_r_693_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; 
v_unused_979_ = lean_ctor_get(v_r_693_, 4);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_r_693_, 3);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_r_693_, 0);
lean_dec(v_unused_981_);
v___x_966_ = v_r_693_;
v_isShared_967_ = v_isSharedCheck_978_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_v_964_);
lean_inc(v_k_963_);
lean_dec(v_r_693_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_978_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = lean_unsigned_to_nat(3u);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 4, v_l_692_);
lean_ctor_set(v___x_966_, 3, v_l_692_);
lean_ctor_set(v___x_966_, 2, v_v_691_);
lean_ctor_set(v___x_966_, 1, v_k_690_);
lean_ctor_set(v___x_966_, 0, v___x_699_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_k_690_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_v_691_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_l_692_);
v___x_970_ = v_reuseFailAlloc_977_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_972_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_l_692_);
lean_ctor_set(v___x_843_, 3, v_l_692_);
lean_ctor_set(v___x_843_, 2, v_v_962_);
lean_ctor_set(v___x_843_, 1, v_k_961_);
lean_ctor_set(v___x_843_, 0, v___x_699_);
v___x_972_ = v___x_843_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_k_961_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_v_962_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_l_692_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_l_692_);
v___x_972_ = v_reuseFailAlloc_976_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_974_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 4, v___x_972_);
lean_ctor_set(v___x_959_, 3, v___x_970_);
lean_ctor_set(v___x_959_, 2, v_v_964_);
lean_ctor_set(v___x_959_, 1, v_k_963_);
lean_ctor_set(v___x_959_, 0, v___x_968_);
v___x_974_ = v___x_959_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_k_963_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_v_964_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
else
{
lean_object* v_k_988_; lean_object* v_v_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v_k_988_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_k_988_);
v_v_989_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_v_989_);
lean_dec_ref(v___x_845_);
v___x_990_ = lean_unsigned_to_nat(2u);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 4, v_r_693_);
lean_ctor_set(v___x_843_, 3, v_l_509_);
lean_ctor_set(v___x_843_, 2, v_v_989_);
lean_ctor_set(v___x_843_, 1, v_k_988_);
lean_ctor_set(v___x_843_, 0, v___x_990_);
v___x_992_ = v___x_843_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_k_988_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_v_989_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_r_693_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
}
}
else
{
return v_l_509_;
}
}
else
{
return v_r_510_;
}
}
default: 
{
lean_object* v_impl_1000_; lean_object* v___x_1001_; 
v_impl_1000_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_505_, v_r_510_);
v___x_1001_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1000_) == 0)
{
if (lean_obj_tag(v_l_509_) == 0)
{
lean_object* v_size_1002_; lean_object* v_size_1003_; lean_object* v_k_1004_; lean_object* v_v_1005_; lean_object* v_l_1006_; lean_object* v_r_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_size_1002_ = lean_ctor_get(v_impl_1000_, 0);
lean_inc(v_size_1002_);
v_size_1003_ = lean_ctor_get(v_l_509_, 0);
v_k_1004_ = lean_ctor_get(v_l_509_, 1);
v_v_1005_ = lean_ctor_get(v_l_509_, 2);
v_l_1006_ = lean_ctor_get(v_l_509_, 3);
v_r_1007_ = lean_ctor_get(v_l_509_, 4);
lean_inc(v_r_1007_);
v___x_1008_ = lean_unsigned_to_nat(3u);
v___x_1009_ = lean_nat_mul(v___x_1008_, v_size_1002_);
v___x_1010_ = lean_nat_dec_lt(v___x_1009_, v_size_1003_);
lean_dec(v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
lean_dec(v_r_1007_);
v___x_1011_ = lean_nat_add(v___x_1001_, v_size_1003_);
v___x_1012_ = lean_nat_add(v___x_1011_, v_size_1002_);
lean_dec(v_size_1002_);
lean_dec(v___x_1011_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_impl_1000_);
lean_ctor_set(v___x_512_, 0, v___x_1012_);
v___x_1014_ = v___x_512_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_1015_, 4, v_impl_1000_);
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
lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1081_; 
lean_inc(v_l_1006_);
lean_inc(v_v_1005_);
lean_inc(v_k_1004_);
lean_inc(v_size_1003_);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; lean_object* v_unused_1083_; lean_object* v_unused_1084_; lean_object* v_unused_1085_; lean_object* v_unused_1086_; 
v_unused_1082_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_l_509_, 2);
lean_dec(v_unused_1084_);
v_unused_1085_ = lean_ctor_get(v_l_509_, 1);
lean_dec(v_unused_1085_);
v_unused_1086_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_1086_);
v___x_1017_ = v_l_509_;
v_isShared_1018_ = v_isSharedCheck_1081_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v_l_509_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1081_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_size_1019_; lean_object* v_size_1020_; lean_object* v_k_1021_; lean_object* v_v_1022_; lean_object* v_l_1023_; lean_object* v_r_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v_size_1019_ = lean_ctor_get(v_l_1006_, 0);
v_size_1020_ = lean_ctor_get(v_r_1007_, 0);
v_k_1021_ = lean_ctor_get(v_r_1007_, 1);
v_v_1022_ = lean_ctor_get(v_r_1007_, 2);
v_l_1023_ = lean_ctor_get(v_r_1007_, 3);
v_r_1024_ = lean_ctor_get(v_r_1007_, 4);
v___x_1025_ = lean_unsigned_to_nat(2u);
v___x_1026_ = lean_nat_mul(v___x_1025_, v_size_1019_);
v___x_1027_ = lean_nat_dec_lt(v_size_1020_, v___x_1026_);
lean_dec(v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1056_; 
lean_inc(v_r_1024_);
lean_inc(v_l_1023_);
lean_inc(v_v_1022_);
lean_inc(v_k_1021_);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_r_1007_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; lean_object* v_unused_1058_; lean_object* v_unused_1059_; lean_object* v_unused_1060_; lean_object* v_unused_1061_; 
v_unused_1057_ = lean_ctor_get(v_r_1007_, 4);
lean_dec(v_unused_1057_);
v_unused_1058_ = lean_ctor_get(v_r_1007_, 3);
lean_dec(v_unused_1058_);
v_unused_1059_ = lean_ctor_get(v_r_1007_, 2);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_r_1007_, 1);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_r_1007_, 0);
lean_dec(v_unused_1061_);
v___x_1029_ = v_r_1007_;
v_isShared_1030_ = v_isSharedCheck_1056_;
goto v_resetjp_1028_;
}
else
{
lean_dec(v_r_1007_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1056_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___x_1044_; lean_object* v___y_1046_; 
v___x_1031_ = lean_nat_add(v___x_1001_, v_size_1003_);
lean_dec(v_size_1003_);
v___x_1032_ = lean_nat_add(v___x_1031_, v_size_1002_);
lean_dec(v___x_1031_);
v___x_1044_ = lean_nat_add(v___x_1001_, v_size_1019_);
if (lean_obj_tag(v_l_1023_) == 0)
{
lean_object* v_size_1054_; 
v_size_1054_ = lean_ctor_get(v_l_1023_, 0);
lean_inc(v_size_1054_);
v___y_1046_ = v_size_1054_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_unsigned_to_nat(0u);
v___y_1046_ = v___x_1055_;
goto v___jp_1045_;
}
v___jp_1033_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = lean_nat_add(v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec(v___y_1035_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 4, v_impl_1000_);
lean_ctor_set(v___x_1029_, 3, v_r_1024_);
lean_ctor_set(v___x_1029_, 2, v_v_508_);
lean_ctor_set(v___x_1029_, 1, v_k_507_);
lean_ctor_set(v___x_1029_, 0, v___x_1037_);
v___x_1039_ = v___x_1029_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_r_1024_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_impl_1000_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 4, v___x_1039_);
lean_ctor_set(v___x_1017_, 3, v___y_1034_);
lean_ctor_set(v___x_1017_, 2, v_v_1022_);
lean_ctor_set(v___x_1017_, 1, v_k_1021_);
lean_ctor_set(v___x_1017_, 0, v___x_1032_);
v___x_1041_ = v___x_1017_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_k_1021_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_v_1022_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v___y_1034_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
v___jp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = lean_nat_add(v___x_1044_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec(v___x_1044_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_l_1023_);
lean_ctor_set(v___x_512_, 3, v_l_1006_);
lean_ctor_set(v___x_512_, 2, v_v_1005_);
lean_ctor_set(v___x_512_, 1, v_k_1004_);
lean_ctor_set(v___x_512_, 0, v___x_1047_);
v___x_1049_ = v___x_512_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v_l_1006_);
lean_ctor_set(v_reuseFailAlloc_1053_, 4, v_l_1023_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_nat_add(v___x_1001_, v_size_1002_);
lean_dec(v_size_1002_);
if (lean_obj_tag(v_r_1024_) == 0)
{
lean_object* v_size_1051_; 
v_size_1051_ = lean_ctor_get(v_r_1024_, 0);
lean_inc(v_size_1051_);
v___y_1034_ = v___x_1049_;
v___y_1035_ = v___x_1050_;
v___y_1036_ = v_size_1051_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_unsigned_to_nat(0u);
v___y_1034_ = v___x_1049_;
v___y_1035_ = v___x_1050_;
v___y_1036_ = v___x_1052_;
goto v___jp_1033_;
}
}
}
}
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_del_object(v___x_512_);
v___x_1062_ = lean_nat_add(v___x_1001_, v_size_1003_);
lean_dec(v_size_1003_);
v___x_1063_ = lean_nat_add(v___x_1062_, v_size_1002_);
lean_dec(v___x_1062_);
v___x_1064_ = lean_nat_add(v___x_1001_, v_size_1002_);
lean_dec(v_size_1002_);
v___x_1065_ = lean_nat_add(v___x_1064_, v_size_1020_);
lean_dec(v___x_1064_);
lean_inc_ref(v_impl_1000_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 4, v_impl_1000_);
lean_ctor_set(v___x_1017_, 3, v_r_1007_);
lean_ctor_set(v___x_1017_, 2, v_v_508_);
lean_ctor_set(v___x_1017_, 1, v_k_507_);
lean_ctor_set(v___x_1017_, 0, v___x_1065_);
v___x_1067_ = v___x_1017_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_r_1007_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v_impl_1000_);
v___x_1067_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_isSharedCheck_1074_ = !lean_is_exclusive(v_impl_1000_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; lean_object* v_unused_1076_; lean_object* v_unused_1077_; lean_object* v_unused_1078_; lean_object* v_unused_1079_; 
v_unused_1075_ = lean_ctor_get(v_impl_1000_, 4);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_impl_1000_, 3);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_impl_1000_, 2);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_impl_1000_, 1);
lean_dec(v_unused_1078_);
v_unused_1079_ = lean_ctor_get(v_impl_1000_, 0);
lean_dec(v_unused_1079_);
v___x_1069_ = v_impl_1000_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_dec(v_impl_1000_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 4, v___x_1067_);
lean_ctor_set(v___x_1069_, 3, v_l_1006_);
lean_ctor_set(v___x_1069_, 2, v_v_1005_);
lean_ctor_set(v___x_1069_, 1, v_k_1004_);
lean_ctor_set(v___x_1069_, 0, v___x_1063_);
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_l_1006_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v___x_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v_size_1087_ = lean_ctor_get(v_impl_1000_, 0);
lean_inc(v_size_1087_);
v___x_1088_ = lean_nat_add(v___x_1001_, v_size_1087_);
lean_dec(v_size_1087_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_impl_1000_);
lean_ctor_set(v___x_512_, 0, v___x_1088_);
v___x_1090_ = v___x_512_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_impl_1000_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
else
{
if (lean_obj_tag(v_l_509_) == 0)
{
lean_object* v_l_1092_; 
v_l_1092_ = lean_ctor_get(v_l_509_, 3);
if (lean_obj_tag(v_l_1092_) == 0)
{
lean_object* v_r_1093_; 
lean_inc_ref(v_l_1092_);
v_r_1093_ = lean_ctor_get(v_l_509_, 4);
lean_inc(v_r_1093_);
if (lean_obj_tag(v_r_1093_) == 0)
{
lean_object* v_size_1094_; lean_object* v_k_1095_; lean_object* v_v_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1109_; 
v_size_1094_ = lean_ctor_get(v_l_509_, 0);
v_k_1095_ = lean_ctor_get(v_l_509_, 1);
v_v_1096_ = lean_ctor_get(v_l_509_, 2);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; lean_object* v_unused_1111_; 
v_unused_1110_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_1111_);
v___x_1098_ = v_l_509_;
v_isShared_1099_ = v_isSharedCheck_1109_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_v_1096_);
lean_inc(v_k_1095_);
lean_inc(v_size_1094_);
lean_dec(v_l_509_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1109_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_size_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v_size_1100_ = lean_ctor_get(v_r_1093_, 0);
v___x_1101_ = lean_nat_add(v___x_1001_, v_size_1094_);
lean_dec(v_size_1094_);
v___x_1102_ = lean_nat_add(v___x_1001_, v_size_1100_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v_impl_1000_);
lean_ctor_set(v___x_1098_, 3, v_r_1093_);
lean_ctor_set(v___x_1098_, 2, v_v_508_);
lean_ctor_set(v___x_1098_, 1, v_k_507_);
lean_ctor_set(v___x_1098_, 0, v___x_1102_);
v___x_1104_ = v___x_1098_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_r_1093_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_impl_1000_);
v___x_1104_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1106_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___x_1104_);
lean_ctor_set(v___x_512_, 3, v_l_1092_);
lean_ctor_set(v___x_512_, 2, v_v_1096_);
lean_ctor_set(v___x_512_, 1, v_k_1095_);
lean_ctor_set(v___x_512_, 0, v___x_1101_);
v___x_1106_ = v___x_512_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_k_1095_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_v_1096_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v_l_1092_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v___x_1104_);
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
else
{
lean_object* v_k_1112_; lean_object* v_v_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1124_; 
v_k_1112_ = lean_ctor_get(v_l_509_, 1);
v_v_1113_ = lean_ctor_get(v_l_509_, 2);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; lean_object* v_unused_1126_; lean_object* v_unused_1127_; 
v_unused_1125_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_1125_);
v_unused_1126_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_1127_);
v___x_1115_ = v_l_509_;
v_isShared_1116_ = v_isSharedCheck_1124_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_v_1113_);
lean_inc(v_k_1112_);
lean_dec(v_l_509_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1124_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = lean_unsigned_to_nat(3u);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 3, v_r_1093_);
lean_ctor_set(v___x_1115_, 2, v_v_508_);
lean_ctor_set(v___x_1115_, 1, v_k_507_);
lean_ctor_set(v___x_1115_, 0, v___x_1001_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_r_1093_);
lean_ctor_set(v_reuseFailAlloc_1123_, 4, v_r_1093_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___x_1119_);
lean_ctor_set(v___x_512_, 3, v_l_1092_);
lean_ctor_set(v___x_512_, 2, v_v_1113_);
lean_ctor_set(v___x_512_, 1, v_k_1112_);
lean_ctor_set(v___x_512_, 0, v___x_1117_);
v___x_1121_ = v___x_512_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_k_1112_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_v_1113_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_l_1092_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
else
{
lean_object* v_r_1128_; 
v_r_1128_ = lean_ctor_get(v_l_509_, 4);
lean_inc(v_r_1128_);
if (lean_obj_tag(v_r_1128_) == 0)
{
lean_object* v_k_1129_; lean_object* v_v_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1153_; 
lean_inc(v_l_1092_);
v_k_1129_ = lean_ctor_get(v_l_509_, 1);
v_v_1130_ = lean_ctor_get(v_l_509_, 2);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; lean_object* v_unused_1155_; lean_object* v_unused_1156_; 
v_unused_1154_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_1154_);
v_unused_1155_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_1156_);
v___x_1132_ = v_l_509_;
v_isShared_1133_ = v_isSharedCheck_1153_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_v_1130_);
lean_inc(v_k_1129_);
lean_dec(v_l_509_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1153_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_k_1134_; lean_object* v_v_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1149_; 
v_k_1134_ = lean_ctor_get(v_r_1128_, 1);
v_v_1135_ = lean_ctor_get(v_r_1128_, 2);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_r_1128_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1150_ = lean_ctor_get(v_r_1128_, 4);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_r_1128_, 3);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_r_1128_, 0);
lean_dec(v_unused_1152_);
v___x_1137_ = v_r_1128_;
v_isShared_1138_ = v_isSharedCheck_1149_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_v_1135_);
lean_inc(v_k_1134_);
lean_dec(v_r_1128_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1149_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = lean_unsigned_to_nat(3u);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 4, v_l_1092_);
lean_ctor_set(v___x_1137_, 3, v_l_1092_);
lean_ctor_set(v___x_1137_, 2, v_v_1130_);
lean_ctor_set(v___x_1137_, 1, v_k_1129_);
lean_ctor_set(v___x_1137_, 0, v___x_1001_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_k_1129_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_v_1130_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_l_1092_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_l_1092_);
v___x_1141_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 4, v_l_1092_);
lean_ctor_set(v___x_1132_, 2, v_v_508_);
lean_ctor_set(v___x_1132_, 1, v_k_507_);
lean_ctor_set(v___x_1132_, 0, v___x_1001_);
v___x_1143_ = v___x_1132_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v_l_1092_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v_l_1092_);
v___x_1143_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___x_1143_);
lean_ctor_set(v___x_512_, 3, v___x_1141_);
lean_ctor_set(v___x_512_, 2, v_v_1135_);
lean_ctor_set(v___x_512_, 1, v_k_1134_);
lean_ctor_set(v___x_512_, 0, v___x_1139_);
v___x_1145_ = v___x_512_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_k_1134_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_v_1135_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = lean_unsigned_to_nat(2u);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_r_1128_);
lean_ctor_set(v___x_512_, 0, v___x_1157_);
v___x_1159_ = v___x_512_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v_r_1128_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v___x_1162_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v_l_509_);
lean_ctor_set(v___x_512_, 0, v___x_1001_);
v___x_1162_ = v___x_512_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_1163_, 4, v_l_509_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
}
else
{
return v_t_506_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg___boxed(lean_object* v_k_1166_, lean_object* v_t_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1166_, v_t_1167_);
lean_dec(v_k_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString(lean_object* v_declName_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1171_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1172_ = lean_st_ref_take(v___x_1171_);
v___x_1173_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_declName_1169_, v___x_1172_);
v___x_1174_ = lean_st_ref_set(v___x_1171_, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString___boxed(lean_object* v_declName_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_removeBuiltinDocString(v_declName_1176_);
lean_dec(v_declName_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(lean_object* v_00_u03b2_1179_, lean_object* v_k_1180_, lean_object* v_t_1181_, lean_object* v_h_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1180_, v_t_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___boxed(lean_object* v_00_u03b2_1184_, lean_object* v_k_1185_, lean_object* v_t_1186_, lean_object* v_h_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(v_00_u03b2_1184_, v_k_1185_, v_t_1186_, v_h_1187_);
lean_dec(v_k_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings(){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1191_ = lean_st_ref_get(v___x_1190_);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings___boxed(lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_getBuiltinVersoDocStrings();
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object* v_docString_1195_, lean_object* v_declName_1196_, lean_object* v_env_1197_){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = l_Lean_docStringExt;
v___x_1199_ = l_String_removeLeadingSpaces(v_docString_1195_);
v___x_1200_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1198_, v_env_1197_, v_declName_1196_, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_1201_, lean_object* v___f_1202_, lean_object* v_____r_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_apply_1(v_modifyEnv_1201_, v___f_1202_);
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__0));
v___x_1207_ = l_Lean_stringToMessageData(v___x_1206_);
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__2));
v___x_1210_ = l_Lean_stringToMessageData(v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2(lean_object* v_declName_1211_, lean_object* v_modifyEnv_1212_, lean_object* v___f_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_toBind_1216_, lean_object* v___f_1217_, lean_object* v_____do__lift_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1218_, v_declName_1211_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___x_1220_; 
lean_dec(v___f_1217_);
lean_dec(v_toBind_1216_);
lean_dec_ref(v_inst_1215_);
lean_dec_ref(v_inst_1214_);
lean_dec(v_declName_1211_);
v___x_1220_ = lean_apply_1(v_modifyEnv_1212_, v___f_1213_);
return v___x_1220_;
}
else
{
uint8_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec_ref(v___x_1219_);
lean_dec_ref(v___f_1213_);
lean_dec(v_modifyEnv_1212_);
v___x_1221_ = 0;
v___x_1222_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1223_ = l_Lean_MessageData_ofConstName(v_declName_1211_, v___x_1221_);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = l_Lean_throwError___redArg(v_inst_1214_, v_inst_1215_, v___x_1226_);
v___x_1228_ = lean_apply_4(v_toBind_1216_, lean_box(0), lean_box(0), v___x_1227_, v___f_1217_);
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1229_, lean_object* v_modifyEnv_1230_, lean_object* v___f_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_toBind_1234_, lean_object* v___f_1235_, lean_object* v_____do__lift_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_addDocStringCore___redArg___lam__2(v_declName_1229_, v_modifyEnv_1230_, v___f_1231_, v_inst_1232_, v_inst_1233_, v_toBind_1234_, v___f_1235_, v_____do__lift_1236_);
lean_dec_ref(v_____do__lift_1236_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg(lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_declName_1241_, lean_object* v_docString_1242_){
_start:
{
lean_object* v_toBind_1243_; lean_object* v_getEnv_1244_; lean_object* v_modifyEnv_1245_; lean_object* v___f_1246_; lean_object* v___f_1247_; lean_object* v___f_1248_; lean_object* v___x_1249_; 
v_toBind_1243_ = lean_ctor_get(v_inst_1238_, 1);
lean_inc(v_toBind_1243_);
v_getEnv_1244_ = lean_ctor_get(v_inst_1240_, 0);
lean_inc(v_getEnv_1244_);
v_modifyEnv_1245_ = lean_ctor_get(v_inst_1240_, 1);
lean_inc(v_modifyEnv_1245_);
lean_dec_ref(v_inst_1240_);
lean_inc(v_declName_1241_);
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1246_, 0, v_docString_1242_);
lean_closure_set(v___f_1246_, 1, v_declName_1241_);
lean_inc_ref(v___f_1246_);
lean_inc(v_modifyEnv_1245_);
v___f_1247_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1247_, 0, v_modifyEnv_1245_);
lean_closure_set(v___f_1247_, 1, v___f_1246_);
lean_inc(v_toBind_1243_);
v___f_1248_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1248_, 0, v_declName_1241_);
lean_closure_set(v___f_1248_, 1, v_modifyEnv_1245_);
lean_closure_set(v___f_1248_, 2, v___f_1246_);
lean_closure_set(v___f_1248_, 3, v_inst_1238_);
lean_closure_set(v___f_1248_, 4, v_inst_1239_);
lean_closure_set(v___f_1248_, 5, v_toBind_1243_);
lean_closure_set(v___f_1248_, 6, v___f_1247_);
v___x_1249_ = lean_apply_4(v_toBind_1243_, lean_box(0), lean_box(0), v_getEnv_1244_, v___f_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore(lean_object* v_m_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_declName_1255_, lean_object* v_docString_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_addDocStringCore___redArg(v_inst_1251_, v_inst_1252_, v_inst_1253_, v_declName_1255_, v_docString_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___boxed(lean_object* v_m_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_declName_1263_, lean_object* v_docString_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_addDocStringCore(v_m_1258_, v_inst_1259_, v_inst_1260_, v_inst_1261_, v_inst_1262_, v_declName_1263_, v_docString_1264_);
lean_dec(v_inst_1262_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__0(lean_object* v_declName_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__0___closed__0));
v___x_1270_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_1269_, v_declName_1267_, v_x_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__1(lean_object* v___f_1271_, lean_object* v_env_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1273_ = l_Lean_docStringExt;
v___x_1274_ = lean_box(2);
v___x_1275_ = lean_box(0);
v___x_1276_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_1273_, v_env_1272_, v___f_1271_, v___x_1274_, v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__3___closed__0));
v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3(lean_object* v_declName_1280_, lean_object* v_modifyEnv_1281_, lean_object* v___f_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_toBind_1285_, lean_object* v___f_1286_, lean_object* v_____do__lift_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1287_, v_declName_1280_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___x_1289_; 
lean_dec(v___f_1286_);
lean_dec(v_toBind_1285_);
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
lean_dec(v_declName_1280_);
v___x_1289_ = lean_apply_1(v_modifyEnv_1281_, v___f_1282_);
return v___x_1289_;
}
else
{
uint8_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec_ref(v___x_1288_);
lean_dec_ref(v___f_1282_);
lean_dec(v_modifyEnv_1281_);
v___x_1290_ = 0;
v___x_1291_ = lean_obj_once(&l_Lean_removeDocStringCore___redArg___lam__3___closed__1, &l_Lean_removeDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1);
v___x_1292_ = l_Lean_MessageData_ofConstName(v_declName_1280_, v___x_1290_);
v___x_1293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1293_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = l_Lean_throwError___redArg(v_inst_1283_, v_inst_1284_, v___x_1295_);
v___x_1297_ = lean_apply_4(v_toBind_1285_, lean_box(0), lean_box(0), v___x_1296_, v___f_1286_);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_1298_, lean_object* v_modifyEnv_1299_, lean_object* v___f_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_toBind_1303_, lean_object* v___f_1304_, lean_object* v_____do__lift_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_removeDocStringCore___redArg___lam__3(v_declName_1298_, v_modifyEnv_1299_, v___f_1300_, v_inst_1301_, v_inst_1302_, v_toBind_1303_, v___f_1304_, v_____do__lift_1305_);
lean_dec_ref(v_____do__lift_1305_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg(lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_declName_1310_){
_start:
{
lean_object* v_toBind_1311_; lean_object* v_getEnv_1312_; lean_object* v_modifyEnv_1313_; lean_object* v___f_1314_; lean_object* v___f_1315_; lean_object* v___f_1316_; lean_object* v___f_1317_; lean_object* v___x_1318_; 
v_toBind_1311_ = lean_ctor_get(v_inst_1307_, 1);
lean_inc(v_toBind_1311_);
v_getEnv_1312_ = lean_ctor_get(v_inst_1309_, 0);
lean_inc(v_getEnv_1312_);
v_modifyEnv_1313_ = lean_ctor_get(v_inst_1309_, 1);
lean_inc(v_modifyEnv_1313_);
lean_dec_ref(v_inst_1309_);
lean_inc(v_declName_1310_);
v___f_1314_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1314_, 0, v_declName_1310_);
v___f_1315_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1315_, 0, v___f_1314_);
lean_inc_ref(v___f_1315_);
lean_inc(v_modifyEnv_1313_);
v___f_1316_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1316_, 0, v_modifyEnv_1313_);
lean_closure_set(v___f_1316_, 1, v___f_1315_);
lean_inc(v_toBind_1311_);
v___f_1317_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1317_, 0, v_declName_1310_);
lean_closure_set(v___f_1317_, 1, v_modifyEnv_1313_);
lean_closure_set(v___f_1317_, 2, v___f_1315_);
lean_closure_set(v___f_1317_, 3, v_inst_1307_);
lean_closure_set(v___f_1317_, 4, v_inst_1308_);
lean_closure_set(v___f_1317_, 5, v_toBind_1311_);
lean_closure_set(v___f_1317_, 6, v___f_1316_);
v___x_1318_ = lean_apply_4(v_toBind_1311_, lean_box(0), lean_box(0), v_getEnv_1312_, v___f_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore(lean_object* v_m_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_declName_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_removeDocStringCore___redArg(v_inst_1320_, v_inst_1321_, v_inst_1322_, v_declName_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___boxed(lean_object* v_m_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_declName_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_removeDocStringCore(v_m_1326_, v_inst_1327_, v_inst_1328_, v_inst_1329_, v_inst_1330_, v_declName_1331_);
lean_dec(v_inst_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___redArg(lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_declName_1336_, lean_object* v_docString_x3f_1337_){
_start:
{
if (lean_obj_tag(v_docString_x3f_1337_) == 0)
{
lean_object* v_toApplicative_1338_; lean_object* v_toPure_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_toApplicative_1338_ = lean_ctor_get(v_inst_1333_, 0);
lean_inc_ref(v_toApplicative_1338_);
lean_dec(v_declName_1336_);
lean_dec_ref(v_inst_1335_);
lean_dec_ref(v_inst_1334_);
lean_dec_ref(v_inst_1333_);
v_toPure_1339_ = lean_ctor_get(v_toApplicative_1338_, 1);
lean_inc(v_toPure_1339_);
lean_dec_ref(v_toApplicative_1338_);
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_apply_2(v_toPure_1339_, lean_box(0), v___x_1340_);
return v___x_1341_;
}
else
{
lean_object* v_val_1342_; lean_object* v___x_1343_; 
v_val_1342_ = lean_ctor_get(v_docString_x3f_1337_, 0);
lean_inc(v_val_1342_);
lean_dec_ref(v_docString_x3f_1337_);
v___x_1343_ = l_Lean_addDocStringCore___redArg(v_inst_1333_, v_inst_1334_, v_inst_1335_, v_declName_1336_, v_val_1342_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27(lean_object* v_m_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_declName_1349_, lean_object* v_docString_x3f_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_addDocStringCore_x27___redArg(v_inst_1345_, v_inst_1346_, v_inst_1347_, v_declName_1349_, v_docString_x3f_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___boxed(lean_object* v_m_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_declName_1357_, lean_object* v_docString_x3f_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_addDocStringCore_x27(v_m_1352_, v_inst_1353_, v_inst_1354_, v_inst_1355_, v_inst_1356_, v_declName_1357_, v_docString_x3f_1358_);
lean_dec(v_inst_1356_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object* v_declName_1360_, lean_object* v_target_1361_, lean_object* v_env_1362_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1364_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1363_, v_env_1362_, v_declName_1360_, v_target_1361_);
return v___x_1364_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__2___closed__0));
v___x_1367_ = l_Lean_stringToMessageData(v___x_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object* v___x_1368_, lean_object* v_target_1369_, lean_object* v_declName_1370_, lean_object* v___x_1371_, lean_object* v_modifyEnv_1372_, lean_object* v___f_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_toBind_1376_, lean_object* v___f_1377_, lean_object* v_____do__lift_1378_){
_start:
{
lean_object* v___x_1379_; lean_object* v_toEnvExtension_1380_; lean_object* v_asyncMode_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1379_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_ref(v_toEnvExtension_1380_);
v_asyncMode_1381_ = lean_ctor_get(v_toEnvExtension_1380_, 2);
lean_inc(v_asyncMode_1381_);
lean_dec_ref(v_toEnvExtension_1380_);
v___x_1382_ = 1;
v___x_1383_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1368_, v___x_1379_, v_____do__lift_1378_, v_target_1369_, v_asyncMode_1381_, v___x_1382_);
lean_dec(v_asyncMode_1381_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_declName_1370_);
v___x_1385_ = l_Option_instBEq_beq___redArg(v___x_1371_, v___x_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; 
lean_dec(v___f_1377_);
lean_dec(v_toBind_1376_);
lean_dec_ref(v_inst_1375_);
lean_dec_ref(v_inst_1374_);
v___x_1386_ = lean_apply_1(v_modifyEnv_1372_, v___f_1373_);
return v___x_1386_;
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v___f_1373_);
lean_dec(v_modifyEnv_1372_);
v___x_1387_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__2___closed__1, &l_Lean_addInheritedDocString___redArg___lam__2___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1);
v___x_1388_ = l_Lean_throwError___redArg(v_inst_1374_, v_inst_1375_, v___x_1387_);
v___x_1389_ = lean_apply_4(v_toBind_1376_, lean_box(0), lean_box(0), v___x_1388_, v___f_1377_);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object* v_toBind_1390_, lean_object* v_getEnv_1391_, lean_object* v___f_1392_, lean_object* v_____r_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_apply_4(v_toBind_1390_, lean_box(0), lean_box(0), v_getEnv_1391_, v___f_1392_);
return v___x_1394_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__0));
v___x_1397_ = l_Lean_stringToMessageData(v___x_1396_);
return v___x_1397_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__2));
v___x_1400_ = l_Lean_stringToMessageData(v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object* v___x_1401_, lean_object* v_declName_1402_, lean_object* v_toBind_1403_, lean_object* v_getEnv_1404_, lean_object* v___f_1405_, lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v___f_1408_, lean_object* v_____do__lift_1409_){
_start:
{
lean_object* v___x_1410_; lean_object* v_toEnvExtension_1411_; lean_object* v_asyncMode_1412_; uint8_t v___x_1413_; lean_object* v___x_1414_; 
v___x_1410_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc_ref(v_toEnvExtension_1411_);
v_asyncMode_1412_ = lean_ctor_get(v_toEnvExtension_1411_, 2);
lean_inc(v_asyncMode_1412_);
lean_dec_ref(v_toEnvExtension_1411_);
v___x_1413_ = 1;
lean_inc(v_declName_1402_);
v___x_1414_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1401_, v___x_1410_, v_____do__lift_1409_, v_declName_1402_, v_asyncMode_1412_, v___x_1413_);
lean_dec(v_asyncMode_1412_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v___x_1415_; 
lean_dec(v___f_1408_);
lean_dec_ref(v_inst_1407_);
lean_dec_ref(v_inst_1406_);
lean_dec(v_declName_1402_);
v___x_1415_ = lean_apply_4(v_toBind_1403_, lean_box(0), lean_box(0), v_getEnv_1404_, v___f_1405_);
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v___x_1414_);
lean_dec(v___f_1405_);
lean_dec(v_getEnv_1404_);
v___x_1416_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1417_ = 0;
v___x_1418_ = l_Lean_MessageData_ofConstName(v_declName_1402_, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1416_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__3, &l_Lean_addInheritedDocString___redArg___lam__3___closed__3_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3);
v___x_1421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v___x_1422_ = l_Lean_throwError___redArg(v_inst_1406_, v_inst_1407_, v___x_1421_);
v___x_1423_ = lean_apply_4(v_toBind_1403_, lean_box(0), lean_box(0), v___x_1422_, v___f_1408_);
return v___x_1423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object* v_declName_1424_, lean_object* v_toBind_1425_, lean_object* v_getEnv_1426_, lean_object* v___f_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v___f_1430_, lean_object* v_____do__lift_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1431_, v_declName_1424_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v___x_1433_; 
lean_dec(v___f_1430_);
lean_dec_ref(v_inst_1429_);
lean_dec_ref(v_inst_1428_);
lean_dec(v_declName_1424_);
v___x_1433_ = lean_apply_4(v_toBind_1425_, lean_box(0), lean_box(0), v_getEnv_1426_, v___f_1427_);
return v___x_1433_;
}
else
{
uint8_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec_ref(v___x_1432_);
lean_dec(v___f_1427_);
lean_dec(v_getEnv_1426_);
v___x_1434_ = 0;
v___x_1435_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1436_ = l_Lean_MessageData_ofConstName(v_declName_1424_, v___x_1434_);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = l_Lean_throwError___redArg(v_inst_1428_, v_inst_1429_, v___x_1439_);
v___x_1441_ = lean_apply_4(v_toBind_1425_, lean_box(0), lean_box(0), v___x_1440_, v___f_1430_);
return v___x_1441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object* v_declName_1442_, lean_object* v_toBind_1443_, lean_object* v_getEnv_1444_, lean_object* v___f_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v___f_1448_, lean_object* v_____do__lift_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_addInheritedDocString___redArg___lam__5(v_declName_1442_, v_toBind_1443_, v_getEnv_1444_, v___f_1445_, v_inst_1446_, v_inst_1447_, v___f_1448_, v_____do__lift_1449_);
lean_dec_ref(v_____do__lift_1449_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object* v_inst_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_declName_1455_, lean_object* v_target_1456_){
_start:
{
lean_object* v_toBind_1457_; lean_object* v_getEnv_1458_; lean_object* v_modifyEnv_1459_; lean_object* v___f_1460_; lean_object* v___f_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___f_1464_; lean_object* v___f_1465_; lean_object* v___f_1466_; lean_object* v___f_1467_; lean_object* v___f_1468_; lean_object* v___x_1469_; 
v_toBind_1457_ = lean_ctor_get(v_inst_1452_, 1);
lean_inc(v_toBind_1457_);
v_getEnv_1458_ = lean_ctor_get(v_inst_1454_, 0);
lean_inc(v_getEnv_1458_);
v_modifyEnv_1459_ = lean_ctor_get(v_inst_1454_, 1);
lean_inc(v_modifyEnv_1459_);
lean_dec_ref(v_inst_1454_);
lean_inc(v_target_1456_);
lean_inc(v_declName_1455_);
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1460_, 0, v_declName_1455_);
lean_closure_set(v___f_1460_, 1, v_target_1456_);
lean_inc_ref(v___f_1460_);
lean_inc(v_modifyEnv_1459_);
v___f_1461_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1461_, 0, v_modifyEnv_1459_);
lean_closure_set(v___f_1461_, 1, v___f_1460_);
v___x_1462_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___closed__0));
v___x_1463_ = lean_box(0);
lean_inc(v_toBind_1457_);
lean_inc_ref(v_inst_1453_);
lean_inc_ref(v_inst_1452_);
lean_inc(v_declName_1455_);
v___f_1464_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__2), 11, 10);
lean_closure_set(v___f_1464_, 0, v___x_1463_);
lean_closure_set(v___f_1464_, 1, v_target_1456_);
lean_closure_set(v___f_1464_, 2, v_declName_1455_);
lean_closure_set(v___f_1464_, 3, v___x_1462_);
lean_closure_set(v___f_1464_, 4, v_modifyEnv_1459_);
lean_closure_set(v___f_1464_, 5, v___f_1460_);
lean_closure_set(v___f_1464_, 6, v_inst_1452_);
lean_closure_set(v___f_1464_, 7, v_inst_1453_);
lean_closure_set(v___f_1464_, 8, v_toBind_1457_);
lean_closure_set(v___f_1464_, 9, v___f_1461_);
lean_inc_ref(v___f_1464_);
lean_inc(v_getEnv_1458_);
lean_inc(v_toBind_1457_);
v___f_1465_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1465_, 0, v_toBind_1457_);
lean_closure_set(v___f_1465_, 1, v_getEnv_1458_);
lean_closure_set(v___f_1465_, 2, v___f_1464_);
lean_inc_ref(v_inst_1453_);
lean_inc_ref(v_inst_1452_);
lean_inc(v_getEnv_1458_);
lean_inc(v_toBind_1457_);
lean_inc(v_declName_1455_);
v___f_1466_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__3), 9, 8);
lean_closure_set(v___f_1466_, 0, v___x_1463_);
lean_closure_set(v___f_1466_, 1, v_declName_1455_);
lean_closure_set(v___f_1466_, 2, v_toBind_1457_);
lean_closure_set(v___f_1466_, 3, v_getEnv_1458_);
lean_closure_set(v___f_1466_, 4, v___f_1464_);
lean_closure_set(v___f_1466_, 5, v_inst_1452_);
lean_closure_set(v___f_1466_, 6, v_inst_1453_);
lean_closure_set(v___f_1466_, 7, v___f_1465_);
lean_inc_ref(v___f_1466_);
lean_inc(v_getEnv_1458_);
lean_inc(v_toBind_1457_);
v___f_1467_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1467_, 0, v_toBind_1457_);
lean_closure_set(v___f_1467_, 1, v_getEnv_1458_);
lean_closure_set(v___f_1467_, 2, v___f_1466_);
lean_inc(v_getEnv_1458_);
lean_inc(v_toBind_1457_);
v___f_1468_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1468_, 0, v_declName_1455_);
lean_closure_set(v___f_1468_, 1, v_toBind_1457_);
lean_closure_set(v___f_1468_, 2, v_getEnv_1458_);
lean_closure_set(v___f_1468_, 3, v___f_1466_);
lean_closure_set(v___f_1468_, 4, v_inst_1452_);
lean_closure_set(v___f_1468_, 5, v_inst_1453_);
lean_closure_set(v___f_1468_, 6, v___f_1467_);
v___x_1469_ = lean_apply_4(v_toBind_1457_, lean_box(0), lean_box(0), v_getEnv_1458_, v___f_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object* v_m_1470_, lean_object* v_inst_1471_, lean_object* v_inst_1472_, lean_object* v_inst_1473_, lean_object* v_declName_1474_, lean_object* v_target_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_addInheritedDocString___redArg(v_inst_1471_, v_inst_1472_, v_inst_1473_, v_declName_1474_, v_target_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f(lean_object* v_env_1478_, lean_object* v_declName_1479_, uint8_t v_includeBuiltin_1480_){
_start:
{
lean_object* v___x_1485_; lean_object* v_toEnvExtension_1486_; lean_object* v_asyncMode_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1485_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc_ref(v_toEnvExtension_1486_);
v_asyncMode_1487_ = lean_ctor_get(v_toEnvExtension_1486_, 2);
lean_inc(v_asyncMode_1487_);
lean_dec_ref(v_toEnvExtension_1486_);
v___x_1488_ = lean_box(0);
v___x_1489_ = 1;
lean_inc(v_declName_1479_);
lean_inc_ref(v_env_1478_);
v___x_1490_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1488_, v___x_1485_, v_env_1478_, v_declName_1479_, v_asyncMode_1487_, v___x_1489_);
lean_dec(v_asyncMode_1487_);
if (lean_obj_tag(v___x_1490_) == 1)
{
lean_object* v_val_1491_; 
lean_dec(v_declName_1479_);
v_val_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_val_1491_);
lean_dec_ref(v___x_1490_);
v_declName_1479_ = v_val_1491_;
goto _start;
}
else
{
lean_object* v___x_1493_; lean_object* v_toEnvExtension_1494_; lean_object* v_asyncMode_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_dec(v___x_1490_);
v___x_1493_ = l_Lean_docStringExt;
v_toEnvExtension_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc_ref(v_toEnvExtension_1494_);
v_asyncMode_1495_ = lean_ctor_get(v_toEnvExtension_1494_, 2);
lean_inc(v_asyncMode_1495_);
lean_dec_ref(v_toEnvExtension_1494_);
v___x_1496_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
lean_inc(v_declName_1479_);
lean_inc_ref(v_env_1478_);
v___x_1497_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1496_, v___x_1493_, v_env_1478_, v_declName_1479_, v_asyncMode_1495_, v___x_1489_);
lean_dec(v_asyncMode_1495_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1498_; lean_object* v_toEnvExtension_1499_; lean_object* v_asyncMode_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1498_ = l_Lean_versoDocStringExt;
v_toEnvExtension_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc_ref(v_toEnvExtension_1499_);
v_asyncMode_1500_ = lean_ctor_get(v_toEnvExtension_1499_, 2);
lean_inc(v_asyncMode_1500_);
lean_dec_ref(v_toEnvExtension_1499_);
v___x_1501_ = l_Lean_instInhabitedVersoDocString_default;
lean_inc(v_declName_1479_);
v___x_1502_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1501_, v___x_1498_, v_env_1478_, v_declName_1479_, v_asyncMode_1500_, v___x_1489_);
lean_dec(v_asyncMode_1500_);
if (lean_obj_tag(v___x_1502_) == 0)
{
if (v_includeBuiltin_1480_ == 0)
{
lean_dec(v_declName_1479_);
goto v___jp_1482_;
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1504_ = lean_st_ref_get(v___x_1503_);
v___x_1505_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1504_, v_declName_1479_);
lean_dec(v___x_1504_);
if (lean_obj_tag(v___x_1505_) == 1)
{
lean_object* v_val_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_declName_1479_);
v_val_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_val_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_val_1506_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1510_);
v___x_1512_ = v___x_1508_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec(v___x_1505_);
v___x_1516_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1517_ = lean_st_ref_get(v___x_1516_);
v___x_1518_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1517_, v_declName_1479_);
lean_dec(v_declName_1479_);
lean_dec(v___x_1517_);
if (lean_obj_tag(v___x_1518_) == 1)
{
lean_object* v_val_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1528_; 
v_val_1519_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_val_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_val_1519_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1523_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
}
else
{
lean_dec(v___x_1518_);
goto v___jp_1482_;
}
}
}
}
else
{
lean_object* v_val_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_declName_1479_);
v_val_1529_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1531_ = v___x_1502_;
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_val_1529_);
lean_dec(v___x_1502_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1533_, 0, v_val_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1533_);
v___x_1535_ = v___x_1531_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
return v___x_1536_;
}
}
}
}
else
{
lean_object* v_val_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v_declName_1479_);
lean_dec_ref(v_env_1478_);
v_val_1539_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1541_ = v___x_1497_;
v_isShared_1542_ = v_isSharedCheck_1548_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_val_1539_);
lean_dec(v___x_1497_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1548_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_val_1539_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1543_);
v___x_1545_ = v___x_1541_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
}
}
}
v___jp_1482_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_box(0);
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object* v_env_1549_, lean_object* v_declName_1550_, lean_object* v_includeBuiltin_1551_, lean_object* v_a_1552_){
_start:
{
uint8_t v_includeBuiltin_boxed_1553_; lean_object* v_res_1554_; 
v_includeBuiltin_boxed_1553_ = lean_unbox(v_includeBuiltin_1551_);
v_res_1554_ = l_Lean_findInternalDocString_x3f(v_env_1549_, v_declName_1550_, v_includeBuiltin_boxed_1553_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(lean_object* v_s_1555_, lean_object* v_replacement_1556_, lean_object* v_a_1557_, lean_object* v_b_1558_){
_start:
{
lean_object* v_it_1560_; lean_object* v_startPos_1561_; lean_object* v_endPos_1562_; lean_object* v_it_1571_; 
switch(lean_obj_tag(v_a_1557_))
{
case 0:
{
lean_object* v_pos_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1589_; 
v_pos_1577_ = lean_ctor_get(v_a_1557_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1579_ = v_a_1557_;
v_isShared_1580_ = v_isSharedCheck_1589_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_pos_1577_);
lean_dec(v_a_1557_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1589_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_startInclusive_1581_; lean_object* v_endExclusive_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v_startInclusive_1581_ = lean_ctor_get(v_s_1555_, 1);
v_endExclusive_1582_ = lean_ctor_get(v_s_1555_, 2);
v___x_1583_ = lean_nat_sub(v_endExclusive_1582_, v_startInclusive_1581_);
v___x_1584_ = lean_nat_dec_eq(v_pos_1577_, v___x_1583_);
lean_dec(v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1586_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 1);
v___x_1586_ = v___x_1579_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_pos_1577_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
v_it_1571_ = v___x_1586_;
goto v___jp_1570_;
}
}
else
{
lean_object* v___x_1588_; 
lean_del_object(v___x_1579_);
lean_dec(v_pos_1577_);
v___x_1588_ = lean_box(3);
v_it_1571_ = v___x_1588_;
goto v___jp_1570_;
}
}
}
case 1:
{
lean_object* v_pos_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1602_; 
v_pos_1590_ = lean_ctor_get(v_a_1557_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1592_ = v_a_1557_;
v_isShared_1593_ = v_isSharedCheck_1602_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_pos_1590_);
lean_dec(v_a_1557_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1602_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_str_1594_; lean_object* v_startInclusive_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v_str_1594_ = lean_ctor_get(v_s_1555_, 0);
v_startInclusive_1595_ = lean_ctor_get(v_s_1555_, 1);
v___x_1596_ = lean_nat_add(v_startInclusive_1595_, v_pos_1590_);
v___x_1597_ = lean_string_utf8_next_fast(v_str_1594_, v___x_1596_);
lean_dec(v___x_1596_);
v___x_1598_ = lean_nat_sub(v___x_1597_, v_startInclusive_1595_);
lean_inc(v___x_1598_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1598_);
v___x_1600_ = v___x_1592_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
v_it_1560_ = v___x_1600_;
v_startPos_1561_ = v_pos_1590_;
v_endPos_1562_ = v___x_1598_;
goto v___jp_1559_;
}
}
}
case 2:
{
lean_object* v_needle_1603_; lean_object* v_table_1604_; lean_object* v_stackPos_1605_; lean_object* v_needlePos_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1665_; 
v_needle_1603_ = lean_ctor_get(v_a_1557_, 0);
v_table_1604_ = lean_ctor_get(v_a_1557_, 1);
v_stackPos_1605_ = lean_ctor_get(v_a_1557_, 2);
v_needlePos_1606_ = lean_ctor_get(v_a_1557_, 3);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1608_ = v_a_1557_;
v_isShared_1609_ = v_isSharedCheck_1665_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_needlePos_1606_);
lean_inc(v_stackPos_1605_);
lean_inc(v_table_1604_);
lean_inc(v_needle_1603_);
lean_dec(v_a_1557_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1665_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v_str_1610_; lean_object* v_startInclusive_1611_; lean_object* v_endExclusive_1612_; lean_object* v_str_1613_; lean_object* v_startInclusive_1614_; lean_object* v_endExclusive_1615_; lean_object* v_basePos_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_str_1610_ = lean_ctor_get(v_needle_1603_, 0);
v_startInclusive_1611_ = lean_ctor_get(v_needle_1603_, 1);
v_endExclusive_1612_ = lean_ctor_get(v_needle_1603_, 2);
v_str_1613_ = lean_ctor_get(v_s_1555_, 0);
v_startInclusive_1614_ = lean_ctor_get(v_s_1555_, 1);
v_endExclusive_1615_ = lean_ctor_get(v_s_1555_, 2);
v_basePos_1616_ = lean_nat_sub(v_stackPos_1605_, v_needlePos_1606_);
v___x_1617_ = lean_nat_sub(v_endExclusive_1612_, v_startInclusive_1611_);
v___x_1618_ = lean_nat_add(v_basePos_1616_, v___x_1617_);
v___x_1619_ = lean_nat_sub(v_endExclusive_1615_, v_startInclusive_1614_);
v___x_1620_ = lean_nat_dec_le(v___x_1618_, v___x_1619_);
lean_dec(v___x_1618_);
if (v___x_1620_ == 0)
{
uint8_t v___x_1621_; 
lean_dec(v___x_1617_);
lean_del_object(v___x_1608_);
lean_dec(v_needlePos_1606_);
lean_dec(v_stackPos_1605_);
lean_dec_ref(v_table_1604_);
lean_dec_ref(v_needle_1603_);
v___x_1621_ = l_String_instDecidableLtRaw___aux__1(v_basePos_1616_, v___x_1619_);
if (v___x_1621_ == 0)
{
lean_dec(v___x_1619_);
lean_dec(v_basePos_1616_);
lean_dec_ref(v_s_1555_);
return v_b_1558_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = l_String_Slice_pos_x21(v_s_1555_, v_basePos_1616_);
lean_dec(v_basePos_1616_);
v___x_1623_ = lean_box(3);
v_it_1560_ = v___x_1623_;
v_startPos_1561_ = v___x_1622_;
v_endPos_1562_ = v___x_1619_;
goto v___jp_1559_;
}
}
else
{
lean_object* v___x_1624_; uint8_t v_stackByte_1625_; lean_object* v___x_1626_; uint8_t v_patByte_1627_; uint8_t v___x_1628_; 
lean_dec(v___x_1619_);
v___x_1624_ = lean_nat_add(v_startInclusive_1614_, v_stackPos_1605_);
v_stackByte_1625_ = lean_string_get_byte_fast(v_str_1613_, v___x_1624_);
v___x_1626_ = lean_nat_add(v_startInclusive_1611_, v_needlePos_1606_);
v_patByte_1627_ = lean_string_get_byte_fast(v_str_1610_, v___x_1626_);
v___x_1628_ = lean_uint8_dec_eq(v_stackByte_1625_, v_patByte_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
lean_dec(v___x_1617_);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_nat_dec_eq(v_needlePos_1606_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_newNeedlePos_1633_; uint8_t v___x_1634_; 
v___x_1631_ = lean_unsigned_to_nat(1u);
v___x_1632_ = lean_nat_sub(v_needlePos_1606_, v___x_1631_);
lean_dec(v_needlePos_1606_);
v_newNeedlePos_1633_ = lean_array_fget_borrowed(v_table_1604_, v___x_1632_);
lean_dec(v___x_1632_);
v___x_1634_ = lean_nat_dec_eq(v_newNeedlePos_1633_, v___x_1629_);
if (v___x_1634_ == 0)
{
lean_object* v_oldBasePos_1635_; lean_object* v___x_1636_; lean_object* v_newBasePos_1637_; lean_object* v___x_1639_; 
lean_inc(v_newNeedlePos_1633_);
v_oldBasePos_1635_ = l_String_Slice_pos_x21(v_s_1555_, v_basePos_1616_);
lean_dec(v_basePos_1616_);
v___x_1636_ = lean_nat_sub(v_stackPos_1605_, v_newNeedlePos_1633_);
v_newBasePos_1637_ = l_String_Slice_pos_x21(v_s_1555_, v___x_1636_);
lean_dec(v___x_1636_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 3, v_newNeedlePos_1633_);
v___x_1639_ = v___x_1608_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_needle_1603_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_table_1604_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_stackPos_1605_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_newNeedlePos_1633_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
v_it_1560_ = v___x_1639_;
v_startPos_1561_ = v_oldBasePos_1635_;
v_endPos_1562_ = v_newBasePos_1637_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_basePos_1641_; lean_object* v_nextStackPos_1642_; lean_object* v___x_1644_; 
v_basePos_1641_ = l_String_Slice_pos_x21(v_s_1555_, v_basePos_1616_);
lean_dec(v_basePos_1616_);
v_nextStackPos_1642_ = l_String_Slice_posGE___redArg(v_s_1555_, v_stackPos_1605_);
lean_inc(v_nextStackPos_1642_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 3, v___x_1629_);
lean_ctor_set(v___x_1608_, 2, v_nextStackPos_1642_);
v___x_1644_ = v___x_1608_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_needle_1603_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_table_1604_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_nextStackPos_1642_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v___x_1629_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
v_it_1560_ = v___x_1644_;
v_startPos_1561_ = v_basePos_1641_;
v_endPos_1562_ = v_nextStackPos_1642_;
goto v___jp_1559_;
}
}
}
else
{
lean_object* v_basePos_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v_nextStackPos_1649_; lean_object* v___x_1651_; 
lean_dec(v_basePos_1616_);
lean_dec(v_needlePos_1606_);
v_basePos_1646_ = l_String_Slice_pos_x21(v_s_1555_, v_stackPos_1605_);
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = lean_nat_add(v_stackPos_1605_, v___x_1647_);
lean_dec(v_stackPos_1605_);
v_nextStackPos_1649_ = l_String_Slice_posGE___redArg(v_s_1555_, v___x_1648_);
lean_inc(v_nextStackPos_1649_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 3, v___x_1629_);
lean_ctor_set(v___x_1608_, 2, v_nextStackPos_1649_);
v___x_1651_ = v___x_1608_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_needle_1603_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_table_1604_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_nextStackPos_1649_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v___x_1629_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
v_it_1560_ = v___x_1651_;
v_startPos_1561_ = v_basePos_1646_;
v_endPos_1562_ = v_nextStackPos_1649_;
goto v___jp_1559_;
}
}
}
else
{
lean_object* v___x_1653_; lean_object* v_nextStackPos_1654_; lean_object* v_nextNeedlePos_1655_; uint8_t v___x_1656_; 
lean_dec(v_basePos_1616_);
v___x_1653_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1654_ = lean_nat_add(v_stackPos_1605_, v___x_1653_);
lean_dec(v_stackPos_1605_);
v_nextNeedlePos_1655_ = lean_nat_add(v_needlePos_1606_, v___x_1653_);
lean_dec(v_needlePos_1606_);
v___x_1656_ = lean_nat_dec_eq(v_nextNeedlePos_1655_, v___x_1617_);
lean_dec(v___x_1617_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1658_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 3, v_nextNeedlePos_1655_);
lean_ctor_set(v___x_1608_, 2, v_nextStackPos_1654_);
v___x_1658_ = v___x_1608_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_needle_1603_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_table_1604_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_nextStackPos_1654_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_nextNeedlePos_1655_);
v___x_1658_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
v_a_1557_ = v___x_1658_;
goto _start;
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_dec(v_nextNeedlePos_1655_);
v___x_1661_ = lean_unsigned_to_nat(0u);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 3, v___x_1661_);
lean_ctor_set(v___x_1608_, 2, v_nextStackPos_1654_);
v___x_1663_ = v___x_1608_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_needle_1603_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_table_1604_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_nextStackPos_1654_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
v_it_1571_ = v___x_1663_;
goto v___jp_1570_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1555_);
return v_b_1558_;
}
}
v___jp_1559_:
{
lean_object* v___x_1563_; lean_object* v_str_1564_; lean_object* v_startInclusive_1565_; lean_object* v_endExclusive_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_inc_ref(v_s_1555_);
v___x_1563_ = l_String_Slice_slice_x21(v_s_1555_, v_startPos_1561_, v_endPos_1562_);
lean_dec(v_endPos_1562_);
lean_dec(v_startPos_1561_);
v_str_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc_ref(v_str_1564_);
v_startInclusive_1565_ = lean_ctor_get(v___x_1563_, 1);
lean_inc(v_startInclusive_1565_);
v_endExclusive_1566_ = lean_ctor_get(v___x_1563_, 2);
lean_inc(v_endExclusive_1566_);
lean_dec_ref(v___x_1563_);
v___x_1567_ = lean_string_utf8_extract(v_str_1564_, v_startInclusive_1565_, v_endExclusive_1566_);
lean_dec(v_endExclusive_1566_);
lean_dec(v_startInclusive_1565_);
lean_dec_ref(v_str_1564_);
v___x_1568_ = lean_string_append(v_b_1558_, v___x_1567_);
lean_dec_ref(v___x_1567_);
v_a_1557_ = v_it_1560_;
v_b_1558_ = v___x_1568_;
goto _start;
}
v___jp_1570_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_string_utf8_byte_size(v_replacement_1556_);
v___x_1574_ = lean_string_utf8_extract(v_replacement_1556_, v___x_1572_, v___x_1573_);
v___x_1575_ = lean_string_append(v_b_1558_, v___x_1574_);
lean_dec_ref(v___x_1574_);
v_a_1557_ = v_it_1571_;
v_b_1558_ = v___x_1575_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_s_1666_, lean_object* v_replacement_1667_, lean_object* v_a_1668_, lean_object* v_b_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1666_, v_replacement_1667_, v_a_1668_, v_b_1669_);
lean_dec_ref(v_replacement_1667_);
return v_res_1670_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1673_ = lean_string_utf8_byte_size(v___x_1672_);
return v___x_1673_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1676_ = lean_nat_dec_eq(v___x_1675_, v___x_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1680_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v___x_1678_);
lean_ctor_set(v___x_1680_, 2, v___x_1677_);
return v___x_1680_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1682_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1681_);
return v___x_1682_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4);
v___x_1685_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1686_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v___x_1684_);
lean_ctor_set(v___x_1686_, 2, v___x_1683_);
lean_ctor_set(v___x_1686_, 3, v___x_1683_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(lean_object* v_s_1689_, lean_object* v_replacement_1690_){
_start:
{
lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_1692_ = lean_uint8_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5);
v___x_1694_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1689_, v_replacement_1690_, v___x_1693_, v___x_1691_);
return v___x_1694_;
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__6));
v___x_1696_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1689_, v_replacement_1690_, v___x_1695_, v___x_1691_);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_s_1697_, lean_object* v_replacement_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v_s_1697_, v_replacement_1698_);
lean_dec_ref(v_replacement_1698_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(lean_object* v_as_1707_, size_t v_sz_1708_, size_t v_i_1709_, lean_object* v_b_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_usize_dec_lt(v_i_1709_, v_sz_1708_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_b_1710_);
lean_ctor_set(v___x_1714_, 1, v___y_1712_);
return v___x_1714_;
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1716_; lean_object* v_snd_1717_; lean_object* v___x_1718_; size_t v___x_1719_; size_t v___x_1720_; 
v_a_1715_ = lean_array_uget_borrowed(v_as_1707_, v_i_1709_);
lean_inc(v_a_1715_);
v___x_1716_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_a_1715_, v___y_1711_, v___y_1712_);
v_snd_1717_ = lean_ctor_get(v___x_1716_, 1);
lean_inc(v_snd_1717_);
lean_dec_ref(v___x_1716_);
v___x_1718_ = lean_box(0);
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1709_, v___x_1719_);
v_i_1709_ = v___x_1720_;
v_b_1710_ = v___x_1718_;
v___y_1712_ = v_snd_1717_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1731_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__12));
v___x_1732_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_1733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
lean_ctor_set(v___x_1733_, 2, v___x_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(lean_object* v_x_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
switch(lean_obj_tag(v_x_1735_))
{
case 0:
{
lean_object* v_string_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_string_1738_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_string_1738_);
lean_dec_ref(v_x_1735_);
v___x_1739_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1738_);
lean_dec_ref(v_string_1738_);
v___x_1740_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1739_, v_a_1737_);
lean_dec_ref(v___x_1739_);
return v___x_1740_;
}
case 1:
{
lean_object* v_content_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1782_; 
v_content_1741_ = lean_ctor_get(v_x_1735_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_x_1735_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1743_ = v_x_1735_;
v_isShared_1744_ = v_isSharedCheck_1782_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_content_1741_);
lean_dec(v_x_1735_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1782_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set_tag(v___x_1743_, 9);
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_content_1741_);
v___x_1746_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; lean_object* v_snd_1748_; lean_object* v_fst_1749_; lean_object* v_fst_1750_; lean_object* v_snd_1751_; uint8_t v_inEmph_1753_; uint8_t v_inBold_1754_; uint8_t v_inLink_1755_; lean_object* v_linePrefix_1756_; lean_object* v___y_1757_; lean_object* v___x_1768_; uint8_t v_inEmph_1769_; 
v___x_1747_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1746_);
v_snd_1748_ = lean_ctor_get(v___x_1747_, 1);
lean_inc(v_snd_1748_);
v_fst_1749_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_fst_1749_);
lean_dec_ref(v___x_1747_);
v_fst_1750_ = lean_ctor_get(v_snd_1748_, 0);
lean_inc(v_fst_1750_);
v_snd_1751_ = lean_ctor_get(v_snd_1748_, 1);
lean_inc(v_snd_1751_);
lean_dec(v_snd_1748_);
v___x_1768_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_1749_, v_a_1737_);
lean_dec(v_fst_1749_);
v_inEmph_1769_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1);
if (v_inEmph_1769_ == 0)
{
lean_object* v_snd_1770_; uint8_t v_inBold_1771_; uint8_t v_inLink_1772_; lean_object* v_linePrefix_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v_snd_1776_; 
v_snd_1770_ = lean_ctor_get(v___x_1768_, 1);
lean_inc(v_snd_1770_);
lean_dec_ref(v___x_1768_);
v_inBold_1771_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 1);
v_inLink_1772_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 2);
v_linePrefix_1773_ = lean_ctor_get(v_a_1736_, 0);
v___x_1774_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0));
v___x_1775_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1774_, v_snd_1770_);
v_snd_1776_ = lean_ctor_get(v___x_1775_, 1);
lean_inc(v_snd_1776_);
lean_dec_ref(v___x_1775_);
v_inEmph_1753_ = v_inEmph_1769_;
v_inBold_1754_ = v_inBold_1771_;
v_inLink_1755_ = v_inLink_1772_;
v_linePrefix_1756_ = v_linePrefix_1773_;
v___y_1757_ = v_snd_1776_;
goto v___jp_1752_;
}
else
{
lean_object* v_snd_1777_; uint8_t v_inBold_1778_; uint8_t v_inLink_1779_; lean_object* v_linePrefix_1780_; 
v_snd_1777_ = lean_ctor_get(v___x_1768_, 1);
lean_inc(v_snd_1777_);
lean_dec_ref(v___x_1768_);
v_inBold_1778_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 1);
v_inLink_1779_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 2);
v_linePrefix_1780_ = lean_ctor_get(v_a_1736_, 0);
v_inEmph_1753_ = v_inEmph_1769_;
v_inBold_1754_ = v_inBold_1778_;
v_inLink_1755_ = v_inLink_1779_;
v_linePrefix_1756_ = v_linePrefix_1780_;
v___y_1757_ = v_snd_1777_;
goto v___jp_1752_;
}
v___jp_1752_:
{
uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = 1;
lean_inc_ref(v_linePrefix_1756_);
v___x_1759_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1759_, 0, v_linePrefix_1756_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*1, v___x_1758_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*1 + 1, v_inBold_1754_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*1 + 2, v_inLink_1755_);
v___x_1760_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_fst_1750_, v___x_1759_, v___y_1757_);
lean_dec_ref(v___x_1759_);
if (v_inEmph_1753_ == 0)
{
lean_object* v_snd_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v_snd_1764_; lean_object* v___x_1765_; 
v_snd_1761_ = lean_ctor_get(v___x_1760_, 1);
lean_inc(v_snd_1761_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0));
v___x_1763_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1762_, v_snd_1761_);
v_snd_1764_ = lean_ctor_get(v___x_1763_, 1);
lean_inc(v_snd_1764_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1751_, v_snd_1764_);
lean_dec(v_snd_1751_);
return v___x_1765_;
}
else
{
lean_object* v_snd_1766_; lean_object* v___x_1767_; 
v_snd_1766_ = lean_ctor_get(v___x_1760_, 1);
lean_inc(v_snd_1766_);
lean_dec_ref(v___x_1760_);
v___x_1767_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1751_, v_snd_1766_);
lean_dec(v_snd_1751_);
return v___x_1767_;
}
}
}
}
}
case 2:
{
lean_object* v_content_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1821_; 
v_content_1783_ = lean_ctor_get(v_x_1735_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_x_1735_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1785_ = v_x_1735_;
v_isShared_1786_ = v_isSharedCheck_1821_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_content_1783_);
lean_dec(v_x_1735_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1821_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 9);
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_content_1783_);
v___x_1788_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1789_; lean_object* v_snd_1790_; lean_object* v_fst_1791_; lean_object* v_fst_1792_; lean_object* v_snd_1793_; uint8_t v_inBold_1795_; uint8_t v_inLink_1796_; lean_object* v_linePrefix_1797_; lean_object* v___y_1798_; lean_object* v___x_1809_; uint8_t v_inBold_1810_; 
v___x_1789_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1788_);
v_snd_1790_ = lean_ctor_get(v___x_1789_, 1);
lean_inc(v_snd_1790_);
v_fst_1791_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_fst_1791_);
lean_dec_ref(v___x_1789_);
v_fst_1792_ = lean_ctor_get(v_snd_1790_, 0);
lean_inc(v_fst_1792_);
v_snd_1793_ = lean_ctor_get(v_snd_1790_, 1);
lean_inc(v_snd_1793_);
lean_dec(v_snd_1790_);
v___x_1809_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_1791_, v_a_1737_);
lean_dec(v_fst_1791_);
v_inBold_1810_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 1);
if (v_inBold_1810_ == 0)
{
lean_object* v_snd_1811_; uint8_t v_inLink_1812_; lean_object* v_linePrefix_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v_snd_1816_; 
v_snd_1811_ = lean_ctor_get(v___x_1809_, 1);
lean_inc(v_snd_1811_);
lean_dec_ref(v___x_1809_);
v_inLink_1812_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 2);
v_linePrefix_1813_ = lean_ctor_get(v_a_1736_, 0);
v___x_1814_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1));
v___x_1815_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1814_, v_snd_1811_);
v_snd_1816_ = lean_ctor_get(v___x_1815_, 1);
lean_inc(v_snd_1816_);
lean_dec_ref(v___x_1815_);
v_inBold_1795_ = v_inBold_1810_;
v_inLink_1796_ = v_inLink_1812_;
v_linePrefix_1797_ = v_linePrefix_1813_;
v___y_1798_ = v_snd_1816_;
goto v___jp_1794_;
}
else
{
lean_object* v_snd_1817_; uint8_t v_inLink_1818_; lean_object* v_linePrefix_1819_; 
v_snd_1817_ = lean_ctor_get(v___x_1809_, 1);
lean_inc(v_snd_1817_);
lean_dec_ref(v___x_1809_);
v_inLink_1818_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 2);
v_linePrefix_1819_ = lean_ctor_get(v_a_1736_, 0);
v_inBold_1795_ = v_inBold_1810_;
v_inLink_1796_ = v_inLink_1818_;
v_linePrefix_1797_ = v_linePrefix_1819_;
v___y_1798_ = v_snd_1817_;
goto v___jp_1794_;
}
v___jp_1794_:
{
uint8_t v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = 1;
lean_inc_ref(v_linePrefix_1797_);
v___x_1800_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1800_, 0, v_linePrefix_1797_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*1, v___x_1799_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*1 + 1, v_inBold_1795_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*1 + 2, v_inLink_1796_);
v___x_1801_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_fst_1792_, v___x_1800_, v___y_1798_);
lean_dec_ref(v___x_1800_);
if (v_inBold_1795_ == 0)
{
lean_object* v_snd_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v_snd_1805_; lean_object* v___x_1806_; 
v_snd_1802_ = lean_ctor_get(v___x_1801_, 1);
lean_inc(v_snd_1802_);
lean_dec_ref(v___x_1801_);
v___x_1803_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1));
v___x_1804_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1803_, v_snd_1802_);
v_snd_1805_ = lean_ctor_get(v___x_1804_, 1);
lean_inc(v_snd_1805_);
lean_dec_ref(v___x_1804_);
v___x_1806_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1793_, v_snd_1805_);
lean_dec(v_snd_1793_);
return v___x_1806_;
}
else
{
lean_object* v_snd_1807_; lean_object* v___x_1808_; 
v_snd_1807_ = lean_ctor_get(v___x_1801_, 1);
lean_inc(v_snd_1807_);
lean_dec_ref(v___x_1801_);
v___x_1808_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1793_, v_snd_1807_);
lean_dec(v_snd_1793_);
return v___x_1808_;
}
}
}
}
}
case 3:
{
lean_object* v_string_1822_; lean_object* v___y_1824_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_fst_1829_; uint8_t v___x_1830_; 
v_string_1822_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_string_1822_);
lean_dec_ref(v_x_1735_);
v___x_1827_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__2));
v___x_1828_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v___x_1827_, v_a_1737_);
v_fst_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_fst_1829_);
v___x_1830_ = lean_unbox(v_fst_1829_);
lean_dec(v_fst_1829_);
if (v___x_1830_ == 0)
{
lean_object* v_snd_1831_; 
v_snd_1831_ = lean_ctor_get(v___x_1828_, 1);
lean_inc(v_snd_1831_);
lean_dec_ref(v___x_1828_);
v___y_1824_ = v_snd_1831_;
goto v___jp_1823_;
}
else
{
lean_object* v_snd_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v_snd_1835_; 
v_snd_1832_ = lean_ctor_get(v___x_1828_, 1);
lean_inc(v_snd_1832_);
lean_dec_ref(v___x_1828_);
v___x_1833_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__3));
v___x_1834_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1833_, v_snd_1832_);
v_snd_1835_ = lean_ctor_get(v___x_1834_, 1);
lean_inc(v_snd_1835_);
lean_dec_ref(v___x_1834_);
v___y_1824_ = v_snd_1835_;
goto v___jp_1823_;
}
v___jp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1822_);
v___x_1826_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1825_, v___y_1824_);
lean_dec_ref(v___x_1825_);
return v___x_1826_;
}
}
case 4:
{
uint8_t v_mode_1836_; 
v_mode_1836_ = lean_ctor_get_uint8(v_x_1735_, sizeof(void*)*1);
if (v_mode_1836_ == 0)
{
lean_object* v_string_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v_string_1837_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_string_1837_);
lean_dec_ref(v_x_1735_);
v___x_1838_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__4));
v___x_1839_ = lean_string_append(v___x_1838_, v_string_1837_);
lean_dec_ref(v_string_1837_);
v___x_1840_ = lean_string_append(v___x_1839_, v___x_1838_);
v___x_1841_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1840_, v_a_1737_);
lean_dec_ref(v___x_1840_);
return v___x_1841_;
}
else
{
lean_object* v_string_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_string_1842_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_string_1842_);
lean_dec_ref(v_x_1735_);
v___x_1843_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__5));
v___x_1844_ = lean_string_append(v___x_1843_, v_string_1842_);
lean_dec_ref(v_string_1842_);
v___x_1845_ = lean_string_append(v___x_1844_, v___x_1843_);
v___x_1846_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1845_, v_a_1737_);
lean_dec_ref(v___x_1845_);
return v___x_1846_;
}
}
case 5:
{
lean_object* v_string_1847_; lean_object* v_linePrefix_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_string_1847_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_string_1847_);
lean_dec_ref(v_x_1735_);
v_linePrefix_1848_ = lean_ctor_get(v_a_1736_, 0);
v___x_1849_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1850_ = lean_string_append(v___x_1849_, v_linePrefix_1848_);
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_string_utf8_byte_size(v_string_1847_);
v___x_1853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1853_, 0, v_string_1847_);
lean_ctor_set(v___x_1853_, 1, v___x_1851_);
lean_ctor_set(v___x_1853_, 2, v___x_1852_);
v___x_1854_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v___x_1853_, v___x_1850_);
lean_dec_ref(v___x_1850_);
v___x_1855_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1854_, v_a_1737_);
lean_dec_ref(v___x_1854_);
return v___x_1855_;
}
case 6:
{
uint8_t v_inLink_1856_; 
v_inLink_1856_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*1 + 2);
if (v_inLink_1856_ == 0)
{
lean_object* v_content_1857_; lean_object* v_url_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v_snd_1861_; lean_object* v___x_1862_; size_t v_sz_1863_; size_t v___x_1864_; lean_object* v___x_1865_; lean_object* v_snd_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v_snd_1869_; lean_object* v___x_1870_; lean_object* v_snd_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_content_1857_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_content_1857_);
v_url_1858_ = lean_ctor_get(v_x_1735_, 1);
lean_inc_ref(v_url_1858_);
lean_dec_ref(v_x_1735_);
v___x_1859_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__6));
v___x_1860_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1859_, v_a_1737_);
v_snd_1861_ = lean_ctor_get(v___x_1860_, 1);
lean_inc(v_snd_1861_);
lean_dec_ref(v___x_1860_);
v___x_1862_ = lean_box(0);
v_sz_1863_ = lean_array_size(v_content_1857_);
v___x_1864_ = ((size_t)0ULL);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1857_, v_sz_1863_, v___x_1864_, v___x_1862_, v_a_1736_, v_snd_1861_);
lean_dec_ref(v_content_1857_);
v_snd_1866_ = lean_ctor_get(v___x_1865_, 1);
lean_inc(v_snd_1866_);
lean_dec_ref(v___x_1865_);
v___x_1867_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7));
v___x_1868_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1867_, v_snd_1866_);
v_snd_1869_ = lean_ctor_get(v___x_1868_, 1);
lean_inc(v_snd_1869_);
lean_dec_ref(v___x_1868_);
v___x_1870_ = l_Lean_Doc_MarkdownM_push___redArg(v_url_1858_, v_snd_1869_);
lean_dec_ref(v_url_1858_);
v_snd_1871_ = lean_ctor_get(v___x_1870_, 1);
lean_inc(v_snd_1871_);
lean_dec_ref(v___x_1870_);
v___x_1872_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_1873_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1872_, v_snd_1871_);
return v___x_1873_;
}
else
{
lean_object* v_content_1874_; lean_object* v___x_1875_; size_t v_sz_1876_; size_t v___x_1877_; lean_object* v___x_1878_; lean_object* v_snd_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
v_content_1874_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_content_1874_);
lean_dec_ref(v_x_1735_);
v___x_1875_ = lean_box(0);
v_sz_1876_ = lean_array_size(v_content_1874_);
v___x_1877_ = ((size_t)0ULL);
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1874_, v_sz_1876_, v___x_1877_, v___x_1875_, v_a_1736_, v_a_1737_);
lean_dec_ref(v_content_1874_);
v_snd_1879_ = lean_ctor_get(v___x_1878_, 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1886_ == 0)
{
lean_object* v_unused_1887_; 
v_unused_1887_ = lean_ctor_get(v___x_1878_, 0);
lean_dec(v_unused_1887_);
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_snd_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1875_);
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_snd_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
case 7:
{
lean_object* v_name_1888_; lean_object* v_content_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v_snd_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1934_; 
v_name_1888_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_name_1888_);
v_content_1889_ = lean_ctor_get(v_x_1735_, 1);
lean_inc_ref(v_content_1889_);
lean_dec_ref(v_x_1735_);
v___x_1890_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__9));
v___x_1891_ = lean_string_append(v___x_1890_, v_name_1888_);
v___x_1892_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10));
v___x_1893_ = lean_string_append(v___x_1891_, v___x_1892_);
v___x_1894_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1893_, v_a_1737_);
lean_dec_ref(v___x_1893_);
v_snd_1895_ = lean_ctor_get(v___x_1894_, 1);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v___x_1894_, 0);
lean_dec(v_unused_1935_);
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1934_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_snd_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1934_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v_snd_1900_; lean_object* v___y_1919_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1921_ = lean_unsigned_to_nat(0u);
v___x_1922_ = lean_array_get_size(v_content_1889_);
v___x_1923_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11));
v___x_1924_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13);
v___x_1925_ = lean_nat_dec_lt(v___x_1921_, v___x_1922_);
if (v___x_1925_ == 0)
{
lean_dec_ref(v_content_1889_);
v_snd_1900_ = v___x_1924_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_nat_dec_le(v___x_1922_, v___x_1922_);
if (v___x_1927_ == 0)
{
if (v___x_1925_ == 0)
{
lean_dec_ref(v_content_1889_);
v_snd_1900_ = v___x_1924_;
goto v___jp_1899_;
}
else
{
size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = ((size_t)0ULL);
v___x_1929_ = lean_usize_of_nat(v___x_1922_);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1889_, v___x_1928_, v___x_1929_, v___x_1926_, v___x_1923_, v___x_1924_);
lean_dec_ref(v_content_1889_);
v___y_1919_ = v___x_1930_;
goto v___jp_1918_;
}
}
else
{
size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = ((size_t)0ULL);
v___x_1932_ = lean_usize_of_nat(v___x_1922_);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1889_, v___x_1931_, v___x_1932_, v___x_1926_, v___x_1923_, v___x_1924_);
lean_dec_ref(v_content_1889_);
v___y_1919_ = v___x_1933_;
goto v___jp_1918_;
}
}
v___jp_1899_:
{
lean_object* v_priorBlocks_1901_; lean_object* v_currentBlock_1902_; lean_object* v_footnotes_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1917_; 
v_priorBlocks_1901_ = lean_ctor_get(v_snd_1895_, 0);
v_currentBlock_1902_ = lean_ctor_get(v_snd_1895_, 1);
v_footnotes_1903_ = lean_ctor_get(v_snd_1895_, 2);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_snd_1895_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1905_ = v_snd_1895_;
v_isShared_1906_ = v_isSharedCheck_1917_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_footnotes_1903_);
lean_inc(v_currentBlock_1902_);
lean_inc(v_priorBlocks_1901_);
lean_dec(v_snd_1895_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1917_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1907_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(v_snd_1900_);
v___x_1908_ = lean_box(0);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v___x_1907_);
lean_ctor_set(v___x_1897_, 0, v_name_1888_);
v___x_1910_ = v___x_1897_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_name_1888_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v___x_1907_);
v___x_1910_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1911_ = lean_array_push(v_footnotes_1903_, v___x_1910_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 2, v___x_1911_);
v___x_1913_ = v___x_1905_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_priorBlocks_1901_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_currentBlock_1902_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1908_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
return v___x_1914_;
}
}
}
}
v___jp_1918_:
{
lean_object* v_snd_1920_; 
v_snd_1920_ = lean_ctor_get(v___y_1919_, 1);
lean_inc(v_snd_1920_);
lean_dec_ref(v___y_1919_);
v_snd_1900_ = v_snd_1920_;
goto v___jp_1899_;
}
}
}
case 8:
{
lean_object* v_alt_1936_; lean_object* v_url_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_alt_1936_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_alt_1936_);
v_url_1937_ = lean_ctor_get(v_x_1735_, 1);
lean_inc_ref(v_url_1937_);
lean_dec_ref(v_x_1735_);
v___x_1938_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__14));
v___x_1939_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1936_);
lean_dec_ref(v_alt_1936_);
v___x_1940_ = lean_string_append(v___x_1938_, v___x_1939_);
lean_dec_ref(v___x_1939_);
v___x_1941_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7));
v___x_1942_ = lean_string_append(v___x_1940_, v___x_1941_);
v___x_1943_ = lean_string_append(v___x_1942_, v_url_1937_);
lean_dec_ref(v_url_1937_);
v___x_1944_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_1945_ = lean_string_append(v___x_1943_, v___x_1944_);
v___x_1946_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1945_, v_a_1737_);
lean_dec_ref(v___x_1945_);
return v___x_1946_;
}
case 9:
{
lean_object* v_content_1947_; lean_object* v___x_1948_; size_t v_sz_1949_; size_t v___x_1950_; lean_object* v___x_1951_; lean_object* v_snd_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
v_content_1947_ = lean_ctor_get(v_x_1735_, 0);
lean_inc_ref(v_content_1947_);
lean_dec_ref(v_x_1735_);
v___x_1948_ = lean_box(0);
v_sz_1949_ = lean_array_size(v_content_1947_);
v___x_1950_ = ((size_t)0ULL);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1947_, v_sz_1949_, v___x_1950_, v___x_1948_, v_a_1736_, v_a_1737_);
lean_dec_ref(v_content_1947_);
v_snd_1952_ = lean_ctor_get(v___x_1951_, 1);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; 
v_unused_1960_ = lean_ctor_get(v___x_1951_, 0);
lean_dec(v_unused_1960_);
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_snd_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1948_);
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_snd_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
default: 
{
lean_object* v_content_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v_content_1961_ = lean_ctor_get(v_x_1735_, 1);
lean_inc_ref(v_content_1961_);
lean_dec_ref(v_x_1735_);
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = lean_array_get_size(v_content_1961_);
v___x_1964_ = lean_box(0);
v___x_1965_ = lean_nat_dec_lt(v___x_1962_, v___x_1963_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_dec_ref(v_content_1961_);
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set(v___x_1966_, 1, v_a_1737_);
return v___x_1966_;
}
else
{
uint8_t v___x_1967_; 
v___x_1967_ = lean_nat_dec_le(v___x_1963_, v___x_1963_);
if (v___x_1967_ == 0)
{
if (v___x_1965_ == 0)
{
lean_object* v___x_1968_; 
lean_dec_ref(v_content_1961_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1964_);
lean_ctor_set(v___x_1968_, 1, v_a_1737_);
return v___x_1968_;
}
else
{
size_t v___x_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = ((size_t)0ULL);
v___x_1970_ = lean_usize_of_nat(v___x_1963_);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1961_, v___x_1969_, v___x_1970_, v___x_1964_, v_a_1736_, v_a_1737_);
lean_dec_ref(v_content_1961_);
return v___x_1971_;
}
}
else
{
size_t v___x_1972_; size_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = ((size_t)0ULL);
v___x_1973_ = lean_usize_of_nat(v___x_1963_);
v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1961_, v___x_1972_, v___x_1973_, v___x_1964_, v_a_1736_, v_a_1737_);
lean_dec_ref(v_content_1961_);
return v___x_1974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(lean_object* v_as_1975_, size_t v_i_1976_, size_t v_stop_1977_, lean_object* v_b_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
uint8_t v___x_1981_; 
v___x_1981_ = lean_usize_dec_eq(v_i_1976_, v_stop_1977_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v_fst_1984_; lean_object* v_snd_1985_; size_t v___x_1986_; size_t v___x_1987_; 
v___x_1982_ = lean_array_uget_borrowed(v_as_1975_, v_i_1976_);
lean_inc(v___x_1982_);
v___x_1983_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_1982_, v___y_1979_, v___y_1980_);
v_fst_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_fst_1984_);
v_snd_1985_ = lean_ctor_get(v___x_1983_, 1);
lean_inc(v_snd_1985_);
lean_dec_ref(v___x_1983_);
v___x_1986_ = ((size_t)1ULL);
v___x_1987_ = lean_usize_add(v_i_1976_, v___x_1986_);
v_i_1976_ = v___x_1987_;
v_b_1978_ = v_fst_1984_;
v___y_1980_ = v_snd_1985_;
goto _start;
}
else
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_b_1978_);
lean_ctor_set(v___x_1989_, 1, v___y_1980_);
return v___x_1989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1990_, lean_object* v_i_1991_, lean_object* v_stop_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
size_t v_i_boxed_1996_; size_t v_stop_boxed_1997_; lean_object* v_res_1998_; 
v_i_boxed_1996_ = lean_unbox_usize(v_i_1991_);
lean_dec(v_i_1991_);
v_stop_boxed_1997_ = lean_unbox_usize(v_stop_1992_);
lean_dec(v_stop_1992_);
v_res_1998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_as_1990_, v_i_boxed_1996_, v_stop_boxed_1997_, v_b_1993_, v___y_1994_, v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec_ref(v_as_1990_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2___boxed(lean_object* v_as_1999_, lean_object* v_sz_2000_, lean_object* v_i_2001_, lean_object* v_b_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
size_t v_sz_boxed_2005_; size_t v_i_boxed_2006_; lean_object* v_res_2007_; 
v_sz_boxed_2005_ = lean_unbox_usize(v_sz_2000_);
lean_dec(v_sz_2000_);
v_i_boxed_2006_ = lean_unbox_usize(v_i_2001_);
lean_dec(v_i_2001_);
v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_as_1999_, v_sz_boxed_2005_, v_i_boxed_2006_, v_b_2002_, v___y_2003_, v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec_ref(v_as_1999_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___boxed(lean_object* v_x_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_x_2008_, v_a_2009_, v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(lean_object* v_as_2014_, size_t v_sz_2015_, size_t v_i_2016_, lean_object* v_b_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
uint8_t v___x_2020_; 
v___x_2020_ = lean_usize_dec_lt(v_i_2016_, v_sz_2015_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v_b_2017_);
lean_ctor_set(v___x_2021_, 1, v___y_2019_);
return v___x_2021_;
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2023_; lean_object* v_snd_2024_; lean_object* v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; 
v_a_2022_ = lean_array_uget_borrowed(v_as_2014_, v_i_2016_);
lean_inc_ref(v___y_2018_);
lean_inc(v_a_2022_);
v___x_2023_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v_a_2022_, v___y_2018_, v___y_2019_);
v_snd_2024_ = lean_ctor_get(v___x_2023_, 1);
lean_inc(v_snd_2024_);
lean_dec_ref(v___x_2023_);
v___x_2025_ = lean_box(0);
v___x_2026_ = ((size_t)1ULL);
v___x_2027_ = lean_usize_add(v_i_2016_, v___x_2026_);
v_i_2016_ = v___x_2027_;
v_b_2017_ = v___x_2025_;
v___y_2019_ = v_snd_2024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(lean_object* v_as_2029_, size_t v_sz_2030_, size_t v_i_2031_, lean_object* v_b_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_usize_dec_lt(v_i_2031_, v_sz_2030_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
lean_dec_ref(v___y_2033_);
v___x_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2036_, 0, v_b_2032_);
lean_ctor_set(v___x_2036_, 1, v___y_2034_);
return v___x_2036_;
}
else
{
uint8_t v_inEmph_2037_; uint8_t v_inBold_2038_; uint8_t v_inLink_2039_; lean_object* v_linePrefix_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v_snd_2044_; lean_object* v___x_2045_; lean_object* v_a_2046_; size_t v_sz_2047_; size_t v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v_snd_2053_; size_t v___x_2054_; size_t v___x_2055_; 
v_inEmph_2037_ = lean_ctor_get_uint8(v___y_2033_, sizeof(void*)*1);
v_inBold_2038_ = lean_ctor_get_uint8(v___y_2033_, sizeof(void*)*1 + 1);
v_inLink_2039_ = lean_ctor_get_uint8(v___y_2033_, sizeof(void*)*1 + 2);
v_linePrefix_2040_ = lean_ctor_get(v___y_2033_, 0);
v___x_2041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0));
lean_inc_ref(v_linePrefix_2040_);
v___x_2042_ = lean_string_append(v_linePrefix_2040_, v___x_2041_);
v___x_2043_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2042_, v___y_2034_);
lean_dec_ref(v___x_2042_);
v_snd_2044_ = lean_ctor_get(v___x_2043_, 1);
lean_inc(v_snd_2044_);
lean_dec_ref(v___x_2043_);
v___x_2045_ = lean_box(0);
v_a_2046_ = lean_array_uget_borrowed(v_as_2029_, v_i_2031_);
v_sz_2047_ = lean_array_size(v_a_2046_);
v___x_2048_ = ((size_t)0ULL);
v___x_2049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
lean_inc_ref(v_linePrefix_2040_);
v___x_2050_ = lean_string_append(v_linePrefix_2040_, v___x_2049_);
v___x_2051_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*1, v_inEmph_2037_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*1 + 1, v_inBold_2038_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*1 + 2, v_inLink_2039_);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_a_2046_, v_sz_2047_, v___x_2048_, v___x_2045_, v___x_2051_, v_snd_2044_);
lean_dec_ref(v___x_2051_);
v_snd_2053_ = lean_ctor_get(v___x_2052_, 1);
lean_inc(v_snd_2053_);
lean_dec_ref(v___x_2052_);
v___x_2054_ = ((size_t)1ULL);
v___x_2055_ = lean_usize_add(v_i_2031_, v___x_2054_);
v_i_2031_ = v___x_2055_;
v_b_2032_ = v___x_2045_;
v___y_2034_ = v_snd_2053_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(lean_object* v_as_2058_, size_t v_sz_2059_, size_t v_i_2060_, lean_object* v_b_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
uint8_t v___x_2064_; 
v___x_2064_ = lean_usize_dec_lt(v_i_2060_, v_sz_2059_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
lean_dec_ref(v___y_2062_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v_b_2061_);
lean_ctor_set(v___x_2065_, 1, v___y_2063_);
return v___x_2065_;
}
else
{
uint8_t v_inEmph_2066_; uint8_t v_inBold_2067_; uint8_t v_inLink_2068_; lean_object* v_linePrefix_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v_snd_2075_; lean_object* v_a_2076_; lean_object* v___x_2077_; size_t v_sz_2078_; size_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v_snd_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; size_t v___x_2087_; size_t v___x_2088_; 
v_inEmph_2066_ = lean_ctor_get_uint8(v___y_2062_, sizeof(void*)*1);
v_inBold_2067_ = lean_ctor_get_uint8(v___y_2062_, sizeof(void*)*1 + 1);
v_inLink_2068_ = lean_ctor_get_uint8(v___y_2062_, sizeof(void*)*1 + 2);
v_linePrefix_2069_ = lean_ctor_get(v___y_2062_, 0);
lean_inc(v_b_2061_);
v___x_2070_ = l_Nat_reprFast(v_b_2061_);
v___x_2071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0));
v___x_2072_ = lean_string_append(v___x_2070_, v___x_2071_);
lean_inc_ref(v_linePrefix_2069_);
v___x_2073_ = lean_string_append(v_linePrefix_2069_, v___x_2072_);
lean_dec_ref(v___x_2072_);
v___x_2074_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2073_, v___y_2063_);
lean_dec_ref(v___x_2073_);
v_snd_2075_ = lean_ctor_get(v___x_2074_, 1);
lean_inc(v_snd_2075_);
lean_dec_ref(v___x_2074_);
v_a_2076_ = lean_array_uget_borrowed(v_as_2058_, v_i_2060_);
v___x_2077_ = lean_box(0);
v_sz_2078_ = lean_array_size(v_a_2076_);
v___x_2079_ = ((size_t)0ULL);
v___x_2080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
lean_inc_ref(v_linePrefix_2069_);
v___x_2081_ = lean_string_append(v_linePrefix_2069_, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*1, v_inEmph_2066_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*1 + 1, v_inBold_2067_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*1 + 2, v_inLink_2068_);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_a_2076_, v_sz_2078_, v___x_2079_, v___x_2077_, v___x_2082_, v_snd_2075_);
lean_dec_ref(v___x_2082_);
v_snd_2084_ = lean_ctor_get(v___x_2083_, 1);
lean_inc(v_snd_2084_);
lean_dec_ref(v___x_2083_);
v___x_2085_ = lean_unsigned_to_nat(1u);
v___x_2086_ = lean_nat_add(v_b_2061_, v___x_2085_);
lean_dec(v_b_2061_);
v___x_2087_ = ((size_t)1ULL);
v___x_2088_ = lean_usize_add(v_i_2060_, v___x_2087_);
v_i_2060_ = v___x_2088_;
v_b_2061_ = v___x_2086_;
v___y_2063_ = v_snd_2084_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(lean_object* v_as_2093_, size_t v_sz_2094_, size_t v_i_2095_, lean_object* v_b_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v___x_2099_; 
v___x_2099_ = lean_usize_dec_lt(v_i_2095_, v_sz_2094_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; 
lean_dec_ref(v___y_2097_);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v_b_2096_);
lean_ctor_set(v___x_2100_, 1, v___y_2098_);
return v___x_2100_;
}
else
{
uint8_t v_inEmph_2101_; uint8_t v_inBold_2102_; uint8_t v_inLink_2103_; lean_object* v_linePrefix_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v_snd_2108_; lean_object* v_a_2109_; lean_object* v_term_2110_; lean_object* v_desc_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v_snd_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v_snd_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v_snd_2123_; lean_object* v___x_2124_; lean_object* v_snd_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v_snd_2128_; lean_object* v___x_2129_; size_t v___x_2130_; size_t v___x_2131_; 
v_inEmph_2101_ = lean_ctor_get_uint8(v___y_2097_, sizeof(void*)*1);
v_inBold_2102_ = lean_ctor_get_uint8(v___y_2097_, sizeof(void*)*1 + 1);
v_inLink_2103_ = lean_ctor_get_uint8(v___y_2097_, sizeof(void*)*1 + 2);
v_linePrefix_2104_ = lean_ctor_get(v___y_2097_, 0);
v___x_2105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0));
lean_inc_ref(v_linePrefix_2104_);
v___x_2106_ = lean_string_append(v_linePrefix_2104_, v___x_2105_);
v___x_2107_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2106_, v___y_2098_);
lean_dec_ref(v___x_2106_);
v_snd_2108_ = lean_ctor_get(v___x_2107_, 1);
lean_inc(v_snd_2108_);
lean_dec_ref(v___x_2107_);
v_a_2109_ = lean_array_uget_borrowed(v_as_2093_, v_i_2095_);
v_term_2110_ = lean_ctor_get(v_a_2109_, 0);
v_desc_2111_ = lean_ctor_get(v_a_2109_, 1);
lean_inc_ref(v_term_2110_);
v___x_2112_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_term_2110_);
v___x_2113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
lean_inc_ref(v_linePrefix_2104_);
v___x_2114_ = lean_string_append(v_linePrefix_2104_, v___x_2113_);
lean_inc_ref(v___x_2114_);
v___x_2115_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1, v_inEmph_2101_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1 + 1, v_inBold_2102_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1 + 2, v_inLink_2103_);
v___x_2116_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_2112_, v___x_2115_, v_snd_2108_);
v_snd_2117_ = lean_ctor_get(v___x_2116_, 1);
lean_inc(v_snd_2117_);
lean_dec_ref(v___x_2116_);
v___x_2118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__1));
v___x_2119_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_2118_, v___x_2115_, v_snd_2117_);
v_snd_2120_ = lean_ctor_get(v___x_2119_, 1);
lean_inc(v_snd_2120_);
lean_dec_ref(v___x_2119_);
v___x_2121_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2122_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2121_, v_snd_2120_);
v_snd_2123_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_snd_2123_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2114_, v_snd_2123_);
lean_dec_ref(v___x_2114_);
v_snd_2125_ = lean_ctor_get(v___x_2124_, 1);
lean_inc(v_snd_2125_);
lean_dec_ref(v___x_2124_);
lean_inc_ref(v_desc_2111_);
v___x_2126_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_desc_2111_);
v___x_2127_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v___x_2126_, v___x_2115_, v_snd_2125_);
v_snd_2128_ = lean_ctor_get(v___x_2127_, 1);
lean_inc(v_snd_2128_);
lean_dec_ref(v___x_2127_);
v___x_2129_ = lean_box(0);
v___x_2130_ = ((size_t)1ULL);
v___x_2131_ = lean_usize_add(v_i_2095_, v___x_2130_);
v_i_2095_ = v___x_2131_;
v_b_2096_ = v___x_2129_;
v___y_2098_ = v_snd_2128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(lean_object* v_x_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
switch(lean_obj_tag(v_x_2134_))
{
case 0:
{
lean_object* v_contents_2137_; lean_object* v___x_2138_; size_t v_sz_2139_; size_t v___x_2140_; lean_object* v___x_2141_; lean_object* v_snd_2142_; lean_object* v___x_2143_; 
v_contents_2137_ = lean_ctor_get(v_x_2134_, 0);
lean_inc_ref(v_contents_2137_);
lean_dec_ref(v_x_2134_);
v___x_2138_ = lean_box(0);
v_sz_2139_ = lean_array_size(v_contents_2137_);
v___x_2140_ = ((size_t)0ULL);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_contents_2137_, v_sz_2139_, v___x_2140_, v___x_2138_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec_ref(v_contents_2137_);
v_snd_2142_ = lean_ctor_get(v___x_2141_, 1);
lean_inc(v_snd_2142_);
lean_dec_ref(v___x_2141_);
v___x_2143_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2142_);
return v___x_2143_;
}
case 1:
{
lean_object* v_content_2144_; lean_object* v___y_2146_; lean_object* v___y_2147_; uint8_t v___y_2155_; lean_object* v_currentBlock_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v_content_2144_ = lean_ctor_get(v_x_2134_, 0);
lean_inc_ref(v_content_2144_);
lean_dec_ref(v_x_2134_);
v_currentBlock_2159_ = lean_ctor_get(v_a_2136_, 1);
v___x_2160_ = lean_string_utf8_byte_size(v_currentBlock_2159_);
v___x_2161_ = lean_unsigned_to_nat(0u);
v___x_2162_ = lean_nat_dec_eq(v___x_2160_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2163_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2164_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_2165_ = lean_nat_dec_le(v___x_2164_, v___x_2160_);
if (v___x_2165_ == 0)
{
v___y_2155_ = v___x_2162_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_nat_sub(v___x_2160_, v___x_2164_);
v___x_2167_ = lean_string_memcmp(v_currentBlock_2159_, v___x_2163_, v___x_2166_, v___x_2161_, v___x_2164_);
lean_dec(v___x_2166_);
v___y_2155_ = v___x_2167_;
goto v___jp_2154_;
}
}
else
{
v___y_2155_ = v___x_2162_;
goto v___jp_2154_;
}
v___jp_2145_:
{
lean_object* v_linePrefix_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v_snd_2152_; lean_object* v___x_2153_; 
v_linePrefix_2148_ = lean_ctor_get(v___y_2146_, 0);
lean_inc_ref(v_linePrefix_2148_);
lean_dec_ref(v___y_2146_);
v___x_2149_ = lean_string_length(v_linePrefix_2148_);
lean_dec_ref(v_linePrefix_2148_);
v___x_2150_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v___x_2149_, v_content_2144_);
lean_dec_ref(v_content_2144_);
v___x_2151_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2150_, v___y_2147_);
lean_dec_ref(v___x_2150_);
v_snd_2152_ = lean_ctor_get(v___x_2151_, 1);
lean_inc(v_snd_2152_);
lean_dec_ref(v___x_2151_);
v___x_2153_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2152_);
return v___x_2153_;
}
v___jp_2154_:
{
if (v___y_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v_snd_2158_; 
v___x_2156_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2157_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2156_, v_a_2136_);
v_snd_2158_ = lean_ctor_get(v___x_2157_, 1);
lean_inc(v_snd_2158_);
lean_dec_ref(v___x_2157_);
v___y_2146_ = v_a_2135_;
v___y_2147_ = v_snd_2158_;
goto v___jp_2145_;
}
else
{
v___y_2146_ = v_a_2135_;
v___y_2147_ = v_a_2136_;
goto v___jp_2145_;
}
}
}
case 2:
{
lean_object* v_items_2168_; lean_object* v___x_2169_; size_t v_sz_2170_; size_t v___x_2171_; lean_object* v___x_2172_; lean_object* v_snd_2173_; lean_object* v___x_2174_; 
v_items_2168_ = lean_ctor_get(v_x_2134_, 0);
lean_inc_ref(v_items_2168_);
lean_dec_ref(v_x_2134_);
v___x_2169_ = lean_box(0);
v_sz_2170_ = lean_array_size(v_items_2168_);
v___x_2171_ = ((size_t)0ULL);
v___x_2172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_items_2168_, v_sz_2170_, v___x_2171_, v___x_2169_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_items_2168_);
v_snd_2173_ = lean_ctor_get(v___x_2172_, 1);
lean_inc(v_snd_2173_);
lean_dec_ref(v___x_2172_);
v___x_2174_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2173_);
return v___x_2174_;
}
case 3:
{
lean_object* v_start_2175_; lean_object* v_items_2176_; lean_object* v___y_2178_; lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v_start_2175_ = lean_ctor_get(v_x_2134_, 0);
lean_inc(v_start_2175_);
v_items_2176_ = lean_ctor_get(v_x_2134_, 1);
lean_inc_ref(v_items_2176_);
lean_dec_ref(v_x_2134_);
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = l_Int_toNat(v_start_2175_);
lean_dec(v_start_2175_);
v___x_2186_ = lean_nat_dec_le(v___x_2184_, v___x_2185_);
if (v___x_2186_ == 0)
{
lean_dec(v___x_2185_);
v___y_2178_ = v___x_2184_;
goto v___jp_2177_;
}
else
{
v___y_2178_ = v___x_2185_;
goto v___jp_2177_;
}
v___jp_2177_:
{
size_t v_sz_2179_; size_t v___x_2180_; lean_object* v___x_2181_; lean_object* v_snd_2182_; lean_object* v___x_2183_; 
v_sz_2179_ = lean_array_size(v_items_2176_);
v___x_2180_ = ((size_t)0ULL);
v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_items_2176_, v_sz_2179_, v___x_2180_, v___y_2178_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_items_2176_);
v_snd_2182_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_snd_2182_);
lean_dec_ref(v___x_2181_);
v___x_2183_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2182_);
return v___x_2183_;
}
}
case 4:
{
lean_object* v_items_2187_; lean_object* v___x_2188_; size_t v_sz_2189_; size_t v___x_2190_; lean_object* v___x_2191_; lean_object* v_snd_2192_; lean_object* v___x_2193_; 
v_items_2187_ = lean_ctor_get(v_x_2134_, 0);
lean_inc_ref(v_items_2187_);
lean_dec_ref(v_x_2134_);
v___x_2188_ = lean_box(0);
v_sz_2189_ = lean_array_size(v_items_2187_);
v___x_2190_ = ((size_t)0ULL);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_items_2187_, v_sz_2189_, v___x_2190_, v___x_2188_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_items_2187_);
v_snd_2192_ = lean_ctor_get(v___x_2191_, 1);
lean_inc(v_snd_2192_);
lean_dec_ref(v___x_2191_);
v___x_2193_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2192_);
return v___x_2193_;
}
case 5:
{
lean_object* v_items_2194_; uint8_t v_inEmph_2195_; uint8_t v_inBold_2196_; uint8_t v_inLink_2197_; lean_object* v_linePrefix_2198_; lean_object* v___x_2199_; size_t v_sz_2200_; size_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_snd_2206_; lean_object* v___x_2207_; 
v_items_2194_ = lean_ctor_get(v_x_2134_, 0);
lean_inc_ref(v_items_2194_);
lean_dec_ref(v_x_2134_);
v_inEmph_2195_ = lean_ctor_get_uint8(v_a_2135_, sizeof(void*)*1);
v_inBold_2196_ = lean_ctor_get_uint8(v_a_2135_, sizeof(void*)*1 + 1);
v_inLink_2197_ = lean_ctor_get_uint8(v_a_2135_, sizeof(void*)*1 + 2);
v_linePrefix_2198_ = lean_ctor_get(v_a_2135_, 0);
lean_inc_ref(v_linePrefix_2198_);
lean_dec_ref(v_a_2135_);
v___x_2199_ = lean_box(0);
v_sz_2200_ = lean_array_size(v_items_2194_);
v___x_2201_ = ((size_t)0ULL);
v___x_2202_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0));
v___x_2203_ = lean_string_append(v_linePrefix_2198_, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1, v_inEmph_2195_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1 + 1, v_inBold_2196_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1 + 2, v_inLink_2197_);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_items_2194_, v_sz_2200_, v___x_2201_, v___x_2199_, v___x_2204_, v_a_2136_);
lean_dec_ref(v___x_2204_);
lean_dec_ref(v_items_2194_);
v_snd_2206_ = lean_ctor_get(v___x_2205_, 1);
lean_inc(v_snd_2206_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2206_);
return v___x_2207_;
}
case 6:
{
lean_object* v_content_2208_; lean_object* v___x_2209_; size_t v_sz_2210_; size_t v___x_2211_; lean_object* v___x_2212_; lean_object* v_snd_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_content_2208_ = lean_ctor_get(v_x_2134_, 0);
lean_inc_ref(v_content_2208_);
lean_dec_ref(v_x_2134_);
v___x_2209_ = lean_box(0);
v_sz_2210_ = lean_array_size(v_content_2208_);
v___x_2211_ = ((size_t)0ULL);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_content_2208_, v_sz_2210_, v___x_2211_, v___x_2209_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec_ref(v_content_2208_);
v_snd_2213_ = lean_ctor_get(v___x_2212_, 1);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v___x_2212_, 0);
lean_dec(v_unused_2221_);
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_snd_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2209_);
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_snd_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
default: 
{
lean_object* v_content_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2243_; 
v_content_2222_ = lean_ctor_get(v_x_2134_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_x_2134_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; 
v_unused_2244_ = lean_ctor_get(v_x_2134_, 0);
lean_dec(v_unused_2244_);
v___x_2224_ = v_x_2134_;
v_isShared_2225_ = v_isSharedCheck_2243_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_content_2222_);
lean_dec(v_x_2134_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2243_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = lean_array_get_size(v_content_2222_);
v___x_2228_ = lean_box(0);
v___x_2229_ = lean_nat_dec_lt(v___x_2226_, v___x_2227_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2231_; 
lean_dec_ref(v_content_2222_);
lean_dec_ref(v_a_2135_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set_tag(v___x_2224_, 0);
lean_ctor_set(v___x_2224_, 1, v_a_2136_);
lean_ctor_set(v___x_2224_, 0, v___x_2228_);
v___x_2231_ = v___x_2224_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_a_2136_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
else
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_nat_dec_le(v___x_2227_, v___x_2227_);
if (v___x_2233_ == 0)
{
if (v___x_2229_ == 0)
{
lean_object* v___x_2235_; 
lean_dec_ref(v_content_2222_);
lean_dec_ref(v_a_2135_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set_tag(v___x_2224_, 0);
lean_ctor_set(v___x_2224_, 1, v_a_2136_);
lean_ctor_set(v___x_2224_, 0, v___x_2228_);
v___x_2235_ = v___x_2224_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_a_2136_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
else
{
size_t v___x_2237_; size_t v___x_2238_; lean_object* v___x_2239_; 
lean_del_object(v___x_2224_);
v___x_2237_ = ((size_t)0ULL);
v___x_2238_ = lean_usize_of_nat(v___x_2227_);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_content_2222_, v___x_2237_, v___x_2238_, v___x_2228_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec_ref(v_content_2222_);
return v___x_2239_;
}
}
else
{
size_t v___x_2240_; size_t v___x_2241_; lean_object* v___x_2242_; 
lean_del_object(v___x_2224_);
v___x_2240_ = ((size_t)0ULL);
v___x_2241_ = lean_usize_of_nat(v___x_2227_);
v___x_2242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_content_2222_, v___x_2240_, v___x_2241_, v___x_2228_, v_a_2135_, v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec_ref(v_content_2222_);
return v___x_2242_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(lean_object* v_as_2245_, size_t v_i_2246_, size_t v_stop_2247_, lean_object* v_b_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_usize_dec_eq(v_i_2246_, v_stop_2247_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v_fst_2254_; lean_object* v_snd_2255_; size_t v___x_2256_; size_t v___x_2257_; 
v___x_2252_ = lean_array_uget_borrowed(v_as_2245_, v_i_2246_);
lean_inc_ref(v___y_2249_);
lean_inc(v___x_2252_);
v___x_2253_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v___x_2252_, v___y_2249_, v___y_2250_);
v_fst_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_fst_2254_);
v_snd_2255_ = lean_ctor_get(v___x_2253_, 1);
lean_inc(v_snd_2255_);
lean_dec_ref(v___x_2253_);
v___x_2256_ = ((size_t)1ULL);
v___x_2257_ = lean_usize_add(v_i_2246_, v___x_2256_);
v_i_2246_ = v___x_2257_;
v_b_2248_ = v_fst_2254_;
v___y_2250_ = v_snd_2255_;
goto _start;
}
else
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2259_, 0, v_b_2248_);
lean_ctor_set(v___x_2259_, 1, v___y_2250_);
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___boxed(lean_object* v_as_2260_, lean_object* v_i_2261_, lean_object* v_stop_2262_, lean_object* v_b_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
size_t v_i_boxed_2266_; size_t v_stop_boxed_2267_; lean_object* v_res_2268_; 
v_i_boxed_2266_ = lean_unbox_usize(v_i_2261_);
lean_dec(v_i_2261_);
v_stop_boxed_2267_ = lean_unbox_usize(v_stop_2262_);
lean_dec(v_stop_2262_);
v_res_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_as_2260_, v_i_boxed_2266_, v_stop_boxed_2267_, v_b_2263_, v___y_2264_, v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_as_2260_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2___boxed(lean_object* v_as_2269_, lean_object* v_sz_2270_, lean_object* v_i_2271_, lean_object* v_b_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
size_t v_sz_boxed_2275_; size_t v_i_boxed_2276_; lean_object* v_res_2277_; 
v_sz_boxed_2275_ = lean_unbox_usize(v_sz_2270_);
lean_dec(v_sz_2270_);
v_i_boxed_2276_ = lean_unbox_usize(v_i_2271_);
lean_dec(v_i_2271_);
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_as_2269_, v_sz_boxed_2275_, v_i_boxed_2276_, v_b_2272_, v___y_2273_, v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v_as_2269_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___boxed(lean_object* v_as_2278_, lean_object* v_sz_2279_, lean_object* v_i_2280_, lean_object* v_b_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
size_t v_sz_boxed_2284_; size_t v_i_boxed_2285_; lean_object* v_res_2286_; 
v_sz_boxed_2284_ = lean_unbox_usize(v_sz_2279_);
lean_dec(v_sz_2279_);
v_i_boxed_2285_ = lean_unbox_usize(v_i_2280_);
lean_dec(v_i_2280_);
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_as_2278_, v_sz_boxed_2284_, v_i_boxed_2285_, v_b_2281_, v___y_2282_, v___y_2283_);
lean_dec_ref(v_as_2278_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___boxed(lean_object* v_as_2287_, lean_object* v_sz_2288_, lean_object* v_i_2289_, lean_object* v_b_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
size_t v_sz_boxed_2293_; size_t v_i_boxed_2294_; lean_object* v_res_2295_; 
v_sz_boxed_2293_ = lean_unbox_usize(v_sz_2288_);
lean_dec(v_sz_2288_);
v_i_boxed_2294_ = lean_unbox_usize(v_i_2289_);
lean_dec(v_i_2289_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_as_2287_, v_sz_boxed_2293_, v_i_boxed_2294_, v_b_2290_, v___y_2291_, v___y_2292_);
lean_dec_ref(v_as_2287_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___boxed(lean_object* v_as_2296_, lean_object* v_sz_2297_, lean_object* v_i_2298_, lean_object* v_b_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
size_t v_sz_boxed_2302_; size_t v_i_boxed_2303_; lean_object* v_res_2304_; 
v_sz_boxed_2302_ = lean_unbox_usize(v_sz_2297_);
lean_dec(v_sz_2297_);
v_i_boxed_2303_ = lean_unbox_usize(v_i_2298_);
lean_dec(v_i_2298_);
v_res_2304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_as_2296_, v_sz_boxed_2302_, v_i_boxed_2303_, v_b_2299_, v___y_2300_, v___y_2301_);
lean_dec_ref(v_as_2296_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(lean_object* v_x_2305_, lean_object* v_x_2306_){
_start:
{
lean_object* v_zero_2307_; uint8_t v_isZero_2308_; 
v_zero_2307_ = lean_unsigned_to_nat(0u);
v_isZero_2308_ = lean_nat_dec_eq(v_x_2305_, v_zero_2307_);
if (v_isZero_2308_ == 1)
{
lean_dec(v_x_2305_);
return v_x_2306_;
}
else
{
uint32_t v___x_2309_; lean_object* v_one_2310_; lean_object* v_n_2311_; lean_object* v___x_2312_; 
v___x_2309_ = 35;
v_one_2310_ = lean_unsigned_to_nat(1u);
v_n_2311_ = lean_nat_sub(v_x_2305_, v_one_2310_);
lean_dec(v_x_2305_);
v___x_2312_ = lean_string_push(v_x_2306_, v___x_2309_);
v_x_2305_ = v_n_2311_;
v_x_2306_ = v___x_2312_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(lean_object* v_level_2315_, lean_object* v_part_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_snd_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v_snd_2327_; lean_object* v_title_2328_; lean_object* v_content_2329_; lean_object* v_subParts_2330_; lean_object* v___x_2331_; size_t v_sz_2332_; size_t v___x_2333_; lean_object* v___x_2334_; lean_object* v_snd_2335_; lean_object* v___x_2336_; lean_object* v_snd_2337_; size_t v_sz_2338_; lean_object* v___x_2339_; lean_object* v_snd_2340_; lean_object* v___x_2341_; lean_object* v_snd_2342_; size_t v_sz_2343_; lean_object* v___x_2344_; lean_object* v_snd_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
v___x_2319_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_2320_ = lean_unsigned_to_nat(1u);
v___x_2321_ = lean_nat_add(v_level_2315_, v___x_2320_);
lean_inc(v___x_2321_);
v___x_2322_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v___x_2321_, v___x_2319_);
v___x_2323_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2322_, v_a_2318_);
lean_dec_ref(v___x_2322_);
v_snd_2324_ = lean_ctor_get(v___x_2323_, 1);
lean_inc(v_snd_2324_);
lean_dec_ref(v___x_2323_);
v___x_2325_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0));
v___x_2326_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2325_, v_snd_2324_);
v_snd_2327_ = lean_ctor_get(v___x_2326_, 1);
lean_inc(v_snd_2327_);
lean_dec_ref(v___x_2326_);
v_title_2328_ = lean_ctor_get(v_part_2316_, 0);
v_content_2329_ = lean_ctor_get(v_part_2316_, 3);
v_subParts_2330_ = lean_ctor_get(v_part_2316_, 4);
v___x_2331_ = lean_box(0);
v_sz_2332_ = lean_array_size(v_title_2328_);
v___x_2333_ = ((size_t)0ULL);
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_title_2328_, v_sz_2332_, v___x_2333_, v___x_2331_, v_a_2317_, v_snd_2327_);
v_snd_2335_ = lean_ctor_get(v___x_2334_, 1);
lean_inc(v_snd_2335_);
lean_dec_ref(v___x_2334_);
v___x_2336_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2335_);
v_snd_2337_ = lean_ctor_get(v___x_2336_, 1);
lean_inc(v_snd_2337_);
lean_dec_ref(v___x_2336_);
v_sz_2338_ = lean_array_size(v_content_2329_);
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_content_2329_, v_sz_2338_, v___x_2333_, v___x_2331_, v_a_2317_, v_snd_2337_);
v_snd_2340_ = lean_ctor_get(v___x_2339_, 1);
lean_inc(v_snd_2340_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2340_);
v_snd_2342_ = lean_ctor_get(v___x_2341_, 1);
lean_inc(v_snd_2342_);
lean_dec_ref(v___x_2341_);
v_sz_2343_ = lean_array_size(v_subParts_2330_);
v___x_2344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2321_, v_subParts_2330_, v_sz_2343_, v___x_2333_, v___x_2331_, v_a_2317_, v_snd_2342_);
lean_dec(v___x_2321_);
v_snd_2345_ = lean_ctor_get(v___x_2344_, 1);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; 
v_unused_2353_ = lean_ctor_get(v___x_2344_, 0);
lean_dec(v_unused_2353_);
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_snd_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2331_);
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_snd_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(lean_object* v___x_2354_, lean_object* v_as_2355_, size_t v_sz_2356_, size_t v_i_2357_, lean_object* v_b_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
uint8_t v___x_2361_; 
v___x_2361_ = lean_usize_dec_lt(v_i_2357_, v_sz_2356_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v_b_2358_);
lean_ctor_set(v___x_2362_, 1, v___y_2360_);
return v___x_2362_;
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2364_; lean_object* v_snd_2365_; lean_object* v___x_2366_; size_t v___x_2367_; size_t v___x_2368_; 
v_a_2363_ = lean_array_uget_borrowed(v_as_2355_, v_i_2357_);
v___x_2364_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v___x_2354_, v_a_2363_, v___y_2359_, v___y_2360_);
v_snd_2365_ = lean_ctor_get(v___x_2364_, 1);
lean_inc(v_snd_2365_);
lean_dec_ref(v___x_2364_);
v___x_2366_ = lean_box(0);
v___x_2367_ = ((size_t)1ULL);
v___x_2368_ = lean_usize_add(v_i_2357_, v___x_2367_);
v_i_2357_ = v___x_2368_;
v_b_2358_ = v___x_2366_;
v___y_2360_ = v_snd_2365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg___boxed(lean_object* v___x_2370_, lean_object* v_as_2371_, lean_object* v_sz_2372_, lean_object* v_i_2373_, lean_object* v_b_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
size_t v_sz_boxed_2377_; size_t v_i_boxed_2378_; lean_object* v_res_2379_; 
v_sz_boxed_2377_ = lean_unbox_usize(v_sz_2372_);
lean_dec(v_sz_2372_);
v_i_boxed_2378_ = lean_unbox_usize(v_i_2373_);
lean_dec(v_i_2373_);
v_res_2379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2370_, v_as_2371_, v_sz_boxed_2377_, v_i_boxed_2378_, v_b_2374_, v___y_2375_, v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec_ref(v_as_2371_);
lean_dec(v___x_2370_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___boxed(lean_object* v_level_2380_, lean_object* v_part_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_level_2380_, v_part_2381_, v_a_2382_, v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec_ref(v_part_2381_);
lean_dec(v_level_2380_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(lean_object* v_as_2385_, size_t v_sz_2386_, size_t v_i_2387_, lean_object* v_b_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_usize_dec_lt(v_i_2387_, v_sz_2386_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v_b_2388_);
lean_ctor_set(v___x_2392_, 1, v___y_2390_);
return v___x_2392_;
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v_snd_2396_; lean_object* v___x_2397_; size_t v___x_2398_; size_t v___x_2399_; 
v_a_2393_ = lean_array_uget_borrowed(v_as_2385_, v_i_2387_);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v___x_2394_, v_a_2393_, v___y_2389_, v___y_2390_);
v_snd_2396_ = lean_ctor_get(v___x_2395_, 1);
lean_inc(v_snd_2396_);
lean_dec_ref(v___x_2395_);
v___x_2397_ = lean_box(0);
v___x_2398_ = ((size_t)1ULL);
v___x_2399_ = lean_usize_add(v_i_2387_, v___x_2398_);
v_i_2387_ = v___x_2399_;
v_b_2388_ = v___x_2397_;
v___y_2390_ = v_snd_2396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3___boxed(lean_object* v_as_2401_, lean_object* v_sz_2402_, lean_object* v_i_2403_, lean_object* v_b_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
size_t v_sz_boxed_2407_; size_t v_i_boxed_2408_; lean_object* v_res_2409_; 
v_sz_boxed_2407_ = lean_unbox_usize(v_sz_2402_);
lean_dec(v_sz_2402_);
v_i_boxed_2408_ = lean_unbox_usize(v_i_2403_);
lean_dec(v_i_2403_);
v_res_2409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(v_as_2401_, v_sz_boxed_2407_, v_i_boxed_2408_, v_b_2404_, v___y_2405_, v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec_ref(v_as_2401_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(lean_object* v_text_2410_, size_t v_sz_2411_, size_t v___x_2412_, lean_object* v___x_2413_, lean_object* v_subsections_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2417_; lean_object* v_snd_2418_; size_t v_sz_2419_; lean_object* v___x_2420_; lean_object* v_snd_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_text_2410_, v_sz_2411_, v___x_2412_, v___x_2413_, v___y_2415_, v___y_2416_);
v_snd_2418_ = lean_ctor_get(v___x_2417_, 1);
lean_inc(v_snd_2418_);
lean_dec_ref(v___x_2417_);
v_sz_2419_ = lean_array_size(v_subsections_2414_);
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(v_subsections_2414_, v_sz_2419_, v___x_2412_, v___x_2413_, v___y_2415_, v_snd_2418_);
v_snd_2421_ = lean_ctor_get(v___x_2420_, 1);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2428_ == 0)
{
lean_object* v_unused_2429_; 
v_unused_2429_ = lean_ctor_get(v___x_2420_, 0);
lean_dec(v_unused_2429_);
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_snd_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2413_);
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_snd_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed(lean_object* v_text_2430_, lean_object* v_sz_2431_, lean_object* v___x_2432_, lean_object* v___x_2433_, lean_object* v_subsections_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
size_t v_sz_boxed_2437_; size_t v___x_10662__boxed_2438_; lean_object* v_res_2439_; 
v_sz_boxed_2437_ = lean_unbox_usize(v_sz_2431_);
lean_dec(v_sz_2431_);
v___x_10662__boxed_2438_ = lean_unbox_usize(v___x_2432_);
lean_dec(v___x_2432_);
v_res_2439_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(v_text_2430_, v_sz_boxed_2437_, v___x_10662__boxed_2438_, v___x_2433_, v_subsections_2434_, v___y_2435_, v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec_ref(v_subsections_2434_);
lean_dec_ref(v_text_2430_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(lean_object* v_a_2442_){
_start:
{
lean_object* v_text_2443_; lean_object* v_subsections_2444_; lean_object* v___x_2445_; size_t v_sz_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___f_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_text_2443_ = lean_ctor_get(v_a_2442_, 0);
lean_inc_ref(v_text_2443_);
v_subsections_2444_ = lean_ctor_get(v_a_2442_, 1);
lean_inc_ref(v_subsections_2444_);
lean_dec_ref(v_a_2442_);
v___x_2445_ = lean_box(0);
v_sz_2446_ = lean_array_size(v_text_2443_);
v___x_2447_ = lean_box_usize(v_sz_2446_);
v___x_2448_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1));
v___f_2449_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2449_, 0, v_text_2443_);
lean_closure_set(v___f_2449_, 1, v___x_2447_);
lean_closure_set(v___f_2449_, 2, v___x_2448_);
lean_closure_set(v___f_2449_, 3, v___x_2445_);
lean_closure_set(v___f_2449_, 4, v_subsections_2444_);
v___x_2450_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11));
v___x_2451_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13);
v___x_2452_ = l_Lean_Doc_MarkdownM_run_x27(v___f_2449_, v___x_2450_, v___x_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(lean_object* v_p_2453_, lean_object* v_level_2454_, lean_object* v_part_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_level_2454_, v_part_2455_, v_a_2456_, v_a_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___boxed(lean_object* v_p_2459_, lean_object* v_level_2460_, lean_object* v_part_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(v_p_2459_, v_level_2460_, v_part_2461_, v_a_2462_, v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec_ref(v_part_2461_);
lean_dec(v_level_2460_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(lean_object* v_p_2465_, lean_object* v___x_2466_, lean_object* v_as_2467_, size_t v_sz_2468_, size_t v_i_2469_, lean_object* v_b_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2466_, v_as_2467_, v_sz_2468_, v_i_2469_, v_b_2470_, v___y_2471_, v___y_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___boxed(lean_object* v_p_2474_, lean_object* v___x_2475_, lean_object* v_as_2476_, lean_object* v_sz_2477_, lean_object* v_i_2478_, lean_object* v_b_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
size_t v_sz_boxed_2482_; size_t v_i_boxed_2483_; lean_object* v_res_2484_; 
v_sz_boxed_2482_ = lean_unbox_usize(v_sz_2477_);
lean_dec(v_sz_2477_);
v_i_boxed_2483_ = lean_unbox_usize(v_i_2478_);
lean_dec(v_i_2478_);
v_res_2484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(v_p_2474_, v___x_2475_, v_as_2476_, v_sz_boxed_2482_, v_i_boxed_2483_, v_b_2479_, v___y_2480_, v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec_ref(v_as_2476_);
lean_dec(v___x_2475_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2(lean_object* v_s_2485_, lean_object* v_pattern_2486_, lean_object* v_replacement_2487_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v_s_2485_, v_replacement_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___boxed(lean_object* v_s_2489_, lean_object* v_pattern_2490_, lean_object* v_replacement_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2(v_s_2489_, v_pattern_2490_, v_replacement_2491_);
lean_dec_ref(v_replacement_2491_);
lean_dec_ref(v_pattern_2490_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6(lean_object* v_s_2493_, lean_object* v_replacement_2494_, lean_object* v_inst_2495_, lean_object* v_R_2496_, lean_object* v_a_2497_, lean_object* v_b_2498_, lean_object* v_c_2499_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_2493_, v_replacement_2494_, v_a_2497_, v_b_2498_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___boxed(lean_object* v_s_2501_, lean_object* v_replacement_2502_, lean_object* v_inst_2503_, lean_object* v_R_2504_, lean_object* v_a_2505_, lean_object* v_b_2506_, lean_object* v_c_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6(v_s_2501_, v_replacement_2502_, v_inst_2503_, v_R_2504_, v_a_2505_, v_b_2506_, v_c_2507_);
lean_dec_ref(v_replacement_2502_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_2509_, lean_object* v_declName_2510_, uint8_t v_includeBuiltin_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_findInternalDocString_x3f(v_env_2509_, v_declName_2510_, v_includeBuiltin_2511_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2542_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2542_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2542_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
if (lean_obj_tag(v_a_2514_) == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2518_ = lean_box(0);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2518_);
v___x_2520_ = v___x_2516_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
else
{
lean_object* v_val_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2541_; 
v_val_2522_ = lean_ctor_get(v_a_2514_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_a_2514_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2524_ = v_a_2514_;
v_isShared_2525_ = v_isSharedCheck_2541_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_val_2522_);
lean_dec(v_a_2514_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2541_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
if (lean_obj_tag(v_val_2522_) == 0)
{
lean_object* v_val_2526_; lean_object* v___x_2528_; 
v_val_2526_ = lean_ctor_get(v_val_2522_, 0);
lean_inc(v_val_2526_);
lean_dec_ref(v_val_2522_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v_val_2526_);
v___x_2528_ = v___x_2524_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_val_2526_);
v___x_2528_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2530_; 
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2528_);
v___x_2530_ = v___x_2516_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
else
{
lean_object* v_val_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
v_val_2533_ = lean_ctor_get(v_val_2522_, 0);
lean_inc(v_val_2533_);
lean_dec_ref(v_val_2522_);
v___x_2534_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(v_val_2533_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2534_);
v___x_2536_ = v___x_2524_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2538_; 
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2536_);
v___x_2538_ = v___x_2516_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
v_a_2543_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2513_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2513_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_2551_, lean_object* v_declName_2552_, lean_object* v_includeBuiltin_2553_, lean_object* v_a_2554_){
_start:
{
uint8_t v_includeBuiltin_boxed_2555_; lean_object* v_res_2556_; 
v_includeBuiltin_boxed_2555_ = lean_unbox(v_includeBuiltin_2553_);
v_res_2556_ = l_Lean_findSimpleDocString_x3f(v_env_2551_, v_declName_2552_, v_includeBuiltin_boxed_2555_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object* v_x_2559_, lean_object* v_x_2560_, lean_object* v_es_2561_, uint8_t v_level_2562_){
_start:
{
uint8_t v___x_2563_; uint8_t v___x_2564_; 
v___x_2563_ = 1;
v___x_2564_ = l_Lean_instOrdOLeanLevel_ord(v_level_2562_, v___x_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; 
lean_dec(v_es_2561_);
v___x_2565_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_));
return v___x_2565_;
}
else
{
lean_object* v___x_2566_; 
v___x_2566_ = lean_array_mk(v_es_2561_);
return v___x_2566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object* v_x_2567_, lean_object* v_x_2568_, lean_object* v_es_2569_, lean_object* v_level_2570_){
_start:
{
uint8_t v_level_boxed_2571_; lean_object* v_res_2572_; 
v_level_boxed_2571_ = lean_unbox(v_level_2570_);
v_res_2572_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(v_x_2567_, v_x_2568_, v_es_2569_, v_level_boxed_2571_);
lean_dec_ref(v_x_2568_);
lean_dec_ref(v_x_2567_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object* v_es_2573_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_array_mk(v_es_2573_);
return v___x_2574_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2575_ = lean_unsigned_to_nat(32u);
v___x_2576_ = lean_mk_empty_array_with_capacity(v___x_2575_);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object* v___x_2578_, lean_object* v_x_2579_){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; size_t v___x_2583_; lean_object* v___x_2584_; 
v___x_2580_ = lean_unsigned_to_nat(32u);
v___x_2581_ = lean_mk_empty_array_with_capacity(v___x_2580_);
v___x_2582_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_);
v___x_2583_ = ((size_t)5ULL);
lean_inc(v___x_2578_);
v___x_2584_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2581_);
lean_ctor_set(v___x_2584_, 2, v___x_2578_);
lean_ctor_set(v___x_2584_, 3, v___x_2578_);
lean_ctor_set_usize(v___x_2584_, 4, v___x_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object* v___x_2585_, lean_object* v_x_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(v___x_2585_, v_x_2586_);
lean_dec_ref(v_x_2586_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_));
v___x_2609_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object* v_a_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_();
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object* v_env_2612_, lean_object* v_doc_2613_){
_start:
{
lean_object* v___x_2614_; lean_object* v_toEnvExtension_2615_; lean_object* v_asyncMode_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2614_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc_ref(v_toEnvExtension_2615_);
v_asyncMode_2616_ = lean_ctor_get(v_toEnvExtension_2615_, 2);
lean_inc(v_asyncMode_2616_);
lean_dec_ref(v_toEnvExtension_2615_);
v___x_2617_ = lean_box(0);
v___x_2618_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2614_, v_env_2612_, v_doc_2613_, v_asyncMode_2616_, v___x_2617_);
lean_dec(v_asyncMode_2616_);
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_getMainModuleDoc___closed__0(void){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object* v_env_2620_){
_start:
{
lean_object* v___x_2621_; lean_object* v_toEnvExtension_2622_; lean_object* v_asyncMode_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2621_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc_ref(v_toEnvExtension_2622_);
v_asyncMode_2623_ = lean_ctor_get(v_toEnvExtension_2622_, 2);
lean_inc(v_asyncMode_2623_);
lean_dec_ref(v_toEnvExtension_2622_);
v___x_2624_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2625_ = lean_box(0);
v___x_2626_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2624_, v___x_2621_, v_env_2620_, v_asyncMode_2623_, v___x_2625_);
lean_dec(v_asyncMode_2623_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_getModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2628_ = lean_box(0);
v___x_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
lean_ctor_set(v___x_2629_, 1, v___x_2627_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object* v_env_2630_, lean_object* v_moduleName_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_Environment_getModuleIdx_x3f(v_env_2630_, v_moduleName_2631_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_box(0);
return v___x_2633_;
}
else
{
lean_object* v_val_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2645_; 
v_val_2634_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2636_ = v___x_2632_;
v_isShared_2637_ = v_isSharedCheck_2645_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_val_2634_);
lean_dec(v___x_2632_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2645_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
v___x_2638_ = lean_obj_once(&l_Lean_getModuleDoc_x3f___closed__0, &l_Lean_getModuleDoc_x3f___closed__0_once, _init_l_Lean_getModuleDoc_x3f___closed__0);
v___x_2639_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v___x_2640_ = 1;
v___x_2641_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2638_, v___x_2639_, v_env_2630_, v_val_2634_, v___x_2640_);
lean_dec(v_val_2634_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2641_);
v___x_2643_ = v___x_2636_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object* v_env_2646_, lean_object* v_moduleName_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_getModuleDoc_x3f(v_env_2646_, v_moduleName_2647_);
lean_dec(v_moduleName_2647_);
lean_dec_ref(v_env_2646_);
return v_res_2648_;
}
}
static lean_object* _init_l_Lean_getDocStringText___redArg___closed__1(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__0));
v___x_2651_ = l_Lean_stringToMessageData(v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object* v_inst_2655_, lean_object* v_inst_2656_, lean_object* v_stx_2657_){
_start:
{
lean_object* v_toApplicative_2664_; lean_object* v_toPure_2665_; lean_object* v_val_2667_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v_toApplicative_2664_ = lean_ctor_get(v_inst_2655_, 0);
v_toPure_2665_ = lean_ctor_get(v_toApplicative_2664_, 1);
v___x_2674_ = lean_unsigned_to_nat(1u);
v___x_2675_ = l_Lean_Syntax_getArg(v_stx_2657_, v___x_2674_);
switch(lean_obj_tag(v___x_2675_))
{
case 2:
{
lean_object* v_val_2676_; 
lean_inc(v_toPure_2665_);
lean_dec(v_stx_2657_);
lean_dec_ref(v_inst_2656_);
lean_dec_ref(v_inst_2655_);
v_val_2676_ = lean_ctor_get(v___x_2675_, 1);
lean_inc_ref(v_val_2676_);
lean_dec_ref(v___x_2675_);
v_val_2667_ = v_val_2676_;
goto v___jp_2666_;
}
case 1:
{
lean_object* v_kind_2677_; 
v_kind_2677_ = lean_ctor_get(v___x_2675_, 1);
lean_inc(v_kind_2677_);
if (lean_obj_tag(v_kind_2677_) == 1)
{
lean_object* v_pre_2678_; 
v_pre_2678_ = lean_ctor_get(v_kind_2677_, 0);
lean_inc(v_pre_2678_);
if (lean_obj_tag(v_pre_2678_) == 1)
{
lean_object* v_pre_2679_; 
v_pre_2679_ = lean_ctor_get(v_pre_2678_, 0);
lean_inc(v_pre_2679_);
if (lean_obj_tag(v_pre_2679_) == 1)
{
lean_object* v_pre_2680_; 
v_pre_2680_ = lean_ctor_get(v_pre_2679_, 0);
lean_inc(v_pre_2680_);
if (lean_obj_tag(v_pre_2680_) == 1)
{
lean_object* v_pre_2681_; 
v_pre_2681_ = lean_ctor_get(v_pre_2680_, 0);
if (lean_obj_tag(v_pre_2681_) == 0)
{
lean_object* v_str_2682_; lean_object* v_str_2683_; lean_object* v_str_2684_; lean_object* v_str_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v_str_2682_ = lean_ctor_get(v_kind_2677_, 1);
lean_inc_ref(v_str_2682_);
lean_dec_ref(v_kind_2677_);
v_str_2683_ = lean_ctor_get(v_pre_2678_, 1);
lean_inc_ref(v_str_2683_);
lean_dec_ref(v_pre_2678_);
v_str_2684_ = lean_ctor_get(v_pre_2679_, 1);
lean_inc_ref(v_str_2684_);
lean_dec_ref(v_pre_2679_);
v_str_2685_ = lean_ctor_get(v_pre_2680_, 1);
lean_inc_ref(v_str_2685_);
lean_dec_ref(v_pre_2680_);
v___x_2686_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_2687_ = lean_string_dec_eq(v_str_2685_, v___x_2686_);
lean_dec_ref(v_str_2685_);
if (v___x_2687_ == 0)
{
lean_dec_ref(v_str_2684_);
lean_dec_ref(v_str_2683_);
lean_dec_ref(v_str_2682_);
lean_dec_ref(v___x_2675_);
goto v___jp_2658_;
}
else
{
lean_object* v___x_2688_; uint8_t v___x_2689_; 
v___x_2688_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__2));
v___x_2689_ = lean_string_dec_eq(v_str_2684_, v___x_2688_);
lean_dec_ref(v_str_2684_);
if (v___x_2689_ == 0)
{
lean_dec_ref(v_str_2683_);
lean_dec_ref(v_str_2682_);
lean_dec_ref(v___x_2675_);
goto v___jp_2658_;
}
else
{
lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2690_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__3));
v___x_2691_ = lean_string_dec_eq(v_str_2683_, v___x_2690_);
lean_dec_ref(v_str_2683_);
if (v___x_2691_ == 0)
{
lean_dec_ref(v_str_2682_);
lean_dec_ref(v___x_2675_);
goto v___jp_2658_;
}
else
{
lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2692_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__4));
v___x_2693_ = lean_string_dec_eq(v_str_2682_, v___x_2692_);
lean_dec_ref(v_str_2682_);
if (v___x_2693_ == 0)
{
lean_dec_ref(v___x_2675_);
goto v___jp_2658_;
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_unsigned_to_nat(0u);
v___x_2695_ = l_Lean_Syntax_getArg(v___x_2675_, v___x_2694_);
lean_dec_ref(v___x_2675_);
if (lean_obj_tag(v___x_2695_) == 2)
{
lean_object* v_val_2696_; 
lean_inc(v_toPure_2665_);
lean_dec(v_stx_2657_);
lean_dec_ref(v_inst_2656_);
lean_dec_ref(v_inst_2655_);
v_val_2696_ = lean_ctor_get(v___x_2695_, 1);
lean_inc_ref(v_val_2696_);
lean_dec_ref(v___x_2695_);
v_val_2667_ = v_val_2696_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_dec(v___x_2695_);
v___x_2697_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2657_);
v___x_2698_ = l_Lean_MessageData_ofSyntax(v_stx_2657_);
v___x_2699_ = l_Lean_indentD(v___x_2698_);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2697_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = l_Lean_throwErrorAt___redArg(v_inst_2655_, v_inst_2656_, v_stx_2657_, v___x_2700_);
return v___x_2701_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2680_);
lean_dec_ref(v_pre_2679_);
lean_dec_ref(v_pre_2678_);
lean_dec_ref(v_kind_2677_);
lean_dec_ref(v___x_2675_);
goto v___jp_2658_;
}
}
else
{
lean_dec(v_pre_2680_);
lean_dec_ref(v_pre_2679_);
lean_dec_ref(v_pre_2678_);
lean_dec_ref(v_kind_2677_);
lean_dec_ref(v___x_2675_);
goto v___jp_2658_;
}
}
else
{
lean_dec_ref(v_pre_2678_);
lean_dec(v_pre_2679_);
lean_dec_ref(v_kind_2677_);
lean_dec_ref(v___x_2675_);
goto v___jp_2658_;
}
}
else
{
lean_dec(v_pre_2678_);
lean_dec_ref(v_kind_2677_);
lean_dec_ref(v___x_2675_);
goto v___jp_2658_;
}
}
else
{
lean_dec_ref(v___x_2675_);
lean_dec(v_kind_2677_);
goto v___jp_2658_;
}
}
default: 
{
lean_dec(v___x_2675_);
goto v___jp_2658_;
}
}
v___jp_2658_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2659_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2657_);
v___x_2660_ = l_Lean_MessageData_ofSyntax(v_stx_2657_);
v___x_2661_ = l_Lean_indentD(v___x_2660_);
v___x_2662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2659_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
v___x_2663_ = l_Lean_throwErrorAt___redArg(v_inst_2655_, v_inst_2656_, v_stx_2657_, v___x_2662_);
return v___x_2663_;
}
v___jp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2668_ = lean_unsigned_to_nat(0u);
v___x_2669_ = lean_string_utf8_byte_size(v_val_2667_);
v___x_2670_ = lean_unsigned_to_nat(2u);
v___x_2671_ = lean_nat_sub(v___x_2669_, v___x_2670_);
v___x_2672_ = lean_string_utf8_extract(v_val_2667_, v___x_2668_, v___x_2671_);
lean_dec(v___x_2671_);
lean_dec_ref(v_val_2667_);
v___x_2673_ = lean_apply_2(v_toPure_2665_, lean_box(0), v___x_2672_);
return v___x_2673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object* v_m_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_stx_2705_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Lean_getDocStringText___redArg(v_inst_2703_, v_inst_2704_, v_stx_2705_);
return v___x_2706_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_2708_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default___closed__0));
v___x_2709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
lean_ctor_set(v___x_2709_, 2, v___x_2707_);
return v___x_2709_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default(void){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_obj_once(&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0, &l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_once, _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0);
return v___x_2710_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet(void){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object* v_a_2712_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_nat_to_int(v_a_2712_);
return v___x_2713_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = lean_unsigned_to_nat(2u);
v___x_2721_ = lean_nat_to_int(v___x_2720_);
return v___x_2721_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = lean_unsigned_to_nat(1u);
v___x_2723_ = lean_nat_to_int(v___x_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object* v_x_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_){
_start:
{
if (lean_obj_tag(v_x_2738_) == 0)
{
lean_dec(v_x_2736_);
return v_x_2737_;
}
else
{
lean_object* v_head_2739_; lean_object* v_tail_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2751_; 
v_head_2739_ = lean_ctor_get(v_x_2738_, 0);
v_tail_2740_ = lean_ctor_get(v_x_2738_, 1);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_x_2738_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2742_ = v_x_2738_;
v_isShared_2743_ = v_isSharedCheck_2751_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_tail_2740_);
lean_inc(v_head_2739_);
lean_dec(v_x_2738_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2751_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
lean_inc(v_x_2736_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set_tag(v___x_2742_, 5);
lean_ctor_set(v___x_2742_, 1, v_x_2736_);
lean_ctor_set(v___x_2742_, 0, v_x_2737_);
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_x_2737_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_x_2736_);
v___x_2745_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2746_ = lean_unsigned_to_nat(0u);
v___x_2747_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2739_, v___x_2746_);
v___x_2748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2745_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v_x_2737_ = v___x_2748_;
v_x_2738_ = v_tail_2740_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object* v_x_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_){
_start:
{
if (lean_obj_tag(v_x_2754_) == 0)
{
lean_dec(v_x_2752_);
return v_x_2753_;
}
else
{
lean_object* v_head_2755_; lean_object* v_tail_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2767_; 
v_head_2755_ = lean_ctor_get(v_x_2754_, 0);
v_tail_2756_ = lean_ctor_get(v_x_2754_, 1);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_x_2754_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2758_ = v_x_2754_;
v_isShared_2759_ = v_isSharedCheck_2767_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_tail_2756_);
lean_inc(v_head_2755_);
lean_dec(v_x_2754_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2767_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
lean_inc(v_x_2752_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set_tag(v___x_2758_, 5);
lean_ctor_set(v___x_2758_, 1, v_x_2752_);
lean_ctor_set(v___x_2758_, 0, v_x_2753_);
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_x_2753_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v_x_2752_);
v___x_2761_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2762_ = lean_unsigned_to_nat(0u);
v___x_2763_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2755_, v___x_2762_);
v___x_2764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2761_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(v_x_2752_, v___x_2764_, v_tail_2756_);
return v___x_2765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2768_, lean_object* v_x_2769_){
_start:
{
if (lean_obj_tag(v_x_2768_) == 0)
{
lean_object* v___x_2770_; 
lean_dec(v_x_2769_);
v___x_2770_ = lean_box(0);
return v___x_2770_;
}
else
{
lean_object* v_tail_2771_; 
v_tail_2771_ = lean_ctor_get(v_x_2768_, 1);
if (lean_obj_tag(v_tail_2771_) == 0)
{
lean_object* v_head_2772_; lean_object* v___x_2773_; 
lean_dec(v_x_2769_);
v_head_2772_ = lean_ctor_get(v_x_2768_, 0);
lean_inc(v_head_2772_);
lean_dec_ref(v_x_2768_);
v___x_2773_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2772_);
return v___x_2773_;
}
else
{
lean_object* v_head_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_inc(v_tail_2771_);
v_head_2774_ = lean_ctor_get(v_x_2768_, 0);
lean_inc(v_head_2774_);
lean_dec_ref(v_x_2768_);
v___x_2775_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2774_);
v___x_2776_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(v_x_2769_, v___x_2775_, v_tail_2771_);
return v___x_2776_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0));
v___x_2779_ = lean_string_length(v___x_2778_);
return v___x_2779_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4);
v___x_2781_ = lean_nat_to_int(v___x_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_xs_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2790_ = lean_array_get_size(v_xs_2789_);
v___x_2791_ = lean_unsigned_to_nat(0u);
v___x_2792_ = lean_nat_dec_eq(v___x_2790_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2793_ = lean_array_to_list(v_xs_2789_);
v___x_2794_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2795_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_2793_, v___x_2794_);
v___x_2796_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_2797_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_2798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
lean_ctor_set(v___x_2798_, 1, v___x_2795_);
v___x_2799_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2796_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = l_Std_Format_fill(v___x_2801_);
return v___x_2802_;
}
else
{
lean_object* v___x_2803_; 
lean_dec_ref(v_xs_2789_);
v___x_2803_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_2803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_2858_, lean_object* v_prec_2859_){
_start:
{
switch(lean_obj_tag(v_x_2858_))
{
case 0:
{
lean_object* v_string_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2880_; 
v_string_2860_ = lean_ctor_get(v_x_2858_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v_x_2858_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2862_ = v_x_2858_;
v_isShared_2863_ = v_isSharedCheck_2880_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_string_2860_);
lean_dec(v_x_2858_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2880_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___y_2865_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2876_ = lean_unsigned_to_nat(1024u);
v___x_2877_ = lean_nat_dec_le(v___x_2876_, v_prec_2859_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
v___x_2878_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2865_ = v___x_2878_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_2879_; 
v___x_2879_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2865_ = v___x_2879_;
goto v___jp_2864_;
}
v___jp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2866_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_2867_ = l_String_quote(v_string_2860_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set_tag(v___x_2862_, 3);
lean_ctor_set(v___x_2862_, 0, v___x_2867_);
v___x_2869_ = v___x_2862_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2866_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___y_2865_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = 0;
v___x_2873_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2873_, 0, v___x_2871_);
lean_ctor_set_uint8(v___x_2873_, sizeof(void*)*1, v___x_2872_);
v___x_2874_ = l_Repr_addAppParen(v___x_2873_, v_prec_2859_);
return v___x_2874_;
}
}
}
}
case 1:
{
lean_object* v_content_2881_; lean_object* v___y_2883_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v_content_2881_ = lean_ctor_get(v_x_2858_, 0);
lean_inc_ref(v_content_2881_);
lean_dec_ref(v_x_2858_);
v___x_2891_ = lean_unsigned_to_nat(1024u);
v___x_2892_ = lean_nat_dec_le(v___x_2891_, v_prec_2859_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; 
v___x_2893_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2883_ = v___x_2893_;
goto v___jp_2882_;
}
else
{
lean_object* v___x_2894_; 
v___x_2894_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2883_ = v___x_2894_;
goto v___jp_2882_;
}
v___jp_2882_:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2884_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7));
v___x_2885_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2881_);
v___x_2886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2884_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
v___x_2887_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___y_2883_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___x_2888_ = 0;
v___x_2889_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*1, v___x_2888_);
v___x_2890_ = l_Repr_addAppParen(v___x_2889_, v_prec_2859_);
return v___x_2890_;
}
}
case 2:
{
lean_object* v_content_2895_; lean_object* v___y_2897_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v_content_2895_ = lean_ctor_get(v_x_2858_, 0);
lean_inc_ref(v_content_2895_);
lean_dec_ref(v_x_2858_);
v___x_2905_ = lean_unsigned_to_nat(1024u);
v___x_2906_ = lean_nat_dec_le(v___x_2905_, v_prec_2859_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2897_ = v___x_2907_;
goto v___jp_2896_;
}
else
{
lean_object* v___x_2908_; 
v___x_2908_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2897_ = v___x_2908_;
goto v___jp_2896_;
}
v___jp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2898_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10));
v___x_2899_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2895_);
v___x_2900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___y_2897_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = 0;
v___x_2903_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set_uint8(v___x_2903_, sizeof(void*)*1, v___x_2902_);
v___x_2904_ = l_Repr_addAppParen(v___x_2903_, v_prec_2859_);
return v___x_2904_;
}
}
case 3:
{
lean_object* v_string_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2929_; 
v_string_2909_ = lean_ctor_get(v_x_2858_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_x_2858_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2911_ = v_x_2858_;
v_isShared_2912_ = v_isSharedCheck_2929_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_string_2909_);
lean_dec(v_x_2858_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2929_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___y_2914_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v___x_2925_ = lean_unsigned_to_nat(1024u);
v___x_2926_ = lean_nat_dec_le(v___x_2925_, v_prec_2859_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2914_ = v___x_2927_;
goto v___jp_2913_;
}
else
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2914_ = v___x_2928_;
goto v___jp_2913_;
}
v___jp_2913_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2915_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13));
v___x_2916_ = l_String_quote(v_string_2909_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v___x_2916_);
v___x_2918_ = v___x_2911_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; uint8_t v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2915_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___y_2914_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = 0;
v___x_2922_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2922_, 0, v___x_2920_);
lean_ctor_set_uint8(v___x_2922_, sizeof(void*)*1, v___x_2921_);
v___x_2923_ = l_Repr_addAppParen(v___x_2922_, v_prec_2859_);
return v___x_2923_;
}
}
}
}
case 4:
{
uint8_t v_mode_2930_; lean_object* v_string_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2956_; 
v_mode_2930_ = lean_ctor_get_uint8(v_x_2858_, sizeof(void*)*1);
v_string_2931_ = lean_ctor_get(v_x_2858_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_x_2858_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2933_ = v_x_2858_;
v_isShared_2934_ = v_isSharedCheck_2956_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_string_2931_);
lean_dec(v_x_2858_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2956_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___y_2936_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2952_ = lean_unsigned_to_nat(1024u);
v___x_2953_ = lean_nat_dec_le(v___x_2952_, v_prec_2859_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; 
v___x_2954_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2936_ = v___x_2954_;
goto v___jp_2935_;
}
else
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2936_ = v___x_2955_;
goto v___jp_2935_;
}
v___jp_2935_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; lean_object* v___x_2949_; 
v___x_2937_ = lean_box(1);
v___x_2938_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16));
v___x_2939_ = lean_unsigned_to_nat(1024u);
v___x_2940_ = l_Lean_Doc_instReprMathMode_repr(v_mode_2930_, v___x_2939_);
v___x_2941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2938_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2937_);
v___x_2943_ = l_String_quote(v_string_2931_);
v___x_2944_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2942_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___y_2936_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
v___x_2947_ = 0;
if (v_isShared_2934_ == 0)
{
lean_ctor_set_tag(v___x_2933_, 6);
lean_ctor_set(v___x_2933_, 0, v___x_2946_);
v___x_2949_ = v___x_2933_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2946_);
v___x_2949_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; 
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*1, v___x_2947_);
v___x_2950_ = l_Repr_addAppParen(v___x_2949_, v_prec_2859_);
return v___x_2950_;
}
}
}
}
case 5:
{
lean_object* v_string_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2977_; 
v_string_2957_ = lean_ctor_get(v_x_2858_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_x_2858_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2959_ = v_x_2858_;
v_isShared_2960_ = v_isSharedCheck_2977_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_string_2957_);
lean_dec(v_x_2858_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2977_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___y_2962_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2973_ = lean_unsigned_to_nat(1024u);
v___x_2974_ = lean_nat_dec_le(v___x_2973_, v_prec_2859_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2962_ = v___x_2975_;
goto v___jp_2961_;
}
else
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2962_ = v___x_2976_;
goto v___jp_2961_;
}
v___jp_2961_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2963_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19));
v___x_2964_ = l_String_quote(v_string_2957_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set_tag(v___x_2959_, 3);
lean_ctor_set(v___x_2959_, 0, v___x_2964_);
v___x_2966_ = v___x_2959_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2963_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___y_2962_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = 0;
v___x_2970_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2970_, 0, v___x_2968_);
lean_ctor_set_uint8(v___x_2970_, sizeof(void*)*1, v___x_2969_);
v___x_2971_ = l_Repr_addAppParen(v___x_2970_, v_prec_2859_);
return v___x_2971_;
}
}
}
}
case 6:
{
lean_object* v_content_2978_; lean_object* v_url_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3003_; 
v_content_2978_ = lean_ctor_get(v_x_2858_, 0);
v_url_2979_ = lean_ctor_get(v_x_2858_, 1);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_x_2858_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2981_ = v_x_2858_;
v_isShared_2982_ = v_isSharedCheck_3003_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_url_2979_);
lean_inc(v_content_2978_);
lean_dec(v_x_2858_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3003_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___y_2984_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2999_ = lean_unsigned_to_nat(1024u);
v___x_3000_ = lean_nat_dec_le(v___x_2999_, v_prec_2859_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2984_ = v___x_3001_;
goto v___jp_2983_;
}
else
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2984_ = v___x_3002_;
goto v___jp_2983_;
}
v___jp_2983_:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2985_ = lean_box(1);
v___x_2986_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22));
v___x_2987_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2978_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set_tag(v___x_2981_, 5);
lean_ctor_set(v___x_2981_, 1, v___x_2987_);
lean_ctor_set(v___x_2981_, 0, v___x_2986_);
v___x_2989_ = v___x_2981_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2986_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
lean_ctor_set(v___x_2990_, 1, v___x_2985_);
v___x_2991_ = l_String_quote(v_url_2979_);
v___x_2992_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
v___x_2993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2990_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___y_2984_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = 0;
v___x_2996_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2996_, 0, v___x_2994_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*1, v___x_2995_);
v___x_2997_ = l_Repr_addAppParen(v___x_2996_, v_prec_2859_);
return v___x_2997_;
}
}
}
}
case 7:
{
lean_object* v_name_3004_; lean_object* v_content_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3029_; 
v_name_3004_ = lean_ctor_get(v_x_2858_, 0);
v_content_3005_ = lean_ctor_get(v_x_2858_, 1);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_x_2858_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3007_ = v_x_2858_;
v_isShared_3008_ = v_isSharedCheck_3029_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_content_3005_);
lean_inc(v_name_3004_);
lean_dec(v_x_2858_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3029_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___y_3010_; lean_object* v___x_3025_; uint8_t v___x_3026_; 
v___x_3025_ = lean_unsigned_to_nat(1024u);
v___x_3026_ = lean_nat_dec_le(v___x_3025_, v_prec_2859_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; 
v___x_3027_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3010_ = v___x_3027_;
goto v___jp_3009_;
}
else
{
lean_object* v___x_3028_; 
v___x_3028_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3010_ = v___x_3028_;
goto v___jp_3009_;
}
v___jp_3009_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3011_ = lean_box(1);
v___x_3012_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25));
v___x_3013_ = l_String_quote(v_name_3004_);
v___x_3014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set_tag(v___x_3007_, 5);
lean_ctor_set(v___x_3007_, 1, v___x_3014_);
lean_ctor_set(v___x_3007_, 0, v___x_3012_);
v___x_3016_ = v___x_3007_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3012_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set(v___x_3017_, 1, v___x_3011_);
v___x_3018_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3005_);
v___x_3019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___y_3010_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = 0;
v___x_3022_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set_uint8(v___x_3022_, sizeof(void*)*1, v___x_3021_);
v___x_3023_ = l_Repr_addAppParen(v___x_3022_, v_prec_2859_);
return v___x_3023_;
}
}
}
}
case 8:
{
lean_object* v_alt_3030_; lean_object* v_url_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3056_; 
v_alt_3030_ = lean_ctor_get(v_x_2858_, 0);
v_url_3031_ = lean_ctor_get(v_x_2858_, 1);
v_isSharedCheck_3056_ = !lean_is_exclusive(v_x_2858_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3033_ = v_x_2858_;
v_isShared_3034_ = v_isSharedCheck_3056_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_url_3031_);
lean_inc(v_alt_3030_);
lean_dec(v_x_2858_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3056_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___y_3036_; lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = lean_unsigned_to_nat(1024u);
v___x_3053_ = lean_nat_dec_le(v___x_3052_, v_prec_2859_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3036_ = v___x_3054_;
goto v___jp_3035_;
}
else
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3036_ = v___x_3055_;
goto v___jp_3035_;
}
v___jp_3035_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3037_ = lean_box(1);
v___x_3038_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28));
v___x_3039_ = l_String_quote(v_alt_3030_);
v___x_3040_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set_tag(v___x_3033_, 5);
lean_ctor_set(v___x_3033_, 1, v___x_3040_);
lean_ctor_set(v___x_3033_, 0, v___x_3038_);
v___x_3042_ = v___x_3033_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
lean_ctor_set(v___x_3043_, 1, v___x_3037_);
v___x_3044_ = l_String_quote(v_url_3031_);
v___x_3045_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
v___x_3046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3043_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___y_3036_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = 0;
v___x_3049_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3049_, 0, v___x_3047_);
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*1, v___x_3048_);
v___x_3050_ = l_Repr_addAppParen(v___x_3049_, v_prec_2859_);
return v___x_3050_;
}
}
}
}
case 9:
{
lean_object* v_content_3057_; lean_object* v___y_3059_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v_content_3057_ = lean_ctor_get(v_x_2858_, 0);
lean_inc_ref(v_content_3057_);
lean_dec_ref(v_x_2858_);
v___x_3067_ = lean_unsigned_to_nat(1024u);
v___x_3068_ = lean_nat_dec_le(v___x_3067_, v_prec_2859_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; 
v___x_3069_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3059_ = v___x_3069_;
goto v___jp_3058_;
}
else
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3059_ = v___x_3070_;
goto v___jp_3058_;
}
v___jp_3058_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3060_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31));
v___x_3061_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3057_);
v___x_3062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3060_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___y_3059_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = 0;
v___x_3065_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set_uint8(v___x_3065_, sizeof(void*)*1, v___x_3064_);
v___x_3066_ = l_Repr_addAppParen(v___x_3065_, v_prec_2859_);
return v___x_3066_;
}
}
default: 
{
lean_object* v_container_3071_; lean_object* v_content_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3120_; 
v_container_3071_ = lean_ctor_get(v_x_2858_, 0);
v_content_3072_ = lean_ctor_get(v_x_2858_, 1);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_x_2858_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3074_ = v_x_2858_;
v_isShared_3075_ = v_isSharedCheck_3120_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_content_3072_);
lean_inc(v_container_3071_);
lean_dec(v_x_2858_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3120_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___y_3077_; lean_object* v___x_3116_; uint8_t v___x_3117_; 
v___x_3116_ = lean_unsigned_to_nat(1024u);
v___x_3117_ = lean_nat_dec_le(v___x_3116_, v_prec_2859_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3077_ = v___x_3118_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3077_ = v___x_3119_;
goto v___jp_3076_;
}
v___jp_3076_:
{
lean_object* v_name_3078_; lean_object* v_val_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3115_; 
v_name_3078_ = lean_ctor_get(v_container_3071_, 0);
v_val_3079_ = lean_ctor_get(v_container_3071_, 1);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_container_3071_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3081_ = v_container_3071_;
v_isShared_3082_ = v_isSharedCheck_3115_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_val_3079_);
lean_inc(v_name_3078_);
lean_dec(v_container_3071_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3115_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3083_ = lean_box(1);
v___x_3084_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34));
v___x_3085_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3086_ = lean_unsigned_to_nat(0u);
v___x_3087_ = l_Lean_Name_reprPrec(v_name_3078_, v___x_3086_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set_tag(v___x_3081_, 5);
lean_ctor_set(v___x_3081_, 1, v___x_3087_);
lean_ctor_set(v___x_3081_, 0, v___x_3085_);
v___x_3089_ = v___x_3081_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; uint8_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3094_; 
v___x_3090_ = l_Std_Format_nestD(v___x_3089_);
v___x_3091_ = 0;
v___x_3092_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3092_, 0, v___x_3090_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*1, v___x_3091_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set_tag(v___x_3074_, 5);
lean_ctor_set(v___x_3074_, 1, v___x_3083_);
lean_ctor_set(v___x_3074_, 0, v___x_3092_);
v___x_3094_ = v___x_3074_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3092_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v___x_3083_);
v___x_3094_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3095_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3096_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3079_);
lean_dec(v_val_3079_);
v___x_3097_ = l_Lean_Name_reprPrec(v___x_3096_, v___x_3086_);
v___x_3098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3095_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3098_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = l_Std_Format_nestD(v___x_3100_);
v___x_3102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*1, v___x_3091_);
v___x_3103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3094_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = l_Std_Format_nestD(v___x_3103_);
v___x_3105_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
lean_ctor_set_uint8(v___x_3105_, sizeof(void*)*1, v___x_3091_);
v___x_3106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3084_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
lean_ctor_set(v___x_3107_, 1, v___x_3083_);
v___x_3108_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3072_);
v___x_3109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3107_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___y_3077_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*1, v___x_3091_);
v___x_3112_ = l_Repr_addAppParen(v___x_3111_, v_prec_2859_);
return v___x_3112_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_3121_){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = lean_unsigned_to_nat(0u);
v___x_3123_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v___y_3121_, v___x_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_3124_, lean_object* v_prec_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_x_3124_, v_prec_3125_);
lean_dec(v_prec_3125_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object* v_xs_3127_){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v___x_3128_ = lean_array_get_size(v_xs_3127_);
v___x_3129_ = lean_unsigned_to_nat(0u);
v___x_3130_ = lean_nat_dec_eq(v___x_3128_, v___x_3129_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3131_ = lean_array_to_list(v_xs_3127_);
v___x_3132_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3133_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_3131_, v___x_3132_);
v___x_3134_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3135_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
lean_ctor_set(v___x_3136_, 1, v___x_3133_);
v___x_3137_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3136_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3134_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
v___x_3140_ = l_Std_Format_fill(v___x_3139_);
return v___x_3140_;
}
else
{
lean_object* v___x_3141_; 
lean_dec_ref(v_xs_3127_);
v___x_3141_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3141_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_unsigned_to_nat(12u);
v___x_3173_ = lean_nat_to_int(v___x_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object* v_x_3174_, lean_object* v_x_3175_, lean_object* v_x_3176_){
_start:
{
if (lean_obj_tag(v_x_3176_) == 0)
{
lean_dec(v_x_3174_);
return v_x_3175_;
}
else
{
lean_object* v_head_3177_; lean_object* v_tail_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3189_; 
v_head_3177_ = lean_ctor_get(v_x_3176_, 0);
v_tail_3178_ = lean_ctor_get(v_x_3176_, 1);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_x_3176_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3180_ = v_x_3176_;
v_isShared_3181_ = v_isSharedCheck_3189_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_tail_3178_);
lean_inc(v_head_3177_);
lean_dec(v_x_3176_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3189_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
lean_inc(v_x_3174_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set_tag(v___x_3180_, 5);
lean_ctor_set(v___x_3180_, 1, v_x_3174_);
lean_ctor_set(v___x_3180_, 0, v_x_3175_);
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_x_3175_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_x_3174_);
v___x_3183_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3184_ = lean_unsigned_to_nat(0u);
v___x_3185_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_3177_, v___x_3184_);
v___x_3186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3183_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v_x_3175_ = v___x_3186_;
v_x_3176_ = v_tail_3178_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object* v_x_3190_, lean_object* v_x_3191_, lean_object* v_x_3192_){
_start:
{
if (lean_obj_tag(v_x_3192_) == 0)
{
lean_dec(v_x_3190_);
return v_x_3191_;
}
else
{
lean_object* v_head_3193_; lean_object* v_tail_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3205_; 
v_head_3193_ = lean_ctor_get(v_x_3192_, 0);
v_tail_3194_ = lean_ctor_get(v_x_3192_, 1);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_x_3192_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3196_ = v_x_3192_;
v_isShared_3197_ = v_isSharedCheck_3205_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_tail_3194_);
lean_inc(v_head_3193_);
lean_dec(v_x_3192_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3205_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
lean_inc(v_x_3190_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set_tag(v___x_3196_, 5);
lean_ctor_set(v___x_3196_, 1, v_x_3190_);
lean_ctor_set(v___x_3196_, 0, v_x_3191_);
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_x_3191_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_x_3190_);
v___x_3199_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3200_ = lean_unsigned_to_nat(0u);
v___x_3201_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_3193_, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3199_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
v___x_3203_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(v_x_3190_, v___x_3202_, v_tail_3194_);
return v___x_3203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object* v_x_3206_, lean_object* v_x_3207_){
_start:
{
if (lean_obj_tag(v_x_3206_) == 0)
{
lean_object* v___x_3208_; 
lean_dec(v_x_3207_);
v___x_3208_ = lean_box(0);
return v___x_3208_;
}
else
{
lean_object* v_tail_3209_; 
v_tail_3209_ = lean_ctor_get(v_x_3206_, 1);
if (lean_obj_tag(v_tail_3209_) == 0)
{
lean_object* v_head_3210_; lean_object* v___x_3211_; 
lean_dec(v_x_3207_);
v_head_3210_ = lean_ctor_get(v_x_3206_, 0);
lean_inc(v_head_3210_);
lean_dec_ref(v_x_3206_);
v___x_3211_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3210_);
return v___x_3211_;
}
else
{
lean_object* v_head_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
lean_inc(v_tail_3209_);
v_head_3212_ = lean_ctor_get(v_x_3206_, 0);
lean_inc(v_head_3212_);
lean_dec_ref(v_x_3206_);
v___x_3213_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3212_);
v___x_3214_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(v_x_3207_, v___x_3213_, v_tail_3209_);
return v___x_3214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object* v_xs_3215_){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; uint8_t v___x_3218_; 
v___x_3216_ = lean_array_get_size(v_xs_3215_);
v___x_3217_ = lean_unsigned_to_nat(0u);
v___x_3218_ = lean_nat_dec_eq(v___x_3216_, v___x_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3219_ = lean_array_to_list(v_xs_3215_);
v___x_3220_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3221_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3219_, v___x_3220_);
v___x_3222_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3223_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v___x_3221_);
v___x_3225_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3224_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3222_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = l_Std_Format_fill(v___x_3227_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; 
lean_dec_ref(v_xs_3215_);
v___x_3229_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3229_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_3232_ = lean_string_length(v___x_3231_);
return v___x_3232_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9);
v___x_3234_ = lean_nat_to_int(v___x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_x_3240_){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3241_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6));
v___x_3242_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3243_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_x_3240_);
v___x_3244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = 0;
v___x_3246_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*1, v___x_3245_);
v___x_3247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3241_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3249_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
lean_ctor_set(v___x_3250_, 1, v___x_3247_);
v___x_3251_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3248_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
lean_ctor_set_uint8(v___x_3254_, sizeof(void*)*1, v___x_3245_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object* v_x_3255_, lean_object* v_x_3256_, lean_object* v_x_3257_){
_start:
{
if (lean_obj_tag(v_x_3257_) == 0)
{
lean_dec(v_x_3255_);
return v_x_3256_;
}
else
{
lean_object* v_head_3258_; lean_object* v_tail_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3269_; 
v_head_3258_ = lean_ctor_get(v_x_3257_, 0);
v_tail_3259_ = lean_ctor_get(v_x_3257_, 1);
v_isSharedCheck_3269_ = !lean_is_exclusive(v_x_3257_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3261_ = v_x_3257_;
v_isShared_3262_ = v_isSharedCheck_3269_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_tail_3259_);
lean_inc(v_head_3258_);
lean_dec(v_x_3257_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3269_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
lean_inc(v_x_3255_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set_tag(v___x_3261_, 5);
lean_ctor_set(v___x_3261_, 1, v_x_3255_);
lean_ctor_set(v___x_3261_, 0, v_x_3256_);
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_x_3256_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_x_3255_);
v___x_3264_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3258_);
v___x_3266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3264_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
v_x_3256_ = v___x_3266_;
v_x_3257_ = v_tail_3259_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object* v_x_3270_, lean_object* v_x_3271_, lean_object* v_x_3272_){
_start:
{
if (lean_obj_tag(v_x_3272_) == 0)
{
lean_dec(v_x_3270_);
return v_x_3271_;
}
else
{
lean_object* v_head_3273_; lean_object* v_tail_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3284_; 
v_head_3273_ = lean_ctor_get(v_x_3272_, 0);
v_tail_3274_ = lean_ctor_get(v_x_3272_, 1);
v_isSharedCheck_3284_ = !lean_is_exclusive(v_x_3272_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3276_ = v_x_3272_;
v_isShared_3277_ = v_isSharedCheck_3284_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_tail_3274_);
lean_inc(v_head_3273_);
lean_dec(v_x_3272_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3284_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
lean_inc(v_x_3270_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set_tag(v___x_3276_, 5);
lean_ctor_set(v___x_3276_, 1, v_x_3270_);
lean_ctor_set(v___x_3276_, 0, v_x_3271_);
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_x_3271_);
lean_ctor_set(v_reuseFailAlloc_3283_, 1, v_x_3270_);
v___x_3279_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3273_);
v___x_3281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(v_x_3270_, v___x_3281_, v_tail_3274_);
return v___x_3282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object* v_x_3285_, lean_object* v_x_3286_){
_start:
{
if (lean_obj_tag(v_x_3285_) == 0)
{
lean_object* v___x_3287_; 
lean_dec(v_x_3286_);
v___x_3287_ = lean_box(0);
return v___x_3287_;
}
else
{
lean_object* v_tail_3288_; 
v_tail_3288_ = lean_ctor_get(v_x_3285_, 1);
if (lean_obj_tag(v_tail_3288_) == 0)
{
lean_object* v_head_3289_; lean_object* v___x_3290_; 
lean_dec(v_x_3286_);
v_head_3289_ = lean_ctor_get(v_x_3285_, 0);
lean_inc(v_head_3289_);
lean_dec_ref(v_x_3285_);
v___x_3290_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3289_);
return v___x_3290_;
}
else
{
lean_object* v_head_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_inc(v_tail_3288_);
v_head_3291_ = lean_ctor_get(v_x_3285_, 0);
lean_inc(v_head_3291_);
lean_dec_ref(v_x_3285_);
v___x_3292_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3291_);
v___x_3293_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(v_x_3286_, v___x_3292_, v_tail_3288_);
return v___x_3293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object* v_xs_3294_){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; 
v___x_3295_ = lean_array_get_size(v_xs_3294_);
v___x_3296_ = lean_unsigned_to_nat(0u);
v___x_3297_ = lean_nat_dec_eq(v___x_3295_, v___x_3296_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3298_ = lean_array_to_list(v_xs_3294_);
v___x_3299_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3300_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(v___x_3298_, v___x_3299_);
v___x_3301_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3302_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v___x_3300_);
v___x_3304_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3301_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = l_Std_Format_fill(v___x_3306_);
return v___x_3307_;
}
else
{
lean_object* v___x_3308_; 
lean_dec_ref(v_xs_3294_);
v___x_3308_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3308_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = lean_unsigned_to_nat(0u);
v___x_3316_ = lean_nat_to_int(v___x_3315_);
return v___x_3316_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = lean_unsigned_to_nat(8u);
v___x_3333_ = lean_nat_to_int(v___x_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_x_3337_){
_start:
{
lean_object* v_term_3338_; lean_object* v_desc_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3371_; 
v_term_3338_ = lean_ctor_get(v_x_3337_, 0);
v_desc_3339_ = lean_ctor_get(v_x_3337_, 1);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_x_3337_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3341_ = v_x_3337_;
v_isShared_3342_ = v_isSharedCheck_3371_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_desc_3339_);
lean_inc(v_term_3338_);
lean_dec(v_x_3337_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3371_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3343_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3344_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3));
v___x_3345_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3346_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_term_3338_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set_tag(v___x_3341_, 4);
lean_ctor_set(v___x_3341_, 1, v___x_3346_);
lean_ctor_set(v___x_3341_, 0, v___x_3345_);
v___x_3348_ = v___x_3341_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3345_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
uint8_t v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3349_ = 0;
v___x_3350_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set_uint8(v___x_3350_, sizeof(void*)*1, v___x_3349_);
v___x_3351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3344_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3351_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = lean_box(1);
v___x_3355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3353_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6));
v___x_3357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3355_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___x_3358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
lean_ctor_set(v___x_3358_, 1, v___x_3343_);
v___x_3359_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_desc_3339_);
v___x_3360_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3345_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
lean_ctor_set_uint8(v___x_3361_, sizeof(void*)*1, v___x_3349_);
v___x_3362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3358_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3364_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
lean_ctor_set(v___x_3365_, 1, v___x_3362_);
v___x_3366_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3365_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3363_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
lean_ctor_set_uint8(v___x_3369_, sizeof(void*)*1, v___x_3349_);
return v___x_3369_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object* v_x_3372_, lean_object* v_x_3373_, lean_object* v_x_3374_){
_start:
{
if (lean_obj_tag(v_x_3374_) == 0)
{
lean_dec(v_x_3372_);
return v_x_3373_;
}
else
{
lean_object* v_head_3375_; lean_object* v_tail_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3386_; 
v_head_3375_ = lean_ctor_get(v_x_3374_, 0);
v_tail_3376_ = lean_ctor_get(v_x_3374_, 1);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_x_3374_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3378_ = v_x_3374_;
v_isShared_3379_ = v_isSharedCheck_3386_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_tail_3376_);
lean_inc(v_head_3375_);
lean_dec(v_x_3374_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3386_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
lean_inc(v_x_3372_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 5);
lean_ctor_set(v___x_3378_, 1, v_x_3372_);
lean_ctor_set(v___x_3378_, 0, v_x_3373_);
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_x_3373_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_x_3372_);
v___x_3381_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3375_);
v___x_3383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3381_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v_x_3373_ = v___x_3383_;
v_x_3374_ = v_tail_3376_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object* v_x_3387_, lean_object* v_x_3388_, lean_object* v_x_3389_){
_start:
{
if (lean_obj_tag(v_x_3389_) == 0)
{
lean_dec(v_x_3387_);
return v_x_3388_;
}
else
{
lean_object* v_head_3390_; lean_object* v_tail_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3401_; 
v_head_3390_ = lean_ctor_get(v_x_3389_, 0);
v_tail_3391_ = lean_ctor_get(v_x_3389_, 1);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_x_3389_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3393_ = v_x_3389_;
v_isShared_3394_ = v_isSharedCheck_3401_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_tail_3391_);
lean_inc(v_head_3390_);
lean_dec(v_x_3389_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3401_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
lean_inc(v_x_3387_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set_tag(v___x_3393_, 5);
lean_ctor_set(v___x_3393_, 1, v_x_3387_);
lean_ctor_set(v___x_3393_, 0, v_x_3388_);
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_x_3388_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v_x_3387_);
v___x_3396_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3390_);
v___x_3398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3396_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(v_x_3387_, v___x_3398_, v_tail_3391_);
return v___x_3399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object* v_x_3402_, lean_object* v_x_3403_){
_start:
{
if (lean_obj_tag(v_x_3402_) == 0)
{
lean_object* v___x_3404_; 
lean_dec(v_x_3403_);
v___x_3404_ = lean_box(0);
return v___x_3404_;
}
else
{
lean_object* v_tail_3405_; 
v_tail_3405_ = lean_ctor_get(v_x_3402_, 1);
if (lean_obj_tag(v_tail_3405_) == 0)
{
lean_object* v_head_3406_; lean_object* v___x_3407_; 
lean_dec(v_x_3403_);
v_head_3406_ = lean_ctor_get(v_x_3402_, 0);
lean_inc(v_head_3406_);
lean_dec_ref(v_x_3402_);
v___x_3407_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3406_);
return v___x_3407_;
}
else
{
lean_object* v_head_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
lean_inc(v_tail_3405_);
v_head_3408_ = lean_ctor_get(v_x_3402_, 0);
lean_inc(v_head_3408_);
lean_dec_ref(v_x_3402_);
v___x_3409_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3408_);
v___x_3410_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(v_x_3403_, v___x_3409_, v_tail_3405_);
return v___x_3410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object* v_xs_3411_){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3412_ = lean_array_get_size(v_xs_3411_);
v___x_3413_ = lean_unsigned_to_nat(0u);
v___x_3414_ = lean_nat_dec_eq(v___x_3412_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3415_ = lean_array_to_list(v_xs_3411_);
v___x_3416_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3417_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(v___x_3415_, v___x_3416_);
v___x_3418_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3419_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
lean_ctor_set(v___x_3420_, 1, v___x_3417_);
v___x_3421_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3422_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3420_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3418_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = l_Std_Format_fill(v___x_3423_);
return v___x_3424_;
}
else
{
lean_object* v___x_3425_; 
lean_dec_ref(v_xs_3411_);
v___x_3425_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object* v_x_3444_, lean_object* v_prec_3445_){
_start:
{
switch(lean_obj_tag(v_x_3444_))
{
case 0:
{
lean_object* v_contents_3446_; lean_object* v___y_3448_; lean_object* v___x_3456_; uint8_t v___x_3457_; 
v_contents_3446_ = lean_ctor_get(v_x_3444_, 0);
lean_inc_ref(v_contents_3446_);
lean_dec_ref(v_x_3444_);
v___x_3456_ = lean_unsigned_to_nat(1024u);
v___x_3457_ = lean_nat_dec_le(v___x_3456_, v_prec_3445_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3448_ = v___x_3458_;
goto v___jp_3447_;
}
else
{
lean_object* v___x_3459_; 
v___x_3459_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3448_ = v___x_3459_;
goto v___jp_3447_;
}
v___jp_3447_:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3449_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2));
v___x_3450_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_contents_3446_);
v___x_3451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3449_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v___x_3452_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___y_3448_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = 0;
v___x_3454_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set_uint8(v___x_3454_, sizeof(void*)*1, v___x_3453_);
v___x_3455_ = l_Repr_addAppParen(v___x_3454_, v_prec_3445_);
return v___x_3455_;
}
}
case 1:
{
lean_object* v_content_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3480_; 
v_content_3460_ = lean_ctor_get(v_x_3444_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_x_3444_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3462_ = v_x_3444_;
v_isShared_3463_ = v_isSharedCheck_3480_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_content_3460_);
lean_dec(v_x_3444_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3480_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___y_3465_; lean_object* v___x_3476_; uint8_t v___x_3477_; 
v___x_3476_ = lean_unsigned_to_nat(1024u);
v___x_3477_ = lean_nat_dec_le(v___x_3476_, v_prec_3445_);
if (v___x_3477_ == 0)
{
lean_object* v___x_3478_; 
v___x_3478_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3465_ = v___x_3478_;
goto v___jp_3464_;
}
else
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3465_ = v___x_3479_;
goto v___jp_3464_;
}
v___jp_3464_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3466_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5));
v___x_3467_ = l_String_quote(v_content_3460_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set_tag(v___x_3462_, 3);
lean_ctor_set(v___x_3462_, 0, v___x_3467_);
v___x_3469_ = v___x_3462_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; uint8_t v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3466_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___y_3465_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = 0;
v___x_3473_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3473_, 0, v___x_3471_);
lean_ctor_set_uint8(v___x_3473_, sizeof(void*)*1, v___x_3472_);
v___x_3474_ = l_Repr_addAppParen(v___x_3473_, v_prec_3445_);
return v___x_3474_;
}
}
}
}
case 2:
{
lean_object* v_items_3481_; lean_object* v___y_3483_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v_items_3481_ = lean_ctor_get(v_x_3444_, 0);
lean_inc_ref(v_items_3481_);
lean_dec_ref(v_x_3444_);
v___x_3491_ = lean_unsigned_to_nat(1024u);
v___x_3492_ = lean_nat_dec_le(v___x_3491_, v_prec_3445_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; 
v___x_3493_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3483_ = v___x_3493_;
goto v___jp_3482_;
}
else
{
lean_object* v___x_3494_; 
v___x_3494_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3483_ = v___x_3494_;
goto v___jp_3482_;
}
v___jp_3482_:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3484_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8));
v___x_3485_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3481_);
v___x_3486_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3484_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___y_3483_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = 0;
v___x_3489_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3489_, 0, v___x_3487_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*1, v___x_3488_);
v___x_3490_ = l_Repr_addAppParen(v___x_3489_, v_prec_3445_);
return v___x_3490_;
}
}
case 3:
{
lean_object* v_start_3495_; lean_object* v_items_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3531_; 
v_start_3495_ = lean_ctor_get(v_x_3444_, 0);
v_items_3496_ = lean_ctor_get(v_x_3444_, 1);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_x_3444_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3498_ = v_x_3444_;
v_isShared_3499_ = v_isSharedCheck_3531_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_items_3496_);
lean_inc(v_start_3495_);
lean_dec(v_x_3444_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3531_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3516_; lean_object* v___x_3527_; uint8_t v___x_3528_; 
v___x_3527_ = lean_unsigned_to_nat(1024u);
v___x_3528_ = lean_nat_dec_le(v___x_3527_, v_prec_3445_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3516_ = v___x_3529_;
goto v___jp_3515_;
}
else
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3516_ = v___x_3530_;
goto v___jp_3515_;
}
v___jp_3500_:
{
lean_object* v___x_3506_; 
if (v_isShared_3499_ == 0)
{
lean_ctor_set_tag(v___x_3498_, 5);
lean_ctor_set(v___x_3498_, 1, v___y_3504_);
lean_ctor_set(v___x_3498_, 0, v___y_3502_);
v___x_3506_ = v___x_3498_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___y_3502_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v___y_3504_);
v___x_3506_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
lean_ctor_set(v___x_3507_, 1, v___y_3503_);
v___x_3508_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3496_);
v___x_3509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3507_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
v___x_3510_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3510_, 0, v___y_3501_);
lean_ctor_set(v___x_3510_, 1, v___x_3509_);
v___x_3511_ = 0;
v___x_3512_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3512_, 0, v___x_3510_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*1, v___x_3511_);
v___x_3513_ = l_Repr_addAppParen(v___x_3512_, v_prec_3445_);
return v___x_3513_;
}
}
v___jp_3515_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v___x_3517_ = lean_box(1);
v___x_3518_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11));
v___x_3519_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12, &l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12);
v___x_3520_ = lean_int_dec_lt(v_start_3495_, v___x_3519_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = l_Int_repr(v_start_3495_);
lean_dec(v_start_3495_);
v___x_3522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
v___y_3501_ = v___y_3516_;
v___y_3502_ = v___x_3518_;
v___y_3503_ = v___x_3517_;
v___y_3504_ = v___x_3522_;
goto v___jp_3500_;
}
else
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3523_ = lean_unsigned_to_nat(1024u);
v___x_3524_ = l_Int_repr(v_start_3495_);
lean_dec(v_start_3495_);
v___x_3525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
v___x_3526_ = l_Repr_addAppParen(v___x_3525_, v___x_3523_);
v___y_3501_ = v___y_3516_;
v___y_3502_ = v___x_3518_;
v___y_3503_ = v___x_3517_;
v___y_3504_ = v___x_3526_;
goto v___jp_3500_;
}
}
}
}
case 4:
{
lean_object* v_items_3532_; lean_object* v___y_3534_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v_items_3532_ = lean_ctor_get(v_x_3444_, 0);
lean_inc_ref(v_items_3532_);
lean_dec_ref(v_x_3444_);
v___x_3542_ = lean_unsigned_to_nat(1024u);
v___x_3543_ = lean_nat_dec_le(v___x_3542_, v_prec_3445_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; 
v___x_3544_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3534_ = v___x_3544_;
goto v___jp_3533_;
}
else
{
lean_object* v___x_3545_; 
v___x_3545_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3534_ = v___x_3545_;
goto v___jp_3533_;
}
v___jp_3533_:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3535_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15));
v___x_3536_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(v_items_3532_);
v___x_3537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3535_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
v___x_3538_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___y_3534_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = 0;
v___x_3540_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3540_, 0, v___x_3538_);
lean_ctor_set_uint8(v___x_3540_, sizeof(void*)*1, v___x_3539_);
v___x_3541_ = l_Repr_addAppParen(v___x_3540_, v_prec_3445_);
return v___x_3541_;
}
}
case 5:
{
lean_object* v_items_3546_; lean_object* v___y_3548_; lean_object* v___x_3556_; uint8_t v___x_3557_; 
v_items_3546_ = lean_ctor_get(v_x_3444_, 0);
lean_inc_ref(v_items_3546_);
lean_dec_ref(v_x_3444_);
v___x_3556_ = lean_unsigned_to_nat(1024u);
v___x_3557_ = lean_nat_dec_le(v___x_3556_, v_prec_3445_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3558_; 
v___x_3558_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3548_ = v___x_3558_;
goto v___jp_3547_;
}
else
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3548_ = v___x_3559_;
goto v___jp_3547_;
}
v___jp_3547_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3549_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18));
v___x_3550_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_items_3546_);
v___x_3551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3549_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___y_3548_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = 0;
v___x_3554_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3554_, 0, v___x_3552_);
lean_ctor_set_uint8(v___x_3554_, sizeof(void*)*1, v___x_3553_);
v___x_3555_ = l_Repr_addAppParen(v___x_3554_, v_prec_3445_);
return v___x_3555_;
}
}
case 6:
{
lean_object* v_content_3560_; lean_object* v___y_3562_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v_content_3560_ = lean_ctor_get(v_x_3444_, 0);
lean_inc_ref(v_content_3560_);
lean_dec_ref(v_x_3444_);
v___x_3570_ = lean_unsigned_to_nat(1024u);
v___x_3571_ = lean_nat_dec_le(v___x_3570_, v_prec_3445_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; 
v___x_3572_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3562_ = v___x_3572_;
goto v___jp_3561_;
}
else
{
lean_object* v___x_3573_; 
v___x_3573_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3562_ = v___x_3573_;
goto v___jp_3561_;
}
v___jp_3561_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; uint8_t v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3563_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21));
v___x_3564_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3560_);
v___x_3565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3563_);
lean_ctor_set(v___x_3565_, 1, v___x_3564_);
v___x_3566_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___y_3562_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = 0;
v___x_3568_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set_uint8(v___x_3568_, sizeof(void*)*1, v___x_3567_);
v___x_3569_ = l_Repr_addAppParen(v___x_3568_, v_prec_3445_);
return v___x_3569_;
}
}
default: 
{
lean_object* v_container_3574_; lean_object* v_content_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3623_; 
v_container_3574_ = lean_ctor_get(v_x_3444_, 0);
v_content_3575_ = lean_ctor_get(v_x_3444_, 1);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_x_3444_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3577_ = v_x_3444_;
v_isShared_3578_ = v_isSharedCheck_3623_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_content_3575_);
lean_inc(v_container_3574_);
lean_dec(v_x_3444_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3623_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___y_3580_; lean_object* v___x_3619_; uint8_t v___x_3620_; 
v___x_3619_ = lean_unsigned_to_nat(1024u);
v___x_3620_ = lean_nat_dec_le(v___x_3619_, v_prec_3445_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; 
v___x_3621_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3580_ = v___x_3621_;
goto v___jp_3579_;
}
else
{
lean_object* v___x_3622_; 
v___x_3622_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3580_ = v___x_3622_;
goto v___jp_3579_;
}
v___jp_3579_:
{
lean_object* v_name_3581_; lean_object* v_val_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3618_; 
v_name_3581_ = lean_ctor_get(v_container_3574_, 0);
v_val_3582_ = lean_ctor_get(v_container_3574_, 1);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_container_3574_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3584_ = v_container_3574_;
v_isShared_3585_ = v_isSharedCheck_3618_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_val_3582_);
lean_inc(v_name_3581_);
lean_dec(v_container_3574_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3618_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; 
v___x_3586_ = lean_box(1);
v___x_3587_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24));
v___x_3588_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3589_ = lean_unsigned_to_nat(0u);
v___x_3590_ = l_Lean_Name_reprPrec(v_name_3581_, v___x_3589_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set_tag(v___x_3584_, 5);
lean_ctor_set(v___x_3584_, 1, v___x_3590_);
lean_ctor_set(v___x_3584_, 0, v___x_3588_);
v___x_3592_ = v___x_3584_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3593_; uint8_t v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3597_; 
v___x_3593_ = l_Std_Format_nestD(v___x_3592_);
v___x_3594_ = 0;
v___x_3595_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3595_, 0, v___x_3593_);
lean_ctor_set_uint8(v___x_3595_, sizeof(void*)*1, v___x_3594_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set_tag(v___x_3577_, 5);
lean_ctor_set(v___x_3577_, 1, v___x_3586_);
lean_ctor_set(v___x_3577_, 0, v___x_3595_);
v___x_3597_ = v___x_3577_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v___x_3586_);
v___x_3597_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3598_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3599_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3582_);
lean_dec(v_val_3582_);
v___x_3600_ = l_Lean_Name_reprPrec(v___x_3599_, v___x_3589_);
v___x_3601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3598_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v___x_3602_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3601_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = l_Std_Format_nestD(v___x_3603_);
v___x_3605_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3605_, 0, v___x_3604_);
lean_ctor_set_uint8(v___x_3605_, sizeof(void*)*1, v___x_3594_);
v___x_3606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3597_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = l_Std_Format_nestD(v___x_3606_);
v___x_3608_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set_uint8(v___x_3608_, sizeof(void*)*1, v___x_3594_);
v___x_3609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3587_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
lean_ctor_set(v___x_3610_, 1, v___x_3586_);
v___x_3611_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3575_);
v___x_3612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3610_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___y_3580_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
lean_ctor_set_uint8(v___x_3614_, sizeof(void*)*1, v___x_3594_);
v___x_3615_ = l_Repr_addAppParen(v___x_3614_, v_prec_3445_);
return v___x_3615_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object* v___y_3624_){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = lean_unsigned_to_nat(0u);
v___x_3626_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v___y_3624_, v___x_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object* v_x_3627_, lean_object* v_prec_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_x_3627_, v_prec_3628_);
lean_dec(v_prec_3628_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object* v_xs_3630_){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; uint8_t v___x_3633_; 
v___x_3631_ = lean_array_get_size(v_xs_3630_);
v___x_3632_ = lean_unsigned_to_nat(0u);
v___x_3633_ = lean_nat_dec_eq(v___x_3631_, v___x_3632_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3634_ = lean_array_to_list(v_xs_3630_);
v___x_3635_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3636_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3634_, v___x_3635_);
v___x_3637_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3638_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
lean_ctor_set(v___x_3639_, 1, v___x_3636_);
v___x_3640_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3639_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
v___x_3642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3637_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = l_Std_Format_fill(v___x_3642_);
return v___x_3643_;
}
else
{
lean_object* v___x_3644_; 
lean_dec_ref(v_xs_3630_);
v___x_3644_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3644_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object* v_x_3648_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = ((lean_object*)(l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1));
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object* v_x_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3650_);
lean_dec(v_x_3650_);
return v_res_3651_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = lean_unsigned_to_nat(9u);
v___x_3662_ = lean_nat_to_int(v___x_3661_);
return v___x_3662_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_unsigned_to_nat(15u);
v___x_3667_ = lean_nat_to_int(v___x_3666_);
return v___x_3667_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = lean_unsigned_to_nat(11u);
v___x_3675_ = lean_nat_to_int(v___x_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object* v_x_3679_, lean_object* v_x_3680_, lean_object* v_x_3681_){
_start:
{
if (lean_obj_tag(v_x_3681_) == 0)
{
lean_dec(v_x_3679_);
return v_x_3680_;
}
else
{
lean_object* v_head_3682_; lean_object* v_tail_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3693_; 
v_head_3682_ = lean_ctor_get(v_x_3681_, 0);
v_tail_3683_ = lean_ctor_get(v_x_3681_, 1);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_x_3681_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3685_ = v_x_3681_;
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_tail_3683_);
lean_inc(v_head_3682_);
lean_dec(v_x_3681_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
lean_inc(v_x_3679_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set_tag(v___x_3685_, 5);
lean_ctor_set(v___x_3685_, 1, v_x_3679_);
lean_ctor_set(v___x_3685_, 0, v_x_3680_);
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_x_3680_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_x_3679_);
v___x_3688_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3689_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3682_);
v___x_3690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(v_x_3679_, v___x_3690_, v_tail_3683_);
return v___x_3691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object* v_x_3694_, lean_object* v_x_3695_){
_start:
{
if (lean_obj_tag(v_x_3694_) == 0)
{
lean_object* v___x_3696_; 
lean_dec(v_x_3695_);
v___x_3696_ = lean_box(0);
return v___x_3696_;
}
else
{
lean_object* v_tail_3697_; 
v_tail_3697_ = lean_ctor_get(v_x_3694_, 1);
if (lean_obj_tag(v_tail_3697_) == 0)
{
lean_object* v_head_3698_; lean_object* v___x_3699_; 
lean_dec(v_x_3695_);
v_head_3698_ = lean_ctor_get(v_x_3694_, 0);
lean_inc(v_head_3698_);
lean_dec_ref(v_x_3694_);
v___x_3699_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3698_);
return v___x_3699_;
}
else
{
lean_object* v_head_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_inc(v_tail_3697_);
v_head_3700_ = lean_ctor_get(v_x_3694_, 0);
lean_inc(v_head_3700_);
lean_dec_ref(v_x_3694_);
v___x_3701_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3700_);
v___x_3702_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(v_x_3695_, v___x_3701_, v_tail_3697_);
return v___x_3702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object* v_xs_3703_){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v___x_3704_ = lean_array_get_size(v_xs_3703_);
v___x_3705_ = lean_unsigned_to_nat(0u);
v___x_3706_ = lean_nat_dec_eq(v___x_3704_, v___x_3705_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3707_ = lean_array_to_list(v_xs_3703_);
v___x_3708_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3709_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(v___x_3707_, v___x_3708_);
v___x_3710_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3711_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
lean_ctor_set(v___x_3712_, 1, v___x_3709_);
v___x_3713_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3710_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = l_Std_Format_fill(v___x_3715_);
return v___x_3716_;
}
else
{
lean_object* v___x_3717_; 
lean_dec_ref(v_xs_3703_);
v___x_3717_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object* v_x_3718_){
_start:
{
lean_object* v_title_3719_; lean_object* v_titleString_3720_; lean_object* v_metadata_3721_; lean_object* v_content_3722_; lean_object* v_subParts_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v_title_3719_ = lean_ctor_get(v_x_3718_, 0);
lean_inc_ref(v_title_3719_);
v_titleString_3720_ = lean_ctor_get(v_x_3718_, 1);
lean_inc_ref(v_titleString_3720_);
v_metadata_3721_ = lean_ctor_get(v_x_3718_, 2);
lean_inc(v_metadata_3721_);
v_content_3722_ = lean_ctor_get(v_x_3718_, 3);
lean_inc_ref(v_content_3722_);
v_subParts_3723_ = lean_ctor_get(v_x_3718_, 4);
lean_inc_ref(v_subParts_3723_);
lean_dec_ref(v_x_3718_);
v___x_3724_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3725_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3));
v___x_3726_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4);
v___x_3727_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_title_3719_);
v___x_3728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3726_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = 0;
v___x_3730_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set_uint8(v___x_3730_, sizeof(void*)*1, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3725_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = lean_box(1);
v___x_3735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6));
v___x_3737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3735_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
lean_ctor_set(v___x_3738_, 1, v___x_3724_);
v___x_3739_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7);
v___x_3740_ = l_String_quote(v_titleString_3720_);
v___x_3741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
v___x_3742_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3739_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
v___x_3743_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
lean_ctor_set_uint8(v___x_3743_, sizeof(void*)*1, v___x_3729_);
v___x_3744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3738_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
lean_ctor_set(v___x_3745_, 1, v___x_3732_);
v___x_3746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
lean_ctor_set(v___x_3746_, 1, v___x_3734_);
v___x_3747_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9));
v___x_3748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3746_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
lean_ctor_set(v___x_3749_, 1, v___x_3724_);
v___x_3750_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3751_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_metadata_3721_);
lean_dec(v_metadata_3721_);
v___x_3752_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
lean_ctor_set_uint8(v___x_3753_, sizeof(void*)*1, v___x_3729_);
v___x_3754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3749_);
lean_ctor_set(v___x_3754_, 1, v___x_3753_);
v___x_3755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
lean_ctor_set(v___x_3755_, 1, v___x_3732_);
v___x_3756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
lean_ctor_set(v___x_3756_, 1, v___x_3734_);
v___x_3757_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11));
v___x_3758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3756_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
v___x_3759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
lean_ctor_set(v___x_3759_, 1, v___x_3724_);
v___x_3760_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12);
v___x_3761_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_content_3722_);
v___x_3762_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
lean_ctor_set_uint8(v___x_3763_, sizeof(void*)*1, v___x_3729_);
v___x_3764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3759_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
lean_ctor_set(v___x_3765_, 1, v___x_3732_);
v___x_3766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
lean_ctor_set(v___x_3766_, 1, v___x_3734_);
v___x_3767_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14));
v___x_3768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3766_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
lean_ctor_set(v___x_3769_, 1, v___x_3724_);
v___x_3770_ = l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(v_subParts_3723_);
v___x_3771_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3750_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
lean_ctor_set_uint8(v___x_3772_, sizeof(void*)*1, v___x_3729_);
v___x_3773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3769_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3775_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
lean_ctor_set(v___x_3776_, 1, v___x_3773_);
v___x_3777_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3776_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3774_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*1, v___x_3729_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object* v_x_3781_, lean_object* v_x_3782_, lean_object* v_x_3783_){
_start:
{
if (lean_obj_tag(v_x_3783_) == 0)
{
lean_dec(v_x_3781_);
return v_x_3782_;
}
else
{
lean_object* v_head_3784_; lean_object* v_tail_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3795_; 
v_head_3784_ = lean_ctor_get(v_x_3783_, 0);
v_tail_3785_ = lean_ctor_get(v_x_3783_, 1);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_x_3783_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3787_ = v_x_3783_;
v_isShared_3788_ = v_isSharedCheck_3795_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_tail_3785_);
lean_inc(v_head_3784_);
lean_dec(v_x_3783_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3795_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
lean_inc(v_x_3781_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set_tag(v___x_3787_, 5);
lean_ctor_set(v___x_3787_, 1, v_x_3781_);
lean_ctor_set(v___x_3787_, 0, v_x_3782_);
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_x_3782_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_x_3781_);
v___x_3790_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3784_);
v___x_3792_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3790_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v_x_3782_ = v___x_3792_;
v_x_3783_ = v_tail_3785_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object* v_x_3796_, lean_object* v_x_3797_){
_start:
{
lean_object* v_fst_3798_; lean_object* v_snd_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3809_; 
v_fst_3798_ = lean_ctor_get(v_x_3796_, 0);
v_snd_3799_ = lean_ctor_get(v_x_3796_, 1);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_x_3796_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3801_ = v_x_3796_;
v_isShared_3802_ = v_isSharedCheck_3809_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_snd_3799_);
lean_inc(v_fst_3798_);
lean_dec(v_x_3796_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3809_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3803_ = l_Lean_instReprDeclarationRange_repr___redArg(v_fst_3798_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set_tag(v___x_3801_, 1);
lean_ctor_set(v___x_3801_, 1, v_x_3797_);
lean_ctor_set(v___x_3801_, 0, v___x_3803_);
v___x_3805_ = v___x_3801_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_x_3797_);
v___x_3805_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3806_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_snd_3799_);
v___x_3807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
lean_ctor_set(v___x_3807_, 1, v___x_3805_);
return v___x_3807_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object* v_x_3810_, lean_object* v_x_3811_, lean_object* v_x_3812_){
_start:
{
if (lean_obj_tag(v_x_3812_) == 0)
{
lean_dec(v_x_3810_);
return v_x_3811_;
}
else
{
lean_object* v_head_3813_; lean_object* v_tail_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3823_; 
v_head_3813_ = lean_ctor_get(v_x_3812_, 0);
v_tail_3814_ = lean_ctor_get(v_x_3812_, 1);
v_isSharedCheck_3823_ = !lean_is_exclusive(v_x_3812_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3816_ = v_x_3812_;
v_isShared_3817_ = v_isSharedCheck_3823_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_tail_3814_);
lean_inc(v_head_3813_);
lean_dec(v_x_3812_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3823_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
lean_inc(v_x_3810_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set_tag(v___x_3816_, 5);
lean_ctor_set(v___x_3816_, 1, v_x_3810_);
lean_ctor_set(v___x_3816_, 0, v_x_3811_);
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_x_3811_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_x_3810_);
v___x_3819_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
lean_object* v___x_3820_; 
v___x_3820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
lean_ctor_set(v___x_3820_, 1, v_head_3813_);
v_x_3811_ = v___x_3820_;
v_x_3812_ = v_tail_3814_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object* v_x_3824_, lean_object* v_x_3825_){
_start:
{
if (lean_obj_tag(v_x_3824_) == 0)
{
lean_object* v___x_3826_; 
lean_dec(v_x_3825_);
v___x_3826_ = lean_box(0);
return v___x_3826_;
}
else
{
lean_object* v_tail_3827_; 
v_tail_3827_ = lean_ctor_get(v_x_3824_, 1);
if (lean_obj_tag(v_tail_3827_) == 0)
{
lean_object* v_head_3828_; 
lean_dec(v_x_3825_);
v_head_3828_ = lean_ctor_get(v_x_3824_, 0);
lean_inc(v_head_3828_);
lean_dec_ref(v_x_3824_);
return v_head_3828_;
}
else
{
lean_object* v_head_3829_; lean_object* v___x_3830_; 
lean_inc(v_tail_3827_);
v_head_3829_ = lean_ctor_get(v_x_3824_, 0);
lean_inc(v_head_3829_);
lean_dec_ref(v_x_3824_);
v___x_3830_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(v_x_3825_, v_head_3829_, v_tail_3827_);
return v___x_3830_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3832_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0));
v___x_3833_ = lean_string_length(v___x_3832_);
return v___x_3833_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1);
v___x_3835_ = lean_nat_to_int(v___x_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object* v_x_3840_){
_start:
{
lean_object* v_fst_3841_; lean_object* v_snd_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3864_; 
v_fst_3841_ = lean_ctor_get(v_x_3840_, 0);
v_snd_3842_ = lean_ctor_get(v_x_3840_, 1);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_x_3840_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3844_ = v_x_3840_;
v_isShared_3845_ = v_isSharedCheck_3864_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_snd_3842_);
lean_inc(v_fst_3841_);
lean_dec(v_x_3840_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3864_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3850_; 
v___x_3846_ = l_Nat_reprFast(v_fst_3841_);
v___x_3847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3846_);
v___x_3848_ = lean_box(0);
if (v_isShared_3845_ == 0)
{
lean_ctor_set_tag(v___x_3844_, 1);
lean_ctor_set(v___x_3844_, 1, v___x_3848_);
lean_ctor_set(v___x_3844_, 0, v___x_3847_);
v___x_3850_ = v___x_3844_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3847_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; uint8_t v___x_3861_; lean_object* v___x_3862_; 
v___x_3851_ = l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(v_snd_3842_, v___x_3850_);
v___x_3852_ = l_List_reverse___redArg(v___x_3851_);
v___x_3853_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3854_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(v___x_3852_, v___x_3853_);
v___x_3855_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2);
v___x_3856_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3));
v___x_3857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
lean_ctor_set(v___x_3857_, 1, v___x_3854_);
v___x_3858_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4));
v___x_3859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3857_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v___x_3860_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3855_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
v___x_3861_ = 0;
v___x_3862_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3862_, 0, v___x_3860_);
lean_ctor_set_uint8(v___x_3862_, sizeof(void*)*1, v___x_3861_);
return v___x_3862_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object* v_x_3865_, lean_object* v_x_3866_, lean_object* v_x_3867_){
_start:
{
if (lean_obj_tag(v_x_3867_) == 0)
{
lean_dec(v_x_3865_);
return v_x_3866_;
}
else
{
lean_object* v_head_3868_; lean_object* v_tail_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3879_; 
v_head_3868_ = lean_ctor_get(v_x_3867_, 0);
v_tail_3869_ = lean_ctor_get(v_x_3867_, 1);
v_isSharedCheck_3879_ = !lean_is_exclusive(v_x_3867_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3871_ = v_x_3867_;
v_isShared_3872_ = v_isSharedCheck_3879_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_tail_3869_);
lean_inc(v_head_3868_);
lean_dec(v_x_3867_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3879_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
lean_inc(v_x_3865_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set_tag(v___x_3871_, 5);
lean_ctor_set(v___x_3871_, 1, v_x_3865_);
lean_ctor_set(v___x_3871_, 0, v_x_3866_);
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_x_3866_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v_x_3865_);
v___x_3874_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3868_);
v___x_3876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3874_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
v_x_3866_ = v___x_3876_;
v_x_3867_ = v_tail_3869_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object* v_x_3880_, lean_object* v_x_3881_, lean_object* v_x_3882_){
_start:
{
if (lean_obj_tag(v_x_3882_) == 0)
{
lean_dec(v_x_3880_);
return v_x_3881_;
}
else
{
lean_object* v_head_3883_; lean_object* v_tail_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3894_; 
v_head_3883_ = lean_ctor_get(v_x_3882_, 0);
v_tail_3884_ = lean_ctor_get(v_x_3882_, 1);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_x_3882_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3886_ = v_x_3882_;
v_isShared_3887_ = v_isSharedCheck_3894_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_tail_3884_);
lean_inc(v_head_3883_);
lean_dec(v_x_3882_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3894_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
lean_inc(v_x_3880_);
if (v_isShared_3887_ == 0)
{
lean_ctor_set_tag(v___x_3886_, 5);
lean_ctor_set(v___x_3886_, 1, v_x_3880_);
lean_ctor_set(v___x_3886_, 0, v_x_3881_);
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_x_3881_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v_x_3880_);
v___x_3889_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3890_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3883_);
v___x_3891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3889_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(v_x_3880_, v___x_3891_, v_tail_3884_);
return v___x_3892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object* v_x_3895_, lean_object* v_x_3896_){
_start:
{
if (lean_obj_tag(v_x_3895_) == 0)
{
lean_object* v___x_3897_; 
lean_dec(v_x_3896_);
v___x_3897_ = lean_box(0);
return v___x_3897_;
}
else
{
lean_object* v_tail_3898_; 
v_tail_3898_ = lean_ctor_get(v_x_3895_, 1);
if (lean_obj_tag(v_tail_3898_) == 0)
{
lean_object* v_head_3899_; lean_object* v___x_3900_; 
lean_dec(v_x_3896_);
v_head_3899_ = lean_ctor_get(v_x_3895_, 0);
lean_inc(v_head_3899_);
lean_dec_ref(v_x_3895_);
v___x_3900_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3899_);
return v___x_3900_;
}
else
{
lean_object* v_head_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_inc(v_tail_3898_);
v_head_3901_ = lean_ctor_get(v_x_3895_, 0);
lean_inc(v_head_3901_);
lean_dec_ref(v_x_3895_);
v___x_3902_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3901_);
v___x_3903_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(v_x_3896_, v___x_3902_, v_tail_3898_);
return v___x_3903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object* v_xs_3904_){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v___x_3905_ = lean_array_get_size(v_xs_3904_);
v___x_3906_ = lean_unsigned_to_nat(0u);
v___x_3907_ = lean_nat_dec_eq(v___x_3905_, v___x_3906_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3908_ = lean_array_to_list(v_xs_3904_);
v___x_3909_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3910_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(v___x_3908_, v___x_3909_);
v___x_3911_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3912_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
lean_ctor_set(v___x_3913_, 1, v___x_3910_);
v___x_3914_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3913_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3911_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
v___x_3917_ = l_Std_Format_fill(v___x_3916_);
return v___x_3917_;
}
else
{
lean_object* v___x_3918_; 
lean_dec_ref(v_xs_3904_);
v___x_3918_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3918_;
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = lean_unsigned_to_nat(20u);
v___x_3935_ = lean_nat_to_int(v___x_3934_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object* v_x_3936_){
_start:
{
lean_object* v_text_3937_; lean_object* v_sections_3938_; lean_object* v_declarationRange_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v_text_3937_ = lean_ctor_get(v_x_3936_, 0);
lean_inc_ref(v_text_3937_);
v_sections_3938_ = lean_ctor_get(v_x_3936_, 1);
lean_inc_ref(v_sections_3938_);
v_declarationRange_3939_ = lean_ctor_get(v_x_3936_, 2);
lean_inc_ref(v_declarationRange_3939_);
lean_dec_ref(v_x_3936_);
v___x_3940_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3941_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3));
v___x_3942_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3943_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_text_3937_);
v___x_3944_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3942_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
v___x_3945_ = 0;
v___x_3946_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3946_, 0, v___x_3944_);
lean_ctor_set_uint8(v___x_3946_, sizeof(void*)*1, v___x_3945_);
v___x_3947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3941_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
v___x_3948_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3947_);
lean_ctor_set(v___x_3949_, 1, v___x_3948_);
v___x_3950_ = lean_box(1);
v___x_3951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3949_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
v___x_3952_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5));
v___x_3953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3951_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___x_3954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
lean_ctor_set(v___x_3954_, 1, v___x_3940_);
v___x_3955_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3956_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(v_sections_3938_);
v___x_3957_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3955_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
lean_ctor_set_uint8(v___x_3958_, sizeof(void*)*1, v___x_3945_);
v___x_3959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3954_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
lean_ctor_set(v___x_3960_, 1, v___x_3948_);
v___x_3961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
lean_ctor_set(v___x_3961_, 1, v___x_3950_);
v___x_3962_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7));
v___x_3963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3961_);
lean_ctor_set(v___x_3963_, 1, v___x_3962_);
v___x_3964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
lean_ctor_set(v___x_3964_, 1, v___x_3940_);
v___x_3965_ = lean_obj_once(&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8, &l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once, _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8);
v___x_3966_ = l_Lean_instReprDeclarationRange_repr___redArg(v_declarationRange_3939_);
v___x_3967_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3965_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
lean_ctor_set_uint8(v___x_3968_, sizeof(void*)*1, v___x_3945_);
v___x_3969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3964_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3971_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
lean_ctor_set(v___x_3972_, 1, v___x_3969_);
v___x_3973_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3972_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3970_);
lean_ctor_set(v___x_3975_, 1, v___x_3974_);
v___x_3976_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
lean_ctor_set_uint8(v___x_3976_, sizeof(void*)*1, v___x_3945_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object* v_x_3977_, lean_object* v_prec_3978_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(v_x_3977_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object* v_x_3980_, lean_object* v_prec_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Lean_VersoModuleDocs_instReprSnippet_repr(v_x_3980_, v_prec_3981_);
lean_dec(v_prec_3981_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object* v_x_3983_, lean_object* v_x_3984_){
_start:
{
lean_object* v___x_3985_; 
v___x_3985_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_x_3983_);
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object* v_x_3986_, lean_object* v_x_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(v_x_3986_, v_x_3987_);
lean_dec(v_x_3987_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_3989_, lean_object* v_prec_3990_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_x_3989_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_x_3992_, lean_object* v_prec_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(v_x_3992_, v_prec_3993_);
lean_dec(v_prec_3993_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object* v_x_3995_, lean_object* v_prec_3996_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_x_3995_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_x_3998_, lean_object* v_prec_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(v_x_3998_, v_prec_3999_);
lean_dec(v_prec_3999_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object* v_x_4001_, lean_object* v_x_4002_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_4001_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object* v_x_4004_, lean_object* v_x_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(v_x_4004_, v_x_4005_);
lean_dec(v_x_4005_);
lean_dec(v_x_4004_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object* v_x_4007_, lean_object* v_prec_4008_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_x_4007_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object* v_x_4010_, lean_object* v_prec_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(v_x_4010_, v_prec_4011_);
lean_dec(v_prec_4011_);
return v_res_4012_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object* v_level_4015_, lean_object* v_snippet_4016_){
_start:
{
lean_object* v_sections_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; uint8_t v___x_4020_; 
v_sections_4017_ = lean_ctor_get(v_snippet_4016_, 1);
v___x_4018_ = lean_unsigned_to_nat(0u);
v___x_4019_ = lean_array_get_size(v_sections_4017_);
v___x_4020_ = lean_nat_dec_lt(v___x_4018_, v___x_4019_);
if (v___x_4020_ == 0)
{
uint8_t v___x_4021_; 
v___x_4021_ = 1;
return v___x_4021_;
}
else
{
lean_object* v___x_4022_; lean_object* v_fst_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; uint8_t v___x_4026_; 
v___x_4022_ = lean_array_fget_borrowed(v_sections_4017_, v___x_4018_);
v_fst_4023_ = lean_ctor_get(v___x_4022_, 0);
v___x_4024_ = lean_unsigned_to_nat(1u);
v___x_4025_ = lean_nat_add(v_level_4015_, v___x_4024_);
v___x_4026_ = lean_nat_dec_le(v_fst_4023_, v___x_4025_);
lean_dec(v___x_4025_);
return v___x_4026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object* v_level_4027_, lean_object* v_snippet_4028_){
_start:
{
uint8_t v_res_4029_; lean_object* v_r_4030_; 
v_res_4029_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_level_4027_, v_snippet_4028_);
lean_dec_ref(v_snippet_4028_);
lean_dec(v_level_4027_);
v_r_4030_ = lean_box(v_res_4029_);
return v_r_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object* v_snippet_4031_){
_start:
{
lean_object* v_sections_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v_sections_4032_ = lean_ctor_get(v_snippet_4031_, 1);
v___x_4033_ = lean_array_get_size(v_sections_4032_);
v___x_4034_ = lean_unsigned_to_nat(1u);
v___x_4035_ = lean_nat_sub(v___x_4033_, v___x_4034_);
v___x_4036_ = lean_nat_dec_lt(v___x_4035_, v___x_4033_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; 
lean_dec(v___x_4035_);
v___x_4037_ = lean_box(0);
return v___x_4037_;
}
else
{
lean_object* v___x_4038_; lean_object* v_fst_4039_; lean_object* v___x_4040_; 
v___x_4038_ = lean_array_fget_borrowed(v_sections_4032_, v___x_4035_);
lean_dec(v___x_4035_);
v_fst_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_fst_4039_);
v___x_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4040_, 0, v_fst_4039_);
return v___x_4040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object* v_snippet_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4041_);
lean_dec_ref(v_snippet_4041_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object* v_snippet_4043_, lean_object* v_block_4044_){
_start:
{
lean_object* v_text_4045_; lean_object* v_sections_4046_; lean_object* v_declarationRange_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; uint8_t v___x_4050_; 
v_text_4045_ = lean_ctor_get(v_snippet_4043_, 0);
v_sections_4046_ = lean_ctor_get(v_snippet_4043_, 1);
v_declarationRange_4047_ = lean_ctor_get(v_snippet_4043_, 2);
v___x_4048_ = lean_array_get_size(v_sections_4046_);
v___x_4049_ = lean_unsigned_to_nat(0u);
v___x_4050_ = lean_nat_dec_eq(v___x_4048_, v___x_4049_);
if (v___x_4050_ == 0)
{
lean_object* v___x_4051_; lean_object* v___x_4052_; uint8_t v___x_4053_; 
v___x_4051_ = lean_unsigned_to_nat(1u);
v___x_4052_ = lean_nat_sub(v___x_4048_, v___x_4051_);
v___x_4053_ = lean_nat_dec_lt(v___x_4052_, v___x_4048_);
if (v___x_4053_ == 0)
{
lean_dec(v___x_4052_);
lean_dec_ref(v_block_4044_);
return v_snippet_4043_;
}
else
{
lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4097_; 
lean_inc_ref(v_declarationRange_4047_);
lean_inc_ref(v_sections_4046_);
lean_inc_ref(v_text_4045_);
v_isSharedCheck_4097_ = !lean_is_exclusive(v_snippet_4043_);
if (v_isSharedCheck_4097_ == 0)
{
lean_object* v_unused_4098_; lean_object* v_unused_4099_; lean_object* v_unused_4100_; 
v_unused_4098_ = lean_ctor_get(v_snippet_4043_, 2);
lean_dec(v_unused_4098_);
v_unused_4099_ = lean_ctor_get(v_snippet_4043_, 1);
lean_dec(v_unused_4099_);
v_unused_4100_ = lean_ctor_get(v_snippet_4043_, 0);
lean_dec(v_unused_4100_);
v___x_4055_ = v_snippet_4043_;
v_isShared_4056_ = v_isSharedCheck_4097_;
goto v_resetjp_4054_;
}
else
{
lean_dec(v_snippet_4043_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4097_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v_v_4057_; lean_object* v_snd_4058_; lean_object* v_snd_4059_; lean_object* v_fst_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4095_; 
v_v_4057_ = lean_array_fget(v_sections_4046_, v___x_4052_);
v_snd_4058_ = lean_ctor_get(v_v_4057_, 1);
lean_inc(v_snd_4058_);
v_snd_4059_ = lean_ctor_get(v_snd_4058_, 1);
lean_inc(v_snd_4059_);
v_fst_4060_ = lean_ctor_get(v_v_4057_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v_v_4057_);
if (v_isSharedCheck_4095_ == 0)
{
lean_object* v_unused_4096_; 
v_unused_4096_ = lean_ctor_get(v_v_4057_, 1);
lean_dec(v_unused_4096_);
v___x_4062_ = v_v_4057_;
v_isShared_4063_ = v_isSharedCheck_4095_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_fst_4060_);
lean_dec(v_v_4057_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4095_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v_fst_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4093_; 
v_fst_4064_ = lean_ctor_get(v_snd_4058_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_snd_4058_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; 
v_unused_4094_ = lean_ctor_get(v_snd_4058_, 1);
lean_dec(v_unused_4094_);
v___x_4066_ = v_snd_4058_;
v_isShared_4067_ = v_isSharedCheck_4093_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_fst_4064_);
lean_dec(v_snd_4058_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4093_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v_title_4068_; lean_object* v_titleString_4069_; lean_object* v_metadata_4070_; lean_object* v_content_4071_; lean_object* v_subParts_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4092_; 
v_title_4068_ = lean_ctor_get(v_snd_4059_, 0);
v_titleString_4069_ = lean_ctor_get(v_snd_4059_, 1);
v_metadata_4070_ = lean_ctor_get(v_snd_4059_, 2);
v_content_4071_ = lean_ctor_get(v_snd_4059_, 3);
v_subParts_4072_ = lean_ctor_get(v_snd_4059_, 4);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_snd_4059_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4074_ = v_snd_4059_;
v_isShared_4075_ = v_isSharedCheck_4092_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_subParts_4072_);
lean_inc(v_content_4071_);
lean_inc(v_metadata_4070_);
lean_inc(v_titleString_4069_);
lean_inc(v_title_4068_);
lean_dec(v_snd_4059_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4092_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4076_; lean_object* v_xs_x27_4077_; lean_object* v___x_4078_; lean_object* v___x_4080_; 
v___x_4076_ = lean_box(0);
v_xs_x27_4077_ = lean_array_fset(v_sections_4046_, v___x_4052_, v___x_4076_);
v___x_4078_ = lean_array_push(v_content_4071_, v_block_4044_);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 3, v___x_4078_);
v___x_4080_ = v___x_4074_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_title_4068_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_titleString_4069_);
lean_ctor_set(v_reuseFailAlloc_4091_, 2, v_metadata_4070_);
lean_ctor_set(v_reuseFailAlloc_4091_, 3, v___x_4078_);
lean_ctor_set(v_reuseFailAlloc_4091_, 4, v_subParts_4072_);
v___x_4080_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
lean_object* v___x_4082_; 
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 1, v___x_4080_);
v___x_4082_ = v___x_4066_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_fst_4064_);
lean_ctor_set(v_reuseFailAlloc_4090_, 1, v___x_4080_);
v___x_4082_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
lean_object* v___x_4084_; 
if (v_isShared_4063_ == 0)
{
lean_ctor_set(v___x_4062_, 1, v___x_4082_);
v___x_4084_ = v___x_4062_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_fst_4060_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4085_ = lean_array_fset(v_xs_x27_4077_, v___x_4052_, v___x_4084_);
lean_dec(v___x_4052_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 1, v___x_4085_);
v___x_4087_ = v___x_4055_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_text_4045_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v___x_4085_);
lean_ctor_set(v_reuseFailAlloc_4088_, 2, v_declarationRange_4047_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
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
lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4108_; 
lean_inc_ref(v_declarationRange_4047_);
lean_inc_ref(v_sections_4046_);
lean_inc_ref(v_text_4045_);
v_isSharedCheck_4108_ = !lean_is_exclusive(v_snippet_4043_);
if (v_isSharedCheck_4108_ == 0)
{
lean_object* v_unused_4109_; lean_object* v_unused_4110_; lean_object* v_unused_4111_; 
v_unused_4109_ = lean_ctor_get(v_snippet_4043_, 2);
lean_dec(v_unused_4109_);
v_unused_4110_ = lean_ctor_get(v_snippet_4043_, 1);
lean_dec(v_unused_4110_);
v_unused_4111_ = lean_ctor_get(v_snippet_4043_, 0);
lean_dec(v_unused_4111_);
v___x_4102_ = v_snippet_4043_;
v_isShared_4103_ = v_isSharedCheck_4108_;
goto v_resetjp_4101_;
}
else
{
lean_dec(v_snippet_4043_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4108_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4104_; lean_object* v___x_4106_; 
v___x_4104_ = lean_array_push(v_text_4045_, v_block_4044_);
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v___x_4104_);
v___x_4106_ = v___x_4102_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4104_);
lean_ctor_set(v_reuseFailAlloc_4107_, 1, v_sections_4046_);
lean_ctor_set(v_reuseFailAlloc_4107_, 2, v_declarationRange_4047_);
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
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object* v_snippet_4112_, lean_object* v_level_4113_, lean_object* v_range_4114_, lean_object* v_part_4115_){
_start:
{
lean_object* v_text_4116_; lean_object* v_sections_4117_; lean_object* v_declarationRange_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4128_; 
v_text_4116_ = lean_ctor_get(v_snippet_4112_, 0);
v_sections_4117_ = lean_ctor_get(v_snippet_4112_, 1);
v_declarationRange_4118_ = lean_ctor_get(v_snippet_4112_, 2);
v_isSharedCheck_4128_ = !lean_is_exclusive(v_snippet_4112_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4120_ = v_snippet_4112_;
v_isShared_4121_ = v_isSharedCheck_4128_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_declarationRange_4118_);
lean_inc(v_sections_4117_);
lean_inc(v_text_4116_);
lean_dec(v_snippet_4112_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4128_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4126_; 
v___x_4122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4122_, 0, v_range_4114_);
lean_ctor_set(v___x_4122_, 1, v_part_4115_);
v___x_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4123_, 0, v_level_4113_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = lean_array_push(v_sections_4117_, v___x_4123_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 1, v___x_4124_);
v___x_4126_ = v___x_4120_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_text_4116_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4127_, 2, v_declarationRange_4118_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0(lean_object* v___x_4129_, lean_object* v___x_4130_, lean_object* v_x_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v___x_4129_, v___x_4130_, v___y_4132_, v___y_4133_, v___y_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_4136_, lean_object* v___x_4137_, lean_object* v_x_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Lean_instToMarkdownSnippet___lam__0(v___x_4136_, v___x_4137_, v_x_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
lean_dec_ref(v___y_4140_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1(lean_object* v___x_4143_, lean_object* v___x_4144_, lean_object* v___x_4145_, lean_object* v_a_4146_, lean_object* v_x_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v___x_4151_; lean_object* v_snd_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4160_; 
v___x_4151_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v___x_4143_, v___x_4144_, v_a_4146_, v___y_4149_, v___y_4150_);
v_snd_4152_ = lean_ctor_get(v___x_4151_, 1);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4160_ == 0)
{
lean_object* v_unused_4161_; 
v_unused_4161_ = lean_ctor_get(v___x_4151_, 0);
lean_dec(v_unused_4161_);
v___x_4154_ = v___x_4151_;
v_isShared_4155_ = v_isSharedCheck_4160_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_snd_4152_);
lean_dec(v___x_4151_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4160_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4156_; lean_object* v___x_4158_; 
v___x_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4145_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 0, v___x_4156_);
v___x_4158_ = v___x_4154_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4156_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v_snd_4152_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_4162_, lean_object* v___x_4163_, lean_object* v___x_4164_, lean_object* v_a_4165_, lean_object* v_x_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_instToMarkdownSnippet___lam__1(v___x_4162_, v___x_4163_, v___x_4164_, v_a_4165_, v_x_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
lean_dec_ref(v___y_4168_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2(lean_object* v___x_4171_, lean_object* v___x_4172_, lean_object* v_a_4173_, lean_object* v_x_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v___x_4178_; lean_object* v_snd_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4187_; 
v___x_4178_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_box(0), v___x_4171_, v_a_4173_, v___y_4176_, v___y_4177_);
v_snd_4179_ = lean_ctor_get(v___x_4178_, 1);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4187_ == 0)
{
lean_object* v_unused_4188_; 
v_unused_4188_ = lean_ctor_get(v___x_4178_, 0);
lean_dec(v_unused_4188_);
v___x_4181_ = v___x_4178_;
v_isShared_4182_ = v_isSharedCheck_4187_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_snd_4179_);
lean_dec(v___x_4178_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4187_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4183_; lean_object* v___x_4185_; 
v___x_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4172_);
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 0, v___x_4183_);
v___x_4185_ = v___x_4181_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4183_);
lean_ctor_set(v_reuseFailAlloc_4186_, 1, v_snd_4179_);
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
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2___boxed(lean_object* v___x_4189_, lean_object* v___x_4190_, lean_object* v_a_4191_, lean_object* v_x_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l_Lean_instToMarkdownSnippet___lam__2(v___x_4189_, v___x_4190_, v_a_4191_, v_x_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
lean_dec_ref(v___y_4194_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3(uint32_t v___x_4197_, lean_object* v_s_4198_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = lean_string_push(v_s_4198_, v___x_4197_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3___boxed(lean_object* v___x_4200_, lean_object* v_s_4201_){
_start:
{
uint32_t v___x_5743__boxed_4202_; lean_object* v_res_4203_; 
v___x_5743__boxed_4202_ = lean_unbox_uint32(v___x_4200_);
lean_dec(v___x_4200_);
v_res_4203_ = l_Lean_instToMarkdownSnippet___lam__3(v___x_5743__boxed_4202_, v_s_4201_);
return v_res_4203_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_4204_; lean_object* v___x_4205_; 
v___x_4204_ = 35;
v___x_4205_ = lean_box_uint32(v___x_4204_);
return v___x_4205_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0(void){
_start:
{
lean_object* v___x_4206_; lean_object* v___f_4207_; 
v___x_4206_ = l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1;
v___f_4207_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__3___boxed), 2, 1);
lean_closure_set(v___f_4207_, 0, v___x_4206_);
return v___f_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4(lean_object* v___x_4208_, lean_object* v___f_4209_, lean_object* v___x_4210_, lean_object* v___f_4211_, lean_object* v_a_4212_, lean_object* v_x_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v_snd_4217_; lean_object* v_fst_4218_; lean_object* v_snd_4219_; lean_object* v___x_4220_; lean_object* v___f_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v_snd_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v_snd_4229_; lean_object* v_title_4230_; lean_object* v_content_4231_; size_t v_sz_4232_; size_t v___x_4233_; lean_object* v___x_5585__overap_4234_; lean_object* v___x_4235_; lean_object* v_snd_4236_; lean_object* v___x_4237_; lean_object* v_snd_4238_; size_t v_sz_4239_; lean_object* v___x_5591__overap_4240_; lean_object* v___x_4241_; lean_object* v_snd_4242_; lean_object* v___x_4243_; lean_object* v_snd_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4252_; 
v_snd_4217_ = lean_ctor_get(v_a_4212_, 1);
lean_inc(v_snd_4217_);
v_fst_4218_ = lean_ctor_get(v_a_4212_, 0);
lean_inc(v_fst_4218_);
lean_dec_ref(v_a_4212_);
v_snd_4219_ = lean_ctor_get(v_snd_4217_, 1);
lean_inc(v_snd_4219_);
lean_dec(v_snd_4217_);
v___x_4220_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___f_4221_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___lam__4___closed__0, &l_Lean_instToMarkdownSnippet___lam__4___closed__0_once, _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0);
v___x_4222_ = lean_unsigned_to_nat(1u);
v___x_4223_ = lean_nat_add(v_fst_4218_, v___x_4222_);
lean_dec(v_fst_4218_);
v___x_4224_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_4221_, v___x_4223_, v___x_4220_);
v___x_4225_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_4224_, v___y_4216_);
lean_dec(v___x_4224_);
v_snd_4226_ = lean_ctor_get(v___x_4225_, 1);
lean_inc(v_snd_4226_);
lean_dec_ref(v___x_4225_);
v___x_4227_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0));
v___x_4228_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_4227_, v_snd_4226_);
v_snd_4229_ = lean_ctor_get(v___x_4228_, 1);
lean_inc(v_snd_4229_);
lean_dec_ref(v___x_4228_);
v_title_4230_ = lean_ctor_get(v_snd_4219_, 0);
lean_inc_ref(v_title_4230_);
v_content_4231_ = lean_ctor_get(v_snd_4219_, 3);
lean_inc_ref(v_content_4231_);
lean_dec(v_snd_4219_);
v_sz_4232_ = lean_array_size(v_title_4230_);
v___x_4233_ = ((size_t)0ULL);
lean_inc_ref(v___x_4208_);
v___x_5585__overap_4234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4208_, v_title_4230_, v___f_4209_, v_sz_4232_, v___x_4233_, v___x_4210_);
lean_inc_ref(v___y_4215_);
v___x_4235_ = lean_apply_2(v___x_5585__overap_4234_, v___y_4215_, v_snd_4229_);
v_snd_4236_ = lean_ctor_get(v___x_4235_, 1);
lean_inc(v_snd_4236_);
lean_dec_ref(v___x_4235_);
v___x_4237_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4236_);
v_snd_4238_ = lean_ctor_get(v___x_4237_, 1);
lean_inc(v_snd_4238_);
lean_dec_ref(v___x_4237_);
v_sz_4239_ = lean_array_size(v_content_4231_);
v___x_5591__overap_4240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4208_, v_content_4231_, v___f_4211_, v_sz_4239_, v___x_4233_, v___x_4210_);
lean_inc_ref(v___y_4215_);
v___x_4241_ = lean_apply_2(v___x_5591__overap_4240_, v___y_4215_, v_snd_4238_);
v_snd_4242_ = lean_ctor_get(v___x_4241_, 1);
lean_inc(v_snd_4242_);
lean_dec_ref(v___x_4241_);
v___x_4243_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4242_);
v_snd_4244_ = lean_ctor_get(v___x_4243_, 1);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4252_ == 0)
{
lean_object* v_unused_4253_; 
v_unused_4253_ = lean_ctor_get(v___x_4243_, 0);
lean_dec(v_unused_4253_);
v___x_4246_ = v___x_4243_;
v_isShared_4247_ = v_isSharedCheck_4252_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_snd_4244_);
lean_dec(v___x_4243_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4252_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4210_);
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 0, v___x_4248_);
v___x_4250_ = v___x_4246_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
lean_ctor_set(v_reuseFailAlloc_4251_, 1, v_snd_4244_);
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
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4___boxed(lean_object* v___x_4254_, lean_object* v___f_4255_, lean_object* v___x_4256_, lean_object* v___f_4257_, lean_object* v_a_4258_, lean_object* v_x_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_instToMarkdownSnippet___lam__4(v___x_4254_, v___f_4255_, v___x_4256_, v___f_4257_, v_a_4258_, v_x_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
lean_dec_ref(v___y_4261_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5(lean_object* v___x_4264_, lean_object* v___x_4265_, lean_object* v___x_4266_, lean_object* v___f_4267_, lean_object* v_x_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v_text_4271_; lean_object* v_sections_4272_; lean_object* v_snd_4274_; lean_object* v___y_4295_; lean_object* v___x_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; 
v_text_4271_ = lean_ctor_get(v_x_4268_, 0);
lean_inc_ref(v_text_4271_);
v_sections_4272_ = lean_ctor_get(v_x_4268_, 1);
lean_inc_ref(v_sections_4272_);
lean_dec_ref(v_x_4268_);
v___x_4297_ = lean_unsigned_to_nat(0u);
v___x_4298_ = lean_array_get_size(v_text_4271_);
v___x_4299_ = lean_nat_dec_lt(v___x_4297_, v___x_4298_);
if (v___x_4299_ == 0)
{
lean_dec_ref(v_text_4271_);
lean_dec_ref(v___f_4267_);
v_snd_4274_ = v___y_4270_;
goto v___jp_4273_;
}
else
{
lean_object* v___x_4300_; uint8_t v___x_4301_; 
v___x_4300_ = lean_box(0);
v___x_4301_ = lean_nat_dec_le(v___x_4298_, v___x_4298_);
if (v___x_4301_ == 0)
{
if (v___x_4299_ == 0)
{
lean_dec_ref(v_text_4271_);
lean_dec_ref(v___f_4267_);
v_snd_4274_ = v___y_4270_;
goto v___jp_4273_;
}
else
{
size_t v___x_4302_; size_t v___x_4303_; lean_object* v___x_5634__overap_4304_; lean_object* v___x_4305_; 
v___x_4302_ = ((size_t)0ULL);
v___x_4303_ = lean_usize_of_nat(v___x_4298_);
lean_inc_ref(v___x_4266_);
v___x_5634__overap_4304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4266_, v___f_4267_, v_text_4271_, v___x_4302_, v___x_4303_, v___x_4300_);
lean_inc_ref(v___y_4269_);
v___x_4305_ = lean_apply_2(v___x_5634__overap_4304_, v___y_4269_, v___y_4270_);
v___y_4295_ = v___x_4305_;
goto v___jp_4294_;
}
}
else
{
size_t v___x_4306_; size_t v___x_4307_; lean_object* v___x_5637__overap_4308_; lean_object* v___x_4309_; 
v___x_4306_ = ((size_t)0ULL);
v___x_4307_ = lean_usize_of_nat(v___x_4298_);
lean_inc_ref(v___x_4266_);
v___x_5637__overap_4308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4266_, v___f_4267_, v_text_4271_, v___x_4306_, v___x_4307_, v___x_4300_);
lean_inc_ref(v___y_4269_);
v___x_4309_ = lean_apply_2(v___x_5637__overap_4308_, v___y_4269_, v___y_4270_);
v___y_4295_ = v___x_4309_;
goto v___jp_4294_;
}
}
v___jp_4273_:
{
lean_object* v___x_4275_; lean_object* v_snd_4276_; lean_object* v___x_4277_; lean_object* v___f_4278_; lean_object* v___f_4279_; lean_object* v___f_4280_; size_t v_sz_4281_; size_t v___x_4282_; lean_object* v___x_5619__overap_4283_; lean_object* v___x_4284_; lean_object* v_snd_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
v___x_4275_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4274_);
v_snd_4276_ = lean_ctor_get(v___x_4275_, 1);
lean_inc(v_snd_4276_);
lean_dec_ref(v___x_4275_);
v___x_4277_ = lean_box(0);
lean_inc_ref(v___x_4264_);
v___f_4278_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__1___boxed), 8, 3);
lean_closure_set(v___f_4278_, 0, v___x_4264_);
lean_closure_set(v___f_4278_, 1, v___x_4265_);
lean_closure_set(v___f_4278_, 2, v___x_4277_);
v___f_4279_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_4279_, 0, v___x_4264_);
lean_closure_set(v___f_4279_, 1, v___x_4277_);
lean_inc_ref(v___x_4266_);
v___f_4280_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__4___boxed), 9, 4);
lean_closure_set(v___f_4280_, 0, v___x_4266_);
lean_closure_set(v___f_4280_, 1, v___f_4279_);
lean_closure_set(v___f_4280_, 2, v___x_4277_);
lean_closure_set(v___f_4280_, 3, v___f_4278_);
v_sz_4281_ = lean_array_size(v_sections_4272_);
v___x_4282_ = ((size_t)0ULL);
v___x_5619__overap_4283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4266_, v_sections_4272_, v___f_4280_, v_sz_4281_, v___x_4282_, v___x_4277_);
lean_inc_ref(v___y_4269_);
v___x_4284_ = lean_apply_2(v___x_5619__overap_4283_, v___y_4269_, v_snd_4276_);
v_snd_4285_ = lean_ctor_get(v___x_4284_, 1);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4292_ == 0)
{
lean_object* v_unused_4293_; 
v_unused_4293_ = lean_ctor_get(v___x_4284_, 0);
lean_dec(v_unused_4293_);
v___x_4287_ = v___x_4284_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_snd_4285_);
lean_dec(v___x_4284_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
lean_ctor_set(v___x_4287_, 0, v___x_4277_);
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4277_);
lean_ctor_set(v_reuseFailAlloc_4291_, 1, v_snd_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
v___jp_4294_:
{
lean_object* v_snd_4296_; 
v_snd_4296_ = lean_ctor_get(v___y_4295_, 1);
lean_inc(v_snd_4296_);
lean_dec_ref(v___y_4295_);
v_snd_4274_ = v_snd_4296_;
goto v___jp_4273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5___boxed(lean_object* v___x_4310_, lean_object* v___x_4311_, lean_object* v___x_4312_, lean_object* v___f_4313_, lean_object* v_x_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Lean_instToMarkdownSnippet___lam__5(v___x_4310_, v___x_4311_, v___x_4312_, v___f_4313_, v_x_4314_, v___y_4315_, v___y_4316_);
lean_dec_ref(v___y_4315_);
return v_res_4317_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___f_4320_; 
v___x_4318_ = l_Lean_instMarkdownBlockElabInlineElabBlock;
v___x_4319_ = l_Lean_instMarkdownInlineElabInline;
v___f_4320_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__0___boxed), 6, 2);
lean_closure_set(v___f_4320_, 0, v___x_4319_);
lean_closure_set(v___f_4320_, 1, v___x_4318_);
return v___f_4320_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___closed__1(void){
_start:
{
lean_object* v___f_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___f_4325_; 
v___f_4321_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___closed__0, &l_Lean_instToMarkdownSnippet___closed__0_once, _init_l_Lean_instToMarkdownSnippet___closed__0);
v___x_4322_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__20, &l_Lean_instMarkdownInlineElabInline___closed__20_once, _init_l_Lean_instMarkdownInlineElabInline___closed__20);
v___x_4323_ = l_Lean_instMarkdownBlockElabInlineElabBlock;
v___x_4324_ = l_Lean_instMarkdownInlineElabInline;
v___f_4325_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__5___boxed), 7, 4);
lean_closure_set(v___f_4325_, 0, v___x_4324_);
lean_closure_set(v___f_4325_, 1, v___x_4323_);
lean_closure_set(v___f_4325_, 2, v___x_4322_);
lean_closure_set(v___f_4325_, 3, v___f_4321_);
return v___f_4325_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet(void){
_start:
{
lean_object* v___f_4326_; 
v___f_4326_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___closed__1, &l_Lean_instToMarkdownSnippet___closed__1_once, _init_l_Lean_instToMarkdownSnippet___closed__1);
return v___f_4326_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0(void){
_start:
{
lean_object* v___x_4327_; 
v___x_4327_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_4327_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1(void){
_start:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4328_ = lean_box(0);
v___x_4329_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_4330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4329_);
lean_ctor_set(v___x_4330_, 1, v___x_4328_);
return v___x_4330_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default(void){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__1, &l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1);
return v___x_4331_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs(void){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l_Lean_instInhabitedVersoModuleDocs_default;
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object* v___x_4339_, lean_object* v_v_4340_, lean_object* v_x_4341_){
_start:
{
lean_object* v_snippets_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4365_; 
v_snippets_4342_ = lean_ctor_get(v_v_4340_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v_v_4340_);
if (v_isSharedCheck_4365_ == 0)
{
lean_object* v_unused_4366_; 
v_unused_4366_ = lean_ctor_get(v_v_4340_, 1);
lean_dec(v_unused_4366_);
v___x_4344_ = v_v_4340_;
v_isShared_4345_ = v_isSharedCheck_4365_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_snippets_4342_);
lean_dec(v_v_4340_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4365_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4353_; 
v___x_4346_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___x_4347_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_4348_ = lean_box(1);
v___x_4349_ = ((lean_object*)(l_Lean_instReprVersoModuleDocs___lam__0___closed__2));
v___x_4350_ = l_Lean_PersistentArray_toArray___redArg(v_snippets_4342_);
lean_dec_ref(v_snippets_4342_);
v___x_4351_ = l_Array_repr___redArg(v___x_4339_, v___x_4350_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set_tag(v___x_4344_, 5);
lean_ctor_set(v___x_4344_, 1, v___x_4351_);
lean_ctor_set(v___x_4344_, 0, v___x_4349_);
v___x_4353_ = v___x_4344_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4349_);
lean_ctor_set(v_reuseFailAlloc_4364_, 1, v___x_4351_);
v___x_4353_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
lean_object* v___x_4354_; uint8_t v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4354_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4346_);
lean_ctor_set(v___x_4354_, 1, v___x_4353_);
v___x_4355_ = 0;
v___x_4356_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4356_, 0, v___x_4354_);
lean_ctor_set_uint8(v___x_4356_, sizeof(void*)*1, v___x_4355_);
lean_inc_ref(v___x_4356_);
v___x_4357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4347_);
lean_ctor_set(v___x_4357_, 1, v___x_4356_);
v___x_4358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4357_);
lean_ctor_set(v___x_4358_, 1, v___x_4348_);
v___x_4359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4358_);
lean_ctor_set(v___x_4359_, 1, v___x_4356_);
v___x_4360_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_4361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4359_);
lean_ctor_set(v___x_4361_, 1, v___x_4360_);
v___x_4362_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4346_);
lean_ctor_set(v___x_4362_, 1, v___x_4361_);
v___x_4363_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
lean_ctor_set_uint8(v___x_4363_, sizeof(void*)*1, v___x_4355_);
return v___x_4363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object* v___x_4367_, lean_object* v_v_4368_, lean_object* v_x_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Lean_instReprVersoModuleDocs___lam__0(v___x_4367_, v_v_4368_, v_x_4369_);
lean_dec(v_x_4369_);
return v_res_4370_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object* v_docs_4374_){
_start:
{
lean_object* v_snippets_4375_; uint8_t v___x_4376_; 
v_snippets_4375_ = lean_ctor_get(v_docs_4374_, 0);
v___x_4376_ = l_Lean_PersistentArray_isEmpty___redArg(v_snippets_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object* v_docs_4377_){
_start:
{
uint8_t v_res_4378_; lean_object* v_r_4379_; 
v_res_4378_ = l_Lean_VersoModuleDocs_isEmpty(v_docs_4377_);
lean_dec_ref(v_docs_4377_);
v_r_4379_ = lean_box(v_res_4378_);
return v_r_4379_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object* v_docs_4380_, lean_object* v_snippet_4381_){
_start:
{
lean_object* v_terminalNesting_4382_; 
v_terminalNesting_4382_ = lean_ctor_get(v_docs_4380_, 1);
if (lean_obj_tag(v_terminalNesting_4382_) == 1)
{
lean_object* v_val_4383_; uint8_t v___x_4384_; 
v_val_4383_ = lean_ctor_get(v_terminalNesting_4382_, 0);
v___x_4384_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4383_, v_snippet_4381_);
return v___x_4384_;
}
else
{
uint8_t v___x_4385_; 
v___x_4385_ = 1;
return v___x_4385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object* v_docs_4386_, lean_object* v_snippet_4387_){
_start:
{
uint8_t v_res_4388_; lean_object* v_r_4389_; 
v_res_4388_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4386_, v_snippet_4387_);
lean_dec_ref(v_snippet_4387_);
lean_dec_ref(v_docs_4386_);
v_r_4389_ = lean_box(v_res_4388_);
return v_r_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object* v_docs_4393_, lean_object* v_snippet_4394_){
_start:
{
uint8_t v___x_4395_; 
v___x_4395_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4393_, v_snippet_4394_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4396_; 
lean_dec_ref(v_snippet_4394_);
lean_dec_ref(v_docs_4393_);
v___x_4396_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__1));
return v___x_4396_;
}
else
{
lean_object* v_snippets_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4407_; 
v_snippets_4397_ = lean_ctor_get(v_docs_4393_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v_docs_4393_);
if (v_isSharedCheck_4407_ == 0)
{
lean_object* v_unused_4408_; 
v_unused_4408_ = lean_ctor_get(v_docs_4393_, 1);
lean_dec(v_unused_4408_);
v___x_4399_ = v_docs_4393_;
v_isShared_4400_ = v_isSharedCheck_4407_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_snippets_4397_);
lean_dec(v_docs_4393_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4407_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4404_; 
lean_inc_ref(v_snippet_4394_);
v___x_4401_ = l_Lean_PersistentArray_push___redArg(v_snippets_4397_, v_snippet_4394_);
v___x_4402_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4394_);
lean_dec_ref(v_snippet_4394_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 1, v___x_4402_);
lean_ctor_set(v___x_4399_, 0, v___x_4401_);
v___x_4404_ = v___x_4399_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4401_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v___x_4402_);
v___x_4404_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
lean_object* v___x_4405_; 
v___x_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4404_);
return v___x_4405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object* v_msg_4409_){
_start:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4410_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_4411_ = lean_panic_fn(v___x_4410_, v_msg_4409_);
return v___x_4411_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_add_x21___closed__2(void){
_start:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4414_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__0));
v___x_4415_ = lean_unsigned_to_nat(4u);
v___x_4416_ = lean_unsigned_to_nat(336u);
v___x_4417_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__1));
v___x_4418_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__0));
v___x_4419_ = l_mkPanicMessageWithDecl(v___x_4418_, v___x_4417_, v___x_4416_, v___x_4415_, v___x_4414_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object* v_docs_4420_, lean_object* v_snippet_4421_){
_start:
{
lean_object* v_snippets_4422_; lean_object* v_terminalNesting_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4437_; 
v_snippets_4422_ = lean_ctor_get(v_docs_4420_, 0);
v_terminalNesting_4423_ = lean_ctor_get(v_docs_4420_, 1);
v_isSharedCheck_4437_ = !lean_is_exclusive(v_docs_4420_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4425_ = v_docs_4420_;
v_isShared_4426_ = v_isSharedCheck_4437_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_terminalNesting_4423_);
lean_inc(v_snippets_4422_);
lean_dec(v_docs_4420_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4437_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
if (lean_obj_tag(v_terminalNesting_4423_) == 1)
{
lean_object* v_val_4433_; uint8_t v___x_4434_; 
v_val_4433_ = lean_ctor_get(v_terminalNesting_4423_, 0);
lean_inc(v_val_4433_);
lean_dec_ref(v_terminalNesting_4423_);
v___x_4434_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4433_, v_snippet_4421_);
lean_dec(v_val_4433_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
lean_del_object(v___x_4425_);
lean_dec_ref(v_snippets_4422_);
lean_dec_ref(v_snippet_4421_);
v___x_4435_ = lean_obj_once(&l_Lean_VersoModuleDocs_add_x21___closed__2, &l_Lean_VersoModuleDocs_add_x21___closed__2_once, _init_l_Lean_VersoModuleDocs_add_x21___closed__2);
v___x_4436_ = l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(v___x_4435_);
return v___x_4436_;
}
else
{
goto v___jp_4427_;
}
}
else
{
lean_dec(v_terminalNesting_4423_);
goto v___jp_4427_;
}
v___jp_4427_:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4431_; 
lean_inc_ref(v_snippet_4421_);
v___x_4428_ = l_Lean_PersistentArray_push___redArg(v_snippets_4422_, v_snippet_4421_);
v___x_4429_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4421_);
lean_dec_ref(v_snippet_4421_);
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 1, v___x_4429_);
lean_ctor_set(v___x_4425_, 0, v___x_4428_);
v___x_4431_ = v___x_4425_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4428_);
lean_ctor_set(v_reuseFailAlloc_4432_, 1, v___x_4429_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object* v_ctx_4438_){
_start:
{
lean_object* v_context_4439_; lean_object* v___x_4440_; 
v_context_4439_ = lean_ctor_get(v_ctx_4438_, 2);
v___x_4440_ = lean_array_get_size(v_context_4439_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object* v_ctx_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4441_);
lean_dec_ref(v_ctx_4441_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object* v_ctx_4446_){
_start:
{
lean_object* v_content_4447_; lean_object* v_priorParts_4448_; lean_object* v_context_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4472_; 
v_content_4447_ = lean_ctor_get(v_ctx_4446_, 0);
v_priorParts_4448_ = lean_ctor_get(v_ctx_4446_, 1);
v_context_4449_ = lean_ctor_get(v_ctx_4446_, 2);
v_isSharedCheck_4472_ = !lean_is_exclusive(v_ctx_4446_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4451_ = v_ctx_4446_;
v_isShared_4452_ = v_isSharedCheck_4472_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_context_4449_);
lean_inc(v_priorParts_4448_);
lean_inc(v_content_4447_);
lean_dec(v_ctx_4446_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4472_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; uint8_t v___x_4455_; 
v___x_4453_ = lean_array_get_size(v_context_4449_);
v___x_4454_ = lean_unsigned_to_nat(0u);
v___x_4455_ = lean_nat_dec_eq(v___x_4453_, v___x_4454_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v_last_4458_; lean_object* v_content_4459_; lean_object* v_priorParts_4460_; lean_object* v_titleString_4461_; lean_object* v_title_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4468_; 
v___x_4456_ = lean_unsigned_to_nat(1u);
v___x_4457_ = lean_nat_sub(v___x_4453_, v___x_4456_);
v_last_4458_ = lean_array_fget_borrowed(v_context_4449_, v___x_4457_);
lean_dec(v___x_4457_);
v_content_4459_ = lean_ctor_get(v_last_4458_, 0);
lean_inc_ref(v_content_4459_);
v_priorParts_4460_ = lean_ctor_get(v_last_4458_, 1);
v_titleString_4461_ = lean_ctor_get(v_last_4458_, 2);
v_title_4462_ = lean_ctor_get(v_last_4458_, 3);
v___x_4463_ = lean_box(0);
lean_inc_ref(v_titleString_4461_);
lean_inc_ref(v_title_4462_);
v___x_4464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4464_, 0, v_title_4462_);
lean_ctor_set(v___x_4464_, 1, v_titleString_4461_);
lean_ctor_set(v___x_4464_, 2, v___x_4463_);
lean_ctor_set(v___x_4464_, 3, v_content_4447_);
lean_ctor_set(v___x_4464_, 4, v_priorParts_4448_);
lean_inc_ref(v_priorParts_4460_);
v___x_4465_ = lean_array_push(v_priorParts_4460_, v___x_4464_);
v___x_4466_ = lean_array_pop(v_context_4449_);
if (v_isShared_4452_ == 0)
{
lean_ctor_set(v___x_4451_, 2, v___x_4466_);
lean_ctor_set(v___x_4451_, 1, v___x_4465_);
lean_ctor_set(v___x_4451_, 0, v_content_4459_);
v___x_4468_ = v___x_4451_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_content_4459_);
lean_ctor_set(v_reuseFailAlloc_4470_, 1, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4470_, 2, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4469_; 
v___x_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4468_);
return v___x_4469_;
}
}
else
{
lean_object* v___x_4471_; 
lean_del_object(v___x_4451_);
lean_dec_ref(v_context_4449_);
lean_dec_ref(v_priorParts_4448_);
lean_dec_ref(v_content_4447_);
v___x_4471_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1));
return v___x_4471_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object* v_ctx_4473_){
_start:
{
lean_object* v_context_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; uint8_t v___x_4477_; 
v_context_4474_ = lean_ctor_get(v_ctx_4473_, 2);
v___x_4475_ = lean_array_get_size(v_context_4474_);
v___x_4476_ = lean_unsigned_to_nat(0u);
v___x_4477_ = lean_nat_dec_eq(v___x_4475_, v___x_4476_);
if (v___x_4477_ == 0)
{
lean_object* v___x_4478_; 
v___x_4478_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4473_);
if (lean_obj_tag(v___x_4478_) == 0)
{
return v___x_4478_;
}
else
{
lean_object* v_a_4479_; 
v_a_4479_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4479_);
lean_dec_ref(v___x_4478_);
v_ctx_4473_ = v_a_4479_;
goto _start;
}
}
else
{
lean_object* v___x_4481_; 
v___x_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4481_, 0, v_ctx_4473_);
return v___x_4481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object* v_ctx_4484_, lean_object* v_partLevel_4485_, lean_object* v_part_4486_){
_start:
{
lean_object* v___x_4487_; uint8_t v___x_4488_; 
v___x_4487_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4484_);
v___x_4488_ = lean_nat_dec_lt(v___x_4487_, v_partLevel_4485_);
if (v___x_4488_ == 0)
{
uint8_t v___x_4489_; 
v___x_4489_ = lean_nat_dec_eq(v_partLevel_4485_, v___x_4487_);
lean_dec(v___x_4487_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4490_; 
v___x_4490_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4484_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_dec_ref(v_part_4486_);
lean_dec(v_partLevel_4485_);
return v___x_4490_;
}
else
{
lean_object* v_a_4491_; 
v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_a_4491_);
lean_dec_ref(v___x_4490_);
v_ctx_4484_ = v_a_4491_;
goto _start;
}
}
else
{
lean_object* v_content_4493_; lean_object* v_priorParts_4494_; lean_object* v_context_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4504_; 
lean_dec(v_partLevel_4485_);
v_content_4493_ = lean_ctor_get(v_ctx_4484_, 0);
v_priorParts_4494_ = lean_ctor_get(v_ctx_4484_, 1);
v_context_4495_ = lean_ctor_get(v_ctx_4484_, 2);
v_isSharedCheck_4504_ = !lean_is_exclusive(v_ctx_4484_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4497_ = v_ctx_4484_;
v_isShared_4498_ = v_isSharedCheck_4504_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_context_4495_);
lean_inc(v_priorParts_4494_);
lean_inc(v_content_4493_);
lean_dec(v_ctx_4484_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4504_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; lean_object* v___x_4501_; 
v___x_4499_ = lean_array_push(v_priorParts_4494_, v_part_4486_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 1, v___x_4499_);
v___x_4501_ = v___x_4497_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_content_4493_);
lean_ctor_set(v_reuseFailAlloc_4503_, 1, v___x_4499_);
lean_ctor_set(v_reuseFailAlloc_4503_, 2, v_context_4495_);
v___x_4501_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
lean_object* v___x_4502_; 
v___x_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4501_);
return v___x_4502_;
}
}
}
}
else
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
lean_dec_ref(v_part_4486_);
lean_dec_ref(v_ctx_4484_);
v___x_4505_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0));
v___x_4506_ = l_Nat_reprFast(v___x_4487_);
v___x_4507_ = lean_string_append(v___x_4505_, v___x_4506_);
lean_dec_ref(v___x_4506_);
v___x_4508_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1));
v___x_4509_ = lean_string_append(v___x_4507_, v___x_4508_);
v___x_4510_ = l_Nat_reprFast(v_partLevel_4485_);
v___x_4511_ = lean_string_append(v___x_4509_, v___x_4510_);
lean_dec_ref(v___x_4510_);
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
return v___x_4512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object* v_ctx_4516_, lean_object* v_blocks_4517_){
_start:
{
lean_object* v_content_4518_; lean_object* v_priorParts_4519_; lean_object* v_context_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4533_; 
v_content_4518_ = lean_ctor_get(v_ctx_4516_, 0);
v_priorParts_4519_ = lean_ctor_get(v_ctx_4516_, 1);
v_context_4520_ = lean_ctor_get(v_ctx_4516_, 2);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_ctx_4516_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4522_ = v_ctx_4516_;
v_isShared_4523_ = v_isSharedCheck_4533_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_context_4520_);
lean_inc(v_priorParts_4519_);
lean_inc(v_content_4518_);
lean_dec(v_ctx_4516_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4533_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4524_ = lean_array_get_size(v_priorParts_4519_);
v___x_4525_ = lean_unsigned_to_nat(0u);
v___x_4526_ = lean_nat_dec_eq(v___x_4524_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; 
lean_del_object(v___x_4522_);
lean_dec_ref(v_context_4520_);
lean_dec_ref(v_priorParts_4519_);
lean_dec_ref(v_content_4518_);
v___x_4527_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1));
return v___x_4527_;
}
else
{
lean_object* v___x_4528_; lean_object* v___x_4530_; 
v___x_4528_ = l_Array_append___redArg(v_content_4518_, v_blocks_4517_);
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 0, v___x_4528_);
v___x_4530_ = v___x_4522_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4528_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v_priorParts_4519_);
lean_ctor_set(v_reuseFailAlloc_4532_, 2, v_context_4520_);
v___x_4530_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
lean_object* v___x_4531_; 
v___x_4531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
return v___x_4531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object* v_ctx_4534_, lean_object* v_blocks_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4534_, v_blocks_4535_);
lean_dec_ref(v_blocks_4535_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object* v_as_4537_, size_t v_sz_4538_, size_t v_i_4539_, lean_object* v_b_4540_){
_start:
{
uint8_t v___x_4541_; 
v___x_4541_ = lean_usize_dec_lt(v_i_4539_, v_sz_4538_);
if (v___x_4541_ == 0)
{
lean_object* v___x_4542_; 
v___x_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4542_, 0, v_b_4540_);
return v___x_4542_;
}
else
{
lean_object* v_a_4543_; lean_object* v_snd_4544_; lean_object* v_fst_4545_; lean_object* v_snd_4546_; lean_object* v___x_4547_; 
v_a_4543_ = lean_array_uget_borrowed(v_as_4537_, v_i_4539_);
v_snd_4544_ = lean_ctor_get(v_a_4543_, 1);
v_fst_4545_ = lean_ctor_get(v_a_4543_, 0);
v_snd_4546_ = lean_ctor_get(v_snd_4544_, 1);
lean_inc(v_snd_4546_);
lean_inc(v_fst_4545_);
v___x_4547_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(v_b_4540_, v_fst_4545_, v_snd_4546_);
if (lean_obj_tag(v___x_4547_) == 0)
{
return v___x_4547_;
}
else
{
lean_object* v_a_4548_; size_t v___x_4549_; size_t v___x_4550_; 
v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc(v_a_4548_);
lean_dec_ref(v___x_4547_);
v___x_4549_ = ((size_t)1ULL);
v___x_4550_ = lean_usize_add(v_i_4539_, v___x_4549_);
v_i_4539_ = v___x_4550_;
v_b_4540_ = v_a_4548_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object* v_as_4552_, lean_object* v_sz_4553_, lean_object* v_i_4554_, lean_object* v_b_4555_){
_start:
{
size_t v_sz_boxed_4556_; size_t v_i_boxed_4557_; lean_object* v_res_4558_; 
v_sz_boxed_4556_ = lean_unbox_usize(v_sz_4553_);
lean_dec(v_sz_4553_);
v_i_boxed_4557_ = lean_unbox_usize(v_i_4554_);
lean_dec(v_i_4554_);
v_res_4558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_as_4552_, v_sz_boxed_4556_, v_i_boxed_4557_, v_b_4555_);
lean_dec_ref(v_as_4552_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object* v_ctx_4559_, lean_object* v_snippet_4560_){
_start:
{
lean_object* v_text_4561_; lean_object* v_sections_4562_; lean_object* v___x_4563_; 
v_text_4561_ = lean_ctor_get(v_snippet_4560_, 0);
v_sections_4562_ = lean_ctor_get(v_snippet_4560_, 1);
v___x_4563_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4559_, v_text_4561_);
if (lean_obj_tag(v___x_4563_) == 0)
{
return v___x_4563_;
}
else
{
lean_object* v_a_4564_; size_t v_sz_4565_; size_t v___x_4566_; lean_object* v___x_4567_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref(v___x_4563_);
v_sz_4565_ = lean_array_size(v_sections_4562_);
v___x_4566_ = ((size_t)0ULL);
v___x_4567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_sections_4562_, v_sz_4565_, v___x_4566_, v_a_4564_);
return v___x_4567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object* v_ctx_4568_, lean_object* v_snippet_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_ctx_4568_, v_snippet_4569_);
lean_dec_ref(v_snippet_4569_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object* v_as_4571_, size_t v_sz_4572_, size_t v_i_4573_, lean_object* v_b_4574_){
_start:
{
uint8_t v___x_4575_; 
v___x_4575_ = lean_usize_dec_lt(v_i_4573_, v_sz_4572_);
if (v___x_4575_ == 0)
{
lean_object* v___x_4576_; 
v___x_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4576_, 0, v_b_4574_);
return v___x_4576_;
}
else
{
lean_object* v_snd_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4599_; 
v_snd_4577_ = lean_ctor_get(v_b_4574_, 1);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_b_4574_);
if (v_isSharedCheck_4599_ == 0)
{
lean_object* v_unused_4600_; 
v_unused_4600_ = lean_ctor_get(v_b_4574_, 0);
lean_dec(v_unused_4600_);
v___x_4579_ = v_b_4574_;
v_isShared_4580_ = v_isSharedCheck_4599_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_snd_4577_);
lean_dec(v_b_4574_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4599_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v_a_4581_; lean_object* v___x_4582_; 
v_a_4581_ = lean_array_uget_borrowed(v_as_4571_, v_i_4573_);
v___x_4582_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4577_, v_a_4581_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
lean_del_object(v___x_4579_);
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___x_4582_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4582_);
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
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4591_; lean_object* v___x_4592_; lean_object* v___x_4594_; 
v_a_4591_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4591_);
lean_dec_ref(v___x_4582_);
v___x_4592_ = lean_box(0);
if (v_isShared_4580_ == 0)
{
lean_ctor_set(v___x_4579_, 1, v_a_4591_);
lean_ctor_set(v___x_4579_, 0, v___x_4592_);
v___x_4594_ = v___x_4579_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4592_);
lean_ctor_set(v_reuseFailAlloc_4598_, 1, v_a_4591_);
v___x_4594_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
size_t v___x_4595_; size_t v___x_4596_; 
v___x_4595_ = ((size_t)1ULL);
v___x_4596_ = lean_usize_add(v_i_4573_, v___x_4595_);
v_i_4573_ = v___x_4596_;
v_b_4574_ = v___x_4594_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4601_, lean_object* v_sz_4602_, lean_object* v_i_4603_, lean_object* v_b_4604_){
_start:
{
size_t v_sz_boxed_4605_; size_t v_i_boxed_4606_; lean_object* v_res_4607_; 
v_sz_boxed_4605_ = lean_unbox_usize(v_sz_4602_);
lean_dec(v_sz_4602_);
v_i_boxed_4606_ = lean_unbox_usize(v_i_4603_);
lean_dec(v_i_4603_);
v_res_4607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4601_, v_sz_boxed_4605_, v_i_boxed_4606_, v_b_4604_);
lean_dec_ref(v_as_4601_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object* v_as_4608_, size_t v_sz_4609_, size_t v_i_4610_, lean_object* v_b_4611_){
_start:
{
uint8_t v___x_4612_; 
v___x_4612_ = lean_usize_dec_lt(v_i_4610_, v_sz_4609_);
if (v___x_4612_ == 0)
{
lean_object* v___x_4613_; 
v___x_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4613_, 0, v_b_4611_);
return v___x_4613_;
}
else
{
lean_object* v_snd_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4636_; 
v_snd_4614_ = lean_ctor_get(v_b_4611_, 1);
v_isSharedCheck_4636_ = !lean_is_exclusive(v_b_4611_);
if (v_isSharedCheck_4636_ == 0)
{
lean_object* v_unused_4637_; 
v_unused_4637_ = lean_ctor_get(v_b_4611_, 0);
lean_dec(v_unused_4637_);
v___x_4616_ = v_b_4611_;
v_isShared_4617_ = v_isSharedCheck_4636_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_snd_4614_);
lean_dec(v_b_4611_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4636_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v_a_4618_; lean_object* v___x_4619_; 
v_a_4618_ = lean_array_uget_borrowed(v_as_4608_, v_i_4610_);
v___x_4619_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4614_, v_a_4618_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4627_; 
lean_del_object(v___x_4616_);
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4622_ = v___x_4619_;
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4619_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_a_4620_);
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
lean_object* v_a_4628_; lean_object* v___x_4629_; lean_object* v___x_4631_; 
v_a_4628_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4628_);
lean_dec_ref(v___x_4619_);
v___x_4629_ = lean_box(0);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 1, v_a_4628_);
lean_ctor_set(v___x_4616_, 0, v___x_4629_);
v___x_4631_ = v___x_4616_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4629_);
lean_ctor_set(v_reuseFailAlloc_4635_, 1, v_a_4628_);
v___x_4631_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
size_t v___x_4632_; size_t v___x_4633_; lean_object* v___x_4634_; 
v___x_4632_ = ((size_t)1ULL);
v___x_4633_ = lean_usize_add(v_i_4610_, v___x_4632_);
v___x_4634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4608_, v_sz_4609_, v___x_4633_, v___x_4631_);
return v___x_4634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object* v_as_4638_, lean_object* v_sz_4639_, lean_object* v_i_4640_, lean_object* v_b_4641_){
_start:
{
size_t v_sz_boxed_4642_; size_t v_i_boxed_4643_; lean_object* v_res_4644_; 
v_sz_boxed_4642_ = lean_unbox_usize(v_sz_4639_);
lean_dec(v_sz_4639_);
v_i_boxed_4643_ = lean_unbox_usize(v_i_4640_);
lean_dec(v_i_4640_);
v_res_4644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_as_4638_, v_sz_boxed_4642_, v_i_boxed_4643_, v_b_4641_);
lean_dec_ref(v_as_4638_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_4645_, size_t v_sz_4646_, size_t v_i_4647_, lean_object* v_b_4648_){
_start:
{
uint8_t v___x_4649_; 
v___x_4649_ = lean_usize_dec_lt(v_i_4647_, v_sz_4646_);
if (v___x_4649_ == 0)
{
lean_object* v___x_4650_; 
v___x_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4650_, 0, v_b_4648_);
return v___x_4650_;
}
else
{
lean_object* v_snd_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4673_; 
v_snd_4651_ = lean_ctor_get(v_b_4648_, 1);
v_isSharedCheck_4673_ = !lean_is_exclusive(v_b_4648_);
if (v_isSharedCheck_4673_ == 0)
{
lean_object* v_unused_4674_; 
v_unused_4674_ = lean_ctor_get(v_b_4648_, 0);
lean_dec(v_unused_4674_);
v___x_4653_ = v_b_4648_;
v_isShared_4654_ = v_isSharedCheck_4673_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_snd_4651_);
lean_dec(v_b_4648_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4673_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v_a_4655_; lean_object* v___x_4656_; 
v_a_4655_ = lean_array_uget_borrowed(v_as_4645_, v_i_4647_);
v___x_4656_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4651_, v_a_4655_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4664_; 
lean_del_object(v___x_4653_);
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4664_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4659_ = v___x_4656_;
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v___x_4656_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v___x_4662_; 
if (v_isShared_4660_ == 0)
{
v___x_4662_ = v___x_4659_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_a_4657_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
else
{
lean_object* v_a_4665_; lean_object* v___x_4666_; lean_object* v___x_4668_; 
v_a_4665_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_a_4665_);
lean_dec_ref(v___x_4656_);
v___x_4666_ = lean_box(0);
if (v_isShared_4654_ == 0)
{
lean_ctor_set(v___x_4653_, 1, v_a_4665_);
lean_ctor_set(v___x_4653_, 0, v___x_4666_);
v___x_4668_ = v___x_4653_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v___x_4666_);
lean_ctor_set(v_reuseFailAlloc_4672_, 1, v_a_4665_);
v___x_4668_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
size_t v___x_4669_; size_t v___x_4670_; 
v___x_4669_ = ((size_t)1ULL);
v___x_4670_ = lean_usize_add(v_i_4647_, v___x_4669_);
v_i_4647_ = v___x_4670_;
v_b_4648_ = v___x_4668_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_4675_, lean_object* v_sz_4676_, lean_object* v_i_4677_, lean_object* v_b_4678_){
_start:
{
size_t v_sz_boxed_4679_; size_t v_i_boxed_4680_; lean_object* v_res_4681_; 
v_sz_boxed_4679_ = lean_unbox_usize(v_sz_4676_);
lean_dec(v_sz_4676_);
v_i_boxed_4680_ = lean_unbox_usize(v_i_4677_);
lean_dec(v_i_4677_);
v_res_4681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4675_, v_sz_boxed_4679_, v_i_boxed_4680_, v_b_4678_);
lean_dec_ref(v_as_4675_);
return v_res_4681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object* v_as_4682_, size_t v_sz_4683_, size_t v_i_4684_, lean_object* v_b_4685_){
_start:
{
uint8_t v___x_4686_; 
v___x_4686_ = lean_usize_dec_lt(v_i_4684_, v_sz_4683_);
if (v___x_4686_ == 0)
{
lean_object* v___x_4687_; 
v___x_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4687_, 0, v_b_4685_);
return v___x_4687_;
}
else
{
lean_object* v_snd_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4710_; 
v_snd_4688_ = lean_ctor_get(v_b_4685_, 1);
v_isSharedCheck_4710_ = !lean_is_exclusive(v_b_4685_);
if (v_isSharedCheck_4710_ == 0)
{
lean_object* v_unused_4711_; 
v_unused_4711_ = lean_ctor_get(v_b_4685_, 0);
lean_dec(v_unused_4711_);
v___x_4690_ = v_b_4685_;
v_isShared_4691_ = v_isSharedCheck_4710_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_snd_4688_);
lean_dec(v_b_4685_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4710_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v_a_4692_; lean_object* v___x_4693_; 
v_a_4692_ = lean_array_uget_borrowed(v_as_4682_, v_i_4684_);
v___x_4693_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4688_, v_a_4692_);
if (lean_obj_tag(v___x_4693_) == 0)
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_del_object(v___x_4690_);
v_a_4694_ = lean_ctor_get(v___x_4693_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4693_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4693_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4693_);
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
v_reuseFailAlloc_4700_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4702_; lean_object* v___x_4703_; lean_object* v___x_4705_; 
v_a_4702_ = lean_ctor_get(v___x_4693_, 0);
lean_inc(v_a_4702_);
lean_dec_ref(v___x_4693_);
v___x_4703_ = lean_box(0);
if (v_isShared_4691_ == 0)
{
lean_ctor_set(v___x_4690_, 1, v_a_4702_);
lean_ctor_set(v___x_4690_, 0, v___x_4703_);
v___x_4705_ = v___x_4690_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v___x_4703_);
lean_ctor_set(v_reuseFailAlloc_4709_, 1, v_a_4702_);
v___x_4705_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
size_t v___x_4706_; size_t v___x_4707_; lean_object* v___x_4708_; 
v___x_4706_ = ((size_t)1ULL);
v___x_4707_ = lean_usize_add(v_i_4684_, v___x_4706_);
v___x_4708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4682_, v_sz_4683_, v___x_4707_, v___x_4705_);
return v___x_4708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4712_, lean_object* v_sz_4713_, lean_object* v_i_4714_, lean_object* v_b_4715_){
_start:
{
size_t v_sz_boxed_4716_; size_t v_i_boxed_4717_; lean_object* v_res_4718_; 
v_sz_boxed_4716_ = lean_unbox_usize(v_sz_4713_);
lean_dec(v_sz_4713_);
v_i_boxed_4717_ = lean_unbox_usize(v_i_4714_);
lean_dec(v_i_4714_);
v_res_4718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_as_4712_, v_sz_boxed_4716_, v_i_boxed_4717_, v_b_4715_);
lean_dec_ref(v_as_4712_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object* v_inh_4719_, lean_object* v_n_4720_, lean_object* v_b_4721_){
_start:
{
if (lean_obj_tag(v_n_4720_) == 0)
{
lean_object* v_cs_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4756_; 
v_cs_4722_ = lean_ctor_get(v_n_4720_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v_n_4720_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4724_ = v_n_4720_;
v_isShared_4725_ = v_isSharedCheck_4756_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_cs_4722_);
lean_dec(v_n_4720_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4756_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; size_t v_sz_4728_; size_t v___x_4729_; lean_object* v___x_4730_; 
v___x_4726_ = lean_box(0);
v___x_4727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4726_);
lean_ctor_set(v___x_4727_, 1, v_b_4721_);
v_sz_4728_ = lean_array_size(v_cs_4722_);
v___x_4729_ = ((size_t)0ULL);
v___x_4730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_inh_4719_, v_cs_4722_, v_sz_4728_, v___x_4729_, v___x_4727_);
lean_dec_ref(v_cs_4722_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
lean_del_object(v___x_4724_);
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4730_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4730_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
else
{
lean_object* v_a_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4755_; 
v_a_4739_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4741_ = v___x_4730_;
v_isShared_4742_ = v_isSharedCheck_4755_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_a_4739_);
lean_dec(v___x_4730_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4755_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v_fst_4743_; 
v_fst_4743_ = lean_ctor_get(v_a_4739_, 0);
if (lean_obj_tag(v_fst_4743_) == 0)
{
lean_object* v_snd_4744_; lean_object* v___x_4746_; 
v_snd_4744_ = lean_ctor_get(v_a_4739_, 1);
lean_inc(v_snd_4744_);
lean_dec(v_a_4739_);
if (v_isShared_4725_ == 0)
{
lean_ctor_set_tag(v___x_4724_, 1);
lean_ctor_set(v___x_4724_, 0, v_snd_4744_);
v___x_4746_ = v___x_4724_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_snd_4744_);
v___x_4746_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
lean_object* v___x_4748_; 
if (v_isShared_4742_ == 0)
{
lean_ctor_set(v___x_4741_, 0, v___x_4746_);
v___x_4748_ = v___x_4741_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4746_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
else
{
lean_object* v_val_4751_; lean_object* v___x_4753_; 
lean_inc_ref(v_fst_4743_);
lean_dec(v_a_4739_);
lean_del_object(v___x_4724_);
v_val_4751_ = lean_ctor_get(v_fst_4743_, 0);
lean_inc(v_val_4751_);
lean_dec_ref(v_fst_4743_);
if (v_isShared_4742_ == 0)
{
lean_ctor_set(v___x_4741_, 0, v_val_4751_);
v___x_4753_ = v___x_4741_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_val_4751_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
}
}
}
else
{
lean_object* v_vs_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4791_; 
v_vs_4757_ = lean_ctor_get(v_n_4720_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v_n_4720_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4759_ = v_n_4720_;
v_isShared_4760_ = v_isSharedCheck_4791_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_vs_4757_);
lean_dec(v_n_4720_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4791_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; size_t v_sz_4763_; size_t v___x_4764_; lean_object* v___x_4765_; 
v___x_4761_ = lean_box(0);
v___x_4762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4761_);
lean_ctor_set(v___x_4762_, 1, v_b_4721_);
v_sz_4763_ = lean_array_size(v_vs_4757_);
v___x_4764_ = ((size_t)0ULL);
v___x_4765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_vs_4757_, v_sz_4763_, v___x_4764_, v___x_4762_);
lean_dec_ref(v_vs_4757_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4773_; 
lean_del_object(v___x_4759_);
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4768_ = v___x_4765_;
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4765_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
}
else
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4790_; 
v_a_4774_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4776_ = v___x_4765_;
v_isShared_4777_ = v_isSharedCheck_4790_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4765_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4790_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v_fst_4778_; 
v_fst_4778_ = lean_ctor_get(v_a_4774_, 0);
if (lean_obj_tag(v_fst_4778_) == 0)
{
lean_object* v_snd_4779_; lean_object* v___x_4781_; 
v_snd_4779_ = lean_ctor_get(v_a_4774_, 1);
lean_inc(v_snd_4779_);
lean_dec(v_a_4774_);
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 0, v_snd_4779_);
v___x_4781_ = v___x_4759_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_snd_4779_);
v___x_4781_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
lean_object* v___x_4783_; 
if (v_isShared_4777_ == 0)
{
lean_ctor_set(v___x_4776_, 0, v___x_4781_);
v___x_4783_ = v___x_4776_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4781_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
else
{
lean_object* v_val_4786_; lean_object* v___x_4788_; 
lean_inc_ref(v_fst_4778_);
lean_dec(v_a_4774_);
lean_del_object(v___x_4759_);
v_val_4786_ = lean_ctor_get(v_fst_4778_, 0);
lean_inc(v_val_4786_);
lean_dec_ref(v_fst_4778_);
if (v_isShared_4777_ == 0)
{
lean_ctor_set(v___x_4776_, 0, v_val_4786_);
v___x_4788_ = v___x_4776_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_val_4786_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object* v_inh_4792_, lean_object* v_as_4793_, size_t v_sz_4794_, size_t v_i_4795_, lean_object* v_b_4796_){
_start:
{
uint8_t v___x_4797_; 
v___x_4797_ = lean_usize_dec_lt(v_i_4795_, v_sz_4794_);
if (v___x_4797_ == 0)
{
lean_object* v___x_4798_; 
v___x_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4798_, 0, v_b_4796_);
return v___x_4798_;
}
else
{
lean_object* v_snd_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4833_; 
v_snd_4799_ = lean_ctor_get(v_b_4796_, 1);
v_isSharedCheck_4833_ = !lean_is_exclusive(v_b_4796_);
if (v_isSharedCheck_4833_ == 0)
{
lean_object* v_unused_4834_; 
v_unused_4834_ = lean_ctor_get(v_b_4796_, 0);
lean_dec(v_unused_4834_);
v___x_4801_ = v_b_4796_;
v_isShared_4802_ = v_isSharedCheck_4833_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_snd_4799_);
lean_dec(v_b_4796_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4833_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v_a_4803_; lean_object* v___x_4804_; 
v_a_4803_ = lean_array_uget_borrowed(v_as_4793_, v_i_4795_);
lean_inc(v_snd_4799_);
lean_inc(v_a_4803_);
v___x_4804_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_inh_4792_, v_a_4803_, v_snd_4799_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
lean_del_object(v___x_4801_);
lean_dec(v_snd_4799_);
v_a_4805_ = lean_ctor_get(v___x_4804_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___x_4804_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4804_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
else
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4832_; 
v_a_4813_ = lean_ctor_get(v___x_4804_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4815_ = v___x_4804_;
v_isShared_4816_ = v_isSharedCheck_4832_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4804_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4832_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
if (lean_obj_tag(v_a_4813_) == 0)
{
lean_object* v___x_4817_; lean_object* v___x_4819_; 
v___x_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4817_, 0, v_a_4813_);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 0, v___x_4817_);
v___x_4819_ = v___x_4801_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v___x_4817_);
lean_ctor_set(v_reuseFailAlloc_4823_, 1, v_snd_4799_);
v___x_4819_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
lean_object* v___x_4821_; 
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 0, v___x_4819_);
v___x_4821_ = v___x_4815_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4819_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
else
{
lean_object* v_a_4824_; lean_object* v___x_4825_; lean_object* v___x_4827_; 
lean_del_object(v___x_4815_);
lean_dec(v_snd_4799_);
v_a_4824_ = lean_ctor_get(v_a_4813_, 0);
lean_inc(v_a_4824_);
lean_dec_ref(v_a_4813_);
v___x_4825_ = lean_box(0);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 1, v_a_4824_);
lean_ctor_set(v___x_4801_, 0, v___x_4825_);
v___x_4827_ = v___x_4801_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v___x_4825_);
lean_ctor_set(v_reuseFailAlloc_4831_, 1, v_a_4824_);
v___x_4827_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
size_t v___x_4828_; size_t v___x_4829_; 
v___x_4828_ = ((size_t)1ULL);
v___x_4829_ = lean_usize_add(v_i_4795_, v___x_4828_);
v_i_4795_ = v___x_4829_;
v_b_4796_ = v___x_4827_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object* v_inh_4835_, lean_object* v_as_4836_, lean_object* v_sz_4837_, lean_object* v_i_4838_, lean_object* v_b_4839_){
_start:
{
size_t v_sz_boxed_4840_; size_t v_i_boxed_4841_; lean_object* v_res_4842_; 
v_sz_boxed_4840_ = lean_unbox_usize(v_sz_4837_);
lean_dec(v_sz_4837_);
v_i_boxed_4841_ = lean_unbox_usize(v_i_4838_);
lean_dec(v_i_4838_);
v_res_4842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_inh_4835_, v_as_4836_, v_sz_boxed_4840_, v_i_boxed_4841_, v_b_4839_);
lean_dec_ref(v_as_4836_);
lean_dec_ref(v_inh_4835_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object* v_inh_4843_, lean_object* v_n_4844_, lean_object* v_b_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_inh_4843_, v_n_4844_, v_b_4845_);
lean_dec_ref(v_inh_4843_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object* v_t_4847_, lean_object* v_init_4848_){
_start:
{
lean_object* v_root_4849_; lean_object* v_tail_4850_; lean_object* v___x_4851_; 
v_root_4849_ = lean_ctor_get(v_t_4847_, 0);
lean_inc_ref(v_root_4849_);
v_tail_4850_ = lean_ctor_get(v_t_4847_, 1);
lean_inc_ref(v_tail_4850_);
lean_dec_ref(v_t_4847_);
lean_inc_ref(v_init_4848_);
v___x_4851_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4848_, v_root_4849_, v_init_4848_);
lean_dec_ref(v_init_4848_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4859_; 
lean_dec_ref(v_tail_4850_);
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4854_ = v___x_4851_;
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4851_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v___x_4857_; 
if (v_isShared_4855_ == 0)
{
v___x_4857_ = v___x_4854_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
else
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4896_; 
v_a_4860_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4862_ = v___x_4851_;
v_isShared_4863_ = v_isSharedCheck_4896_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4851_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4896_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
if (lean_obj_tag(v_a_4860_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4866_; 
lean_dec_ref(v_tail_4850_);
v_a_4864_ = lean_ctor_get(v_a_4860_, 0);
lean_inc(v_a_4864_);
lean_dec_ref(v_a_4860_);
if (v_isShared_4863_ == 0)
{
lean_ctor_set(v___x_4862_, 0, v_a_4864_);
v___x_4866_ = v___x_4862_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4864_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; size_t v_sz_4871_; size_t v___x_4872_; lean_object* v___x_4873_; 
lean_del_object(v___x_4862_);
v_a_4868_ = lean_ctor_get(v_a_4860_, 0);
lean_inc(v_a_4868_);
lean_dec_ref(v_a_4860_);
v___x_4869_ = lean_box(0);
v___x_4870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4869_);
lean_ctor_set(v___x_4870_, 1, v_a_4868_);
v_sz_4871_ = lean_array_size(v_tail_4850_);
v___x_4872_ = ((size_t)0ULL);
v___x_4873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_tail_4850_, v_sz_4871_, v___x_4872_, v___x_4870_);
lean_dec_ref(v_tail_4850_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4873_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4873_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
else
{
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4895_; 
v_a_4882_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4884_ = v___x_4873_;
v_isShared_4885_ = v_isSharedCheck_4895_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4873_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4895_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v_fst_4886_; 
v_fst_4886_ = lean_ctor_get(v_a_4882_, 0);
if (lean_obj_tag(v_fst_4886_) == 0)
{
lean_object* v_snd_4887_; lean_object* v___x_4889_; 
v_snd_4887_ = lean_ctor_get(v_a_4882_, 1);
lean_inc(v_snd_4887_);
lean_dec(v_a_4882_);
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 0, v_snd_4887_);
v___x_4889_ = v___x_4884_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_snd_4887_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
else
{
lean_object* v_val_4891_; lean_object* v___x_4893_; 
lean_inc_ref(v_fst_4886_);
lean_dec(v_a_4882_);
v_val_4891_ = lean_ctor_get(v_fst_4886_, 0);
lean_inc(v_val_4891_);
lean_dec_ref(v_fst_4886_);
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 0, v_val_4891_);
v___x_4893_ = v___x_4884_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_val_4891_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_assemble___closed__1(void){
_start:
{
lean_object* v___x_4899_; lean_object* v_ctx_4900_; 
v___x_4899_ = ((lean_object*)(l_Lean_VersoModuleDocs_assemble___closed__0));
v_ctx_4900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctx_4900_, 0, v___x_4899_);
lean_ctor_set(v_ctx_4900_, 1, v___x_4899_);
lean_ctor_set(v_ctx_4900_, 2, v___x_4899_);
return v_ctx_4900_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object* v_docs_4901_){
_start:
{
lean_object* v_snippets_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4939_; 
v_snippets_4902_ = lean_ctor_get(v_docs_4901_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v_docs_4901_);
if (v_isSharedCheck_4939_ == 0)
{
lean_object* v_unused_4940_; 
v_unused_4940_ = lean_ctor_get(v_docs_4901_, 1);
lean_dec(v_unused_4940_);
v___x_4904_ = v_docs_4901_;
v_isShared_4905_ = v_isSharedCheck_4939_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_snippets_4902_);
lean_dec(v_docs_4901_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4939_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v_ctx_4906_; lean_object* v___x_4907_; 
v_ctx_4906_ = lean_obj_once(&l_Lean_VersoModuleDocs_assemble___closed__1, &l_Lean_VersoModuleDocs_assemble___closed__1_once, _init_l_Lean_VersoModuleDocs_assemble___closed__1);
v___x_4907_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_snippets_4902_, v_ctx_4906_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_object* v_a_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4915_; 
lean_del_object(v___x_4904_);
v_a_4908_ = lean_ctor_get(v___x_4907_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v___x_4907_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4910_ = v___x_4907_;
v_isShared_4911_ = v_isSharedCheck_4915_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_a_4908_);
lean_dec(v___x_4907_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4915_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v___x_4913_; 
if (v_isShared_4911_ == 0)
{
v___x_4913_ = v___x_4910_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_a_4908_);
v___x_4913_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
return v___x_4913_;
}
}
}
else
{
lean_object* v_a_4916_; lean_object* v___x_4917_; 
v_a_4916_ = lean_ctor_get(v___x_4907_, 0);
lean_inc(v_a_4916_);
lean_dec_ref(v___x_4907_);
v___x_4917_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(v_a_4916_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4925_; 
lean_del_object(v___x_4904_);
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4920_ = v___x_4917_;
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4917_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4921_ == 0)
{
v___x_4923_ = v___x_4920_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4918_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
else
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4938_; 
v_a_4926_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4938_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4928_ = v___x_4917_;
v_isShared_4929_ = v_isSharedCheck_4938_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4917_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4938_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v_content_4930_; lean_object* v_priorParts_4931_; lean_object* v___x_4933_; 
v_content_4930_ = lean_ctor_get(v_a_4926_, 0);
lean_inc_ref(v_content_4930_);
v_priorParts_4931_ = lean_ctor_get(v_a_4926_, 1);
lean_inc_ref(v_priorParts_4931_);
lean_dec(v_a_4926_);
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 1, v_priorParts_4931_);
lean_ctor_set(v___x_4904_, 0, v_content_4930_);
v___x_4933_ = v___x_4904_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_content_4930_);
lean_ctor_set(v_reuseFailAlloc_4937_, 1, v_priorParts_4931_);
v___x_4933_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
lean_object* v___x_4935_; 
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 0, v___x_4933_);
v___x_4935_ = v___x_4928_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4933_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object* v_x_4943_, lean_object* v_x_4944_, lean_object* v_es_4945_, uint8_t v_level_4946_){
_start:
{
uint8_t v___x_4947_; uint8_t v___x_4948_; 
v___x_4947_ = 1;
v___x_4948_ = l_Lean_instOrdOLeanLevel_ord(v_level_4946_, v___x_4947_);
if (v___x_4948_ == 0)
{
lean_object* v___x_4949_; 
lean_dec(v_es_4945_);
v___x_4949_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_));
return v___x_4949_;
}
else
{
lean_object* v___x_4950_; 
v___x_4950_ = lean_array_mk(v_es_4945_);
return v___x_4950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object* v_x_4951_, lean_object* v_x_4952_, lean_object* v_es_4953_, lean_object* v_level_4954_){
_start:
{
uint8_t v_level_boxed_4955_; lean_object* v_res_4956_; 
v_level_boxed_4955_ = lean_unbox(v_level_4954_);
v_res_4956_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(v_x_4951_, v_x_4952_, v_es_4953_, v_level_boxed_4955_);
lean_dec_ref(v_x_4952_);
lean_dec_ref(v_x_4951_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object* v_es_4957_){
_start:
{
lean_object* v___x_4958_; 
v___x_4958_ = lean_array_mk(v_es_4957_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_4959_, lean_object* v_i_4960_){
_start:
{
lean_object* v_zero_4961_; uint8_t v_isZero_4962_; 
v_zero_4961_ = lean_unsigned_to_nat(0u);
v_isZero_4962_ = lean_nat_dec_eq(v_i_4960_, v_zero_4961_);
if (v_isZero_4962_ == 1)
{
lean_object* v___x_4963_; 
lean_dec(v_i_4960_);
v___x_4963_ = lean_box(0);
return v___x_4963_;
}
else
{
lean_object* v_one_4964_; lean_object* v_n_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v_one_4964_ = lean_unsigned_to_nat(1u);
v_n_4965_ = lean_nat_sub(v_i_4960_, v_one_4964_);
lean_dec(v_i_4960_);
v___x_4966_ = lean_array_fget_borrowed(v_as_4959_, v_n_4965_);
v___x_4967_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v___x_4966_);
if (lean_obj_tag(v___x_4967_) == 0)
{
v_i_4960_ = v_n_4965_;
goto _start;
}
else
{
lean_dec(v_n_4965_);
return v___x_4967_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_4969_, lean_object* v_i_4970_){
_start:
{
lean_object* v_res_4971_; 
v_res_4971_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_4969_, v_i_4970_);
lean_dec_ref(v_as_4969_);
return v_res_4971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_as_4972_, lean_object* v_i_4973_){
_start:
{
lean_object* v_zero_4974_; uint8_t v_isZero_4975_; 
v_zero_4974_ = lean_unsigned_to_nat(0u);
v_isZero_4975_ = lean_nat_dec_eq(v_i_4973_, v_zero_4974_);
if (v_isZero_4975_ == 1)
{
lean_object* v___x_4976_; 
lean_dec(v_i_4973_);
v___x_4976_ = lean_box(0);
return v___x_4976_;
}
else
{
lean_object* v_one_4977_; lean_object* v_n_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v_one_4977_ = lean_unsigned_to_nat(1u);
v_n_4978_ = lean_nat_sub(v_i_4973_, v_one_4977_);
lean_dec(v_i_4973_);
v___x_4979_ = lean_array_fget_borrowed(v_as_4972_, v_n_4978_);
v___x_4980_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(v___x_4979_);
if (lean_obj_tag(v___x_4980_) == 0)
{
v_i_4973_ = v_n_4978_;
goto _start;
}
else
{
lean_dec(v_n_4978_);
return v___x_4980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_x_4982_){
_start:
{
if (lean_obj_tag(v_x_4982_) == 0)
{
lean_object* v_cs_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v_cs_4983_ = lean_ctor_get(v_x_4982_, 0);
v___x_4984_ = lean_array_get_size(v_cs_4983_);
v___x_4985_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_cs_4983_, v___x_4984_);
return v___x_4985_;
}
else
{
lean_object* v_vs_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v_vs_4986_ = lean_ctor_get(v_x_4982_, 0);
v___x_4987_ = lean_array_get_size(v_vs_4986_);
v___x_4988_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(v_vs_4986_, v___x_4987_);
return v___x_4988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_x_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(v_x_4989_);
lean_dec_ref(v_x_4989_);
return v_res_4990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_4991_, lean_object* v_i_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_as_4991_, v_i_4992_);
lean_dec_ref(v_as_4991_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0(lean_object* v_t_4994_){
_start:
{
lean_object* v_root_4995_; lean_object* v_tail_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v_root_4995_ = lean_ctor_get(v_t_4994_, 0);
v_tail_4996_ = lean_ctor_get(v_t_4994_, 1);
v___x_4997_ = lean_array_get_size(v_tail_4996_);
v___x_4998_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(v_tail_4996_, v___x_4997_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_object* v___x_4999_; 
v___x_4999_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(v_root_4995_);
return v___x_4999_;
}
else
{
return v___x_4998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0___boxed(lean_object* v_t_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0(v_t_5000_);
lean_dec_ref(v_t_5000_);
return v_res_5001_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_5002_ = lean_unsigned_to_nat(32u);
v___x_5003_ = lean_mk_empty_array_with_capacity(v___x_5002_);
v___x_5004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5004_, 0, v___x_5003_);
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object* v___x_5005_, lean_object* v_x_5006_){
_start:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; size_t v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5007_ = lean_unsigned_to_nat(32u);
v___x_5008_ = lean_mk_empty_array_with_capacity(v___x_5007_);
v___x_5009_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_);
v___x_5010_ = ((size_t)5ULL);
lean_inc(v___x_5005_);
v___x_5011_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5011_, 0, v___x_5009_);
lean_ctor_set(v___x_5011_, 1, v___x_5008_);
lean_ctor_set(v___x_5011_, 2, v___x_5005_);
lean_ctor_set(v___x_5011_, 3, v___x_5005_);
lean_ctor_set_usize(v___x_5011_, 4, v___x_5010_);
v___x_5012_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0(v___x_5011_);
v___x_5013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5013_, 0, v___x_5011_);
lean_ctor_set(v___x_5013_, 1, v___x_5012_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object* v___x_5014_, lean_object* v_x_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(v___x_5014_, v_x_5015_);
lean_dec_ref(v_x_5015_);
return v_res_5016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5037_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_));
v___x_5038_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5037_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object* v_a_5039_){
_start:
{
lean_object* v_res_5040_; 
v_res_5040_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_();
return v_res_5040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_5041_, lean_object* v_i_5042_, lean_object* v_a_5043_){
_start:
{
lean_object* v___x_5044_; 
v___x_5044_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_5041_, v_i_5042_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_5045_, lean_object* v_i_5046_, lean_object* v_a_5047_){
_start:
{
lean_object* v_res_5048_; 
v_res_5048_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0(v_as_5045_, v_i_5046_, v_a_5047_);
lean_dec_ref(v_as_5045_);
return v_res_5048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_as_5049_, lean_object* v_i_5050_, lean_object* v_a_5051_){
_start:
{
lean_object* v___x_5052_; 
v___x_5052_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_as_5049_, v_i_5050_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___boxed(lean_object* v_as_5053_, lean_object* v_i_5054_, lean_object* v_a_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2(v_as_5053_, v_i_5054_, v_a_5055_);
lean_dec_ref(v_as_5053_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object* v_env_5057_){
_start:
{
lean_object* v___x_5058_; lean_object* v_toEnvExtension_5059_; lean_object* v_asyncMode_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
v___x_5058_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_5059_ = lean_ctor_get(v___x_5058_, 0);
lean_inc_ref(v_toEnvExtension_5059_);
v_asyncMode_5060_ = lean_ctor_get(v_toEnvExtension_5059_, 2);
lean_inc(v_asyncMode_5060_);
lean_dec_ref(v_toEnvExtension_5059_);
v___x_5061_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_5062_ = lean_box(0);
v___x_5063_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5061_, v___x_5058_, v_env_5057_, v_asyncMode_5060_, v___x_5062_);
lean_dec(v_asyncMode_5060_);
return v___x_5063_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object* v_env_5064_){
_start:
{
lean_object* v___x_5065_; 
v___x_5065_ = l_Lean_getMainVersoModuleDocs(v_env_5064_);
return v___x_5065_;
}
}
static lean_object* _init_l_Lean_getVersoModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5066_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_5067_ = lean_box(0);
v___x_5068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5067_);
lean_ctor_set(v___x_5068_, 1, v___x_5066_);
return v___x_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object* v_env_5069_, lean_object* v_moduleName_5070_){
_start:
{
lean_object* v___x_5071_; 
v___x_5071_ = l_Lean_Environment_getModuleIdx_x3f(v_env_5069_, v_moduleName_5070_);
if (lean_obj_tag(v___x_5071_) == 0)
{
lean_object* v___x_5072_; 
v___x_5072_ = lean_box(0);
return v___x_5072_;
}
else
{
lean_object* v_val_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5084_; 
v_val_5073_ = lean_ctor_get(v___x_5071_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5075_ = v___x_5071_;
v_isShared_5076_ = v_isSharedCheck_5084_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_val_5073_);
lean_dec(v___x_5071_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5084_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5077_; lean_object* v___x_5078_; uint8_t v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5082_; 
v___x_5077_ = lean_obj_once(&l_Lean_getVersoModuleDoc_x3f___closed__0, &l_Lean_getVersoModuleDoc_x3f___closed__0_once, _init_l_Lean_getVersoModuleDoc_x3f___closed__0);
v___x_5078_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v___x_5079_ = 1;
v___x_5080_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_5077_, v___x_5078_, v_env_5069_, v_val_5073_, v___x_5079_);
lean_dec(v_val_5073_);
if (v_isShared_5076_ == 0)
{
lean_ctor_set(v___x_5075_, 0, v___x_5080_);
v___x_5082_ = v___x_5075_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v___x_5080_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object* v_env_5085_, lean_object* v_moduleName_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l_Lean_getVersoModuleDoc_x3f(v_env_5085_, v_moduleName_5086_);
lean_dec(v_moduleName_5086_);
lean_dec_ref(v_env_5085_);
return v_res_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object* v_env_5090_, lean_object* v_snippet_5091_){
_start:
{
lean_object* v_docs_5092_; uint8_t v___x_5093_; 
lean_inc_ref(v_env_5090_);
v_docs_5092_ = l_Lean_getMainVersoModuleDocs(v_env_5090_);
v___x_5093_ = l_Lean_VersoModuleDocs_canAdd(v_docs_5092_, v_snippet_5091_);
if (v___x_5093_ == 0)
{
lean_object* v_terminalNesting_5094_; lean_object* v___x_5095_; lean_object* v___y_5097_; 
lean_dec_ref(v_snippet_5091_);
lean_dec_ref(v_env_5090_);
v_terminalNesting_5094_ = lean_ctor_get(v_docs_5092_, 1);
lean_inc(v_terminalNesting_5094_);
lean_dec_ref(v_docs_5092_);
v___x_5095_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__0));
if (lean_obj_tag(v_terminalNesting_5094_) == 0)
{
lean_object* v___x_5102_; 
v___x_5102_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___y_5097_ = v___x_5102_;
goto v___jp_5096_;
}
else
{
lean_object* v_val_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v_val_5103_ = lean_ctor_get(v_terminalNesting_5094_, 0);
lean_inc(v_val_5103_);
lean_dec_ref(v_terminalNesting_5094_);
v___x_5104_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__1));
v___x_5105_ = l_Nat_reprFast(v_val_5103_);
v___x_5106_ = lean_string_append(v___x_5104_, v___x_5105_);
lean_dec_ref(v___x_5105_);
v___x_5107_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_5108_ = lean_string_append(v___x_5106_, v___x_5107_);
v___y_5097_ = v___x_5108_;
goto v___jp_5096_;
}
v___jp_5096_:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; 
v___x_5098_ = lean_string_append(v___x_5095_, v___y_5097_);
lean_dec_ref(v___y_5097_);
v___x_5099_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_5100_ = lean_string_append(v___x_5098_, v___x_5099_);
v___x_5101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5100_);
return v___x_5101_;
}
}
else
{
lean_object* v___x_5109_; lean_object* v_toEnvExtension_5110_; lean_object* v_asyncMode_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; 
lean_dec_ref(v_docs_5092_);
v___x_5109_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_5110_ = lean_ctor_get(v___x_5109_, 0);
lean_inc_ref(v_toEnvExtension_5110_);
v_asyncMode_5111_ = lean_ctor_get(v_toEnvExtension_5110_, 2);
lean_inc(v_asyncMode_5111_);
lean_dec_ref(v_toEnvExtension_5110_);
v___x_5112_ = lean_box(0);
v___x_5113_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5109_, v_env_5090_, v_snippet_5091_, v_asyncMode_5111_, v___x_5112_);
lean_dec(v_asyncMode_5111_);
v___x_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5114_, 0, v___x_5113_);
return v___x_5114_;
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
l_Lean_instInhabitedVersoDocString_default = _init_l_Lean_instInhabitedVersoDocString_default();
lean_mark_persistent(l_Lean_instInhabitedVersoDocString_default);
l_Lean_instInhabitedVersoDocString = _init_l_Lean_instInhabitedVersoDocString();
lean_mark_persistent(l_Lean_instInhabitedVersoDocString);
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
res = l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_docStringExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_docStringExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_versoDocStringExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_versoDocStringExt);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_();
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
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_();
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
