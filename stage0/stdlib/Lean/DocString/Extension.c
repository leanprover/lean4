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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRange_default;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "doc"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "verso"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(146, 8, 133, 236, 68, 139, 240, 234)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(153, 72, 77, 160, 222, 42, 129, 126)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "whether to use Verso syntax in docstrings"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(3, 233, 138, 33, 66, 196, 218, 104)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 198, 182, 78, 108, 58, 220, 60)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_doc_verso;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(146, 8, 133, 236, 68, 139, 240, 234)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(153, 72, 77, 160, 222, 42, 129, 126)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(237, 134, 110, 210, 89, 29, 102, 103)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "whether to use Verso syntax in module docstrings (falls back to `doc.verso` if not set)"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(3, 233, 138, 33, 66, 196, 218, 104)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 198, 182, 78, 108, 58, 220, 60)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(228, 159, 139, 71, 221, 243, 206, 45)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_doc_verso_module;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "docStringExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(220, 176, 252, 112, 223, 70, 141, 135)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
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
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__9_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__8_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(251, 17, 71, 28, 211, 27, 155, 40)}};
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "versoDocStringExt"};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 29, 13, 95, 132, 33, 43, 178)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value;
static lean_once_cell_t l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoModuleDocs_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoModuleDocs_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedVersoModuleDocs_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoModuleDocs_default___closed__2;
static lean_once_cell_t l_Lean_instInhabitedVersoModuleDocs_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoModuleDocs_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoModuleDocs_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_VersoModuleDocs_assemble___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value),((lean_object*)&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value),((lean_object*)&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value)}};
static const lean_object* l_Lean_VersoModuleDocs_assemble___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_assemble___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object*);
static const lean_array_object l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(lean_object* v_name_235_, lean_object* v_decl_236_, lean_object* v_ref_237_){
_start:
{
lean_object* v_defValue_239_; lean_object* v_descr_240_; lean_object* v_deprecation_x3f_241_; lean_object* v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_defValue_239_ = lean_ctor_get(v_decl_236_, 0);
v_descr_240_ = lean_ctor_get(v_decl_236_, 1);
v_deprecation_x3f_241_ = lean_ctor_get(v_decl_236_, 2);
v___x_242_ = lean_alloc_ctor(1, 0, 1);
v___x_243_ = lean_unbox(v_defValue_239_);
lean_ctor_set_uint8(v___x_242_, 0, v___x_243_);
lean_inc(v_deprecation_x3f_241_);
lean_inc_ref(v_descr_240_);
lean_inc_n(v_name_235_, 2);
v___x_244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_244_, 0, v_name_235_);
lean_ctor_set(v___x_244_, 1, v_ref_237_);
lean_ctor_set(v___x_244_, 2, v___x_242_);
lean_ctor_set(v___x_244_, 3, v_descr_240_);
lean_ctor_set(v___x_244_, 4, v_deprecation_x3f_241_);
v___x_245_ = lean_register_option(v_name_235_, v___x_244_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_253_; 
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; 
v_unused_254_ = lean_ctor_get(v___x_245_, 0);
lean_dec(v_unused_254_);
v___x_247_ = v___x_245_;
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
else
{
lean_dec(v___x_245_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
lean_inc(v_defValue_239_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_name_235_);
lean_ctor_set(v___x_249_, 1, v_defValue_239_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_249_);
v___x_251_ = v___x_247_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec(v_name_235_);
v_a_255_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_245_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_245_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_263_, lean_object* v_decl_264_, lean_object* v_ref_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v_name_263_, v_decl_264_, v_ref_265_);
lean_dec_ref(v_decl_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_285_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_286_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_287_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_288_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_285_, v___x_286_, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4____boxed(lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_309_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_310_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_311_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_308_, v___x_309_, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4____boxed(lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_box(1);
v___x_316_ = lean_st_mk_ref(v___x_315_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2____boxed(lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_object* v_k_322_; lean_object* v_v_323_; lean_object* v_l_324_; lean_object* v_r_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_k_322_ = lean_ctor_get(v_x_321_, 1);
v_v_323_ = lean_ctor_get(v_x_321_, 2);
v_l_324_ = lean_ctor_get(v_x_321_, 3);
v_r_325_ = lean_ctor_get(v_x_321_, 4);
v___x_326_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_320_, v_l_324_);
lean_inc(v_v_323_);
lean_inc(v_k_322_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v_k_322_);
lean_ctor_set(v___x_327_, 1, v_v_323_);
v___x_328_ = lean_array_push(v___x_326_, v___x_327_);
v_init_320_ = v___x_328_;
v_x_321_ = v_r_325_;
goto _start;
}
else
{
return v_init_320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_330_, lean_object* v_x_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_330_, v_x_331_);
lean_dec(v_x_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(lean_object* v_x_337_, lean_object* v_s_338_){
_start:
{
lean_object* v___x_339_; lean_object* v_ents_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_339_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v_ents_340_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v___x_339_, v_s_338_);
v___x_341_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
lean_inc_ref(v_ents_340_);
v___x_342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v_ents_340_);
lean_ctor_set(v___x_342_, 2, v_ents_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object* v_x_343_, lean_object* v_s_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(v_x_343_, v_s_344_);
lean_dec(v_s_344_);
lean_dec_ref(v_x_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___f_354_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_355_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_356_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_357_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_355_, v___x_356_, v___f_354_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(lean_object* v_init_360_, lean_object* v_t_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_360_, v_t_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_363_, lean_object* v_t_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(v_init_363_, v_t_364_);
lean_dec(v_t_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_366_, lean_object* v_x_367_){
_start:
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_object* v_k_368_; lean_object* v_v_369_; lean_object* v_l_370_; lean_object* v_r_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_k_368_ = lean_ctor_get(v_x_367_, 1);
v_v_369_ = lean_ctor_get(v_x_367_, 2);
v_l_370_ = lean_ctor_get(v_x_367_, 3);
v_r_371_ = lean_ctor_get(v_x_367_, 4);
v___x_372_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_366_, v_l_370_);
lean_inc(v_v_369_);
lean_inc(v_k_368_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v_k_368_);
lean_ctor_set(v___x_373_, 1, v_v_369_);
v___x_374_ = lean_array_push(v___x_372_, v___x_373_);
v_init_366_ = v___x_374_;
v_x_367_ = v_r_371_;
goto _start;
}
else
{
return v_init_366_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_376_, v_x_377_);
lean_dec(v_x_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(lean_object* v_x_383_, lean_object* v_s_384_){
_start:
{
lean_object* v___x_385_; lean_object* v_ents_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_385_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v_ents_386_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v___x_385_, v_s_384_);
v___x_387_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
lean_inc_ref(v_ents_386_);
v___x_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_ents_386_);
lean_ctor_set(v___x_388_, 2, v_ents_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object* v_x_389_, lean_object* v_s_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(v_x_389_, v_s_390_);
lean_dec(v_s_390_);
lean_dec_ref(v_x_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___f_421_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_422_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_423_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_424_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_422_, v___x_423_, v___f_421_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_();
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(lean_object* v_init_427_, lean_object* v_t_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_427_, v_t_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_430_, lean_object* v_t_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(v_init_430_, v_t_431_);
lean_dec(v_t_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_box(1);
v___x_435_ = lean_st_mk_ref(v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_439_, lean_object* v_x_440_){
_start:
{
if (lean_obj_tag(v_x_440_) == 0)
{
lean_object* v_k_441_; lean_object* v_v_442_; lean_object* v_l_443_; lean_object* v_r_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_k_441_ = lean_ctor_get(v_x_440_, 1);
v_v_442_ = lean_ctor_get(v_x_440_, 2);
v_l_443_ = lean_ctor_get(v_x_440_, 3);
v_r_444_ = lean_ctor_get(v_x_440_, 4);
v___x_445_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_439_, v_l_443_);
lean_inc(v_v_442_);
lean_inc(v_k_441_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_k_441_);
lean_ctor_set(v___x_446_, 1, v_v_442_);
v___x_447_ = lean_array_push(v___x_445_, v___x_446_);
v_init_439_ = v___x_447_;
v_x_440_ = v_r_444_;
goto _start;
}
else
{
return v_init_439_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_449_, v_x_450_);
lean_dec(v_x_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(lean_object* v_x_456_, lean_object* v_s_457_){
_start:
{
lean_object* v___x_458_; lean_object* v_ents_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_458_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v_ents_459_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v___x_458_, v_s_457_);
v___x_460_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
lean_inc_ref(v_ents_459_);
v___x_461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v_ents_459_);
lean_ctor_set(v___x_461_, 2, v_ents_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object* v_x_462_, lean_object* v_s_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(v_x_462_, v_s_463_);
lean_dec(v_s_463_);
lean_dec_ref(v_x_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___f_471_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v___x_472_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v___x_473_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_474_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_472_, v___x_473_, v___f_471_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(lean_object* v_init_477_, lean_object* v_t_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_477_, v_t_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_480_, lean_object* v_t_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(v_init_480_, v_t_481_);
lean_dec(v_t_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString(lean_object* v_declName_483_, lean_object* v_docString_484_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_486_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_487_ = lean_st_ref_take(v___x_486_);
v___x_488_ = l_String_removeLeadingSpaces(v_docString_484_);
v___x_489_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_483_, v___x_488_, v___x_487_);
v___x_490_ = lean_st_ref_set(v___x_486_, v___x_489_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString___boxed(lean_object* v_declName_492_, lean_object* v_docString_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_addBuiltinDocString(v_declName_492_, v_docString_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object* v_k_496_, lean_object* v_t_497_){
_start:
{
if (lean_obj_tag(v_t_497_) == 0)
{
lean_object* v_k_498_; lean_object* v_v_499_; lean_object* v_l_500_; lean_object* v_r_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_1155_; 
v_k_498_ = lean_ctor_get(v_t_497_, 1);
v_v_499_ = lean_ctor_get(v_t_497_, 2);
v_l_500_ = lean_ctor_get(v_t_497_, 3);
v_r_501_ = lean_ctor_get(v_t_497_, 4);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_t_497_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; 
v_unused_1156_ = lean_ctor_get(v_t_497_, 0);
lean_dec(v_unused_1156_);
v___x_503_ = v_t_497_;
v_isShared_504_ = v_isSharedCheck_1155_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_r_501_);
lean_inc(v_l_500_);
lean_inc(v_v_499_);
lean_inc(v_k_498_);
lean_dec(v_t_497_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_1155_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
uint8_t v___x_505_; 
v___x_505_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_496_, v_k_498_);
switch(v___x_505_)
{
case 0:
{
lean_object* v_impl_506_; lean_object* v___x_507_; 
v_impl_506_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_496_, v_l_500_);
v___x_507_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_506_) == 0)
{
if (lean_obj_tag(v_r_501_) == 0)
{
lean_object* v_size_508_; lean_object* v_size_509_; lean_object* v_k_510_; lean_object* v_v_511_; lean_object* v_l_512_; lean_object* v_r_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_size_508_ = lean_ctor_get(v_impl_506_, 0);
lean_inc(v_size_508_);
v_size_509_ = lean_ctor_get(v_r_501_, 0);
v_k_510_ = lean_ctor_get(v_r_501_, 1);
v_v_511_ = lean_ctor_get(v_r_501_, 2);
v_l_512_ = lean_ctor_get(v_r_501_, 3);
lean_inc(v_l_512_);
v_r_513_ = lean_ctor_get(v_r_501_, 4);
v___x_514_ = lean_unsigned_to_nat(3u);
v___x_515_ = lean_nat_mul(v___x_514_, v_size_508_);
v___x_516_ = lean_nat_dec_lt(v___x_515_, v_size_509_);
lean_dec(v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
lean_dec(v_l_512_);
v___x_517_ = lean_nat_add(v___x_507_, v_size_508_);
lean_dec(v_size_508_);
v___x_518_ = lean_nat_add(v___x_517_, v_size_509_);
lean_dec(v___x_517_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 3, v_impl_506_);
lean_ctor_set(v___x_503_, 0, v___x_518_);
v___x_520_ = v___x_503_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_impl_506_);
lean_ctor_set(v_reuseFailAlloc_521_, 4, v_r_501_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
else
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_585_; 
lean_inc(v_r_513_);
lean_inc(v_v_511_);
lean_inc(v_k_510_);
lean_inc(v_size_509_);
v_isSharedCheck_585_ = !lean_is_exclusive(v_r_501_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; lean_object* v_unused_587_; lean_object* v_unused_588_; lean_object* v_unused_589_; lean_object* v_unused_590_; 
v_unused_586_ = lean_ctor_get(v_r_501_, 4);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_r_501_, 3);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_r_501_, 2);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_r_501_, 1);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_r_501_, 0);
lean_dec(v_unused_590_);
v___x_523_ = v_r_501_;
v_isShared_524_ = v_isSharedCheck_585_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_r_501_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_585_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_size_525_; lean_object* v_k_526_; lean_object* v_v_527_; lean_object* v_l_528_; lean_object* v_r_529_; lean_object* v_size_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_size_525_ = lean_ctor_get(v_l_512_, 0);
v_k_526_ = lean_ctor_get(v_l_512_, 1);
v_v_527_ = lean_ctor_get(v_l_512_, 2);
v_l_528_ = lean_ctor_get(v_l_512_, 3);
v_r_529_ = lean_ctor_get(v_l_512_, 4);
v_size_530_ = lean_ctor_get(v_r_513_, 0);
v___x_531_ = lean_unsigned_to_nat(2u);
v___x_532_ = lean_nat_mul(v___x_531_, v_size_530_);
v___x_533_ = lean_nat_dec_lt(v_size_525_, v___x_532_);
lean_dec(v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_561_; 
lean_inc(v_r_529_);
lean_inc(v_l_528_);
lean_inc(v_v_527_);
lean_inc(v_k_526_);
v_isSharedCheck_561_ = !lean_is_exclusive(v_l_512_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; lean_object* v_unused_563_; lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; 
v_unused_562_ = lean_ctor_get(v_l_512_, 4);
lean_dec(v_unused_562_);
v_unused_563_ = lean_ctor_get(v_l_512_, 3);
lean_dec(v_unused_563_);
v_unused_564_ = lean_ctor_get(v_l_512_, 2);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_l_512_, 1);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_l_512_, 0);
lean_dec(v_unused_566_);
v___x_535_ = v_l_512_;
v_isShared_536_ = v_isSharedCheck_561_;
goto v_resetjp_534_;
}
else
{
lean_dec(v_l_512_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_561_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_551_; 
v___x_537_ = lean_nat_add(v___x_507_, v_size_508_);
lean_dec(v_size_508_);
v___x_538_ = lean_nat_add(v___x_537_, v_size_509_);
lean_dec(v_size_509_);
if (lean_obj_tag(v_l_528_) == 0)
{
lean_object* v_size_559_; 
v_size_559_ = lean_ctor_get(v_l_528_, 0);
lean_inc(v_size_559_);
v___y_551_ = v_size_559_;
goto v___jp_550_;
}
else
{
lean_object* v___x_560_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___y_551_ = v___x_560_;
goto v___jp_550_;
}
v___jp_539_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = lean_nat_add(v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec(v___y_541_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 4, v_r_513_);
lean_ctor_set(v___x_535_, 3, v_r_529_);
lean_ctor_set(v___x_535_, 2, v_v_511_);
lean_ctor_set(v___x_535_, 1, v_k_510_);
lean_ctor_set(v___x_535_, 0, v___x_543_);
v___x_545_ = v___x_535_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_k_510_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_v_511_);
lean_ctor_set(v_reuseFailAlloc_549_, 3, v_r_529_);
lean_ctor_set(v_reuseFailAlloc_549_, 4, v_r_513_);
v___x_545_ = v_reuseFailAlloc_549_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_547_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 4, v___x_545_);
lean_ctor_set(v___x_523_, 3, v___y_540_);
lean_ctor_set(v___x_523_, 2, v_v_527_);
lean_ctor_set(v___x_523_, 1, v_k_526_);
lean_ctor_set(v___x_523_, 0, v___x_538_);
v___x_547_ = v___x_523_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_k_526_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_v_527_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v___y_540_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
v___jp_550_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_nat_add(v___x_537_, v___y_551_);
lean_dec(v___y_551_);
lean_dec(v___x_537_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v_l_528_);
lean_ctor_set(v___x_503_, 3, v_impl_506_);
lean_ctor_set(v___x_503_, 0, v___x_552_);
v___x_554_ = v___x_503_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_impl_506_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_l_528_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; 
v___x_555_ = lean_nat_add(v___x_507_, v_size_530_);
if (lean_obj_tag(v_r_529_) == 0)
{
lean_object* v_size_556_; 
v_size_556_ = lean_ctor_get(v_r_529_, 0);
lean_inc(v_size_556_);
v___y_540_ = v___x_554_;
v___y_541_ = v___x_555_;
v___y_542_ = v_size_556_;
goto v___jp_539_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = lean_unsigned_to_nat(0u);
v___y_540_ = v___x_554_;
v___y_541_ = v___x_555_;
v___y_542_ = v___x_557_;
goto v___jp_539_;
}
}
}
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
lean_del_object(v___x_503_);
v___x_567_ = lean_nat_add(v___x_507_, v_size_508_);
lean_dec(v_size_508_);
v___x_568_ = lean_nat_add(v___x_567_, v_size_509_);
lean_dec(v_size_509_);
v___x_569_ = lean_nat_add(v___x_567_, v_size_525_);
lean_dec(v___x_567_);
lean_inc_ref(v_impl_506_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 4, v_l_512_);
lean_ctor_set(v___x_523_, 3, v_impl_506_);
lean_ctor_set(v___x_523_, 2, v_v_499_);
lean_ctor_set(v___x_523_, 1, v_k_498_);
lean_ctor_set(v___x_523_, 0, v___x_569_);
v___x_571_ = v___x_523_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v_impl_506_);
lean_ctor_set(v_reuseFailAlloc_584_, 4, v_l_512_);
v___x_571_ = v_reuseFailAlloc_584_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
v_isSharedCheck_578_ = !lean_is_exclusive(v_impl_506_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; lean_object* v_unused_580_; lean_object* v_unused_581_; lean_object* v_unused_582_; lean_object* v_unused_583_; 
v_unused_579_ = lean_ctor_get(v_impl_506_, 4);
lean_dec(v_unused_579_);
v_unused_580_ = lean_ctor_get(v_impl_506_, 3);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_impl_506_, 2);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_impl_506_, 1);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_impl_506_, 0);
lean_dec(v_unused_583_);
v___x_573_ = v_impl_506_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_impl_506_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 4, v_r_513_);
lean_ctor_set(v___x_573_, 3, v___x_571_);
lean_ctor_set(v___x_573_, 2, v_v_511_);
lean_ctor_set(v___x_573_, 1, v_k_510_);
lean_ctor_set(v___x_573_, 0, v___x_568_);
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_k_510_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_v_511_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_577_, 4, v_r_513_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v_size_591_ = lean_ctor_get(v_impl_506_, 0);
lean_inc(v_size_591_);
v___x_592_ = lean_nat_add(v___x_507_, v_size_591_);
lean_dec(v_size_591_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 3, v_impl_506_);
lean_ctor_set(v___x_503_, 0, v___x_592_);
v___x_594_ = v___x_503_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_impl_506_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v_r_501_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
if (lean_obj_tag(v_r_501_) == 0)
{
lean_object* v_l_596_; 
v_l_596_ = lean_ctor_get(v_r_501_, 3);
lean_inc(v_l_596_);
if (lean_obj_tag(v_l_596_) == 0)
{
lean_object* v_r_597_; 
v_r_597_ = lean_ctor_get(v_r_501_, 4);
lean_inc(v_r_597_);
if (lean_obj_tag(v_r_597_) == 0)
{
lean_object* v_size_598_; lean_object* v_k_599_; lean_object* v_v_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_613_; 
v_size_598_ = lean_ctor_get(v_r_501_, 0);
v_k_599_ = lean_ctor_get(v_r_501_, 1);
v_v_600_ = lean_ctor_get(v_r_501_, 2);
v_isSharedCheck_613_ = !lean_is_exclusive(v_r_501_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; lean_object* v_unused_615_; 
v_unused_614_ = lean_ctor_get(v_r_501_, 4);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_r_501_, 3);
lean_dec(v_unused_615_);
v___x_602_ = v_r_501_;
v_isShared_603_ = v_isSharedCheck_613_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_v_600_);
lean_inc(v_k_599_);
lean_inc(v_size_598_);
lean_dec(v_r_501_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_613_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v_size_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v_size_604_ = lean_ctor_get(v_l_596_, 0);
v___x_605_ = lean_nat_add(v___x_507_, v_size_598_);
lean_dec(v_size_598_);
v___x_606_ = lean_nat_add(v___x_507_, v_size_604_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 4, v_l_596_);
lean_ctor_set(v___x_602_, 3, v_impl_506_);
lean_ctor_set(v___x_602_, 2, v_v_499_);
lean_ctor_set(v___x_602_, 1, v_k_498_);
lean_ctor_set(v___x_602_, 0, v___x_606_);
v___x_608_ = v___x_602_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_impl_506_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_l_596_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v_r_597_);
lean_ctor_set(v___x_503_, 3, v___x_608_);
lean_ctor_set(v___x_503_, 2, v_v_600_);
lean_ctor_set(v___x_503_, 1, v_k_599_);
lean_ctor_set(v___x_503_, 0, v___x_605_);
v___x_610_ = v___x_503_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_k_599_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_v_600_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_r_597_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
else
{
lean_object* v_k_616_; lean_object* v_v_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_640_; 
v_k_616_ = lean_ctor_get(v_r_501_, 1);
v_v_617_ = lean_ctor_get(v_r_501_, 2);
v_isSharedCheck_640_ = !lean_is_exclusive(v_r_501_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; lean_object* v_unused_642_; lean_object* v_unused_643_; 
v_unused_641_ = lean_ctor_get(v_r_501_, 4);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_r_501_, 3);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v_r_501_, 0);
lean_dec(v_unused_643_);
v___x_619_ = v_r_501_;
v_isShared_620_ = v_isSharedCheck_640_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_v_617_);
lean_inc(v_k_616_);
lean_dec(v_r_501_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_640_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_k_621_; lean_object* v_v_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_636_; 
v_k_621_ = lean_ctor_get(v_l_596_, 1);
v_v_622_ = lean_ctor_get(v_l_596_, 2);
v_isSharedCheck_636_ = !lean_is_exclusive(v_l_596_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; lean_object* v_unused_638_; lean_object* v_unused_639_; 
v_unused_637_ = lean_ctor_get(v_l_596_, 4);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_l_596_, 3);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_l_596_, 0);
lean_dec(v_unused_639_);
v___x_624_ = v_l_596_;
v_isShared_625_ = v_isSharedCheck_636_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_v_622_);
lean_inc(v_k_621_);
lean_dec(v_l_596_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_636_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = lean_unsigned_to_nat(3u);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v_r_597_);
lean_ctor_set(v___x_624_, 3, v_r_597_);
lean_ctor_set(v___x_624_, 2, v_v_499_);
lean_ctor_set(v___x_624_, 1, v_k_498_);
lean_ctor_set(v___x_624_, 0, v___x_507_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_r_597_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v_r_597_);
v___x_628_ = v_reuseFailAlloc_635_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_630_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 3, v_r_597_);
lean_ctor_set(v___x_619_, 0, v___x_507_);
v___x_630_ = v___x_619_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_k_616_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_v_617_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v_r_597_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v_r_597_);
v___x_630_ = v_reuseFailAlloc_634_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_632_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v___x_630_);
lean_ctor_set(v___x_503_, 3, v___x_628_);
lean_ctor_set(v___x_503_, 2, v_v_622_);
lean_ctor_set(v___x_503_, 1, v_k_621_);
lean_ctor_set(v___x_503_, 0, v___x_626_);
v___x_632_ = v___x_503_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_644_; 
v_r_644_ = lean_ctor_get(v_r_501_, 4);
lean_inc(v_r_644_);
if (lean_obj_tag(v_r_644_) == 0)
{
lean_object* v_k_645_; lean_object* v_v_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_657_; 
v_k_645_ = lean_ctor_get(v_r_501_, 1);
v_v_646_ = lean_ctor_get(v_r_501_, 2);
v_isSharedCheck_657_ = !lean_is_exclusive(v_r_501_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; lean_object* v_unused_659_; lean_object* v_unused_660_; 
v_unused_658_ = lean_ctor_get(v_r_501_, 4);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v_r_501_, 3);
lean_dec(v_unused_659_);
v_unused_660_ = lean_ctor_get(v_r_501_, 0);
lean_dec(v_unused_660_);
v___x_648_ = v_r_501_;
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_v_646_);
lean_inc(v_k_645_);
lean_dec(v_r_501_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_unsigned_to_nat(3u);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 4, v_l_596_);
lean_ctor_set(v___x_648_, 2, v_v_499_);
lean_ctor_set(v___x_648_, 1, v_k_498_);
lean_ctor_set(v___x_648_, 0, v___x_507_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_656_, 3, v_l_596_);
lean_ctor_set(v_reuseFailAlloc_656_, 4, v_l_596_);
v___x_652_ = v_reuseFailAlloc_656_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_654_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v_r_644_);
lean_ctor_set(v___x_503_, 3, v___x_652_);
lean_ctor_set(v___x_503_, 2, v_v_646_);
lean_ctor_set(v___x_503_, 1, v_k_645_);
lean_ctor_set(v___x_503_, 0, v___x_650_);
v___x_654_ = v___x_503_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_655_, 4, v_r_644_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v_size_661_; lean_object* v_k_662_; lean_object* v_v_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_674_; 
v_size_661_ = lean_ctor_get(v_r_501_, 0);
v_k_662_ = lean_ctor_get(v_r_501_, 1);
v_v_663_ = lean_ctor_get(v_r_501_, 2);
v_isSharedCheck_674_ = !lean_is_exclusive(v_r_501_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; lean_object* v_unused_676_; 
v_unused_675_ = lean_ctor_get(v_r_501_, 4);
lean_dec(v_unused_675_);
v_unused_676_ = lean_ctor_get(v_r_501_, 3);
lean_dec(v_unused_676_);
v___x_665_ = v_r_501_;
v_isShared_666_ = v_isSharedCheck_674_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_v_663_);
lean_inc(v_k_662_);
lean_inc(v_size_661_);
lean_dec(v_r_501_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_674_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 3, v_r_644_);
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_size_661_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_k_662_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v_v_663_);
lean_ctor_set(v_reuseFailAlloc_673_, 3, v_r_644_);
lean_ctor_set(v_reuseFailAlloc_673_, 4, v_r_644_);
v___x_668_ = v_reuseFailAlloc_673_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = lean_unsigned_to_nat(2u);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v___x_668_);
lean_ctor_set(v___x_503_, 3, v_r_644_);
lean_ctor_set(v___x_503_, 0, v___x_669_);
v___x_671_ = v___x_503_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_r_644_);
lean_ctor_set(v_reuseFailAlloc_672_, 4, v___x_668_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
else
{
lean_object* v___x_678_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 3, v_r_501_);
lean_ctor_set(v___x_503_, 0, v___x_507_);
v___x_678_ = v___x_503_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_r_501_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_r_501_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
case 1:
{
lean_del_object(v___x_503_);
lean_dec(v_v_499_);
lean_dec(v_k_498_);
if (lean_obj_tag(v_l_500_) == 0)
{
if (lean_obj_tag(v_r_501_) == 0)
{
lean_object* v_size_680_; lean_object* v_k_681_; lean_object* v_v_682_; lean_object* v_l_683_; lean_object* v_r_684_; lean_object* v_size_685_; lean_object* v_k_686_; lean_object* v_v_687_; lean_object* v_l_688_; lean_object* v_r_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_size_680_ = lean_ctor_get(v_l_500_, 0);
v_k_681_ = lean_ctor_get(v_l_500_, 1);
v_v_682_ = lean_ctor_get(v_l_500_, 2);
v_l_683_ = lean_ctor_get(v_l_500_, 3);
v_r_684_ = lean_ctor_get(v_l_500_, 4);
lean_inc(v_r_684_);
v_size_685_ = lean_ctor_get(v_r_501_, 0);
v_k_686_ = lean_ctor_get(v_r_501_, 1);
v_v_687_ = lean_ctor_get(v_r_501_, 2);
v_l_688_ = lean_ctor_get(v_r_501_, 3);
lean_inc(v_l_688_);
v_r_689_ = lean_ctor_get(v_r_501_, 4);
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_dec_lt(v_size_680_, v_size_685_);
if (v___x_691_ == 0)
{
lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_827_; 
lean_inc(v_l_683_);
lean_inc(v_v_682_);
lean_inc(v_k_681_);
v_isSharedCheck_827_ = !lean_is_exclusive(v_l_500_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; lean_object* v_unused_829_; lean_object* v_unused_830_; lean_object* v_unused_831_; lean_object* v_unused_832_; 
v_unused_828_ = lean_ctor_get(v_l_500_, 4);
lean_dec(v_unused_828_);
v_unused_829_ = lean_ctor_get(v_l_500_, 3);
lean_dec(v_unused_829_);
v_unused_830_ = lean_ctor_get(v_l_500_, 2);
lean_dec(v_unused_830_);
v_unused_831_ = lean_ctor_get(v_l_500_, 1);
lean_dec(v_unused_831_);
v_unused_832_ = lean_ctor_get(v_l_500_, 0);
lean_dec(v_unused_832_);
v___x_693_ = v_l_500_;
v_isShared_694_ = v_isSharedCheck_827_;
goto v_resetjp_692_;
}
else
{
lean_dec(v_l_500_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_827_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v_tree_696_; 
v___x_695_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_681_, v_v_682_, v_l_683_, v_r_684_);
v_tree_696_ = lean_ctor_get(v___x_695_, 2);
lean_inc(v_tree_696_);
if (lean_obj_tag(v_tree_696_) == 0)
{
lean_object* v_k_697_; lean_object* v_v_698_; lean_object* v_size_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_k_697_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_k_697_);
v_v_698_ = lean_ctor_get(v___x_695_, 1);
lean_inc(v_v_698_);
lean_dec_ref(v___x_695_);
v_size_699_ = lean_ctor_get(v_tree_696_, 0);
v___x_700_ = lean_unsigned_to_nat(3u);
v___x_701_ = lean_nat_mul(v___x_700_, v_size_699_);
v___x_702_ = lean_nat_dec_lt(v___x_701_, v_size_685_);
lean_dec(v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
lean_dec(v_l_688_);
v___x_703_ = lean_nat_add(v___x_690_, v_size_699_);
v___x_704_ = lean_nat_add(v___x_703_, v_size_685_);
lean_dec(v___x_703_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 4, v_r_501_);
lean_ctor_set(v___x_693_, 3, v_tree_696_);
lean_ctor_set(v___x_693_, 2, v_v_698_);
lean_ctor_set(v___x_693_, 1, v_k_697_);
lean_ctor_set(v___x_693_, 0, v___x_704_);
v___x_706_ = v___x_693_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_k_697_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_v_698_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_tree_696_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v_r_501_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
else
{
lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_762_; 
lean_inc(v_r_689_);
lean_inc(v_v_687_);
lean_inc(v_k_686_);
lean_inc(v_size_685_);
v_isSharedCheck_762_ = !lean_is_exclusive(v_r_501_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; lean_object* v_unused_764_; lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; 
v_unused_763_ = lean_ctor_get(v_r_501_, 4);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_r_501_, 3);
lean_dec(v_unused_764_);
v_unused_765_ = lean_ctor_get(v_r_501_, 2);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_r_501_, 1);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_r_501_, 0);
lean_dec(v_unused_767_);
v___x_709_ = v_r_501_;
v_isShared_710_ = v_isSharedCheck_762_;
goto v_resetjp_708_;
}
else
{
lean_dec(v_r_501_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_762_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_size_711_; lean_object* v_k_712_; lean_object* v_v_713_; lean_object* v_l_714_; lean_object* v_r_715_; lean_object* v_size_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_size_711_ = lean_ctor_get(v_l_688_, 0);
v_k_712_ = lean_ctor_get(v_l_688_, 1);
v_v_713_ = lean_ctor_get(v_l_688_, 2);
v_l_714_ = lean_ctor_get(v_l_688_, 3);
v_r_715_ = lean_ctor_get(v_l_688_, 4);
v_size_716_ = lean_ctor_get(v_r_689_, 0);
v___x_717_ = lean_unsigned_to_nat(2u);
v___x_718_ = lean_nat_mul(v___x_717_, v_size_716_);
v___x_719_ = lean_nat_dec_lt(v_size_711_, v___x_718_);
lean_dec(v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_747_; 
lean_inc(v_r_715_);
lean_inc(v_l_714_);
lean_inc(v_v_713_);
lean_inc(v_k_712_);
v_isSharedCheck_747_ = !lean_is_exclusive(v_l_688_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; lean_object* v_unused_749_; lean_object* v_unused_750_; lean_object* v_unused_751_; lean_object* v_unused_752_; 
v_unused_748_ = lean_ctor_get(v_l_688_, 4);
lean_dec(v_unused_748_);
v_unused_749_ = lean_ctor_get(v_l_688_, 3);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_l_688_, 2);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_l_688_, 1);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_l_688_, 0);
lean_dec(v_unused_752_);
v___x_721_ = v_l_688_;
v_isShared_722_ = v_isSharedCheck_747_;
goto v_resetjp_720_;
}
else
{
lean_dec(v_l_688_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_747_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_737_; 
v___x_723_ = lean_nat_add(v___x_690_, v_size_699_);
v___x_724_ = lean_nat_add(v___x_723_, v_size_685_);
lean_dec(v_size_685_);
if (lean_obj_tag(v_l_714_) == 0)
{
lean_object* v_size_745_; 
v_size_745_ = lean_ctor_get(v_l_714_, 0);
lean_inc(v_size_745_);
v___y_737_ = v_size_745_;
goto v___jp_736_;
}
else
{
lean_object* v___x_746_; 
v___x_746_ = lean_unsigned_to_nat(0u);
v___y_737_ = v___x_746_;
goto v___jp_736_;
}
v___jp_725_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_nat_add(v___y_726_, v___y_728_);
lean_dec(v___y_728_);
lean_dec(v___y_726_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 4, v_r_689_);
lean_ctor_set(v___x_721_, 3, v_r_715_);
lean_ctor_set(v___x_721_, 2, v_v_687_);
lean_ctor_set(v___x_721_, 1, v_k_686_);
lean_ctor_set(v___x_721_, 0, v___x_729_);
v___x_731_ = v___x_721_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_k_686_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_v_687_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v_r_715_);
lean_ctor_set(v_reuseFailAlloc_735_, 4, v_r_689_);
v___x_731_ = v_reuseFailAlloc_735_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 4, v___x_731_);
lean_ctor_set(v___x_709_, 3, v___y_727_);
lean_ctor_set(v___x_709_, 2, v_v_713_);
lean_ctor_set(v___x_709_, 1, v_k_712_);
lean_ctor_set(v___x_709_, 0, v___x_724_);
v___x_733_ = v___x_709_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_k_712_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_v_713_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v___y_727_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
v___jp_736_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_738_ = lean_nat_add(v___x_723_, v___y_737_);
lean_dec(v___y_737_);
lean_dec(v___x_723_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 4, v_l_714_);
lean_ctor_set(v___x_693_, 3, v_tree_696_);
lean_ctor_set(v___x_693_, 2, v_v_698_);
lean_ctor_set(v___x_693_, 1, v_k_697_);
lean_ctor_set(v___x_693_, 0, v___x_738_);
v___x_740_ = v___x_693_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_k_697_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_v_698_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v_tree_696_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v_l_714_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; 
v___x_741_ = lean_nat_add(v___x_690_, v_size_716_);
if (lean_obj_tag(v_r_715_) == 0)
{
lean_object* v_size_742_; 
v_size_742_ = lean_ctor_get(v_r_715_, 0);
lean_inc(v_size_742_);
v___y_726_ = v___x_741_;
v___y_727_ = v___x_740_;
v___y_728_ = v_size_742_;
goto v___jp_725_;
}
else
{
lean_object* v___x_743_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___y_726_ = v___x_741_;
v___y_727_ = v___x_740_;
v___y_728_ = v___x_743_;
goto v___jp_725_;
}
}
}
}
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_753_ = lean_nat_add(v___x_690_, v_size_699_);
v___x_754_ = lean_nat_add(v___x_753_, v_size_685_);
lean_dec(v_size_685_);
v___x_755_ = lean_nat_add(v___x_753_, v_size_711_);
lean_dec(v___x_753_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 4, v_l_688_);
lean_ctor_set(v___x_709_, 3, v_tree_696_);
lean_ctor_set(v___x_709_, 2, v_v_698_);
lean_ctor_set(v___x_709_, 1, v_k_697_);
lean_ctor_set(v___x_709_, 0, v___x_755_);
v___x_757_ = v___x_709_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_k_697_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_v_698_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_tree_696_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_l_688_);
v___x_757_ = v_reuseFailAlloc_761_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 4, v_r_689_);
lean_ctor_set(v___x_693_, 3, v___x_757_);
lean_ctor_set(v___x_693_, 2, v_v_687_);
lean_ctor_set(v___x_693_, 1, v_k_686_);
lean_ctor_set(v___x_693_, 0, v___x_754_);
v___x_759_ = v___x_693_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_k_686_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_v_687_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_760_, 4, v_r_689_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
else
{
lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_821_; 
lean_inc(v_r_689_);
lean_inc(v_v_687_);
lean_inc(v_k_686_);
lean_inc(v_size_685_);
v_isSharedCheck_821_ = !lean_is_exclusive(v_r_501_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; lean_object* v_unused_823_; lean_object* v_unused_824_; lean_object* v_unused_825_; lean_object* v_unused_826_; 
v_unused_822_ = lean_ctor_get(v_r_501_, 4);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_r_501_, 3);
lean_dec(v_unused_823_);
v_unused_824_ = lean_ctor_get(v_r_501_, 2);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_r_501_, 1);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_r_501_, 0);
lean_dec(v_unused_826_);
v___x_769_ = v_r_501_;
v_isShared_770_ = v_isSharedCheck_821_;
goto v_resetjp_768_;
}
else
{
lean_dec(v_r_501_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_821_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
if (lean_obj_tag(v_l_688_) == 0)
{
if (lean_obj_tag(v_r_689_) == 0)
{
lean_object* v_k_771_; lean_object* v_v_772_; lean_object* v_size_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v_k_771_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_k_771_);
v_v_772_ = lean_ctor_get(v___x_695_, 1);
lean_inc(v_v_772_);
lean_dec_ref(v___x_695_);
v_size_773_ = lean_ctor_get(v_l_688_, 0);
v___x_774_ = lean_nat_add(v___x_690_, v_size_685_);
lean_dec(v_size_685_);
v___x_775_ = lean_nat_add(v___x_690_, v_size_773_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 4, v_l_688_);
lean_ctor_set(v___x_769_, 3, v_tree_696_);
lean_ctor_set(v___x_769_, 2, v_v_772_);
lean_ctor_set(v___x_769_, 1, v_k_771_);
lean_ctor_set(v___x_769_, 0, v___x_775_);
v___x_777_ = v___x_769_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_k_771_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_v_772_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v_tree_696_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_l_688_);
v___x_777_ = v_reuseFailAlloc_781_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_779_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 4, v_r_689_);
lean_ctor_set(v___x_693_, 3, v___x_777_);
lean_ctor_set(v___x_693_, 2, v_v_687_);
lean_ctor_set(v___x_693_, 1, v_k_686_);
lean_ctor_set(v___x_693_, 0, v___x_774_);
v___x_779_ = v___x_693_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_k_686_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_v_687_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_780_, 4, v_r_689_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
else
{
lean_object* v_k_782_; lean_object* v_v_783_; lean_object* v_k_784_; lean_object* v_v_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_799_; 
lean_dec(v_size_685_);
v_k_782_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_k_782_);
v_v_783_ = lean_ctor_get(v___x_695_, 1);
lean_inc(v_v_783_);
lean_dec_ref(v___x_695_);
v_k_784_ = lean_ctor_get(v_l_688_, 1);
v_v_785_ = lean_ctor_get(v_l_688_, 2);
v_isSharedCheck_799_ = !lean_is_exclusive(v_l_688_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; 
v_unused_800_ = lean_ctor_get(v_l_688_, 4);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_l_688_, 3);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_l_688_, 0);
lean_dec(v_unused_802_);
v___x_787_ = v_l_688_;
v_isShared_788_ = v_isSharedCheck_799_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_v_785_);
lean_inc(v_k_784_);
lean_dec(v_l_688_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_799_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = lean_unsigned_to_nat(3u);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 4, v_r_689_);
lean_ctor_set(v___x_787_, 3, v_r_689_);
lean_ctor_set(v___x_787_, 2, v_v_783_);
lean_ctor_set(v___x_787_, 1, v_k_782_);
lean_ctor_set(v___x_787_, 0, v___x_690_);
v___x_791_ = v___x_787_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_k_782_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_v_783_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_r_689_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_r_689_);
v___x_791_ = v_reuseFailAlloc_798_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_793_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 3, v_r_689_);
lean_ctor_set(v___x_769_, 0, v___x_690_);
v___x_793_ = v___x_769_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_k_686_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_v_687_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v_r_689_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v_r_689_);
v___x_793_ = v_reuseFailAlloc_797_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 4, v___x_793_);
lean_ctor_set(v___x_693_, 3, v___x_791_);
lean_ctor_set(v___x_693_, 2, v_v_785_);
lean_ctor_set(v___x_693_, 1, v_k_784_);
lean_ctor_set(v___x_693_, 0, v___x_789_);
v___x_795_ = v___x_693_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_k_784_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_v_785_);
lean_ctor_set(v_reuseFailAlloc_796_, 3, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_796_, 4, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_689_) == 0)
{
lean_object* v_k_803_; lean_object* v_v_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
lean_dec(v_size_685_);
v_k_803_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_k_803_);
v_v_804_ = lean_ctor_get(v___x_695_, 1);
lean_inc(v_v_804_);
lean_dec_ref(v___x_695_);
v___x_805_ = lean_unsigned_to_nat(3u);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 4, v_l_688_);
lean_ctor_set(v___x_769_, 2, v_v_804_);
lean_ctor_set(v___x_769_, 1, v_k_803_);
lean_ctor_set(v___x_769_, 0, v___x_690_);
v___x_807_ = v___x_769_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_k_803_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v_v_804_);
lean_ctor_set(v_reuseFailAlloc_811_, 3, v_l_688_);
lean_ctor_set(v_reuseFailAlloc_811_, 4, v_l_688_);
v___x_807_ = v_reuseFailAlloc_811_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_809_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 4, v_r_689_);
lean_ctor_set(v___x_693_, 3, v___x_807_);
lean_ctor_set(v___x_693_, 2, v_v_687_);
lean_ctor_set(v___x_693_, 1, v_k_686_);
lean_ctor_set(v___x_693_, 0, v___x_805_);
v___x_809_ = v___x_693_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_k_686_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_v_687_);
lean_ctor_set(v_reuseFailAlloc_810_, 3, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_810_, 4, v_r_689_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
else
{
lean_object* v_k_812_; lean_object* v_v_813_; lean_object* v___x_815_; 
v_k_812_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_k_812_);
v_v_813_ = lean_ctor_get(v___x_695_, 1);
lean_inc(v_v_813_);
lean_dec_ref(v___x_695_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 3, v_r_689_);
v___x_815_ = v___x_769_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_size_685_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_k_686_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_v_687_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v_r_689_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_r_689_);
v___x_815_ = v_reuseFailAlloc_820_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_unsigned_to_nat(2u);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 4, v___x_815_);
lean_ctor_set(v___x_693_, 3, v_r_689_);
lean_ctor_set(v___x_693_, 2, v_v_813_);
lean_ctor_set(v___x_693_, 1, v_k_812_);
lean_ctor_set(v___x_693_, 0, v___x_816_);
v___x_818_ = v___x_693_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_k_812_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_v_813_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_r_689_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v___x_815_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
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
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_985_; 
lean_inc(v_r_689_);
lean_inc(v_v_687_);
lean_inc(v_k_686_);
v_isSharedCheck_985_ = !lean_is_exclusive(v_r_501_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; 
v_unused_986_ = lean_ctor_get(v_r_501_, 4);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_r_501_, 3);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_r_501_, 2);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_r_501_, 1);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_r_501_, 0);
lean_dec(v_unused_990_);
v___x_834_ = v_r_501_;
v_isShared_835_ = v_isSharedCheck_985_;
goto v_resetjp_833_;
}
else
{
lean_dec(v_r_501_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_985_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v_tree_837_; 
v___x_836_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_686_, v_v_687_, v_l_688_, v_r_689_);
v_tree_837_ = lean_ctor_get(v___x_836_, 2);
lean_inc(v_tree_837_);
if (lean_obj_tag(v_tree_837_) == 0)
{
lean_object* v_k_838_; lean_object* v_v_839_; lean_object* v_size_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v_k_838_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_k_838_);
v_v_839_ = lean_ctor_get(v___x_836_, 1);
lean_inc(v_v_839_);
lean_dec_ref(v___x_836_);
v_size_840_ = lean_ctor_get(v_tree_837_, 0);
v___x_841_ = lean_unsigned_to_nat(3u);
v___x_842_ = lean_nat_mul(v___x_841_, v_size_840_);
v___x_843_ = lean_nat_dec_lt(v___x_842_, v_size_680_);
lean_dec(v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
lean_dec(v_r_684_);
v___x_844_ = lean_nat_add(v___x_690_, v_size_680_);
v___x_845_ = lean_nat_add(v___x_844_, v_size_840_);
lean_dec(v___x_844_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 4, v_tree_837_);
lean_ctor_set(v___x_834_, 3, v_l_500_);
lean_ctor_set(v___x_834_, 2, v_v_839_);
lean_ctor_set(v___x_834_, 1, v_k_838_);
lean_ctor_set(v___x_834_, 0, v___x_845_);
v___x_847_ = v___x_834_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_k_838_);
lean_ctor_set(v_reuseFailAlloc_848_, 2, v_v_839_);
lean_ctor_set(v_reuseFailAlloc_848_, 3, v_l_500_);
lean_ctor_set(v_reuseFailAlloc_848_, 4, v_tree_837_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
else
{
lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_914_; 
lean_inc(v_l_683_);
lean_inc(v_v_682_);
lean_inc(v_k_681_);
lean_inc(v_size_680_);
v_isSharedCheck_914_ = !lean_is_exclusive(v_l_500_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; lean_object* v_unused_916_; lean_object* v_unused_917_; lean_object* v_unused_918_; lean_object* v_unused_919_; 
v_unused_915_ = lean_ctor_get(v_l_500_, 4);
lean_dec(v_unused_915_);
v_unused_916_ = lean_ctor_get(v_l_500_, 3);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_l_500_, 2);
lean_dec(v_unused_917_);
v_unused_918_ = lean_ctor_get(v_l_500_, 1);
lean_dec(v_unused_918_);
v_unused_919_ = lean_ctor_get(v_l_500_, 0);
lean_dec(v_unused_919_);
v___x_850_ = v_l_500_;
v_isShared_851_ = v_isSharedCheck_914_;
goto v_resetjp_849_;
}
else
{
lean_dec(v_l_500_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_914_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_size_852_; lean_object* v_size_853_; lean_object* v_k_854_; lean_object* v_v_855_; lean_object* v_l_856_; lean_object* v_r_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_size_852_ = lean_ctor_get(v_l_683_, 0);
v_size_853_ = lean_ctor_get(v_r_684_, 0);
v_k_854_ = lean_ctor_get(v_r_684_, 1);
v_v_855_ = lean_ctor_get(v_r_684_, 2);
v_l_856_ = lean_ctor_get(v_r_684_, 3);
v_r_857_ = lean_ctor_get(v_r_684_, 4);
v___x_858_ = lean_unsigned_to_nat(2u);
v___x_859_ = lean_nat_mul(v___x_858_, v_size_852_);
v___x_860_ = lean_nat_dec_lt(v_size_853_, v___x_859_);
lean_dec(v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_898_; 
lean_inc(v_r_857_);
lean_inc(v_l_856_);
lean_inc(v_v_855_);
lean_inc(v_k_854_);
lean_del_object(v___x_850_);
v_isSharedCheck_898_ = !lean_is_exclusive(v_r_684_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; lean_object* v_unused_900_; lean_object* v_unused_901_; lean_object* v_unused_902_; lean_object* v_unused_903_; 
v_unused_899_ = lean_ctor_get(v_r_684_, 4);
lean_dec(v_unused_899_);
v_unused_900_ = lean_ctor_get(v_r_684_, 3);
lean_dec(v_unused_900_);
v_unused_901_ = lean_ctor_get(v_r_684_, 2);
lean_dec(v_unused_901_);
v_unused_902_ = lean_ctor_get(v_r_684_, 1);
lean_dec(v_unused_902_);
v_unused_903_ = lean_ctor_get(v_r_684_, 0);
lean_dec(v_unused_903_);
v___x_862_ = v_r_684_;
v_isShared_863_ = v_isSharedCheck_898_;
goto v_resetjp_861_;
}
else
{
lean_dec(v_r_684_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_898_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___x_886_; lean_object* v___y_888_; 
v___x_864_ = lean_nat_add(v___x_690_, v_size_680_);
lean_dec(v_size_680_);
v___x_865_ = lean_nat_add(v___x_864_, v_size_840_);
lean_dec(v___x_864_);
v___x_886_ = lean_nat_add(v___x_690_, v_size_852_);
if (lean_obj_tag(v_l_856_) == 0)
{
lean_object* v_size_896_; 
v_size_896_ = lean_ctor_get(v_l_856_, 0);
lean_inc(v_size_896_);
v___y_888_ = v_size_896_;
goto v___jp_887_;
}
else
{
lean_object* v___x_897_; 
v___x_897_ = lean_unsigned_to_nat(0u);
v___y_888_ = v___x_897_;
goto v___jp_887_;
}
v___jp_866_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = lean_nat_add(v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec(v___y_868_);
lean_inc_ref(v_tree_837_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 4, v_tree_837_);
lean_ctor_set(v___x_862_, 3, v_r_857_);
lean_ctor_set(v___x_862_, 2, v_v_839_);
lean_ctor_set(v___x_862_, 1, v_k_838_);
lean_ctor_set(v___x_862_, 0, v___x_870_);
v___x_872_ = v___x_862_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_k_838_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_v_839_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_r_857_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v_tree_837_);
v___x_872_ = v_reuseFailAlloc_885_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_isSharedCheck_879_ = !lean_is_exclusive(v_tree_837_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; lean_object* v_unused_881_; lean_object* v_unused_882_; lean_object* v_unused_883_; lean_object* v_unused_884_; 
v_unused_880_ = lean_ctor_get(v_tree_837_, 4);
lean_dec(v_unused_880_);
v_unused_881_ = lean_ctor_get(v_tree_837_, 3);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v_tree_837_, 2);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_tree_837_, 1);
lean_dec(v_unused_883_);
v_unused_884_ = lean_ctor_get(v_tree_837_, 0);
lean_dec(v_unused_884_);
v___x_874_ = v_tree_837_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_dec(v_tree_837_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 4, v___x_872_);
lean_ctor_set(v___x_874_, 3, v___y_867_);
lean_ctor_set(v___x_874_, 2, v_v_855_);
lean_ctor_set(v___x_874_, 1, v_k_854_);
lean_ctor_set(v___x_874_, 0, v___x_865_);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_k_854_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_v_855_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v___y_867_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v___x_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
v___jp_887_:
{
lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_889_ = lean_nat_add(v___x_886_, v___y_888_);
lean_dec(v___y_888_);
lean_dec(v___x_886_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 4, v_l_856_);
lean_ctor_set(v___x_834_, 3, v_l_683_);
lean_ctor_set(v___x_834_, 2, v_v_682_);
lean_ctor_set(v___x_834_, 1, v_k_681_);
lean_ctor_set(v___x_834_, 0, v___x_889_);
v___x_891_ = v___x_834_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_k_681_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_v_682_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_l_683_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_l_856_);
v___x_891_ = v_reuseFailAlloc_895_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_892_; 
v___x_892_ = lean_nat_add(v___x_690_, v_size_840_);
if (lean_obj_tag(v_r_857_) == 0)
{
lean_object* v_size_893_; 
v_size_893_ = lean_ctor_get(v_r_857_, 0);
lean_inc(v_size_893_);
v___y_867_ = v___x_891_;
v___y_868_ = v___x_892_;
v___y_869_ = v_size_893_;
goto v___jp_866_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v___y_867_ = v___x_891_;
v___y_868_ = v___x_892_;
v___y_869_ = v___x_894_;
goto v___jp_866_;
}
}
}
}
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_904_ = lean_nat_add(v___x_690_, v_size_680_);
lean_dec(v_size_680_);
v___x_905_ = lean_nat_add(v___x_904_, v_size_840_);
lean_dec(v___x_904_);
v___x_906_ = lean_nat_add(v___x_690_, v_size_840_);
v___x_907_ = lean_nat_add(v___x_906_, v_size_853_);
lean_dec(v___x_906_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 4, v_tree_837_);
lean_ctor_set(v___x_834_, 3, v_r_684_);
lean_ctor_set(v___x_834_, 2, v_v_839_);
lean_ctor_set(v___x_834_, 1, v_k_838_);
lean_ctor_set(v___x_834_, 0, v___x_907_);
v___x_909_ = v___x_834_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_k_838_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_v_839_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_r_684_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_tree_837_);
v___x_909_ = v_reuseFailAlloc_913_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_911_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 4, v___x_909_);
lean_ctor_set(v___x_850_, 0, v___x_905_);
v___x_911_ = v___x_850_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_k_681_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_v_682_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v_l_683_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_683_) == 0)
{
lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_943_; 
lean_inc_ref(v_l_683_);
lean_inc(v_v_682_);
lean_inc(v_k_681_);
lean_inc(v_size_680_);
v_isSharedCheck_943_ = !lean_is_exclusive(v_l_500_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; lean_object* v_unused_945_; lean_object* v_unused_946_; lean_object* v_unused_947_; lean_object* v_unused_948_; 
v_unused_944_ = lean_ctor_get(v_l_500_, 4);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_l_500_, 3);
lean_dec(v_unused_945_);
v_unused_946_ = lean_ctor_get(v_l_500_, 2);
lean_dec(v_unused_946_);
v_unused_947_ = lean_ctor_get(v_l_500_, 1);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_l_500_, 0);
lean_dec(v_unused_948_);
v___x_921_ = v_l_500_;
v_isShared_922_ = v_isSharedCheck_943_;
goto v_resetjp_920_;
}
else
{
lean_dec(v_l_500_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_943_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
if (lean_obj_tag(v_r_684_) == 0)
{
lean_object* v_k_923_; lean_object* v_v_924_; lean_object* v_size_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v_k_923_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_k_923_);
v_v_924_ = lean_ctor_get(v___x_836_, 1);
lean_inc(v_v_924_);
lean_dec_ref(v___x_836_);
v_size_925_ = lean_ctor_get(v_r_684_, 0);
v___x_926_ = lean_nat_add(v___x_690_, v_size_680_);
lean_dec(v_size_680_);
v___x_927_ = lean_nat_add(v___x_690_, v_size_925_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 4, v_tree_837_);
lean_ctor_set(v___x_834_, 3, v_r_684_);
lean_ctor_set(v___x_834_, 2, v_v_924_);
lean_ctor_set(v___x_834_, 1, v_k_923_);
lean_ctor_set(v___x_834_, 0, v___x_927_);
v___x_929_ = v___x_834_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_k_923_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_v_924_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_r_684_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v_tree_837_);
v___x_929_ = v_reuseFailAlloc_933_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_931_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 4, v___x_929_);
lean_ctor_set(v___x_921_, 0, v___x_926_);
v___x_931_ = v___x_921_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_k_681_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_v_682_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_l_683_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
else
{
lean_object* v_k_934_; lean_object* v_v_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
lean_dec(v_size_680_);
v_k_934_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_k_934_);
v_v_935_ = lean_ctor_get(v___x_836_, 1);
lean_inc(v_v_935_);
lean_dec_ref(v___x_836_);
v___x_936_ = lean_unsigned_to_nat(3u);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 4, v_r_684_);
lean_ctor_set(v___x_834_, 3, v_r_684_);
lean_ctor_set(v___x_834_, 2, v_v_935_);
lean_ctor_set(v___x_834_, 1, v_k_934_);
lean_ctor_set(v___x_834_, 0, v___x_690_);
v___x_938_ = v___x_834_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_k_934_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_v_935_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_r_684_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_r_684_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 4, v___x_938_);
lean_ctor_set(v___x_921_, 0, v___x_936_);
v___x_940_ = v___x_921_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_681_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_682_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_l_683_);
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
}
}
else
{
if (lean_obj_tag(v_r_684_) == 0)
{
lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_973_; 
lean_inc(v_l_683_);
lean_inc(v_v_682_);
lean_inc(v_k_681_);
v_isSharedCheck_973_ = !lean_is_exclusive(v_l_500_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; lean_object* v_unused_975_; lean_object* v_unused_976_; lean_object* v_unused_977_; lean_object* v_unused_978_; 
v_unused_974_ = lean_ctor_get(v_l_500_, 4);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_l_500_, 3);
lean_dec(v_unused_975_);
v_unused_976_ = lean_ctor_get(v_l_500_, 2);
lean_dec(v_unused_976_);
v_unused_977_ = lean_ctor_get(v_l_500_, 1);
lean_dec(v_unused_977_);
v_unused_978_ = lean_ctor_get(v_l_500_, 0);
lean_dec(v_unused_978_);
v___x_950_ = v_l_500_;
v_isShared_951_ = v_isSharedCheck_973_;
goto v_resetjp_949_;
}
else
{
lean_dec(v_l_500_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_973_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_k_952_; lean_object* v_v_953_; lean_object* v_k_954_; lean_object* v_v_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_969_; 
v_k_952_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_k_952_);
v_v_953_ = lean_ctor_get(v___x_836_, 1);
lean_inc(v_v_953_);
lean_dec_ref(v___x_836_);
v_k_954_ = lean_ctor_get(v_r_684_, 1);
v_v_955_ = lean_ctor_get(v_r_684_, 2);
v_isSharedCheck_969_ = !lean_is_exclusive(v_r_684_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; lean_object* v_unused_971_; lean_object* v_unused_972_; 
v_unused_970_ = lean_ctor_get(v_r_684_, 4);
lean_dec(v_unused_970_);
v_unused_971_ = lean_ctor_get(v_r_684_, 3);
lean_dec(v_unused_971_);
v_unused_972_ = lean_ctor_get(v_r_684_, 0);
lean_dec(v_unused_972_);
v___x_957_ = v_r_684_;
v_isShared_958_ = v_isSharedCheck_969_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_v_955_);
lean_inc(v_k_954_);
lean_dec(v_r_684_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_969_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_unsigned_to_nat(3u);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 4, v_l_683_);
lean_ctor_set(v___x_957_, 3, v_l_683_);
lean_ctor_set(v___x_957_, 2, v_v_682_);
lean_ctor_set(v___x_957_, 1, v_k_681_);
lean_ctor_set(v___x_957_, 0, v___x_690_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_k_681_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_v_682_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v_l_683_);
lean_ctor_set(v_reuseFailAlloc_968_, 4, v_l_683_);
v___x_961_ = v_reuseFailAlloc_968_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_963_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 4, v_l_683_);
lean_ctor_set(v___x_834_, 3, v_l_683_);
lean_ctor_set(v___x_834_, 2, v_v_953_);
lean_ctor_set(v___x_834_, 1, v_k_952_);
lean_ctor_set(v___x_834_, 0, v___x_690_);
v___x_963_ = v___x_834_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_k_952_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_v_953_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_l_683_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_l_683_);
v___x_963_ = v_reuseFailAlloc_967_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_965_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v___x_963_);
lean_ctor_set(v___x_950_, 3, v___x_961_);
lean_ctor_set(v___x_950_, 2, v_v_955_);
lean_ctor_set(v___x_950_, 1, v_k_954_);
lean_ctor_set(v___x_950_, 0, v___x_959_);
v___x_965_ = v___x_950_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_k_954_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_v_955_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
}
else
{
lean_object* v_k_979_; lean_object* v_v_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
v_k_979_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_k_979_);
v_v_980_ = lean_ctor_get(v___x_836_, 1);
lean_inc(v_v_980_);
lean_dec_ref(v___x_836_);
v___x_981_ = lean_unsigned_to_nat(2u);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 4, v_r_684_);
lean_ctor_set(v___x_834_, 3, v_l_500_);
lean_ctor_set(v___x_834_, 2, v_v_980_);
lean_ctor_set(v___x_834_, 1, v_k_979_);
lean_ctor_set(v___x_834_, 0, v___x_981_);
v___x_983_ = v___x_834_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_k_979_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_v_980_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_l_500_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v_r_684_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
}
}
else
{
return v_l_500_;
}
}
else
{
return v_r_501_;
}
}
default: 
{
lean_object* v_impl_991_; lean_object* v___x_992_; 
v_impl_991_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_496_, v_r_501_);
v___x_992_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_991_) == 0)
{
if (lean_obj_tag(v_l_500_) == 0)
{
lean_object* v_size_993_; lean_object* v_size_994_; lean_object* v_k_995_; lean_object* v_v_996_; lean_object* v_l_997_; lean_object* v_r_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v_size_993_ = lean_ctor_get(v_impl_991_, 0);
lean_inc(v_size_993_);
v_size_994_ = lean_ctor_get(v_l_500_, 0);
v_k_995_ = lean_ctor_get(v_l_500_, 1);
v_v_996_ = lean_ctor_get(v_l_500_, 2);
v_l_997_ = lean_ctor_get(v_l_500_, 3);
v_r_998_ = lean_ctor_get(v_l_500_, 4);
lean_inc(v_r_998_);
v___x_999_ = lean_unsigned_to_nat(3u);
v___x_1000_ = lean_nat_mul(v___x_999_, v_size_993_);
v___x_1001_ = lean_nat_dec_lt(v___x_1000_, v_size_994_);
lean_dec(v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec(v_r_998_);
v___x_1002_ = lean_nat_add(v___x_992_, v_size_994_);
v___x_1003_ = lean_nat_add(v___x_1002_, v_size_993_);
lean_dec(v_size_993_);
lean_dec(v___x_1002_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v_impl_991_);
lean_ctor_set(v___x_503_, 0, v___x_1003_);
v___x_1005_ = v___x_503_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v_l_500_);
lean_ctor_set(v_reuseFailAlloc_1006_, 4, v_impl_991_);
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
lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1072_; 
lean_inc(v_l_997_);
lean_inc(v_v_996_);
lean_inc(v_k_995_);
lean_inc(v_size_994_);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_l_500_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; lean_object* v_unused_1074_; lean_object* v_unused_1075_; lean_object* v_unused_1076_; lean_object* v_unused_1077_; 
v_unused_1073_ = lean_ctor_get(v_l_500_, 4);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v_l_500_, 3);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_l_500_, 2);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_l_500_, 1);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_l_500_, 0);
lean_dec(v_unused_1077_);
v___x_1008_ = v_l_500_;
v_isShared_1009_ = v_isSharedCheck_1072_;
goto v_resetjp_1007_;
}
else
{
lean_dec(v_l_500_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1072_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_size_1010_; lean_object* v_size_1011_; lean_object* v_k_1012_; lean_object* v_v_1013_; lean_object* v_l_1014_; lean_object* v_r_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_size_1010_ = lean_ctor_get(v_l_997_, 0);
v_size_1011_ = lean_ctor_get(v_r_998_, 0);
v_k_1012_ = lean_ctor_get(v_r_998_, 1);
v_v_1013_ = lean_ctor_get(v_r_998_, 2);
v_l_1014_ = lean_ctor_get(v_r_998_, 3);
v_r_1015_ = lean_ctor_get(v_r_998_, 4);
v___x_1016_ = lean_unsigned_to_nat(2u);
v___x_1017_ = lean_nat_mul(v___x_1016_, v_size_1010_);
v___x_1018_ = lean_nat_dec_lt(v_size_1011_, v___x_1017_);
lean_dec(v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1047_; 
lean_inc(v_r_1015_);
lean_inc(v_l_1014_);
lean_inc(v_v_1013_);
lean_inc(v_k_1012_);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_r_998_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; lean_object* v_unused_1049_; lean_object* v_unused_1050_; lean_object* v_unused_1051_; lean_object* v_unused_1052_; 
v_unused_1048_ = lean_ctor_get(v_r_998_, 4);
lean_dec(v_unused_1048_);
v_unused_1049_ = lean_ctor_get(v_r_998_, 3);
lean_dec(v_unused_1049_);
v_unused_1050_ = lean_ctor_get(v_r_998_, 2);
lean_dec(v_unused_1050_);
v_unused_1051_ = lean_ctor_get(v_r_998_, 1);
lean_dec(v_unused_1051_);
v_unused_1052_ = lean_ctor_get(v_r_998_, 0);
lean_dec(v_unused_1052_);
v___x_1020_ = v_r_998_;
v_isShared_1021_ = v_isSharedCheck_1047_;
goto v_resetjp_1019_;
}
else
{
lean_dec(v_r_998_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1047_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___x_1035_; lean_object* v___y_1037_; 
v___x_1022_ = lean_nat_add(v___x_992_, v_size_994_);
lean_dec(v_size_994_);
v___x_1023_ = lean_nat_add(v___x_1022_, v_size_993_);
lean_dec(v___x_1022_);
v___x_1035_ = lean_nat_add(v___x_992_, v_size_1010_);
if (lean_obj_tag(v_l_1014_) == 0)
{
lean_object* v_size_1045_; 
v_size_1045_ = lean_ctor_get(v_l_1014_, 0);
lean_inc(v_size_1045_);
v___y_1037_ = v_size_1045_;
goto v___jp_1036_;
}
else
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_unsigned_to_nat(0u);
v___y_1037_ = v___x_1046_;
goto v___jp_1036_;
}
v___jp_1024_:
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = lean_nat_add(v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec(v___y_1026_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 4, v_impl_991_);
lean_ctor_set(v___x_1020_, 3, v_r_1015_);
lean_ctor_set(v___x_1020_, 2, v_v_499_);
lean_ctor_set(v___x_1020_, 1, v_k_498_);
lean_ctor_set(v___x_1020_, 0, v___x_1028_);
v___x_1030_ = v___x_1020_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v_r_1015_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v_impl_991_);
v___x_1030_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 4, v___x_1030_);
lean_ctor_set(v___x_1008_, 3, v___y_1025_);
lean_ctor_set(v___x_1008_, 2, v_v_1013_);
lean_ctor_set(v___x_1008_, 1, v_k_1012_);
lean_ctor_set(v___x_1008_, 0, v___x_1023_);
v___x_1032_ = v___x_1008_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_k_1012_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_v_1013_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v___y_1025_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
v___jp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1038_ = lean_nat_add(v___x_1035_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec(v___x_1035_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v_l_1014_);
lean_ctor_set(v___x_503_, 3, v_l_997_);
lean_ctor_set(v___x_503_, 2, v_v_996_);
lean_ctor_set(v___x_503_, 1, v_k_995_);
lean_ctor_set(v___x_503_, 0, v___x_1038_);
v___x_1040_ = v___x_503_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_k_995_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v_v_996_);
lean_ctor_set(v_reuseFailAlloc_1044_, 3, v_l_997_);
lean_ctor_set(v_reuseFailAlloc_1044_, 4, v_l_1014_);
v___x_1040_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_nat_add(v___x_992_, v_size_993_);
lean_dec(v_size_993_);
if (lean_obj_tag(v_r_1015_) == 0)
{
lean_object* v_size_1042_; 
v_size_1042_ = lean_ctor_get(v_r_1015_, 0);
lean_inc(v_size_1042_);
v___y_1025_ = v___x_1040_;
v___y_1026_ = v___x_1041_;
v___y_1027_ = v_size_1042_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_unsigned_to_nat(0u);
v___y_1025_ = v___x_1040_;
v___y_1026_ = v___x_1041_;
v___y_1027_ = v___x_1043_;
goto v___jp_1024_;
}
}
}
}
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
lean_del_object(v___x_503_);
v___x_1053_ = lean_nat_add(v___x_992_, v_size_994_);
lean_dec(v_size_994_);
v___x_1054_ = lean_nat_add(v___x_1053_, v_size_993_);
lean_dec(v___x_1053_);
v___x_1055_ = lean_nat_add(v___x_992_, v_size_993_);
lean_dec(v_size_993_);
v___x_1056_ = lean_nat_add(v___x_1055_, v_size_1011_);
lean_dec(v___x_1055_);
lean_inc_ref(v_impl_991_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 4, v_impl_991_);
lean_ctor_set(v___x_1008_, 3, v_r_998_);
lean_ctor_set(v___x_1008_, 2, v_v_499_);
lean_ctor_set(v___x_1008_, 1, v_k_498_);
lean_ctor_set(v___x_1008_, 0, v___x_1056_);
v___x_1058_ = v___x_1008_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_1071_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_1071_, 3, v_r_998_);
lean_ctor_set(v_reuseFailAlloc_1071_, 4, v_impl_991_);
v___x_1058_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
v_isSharedCheck_1065_ = !lean_is_exclusive(v_impl_991_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; lean_object* v_unused_1067_; lean_object* v_unused_1068_; lean_object* v_unused_1069_; lean_object* v_unused_1070_; 
v_unused_1066_ = lean_ctor_get(v_impl_991_, 4);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_impl_991_, 3);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_impl_991_, 2);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_impl_991_, 1);
lean_dec(v_unused_1069_);
v_unused_1070_ = lean_ctor_get(v_impl_991_, 0);
lean_dec(v_unused_1070_);
v___x_1060_ = v_impl_991_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_dec(v_impl_991_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 4, v___x_1058_);
lean_ctor_set(v___x_1060_, 3, v_l_997_);
lean_ctor_set(v___x_1060_, 2, v_v_996_);
lean_ctor_set(v___x_1060_, 1, v_k_995_);
lean_ctor_set(v___x_1060_, 0, v___x_1054_);
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_k_995_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_v_996_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_l_997_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v___x_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v_size_1078_ = lean_ctor_get(v_impl_991_, 0);
lean_inc(v_size_1078_);
v___x_1079_ = lean_nat_add(v___x_992_, v_size_1078_);
lean_dec(v_size_1078_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v_impl_991_);
lean_ctor_set(v___x_503_, 0, v___x_1079_);
v___x_1081_ = v___x_503_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_l_500_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v_impl_991_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
if (lean_obj_tag(v_l_500_) == 0)
{
lean_object* v_l_1083_; 
v_l_1083_ = lean_ctor_get(v_l_500_, 3);
if (lean_obj_tag(v_l_1083_) == 0)
{
lean_object* v_r_1084_; 
lean_inc_ref(v_l_1083_);
v_r_1084_ = lean_ctor_get(v_l_500_, 4);
lean_inc(v_r_1084_);
if (lean_obj_tag(v_r_1084_) == 0)
{
lean_object* v_size_1085_; lean_object* v_k_1086_; lean_object* v_v_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1100_; 
v_size_1085_ = lean_ctor_get(v_l_500_, 0);
v_k_1086_ = lean_ctor_get(v_l_500_, 1);
v_v_1087_ = lean_ctor_get(v_l_500_, 2);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_l_500_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; lean_object* v_unused_1102_; 
v_unused_1101_ = lean_ctor_get(v_l_500_, 4);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_l_500_, 3);
lean_dec(v_unused_1102_);
v___x_1089_ = v_l_500_;
v_isShared_1090_ = v_isSharedCheck_1100_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_v_1087_);
lean_inc(v_k_1086_);
lean_inc(v_size_1085_);
lean_dec(v_l_500_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1100_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_size_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
v_size_1091_ = lean_ctor_get(v_r_1084_, 0);
v___x_1092_ = lean_nat_add(v___x_992_, v_size_1085_);
lean_dec(v_size_1085_);
v___x_1093_ = lean_nat_add(v___x_992_, v_size_1091_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_impl_991_);
lean_ctor_set(v___x_1089_, 3, v_r_1084_);
lean_ctor_set(v___x_1089_, 2, v_v_499_);
lean_ctor_set(v___x_1089_, 1, v_k_498_);
lean_ctor_set(v___x_1089_, 0, v___x_1093_);
v___x_1095_ = v___x_1089_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_1099_, 3, v_r_1084_);
lean_ctor_set(v_reuseFailAlloc_1099_, 4, v_impl_991_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v___x_1095_);
lean_ctor_set(v___x_503_, 3, v_l_1083_);
lean_ctor_set(v___x_503_, 2, v_v_1087_);
lean_ctor_set(v___x_503_, 1, v_k_1086_);
lean_ctor_set(v___x_503_, 0, v___x_1092_);
v___x_1097_ = v___x_503_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1098_, 3, v_l_1083_);
lean_ctor_set(v_reuseFailAlloc_1098_, 4, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_k_1103_; lean_object* v_v_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1115_; 
v_k_1103_ = lean_ctor_get(v_l_500_, 1);
v_v_1104_ = lean_ctor_get(v_l_500_, 2);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_l_500_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; 
v_unused_1116_ = lean_ctor_get(v_l_500_, 4);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_l_500_, 3);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_l_500_, 0);
lean_dec(v_unused_1118_);
v___x_1106_ = v_l_500_;
v_isShared_1107_ = v_isSharedCheck_1115_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_v_1104_);
lean_inc(v_k_1103_);
lean_dec(v_l_500_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1115_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = lean_unsigned_to_nat(3u);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 3, v_r_1084_);
lean_ctor_set(v___x_1106_, 2, v_v_499_);
lean_ctor_set(v___x_1106_, 1, v_k_498_);
lean_ctor_set(v___x_1106_, 0, v___x_992_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_r_1084_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_r_1084_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1112_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v___x_1110_);
lean_ctor_set(v___x_503_, 3, v_l_1083_);
lean_ctor_set(v___x_503_, 2, v_v_1104_);
lean_ctor_set(v___x_503_, 1, v_k_1103_);
lean_ctor_set(v___x_503_, 0, v___x_1108_);
v___x_1112_ = v___x_503_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_l_1083_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
else
{
lean_object* v_r_1119_; 
v_r_1119_ = lean_ctor_get(v_l_500_, 4);
lean_inc(v_r_1119_);
if (lean_obj_tag(v_r_1119_) == 0)
{
lean_object* v_k_1120_; lean_object* v_v_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1144_; 
lean_inc(v_l_1083_);
v_k_1120_ = lean_ctor_get(v_l_500_, 1);
v_v_1121_ = lean_ctor_get(v_l_500_, 2);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_l_500_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; lean_object* v_unused_1146_; lean_object* v_unused_1147_; 
v_unused_1145_ = lean_ctor_get(v_l_500_, 4);
lean_dec(v_unused_1145_);
v_unused_1146_ = lean_ctor_get(v_l_500_, 3);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_l_500_, 0);
lean_dec(v_unused_1147_);
v___x_1123_ = v_l_500_;
v_isShared_1124_ = v_isSharedCheck_1144_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_v_1121_);
lean_inc(v_k_1120_);
lean_dec(v_l_500_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1144_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_k_1125_; lean_object* v_v_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1140_; 
v_k_1125_ = lean_ctor_get(v_r_1119_, 1);
v_v_1126_ = lean_ctor_get(v_r_1119_, 2);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_r_1119_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; lean_object* v_unused_1142_; lean_object* v_unused_1143_; 
v_unused_1141_ = lean_ctor_get(v_r_1119_, 4);
lean_dec(v_unused_1141_);
v_unused_1142_ = lean_ctor_get(v_r_1119_, 3);
lean_dec(v_unused_1142_);
v_unused_1143_ = lean_ctor_get(v_r_1119_, 0);
lean_dec(v_unused_1143_);
v___x_1128_ = v_r_1119_;
v_isShared_1129_ = v_isSharedCheck_1140_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_v_1126_);
lean_inc(v_k_1125_);
lean_dec(v_r_1119_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1140_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = lean_unsigned_to_nat(3u);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 4, v_l_1083_);
lean_ctor_set(v___x_1128_, 3, v_l_1083_);
lean_ctor_set(v___x_1128_, 2, v_v_1121_);
lean_ctor_set(v___x_1128_, 1, v_k_1120_);
lean_ctor_set(v___x_1128_, 0, v___x_992_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_k_1120_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_v_1121_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v_l_1083_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v_l_1083_);
v___x_1132_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 4, v_l_1083_);
lean_ctor_set(v___x_1123_, 2, v_v_499_);
lean_ctor_set(v___x_1123_, 1, v_k_498_);
lean_ctor_set(v___x_1123_, 0, v___x_992_);
v___x_1134_ = v___x_1123_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_1138_, 3, v_l_1083_);
lean_ctor_set(v_reuseFailAlloc_1138_, 4, v_l_1083_);
v___x_1134_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v___x_1134_);
lean_ctor_set(v___x_503_, 3, v___x_1132_);
lean_ctor_set(v___x_503_, 2, v_v_1126_);
lean_ctor_set(v___x_503_, 1, v_k_1125_);
lean_ctor_set(v___x_503_, 0, v___x_1130_);
v___x_1136_ = v___x_503_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_k_1125_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_v_1126_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = lean_unsigned_to_nat(2u);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v_r_1119_);
lean_ctor_set(v___x_503_, 0, v___x_1148_);
v___x_1150_ = v___x_503_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_l_500_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_r_1119_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
else
{
lean_object* v___x_1153_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v_l_500_);
lean_ctor_set(v___x_503_, 0, v___x_992_);
v___x_1153_ = v___x_503_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v_l_500_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v_l_500_);
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
}
}
}
else
{
return v_t_497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg___boxed(lean_object* v_k_1157_, lean_object* v_t_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1157_, v_t_1158_);
lean_dec(v_k_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString(lean_object* v_declName_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1162_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1163_ = lean_st_ref_take(v___x_1162_);
v___x_1164_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_declName_1160_, v___x_1163_);
v___x_1165_ = lean_st_ref_set(v___x_1162_, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString___boxed(lean_object* v_declName_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_removeBuiltinDocString(v_declName_1167_);
lean_dec(v_declName_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(lean_object* v_00_u03b2_1170_, lean_object* v_k_1171_, lean_object* v_t_1172_, lean_object* v_h_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1171_, v_t_1172_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___boxed(lean_object* v_00_u03b2_1175_, lean_object* v_k_1176_, lean_object* v_t_1177_, lean_object* v_h_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(v_00_u03b2_1175_, v_k_1176_, v_t_1177_, v_h_1178_);
lean_dec(v_k_1176_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings(){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1182_ = lean_st_ref_get(v___x_1181_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings___boxed(lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_getBuiltinVersoDocStrings();
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object* v_docString_1186_, lean_object* v_declName_1187_, lean_object* v_env_1188_){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = l_Lean_docStringExt;
v___x_1190_ = l_String_removeLeadingSpaces(v_docString_1186_);
v___x_1191_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1189_, v_env_1188_, v_declName_1187_, v___x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_1192_, lean_object* v___f_1193_, lean_object* v_____r_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_apply_1(v_modifyEnv_1192_, v___f_1193_);
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__0));
v___x_1198_ = l_Lean_stringToMessageData(v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__2));
v___x_1201_ = l_Lean_stringToMessageData(v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2(lean_object* v_declName_1202_, lean_object* v_modifyEnv_1203_, lean_object* v___f_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_toBind_1207_, lean_object* v___f_1208_, lean_object* v_____do__lift_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1209_, v_declName_1202_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v___x_1211_; 
lean_dec(v___f_1208_);
lean_dec(v_toBind_1207_);
lean_dec_ref(v_inst_1206_);
lean_dec_ref(v_inst_1205_);
lean_dec(v_declName_1202_);
v___x_1211_ = lean_apply_1(v_modifyEnv_1203_, v___f_1204_);
return v___x_1211_;
}
else
{
uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec_ref(v___x_1210_);
lean_dec_ref(v___f_1204_);
lean_dec(v_modifyEnv_1203_);
v___x_1212_ = 0;
v___x_1213_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1214_ = l_Lean_MessageData_ofConstName(v_declName_1202_, v___x_1212_);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = l_Lean_throwError___redArg(v_inst_1205_, v_inst_1206_, v___x_1217_);
v___x_1219_ = lean_apply_4(v_toBind_1207_, lean_box(0), lean_box(0), v___x_1218_, v___f_1208_);
return v___x_1219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1220_, lean_object* v_modifyEnv_1221_, lean_object* v___f_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_toBind_1225_, lean_object* v___f_1226_, lean_object* v_____do__lift_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_addDocStringCore___redArg___lam__2(v_declName_1220_, v_modifyEnv_1221_, v___f_1222_, v_inst_1223_, v_inst_1224_, v_toBind_1225_, v___f_1226_, v_____do__lift_1227_);
lean_dec_ref(v_____do__lift_1227_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg(lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_declName_1232_, lean_object* v_docString_1233_){
_start:
{
lean_object* v_toBind_1234_; lean_object* v_getEnv_1235_; lean_object* v_modifyEnv_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___x_1240_; 
v_toBind_1234_ = lean_ctor_get(v_inst_1229_, 1);
lean_inc_n(v_toBind_1234_, 2);
v_getEnv_1235_ = lean_ctor_get(v_inst_1231_, 0);
lean_inc(v_getEnv_1235_);
v_modifyEnv_1236_ = lean_ctor_get(v_inst_1231_, 1);
lean_inc_n(v_modifyEnv_1236_, 2);
lean_dec_ref(v_inst_1231_);
lean_inc(v_declName_1232_);
v___f_1237_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1237_, 0, v_docString_1233_);
lean_closure_set(v___f_1237_, 1, v_declName_1232_);
lean_inc_ref(v___f_1237_);
v___f_1238_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1238_, 0, v_modifyEnv_1236_);
lean_closure_set(v___f_1238_, 1, v___f_1237_);
v___f_1239_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1239_, 0, v_declName_1232_);
lean_closure_set(v___f_1239_, 1, v_modifyEnv_1236_);
lean_closure_set(v___f_1239_, 2, v___f_1237_);
lean_closure_set(v___f_1239_, 3, v_inst_1229_);
lean_closure_set(v___f_1239_, 4, v_inst_1230_);
lean_closure_set(v___f_1239_, 5, v_toBind_1234_);
lean_closure_set(v___f_1239_, 6, v___f_1238_);
v___x_1240_ = lean_apply_4(v_toBind_1234_, lean_box(0), lean_box(0), v_getEnv_1235_, v___f_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore(lean_object* v_m_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_declName_1246_, lean_object* v_docString_1247_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_addDocStringCore___redArg(v_inst_1242_, v_inst_1243_, v_inst_1244_, v_declName_1246_, v_docString_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___boxed(lean_object* v_m_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_declName_1254_, lean_object* v_docString_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_addDocStringCore(v_m_1249_, v_inst_1250_, v_inst_1251_, v_inst_1252_, v_inst_1253_, v_declName_1254_, v_docString_1255_);
lean_dec(v_inst_1253_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__0(lean_object* v_declName_1258_, lean_object* v_x_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__0___closed__0));
v___x_1261_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_1260_, v_declName_1258_, v_x_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__1(lean_object* v___f_1262_, lean_object* v_env_1263_){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1264_ = l_Lean_docStringExt;
v___x_1265_ = lean_box(2);
v___x_1266_ = lean_box(0);
v___x_1267_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_1264_, v_env_1263_, v___f_1262_, v___x_1265_, v___x_1266_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__3___closed__0));
v___x_1270_ = l_Lean_stringToMessageData(v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3(lean_object* v_declName_1271_, lean_object* v_modifyEnv_1272_, lean_object* v___f_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_toBind_1276_, lean_object* v___f_1277_, lean_object* v_____do__lift_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1278_, v_declName_1271_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v___x_1280_; 
lean_dec(v___f_1277_);
lean_dec(v_toBind_1276_);
lean_dec_ref(v_inst_1275_);
lean_dec_ref(v_inst_1274_);
lean_dec(v_declName_1271_);
v___x_1280_ = lean_apply_1(v_modifyEnv_1272_, v___f_1273_);
return v___x_1280_;
}
else
{
uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec_ref(v___x_1279_);
lean_dec_ref(v___f_1273_);
lean_dec(v_modifyEnv_1272_);
v___x_1281_ = 0;
v___x_1282_ = lean_obj_once(&l_Lean_removeDocStringCore___redArg___lam__3___closed__1, &l_Lean_removeDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1);
v___x_1283_ = l_Lean_MessageData_ofConstName(v_declName_1271_, v___x_1281_);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_throwError___redArg(v_inst_1274_, v_inst_1275_, v___x_1286_);
v___x_1288_ = lean_apply_4(v_toBind_1276_, lean_box(0), lean_box(0), v___x_1287_, v___f_1277_);
return v___x_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_1289_, lean_object* v_modifyEnv_1290_, lean_object* v___f_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_toBind_1294_, lean_object* v___f_1295_, lean_object* v_____do__lift_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_removeDocStringCore___redArg___lam__3(v_declName_1289_, v_modifyEnv_1290_, v___f_1291_, v_inst_1292_, v_inst_1293_, v_toBind_1294_, v___f_1295_, v_____do__lift_1296_);
lean_dec_ref(v_____do__lift_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg(lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_declName_1301_){
_start:
{
lean_object* v_toBind_1302_; lean_object* v_getEnv_1303_; lean_object* v_modifyEnv_1304_; lean_object* v___f_1305_; lean_object* v___f_1306_; lean_object* v___f_1307_; lean_object* v___f_1308_; lean_object* v___x_1309_; 
v_toBind_1302_ = lean_ctor_get(v_inst_1298_, 1);
lean_inc_n(v_toBind_1302_, 2);
v_getEnv_1303_ = lean_ctor_get(v_inst_1300_, 0);
lean_inc(v_getEnv_1303_);
v_modifyEnv_1304_ = lean_ctor_get(v_inst_1300_, 1);
lean_inc_n(v_modifyEnv_1304_, 2);
lean_dec_ref(v_inst_1300_);
lean_inc(v_declName_1301_);
v___f_1305_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1305_, 0, v_declName_1301_);
v___f_1306_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1306_, 0, v___f_1305_);
lean_inc_ref(v___f_1306_);
v___f_1307_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1307_, 0, v_modifyEnv_1304_);
lean_closure_set(v___f_1307_, 1, v___f_1306_);
v___f_1308_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1308_, 0, v_declName_1301_);
lean_closure_set(v___f_1308_, 1, v_modifyEnv_1304_);
lean_closure_set(v___f_1308_, 2, v___f_1306_);
lean_closure_set(v___f_1308_, 3, v_inst_1298_);
lean_closure_set(v___f_1308_, 4, v_inst_1299_);
lean_closure_set(v___f_1308_, 5, v_toBind_1302_);
lean_closure_set(v___f_1308_, 6, v___f_1307_);
v___x_1309_ = lean_apply_4(v_toBind_1302_, lean_box(0), lean_box(0), v_getEnv_1303_, v___f_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore(lean_object* v_m_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_declName_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_removeDocStringCore___redArg(v_inst_1311_, v_inst_1312_, v_inst_1313_, v_declName_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___boxed(lean_object* v_m_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_declName_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_removeDocStringCore(v_m_1317_, v_inst_1318_, v_inst_1319_, v_inst_1320_, v_inst_1321_, v_declName_1322_);
lean_dec(v_inst_1321_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___redArg(lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_declName_1327_, lean_object* v_docString_x3f_1328_){
_start:
{
if (lean_obj_tag(v_docString_x3f_1328_) == 0)
{
lean_object* v_toApplicative_1329_; lean_object* v_toPure_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_toApplicative_1329_ = lean_ctor_get(v_inst_1324_, 0);
lean_inc_ref(v_toApplicative_1329_);
lean_dec(v_declName_1327_);
lean_dec_ref(v_inst_1326_);
lean_dec_ref(v_inst_1325_);
lean_dec_ref(v_inst_1324_);
v_toPure_1330_ = lean_ctor_get(v_toApplicative_1329_, 1);
lean_inc(v_toPure_1330_);
lean_dec_ref(v_toApplicative_1329_);
v___x_1331_ = lean_box(0);
v___x_1332_ = lean_apply_2(v_toPure_1330_, lean_box(0), v___x_1331_);
return v___x_1332_;
}
else
{
lean_object* v_val_1333_; lean_object* v___x_1334_; 
v_val_1333_ = lean_ctor_get(v_docString_x3f_1328_, 0);
lean_inc(v_val_1333_);
lean_dec_ref(v_docString_x3f_1328_);
v___x_1334_ = l_Lean_addDocStringCore___redArg(v_inst_1324_, v_inst_1325_, v_inst_1326_, v_declName_1327_, v_val_1333_);
return v___x_1334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27(lean_object* v_m_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_declName_1340_, lean_object* v_docString_x3f_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_addDocStringCore_x27___redArg(v_inst_1336_, v_inst_1337_, v_inst_1338_, v_declName_1340_, v_docString_x3f_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___boxed(lean_object* v_m_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_declName_1348_, lean_object* v_docString_x3f_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_addDocStringCore_x27(v_m_1343_, v_inst_1344_, v_inst_1345_, v_inst_1346_, v_inst_1347_, v_declName_1348_, v_docString_x3f_1349_);
lean_dec(v_inst_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object* v_declName_1351_, lean_object* v_target_1352_, lean_object* v_env_1353_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1355_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1354_, v_env_1353_, v_declName_1351_, v_target_1352_);
return v___x_1355_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__2___closed__0));
v___x_1358_ = l_Lean_stringToMessageData(v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object* v___x_1359_, lean_object* v_target_1360_, lean_object* v_declName_1361_, lean_object* v___x_1362_, lean_object* v_modifyEnv_1363_, lean_object* v___f_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_toBind_1367_, lean_object* v___f_1368_, lean_object* v_____do__lift_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v_toEnvExtension_1371_; lean_object* v_asyncMode_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1370_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1371_ = lean_ctor_get(v___x_1370_, 0);
v_asyncMode_1372_ = lean_ctor_get(v_toEnvExtension_1371_, 2);
v___x_1373_ = 1;
v___x_1374_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1359_, v___x_1370_, v_____do__lift_1369_, v_target_1360_, v_asyncMode_1372_, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v_declName_1361_);
v___x_1376_ = l_Option_instBEq_beq___redArg(v___x_1362_, v___x_1374_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_dec(v___f_1368_);
lean_dec(v_toBind_1367_);
lean_dec_ref(v_inst_1366_);
lean_dec_ref(v_inst_1365_);
v___x_1377_ = lean_apply_1(v_modifyEnv_1363_, v___f_1364_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec_ref(v___f_1364_);
lean_dec(v_modifyEnv_1363_);
v___x_1378_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__2___closed__1, &l_Lean_addInheritedDocString___redArg___lam__2___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1);
v___x_1379_ = l_Lean_throwError___redArg(v_inst_1365_, v_inst_1366_, v___x_1378_);
v___x_1380_ = lean_apply_4(v_toBind_1367_, lean_box(0), lean_box(0), v___x_1379_, v___f_1368_);
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object* v_toBind_1381_, lean_object* v_getEnv_1382_, lean_object* v___f_1383_, lean_object* v_____r_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_apply_4(v_toBind_1381_, lean_box(0), lean_box(0), v_getEnv_1382_, v___f_1383_);
return v___x_1385_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__0));
v___x_1388_ = l_Lean_stringToMessageData(v___x_1387_);
return v___x_1388_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__2));
v___x_1391_ = l_Lean_stringToMessageData(v___x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object* v___x_1392_, lean_object* v_declName_1393_, lean_object* v_toBind_1394_, lean_object* v_getEnv_1395_, lean_object* v___f_1396_, lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v___f_1399_, lean_object* v_____do__lift_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v_toEnvExtension_1402_; lean_object* v_asyncMode_1403_; uint8_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1401_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1402_ = lean_ctor_get(v___x_1401_, 0);
v_asyncMode_1403_ = lean_ctor_get(v_toEnvExtension_1402_, 2);
v___x_1404_ = 1;
lean_inc(v_declName_1393_);
v___x_1405_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1392_, v___x_1401_, v_____do__lift_1400_, v_declName_1393_, v_asyncMode_1403_, v___x_1404_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v___x_1406_; 
lean_dec(v___f_1399_);
lean_dec_ref(v_inst_1398_);
lean_dec_ref(v_inst_1397_);
lean_dec(v_declName_1393_);
v___x_1406_ = lean_apply_4(v_toBind_1394_, lean_box(0), lean_box(0), v_getEnv_1395_, v___f_1396_);
return v___x_1406_;
}
else
{
lean_object* v___x_1407_; uint8_t v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_dec_ref(v___x_1405_);
lean_dec(v___f_1396_);
lean_dec(v_getEnv_1395_);
v___x_1407_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1408_ = 0;
v___x_1409_ = l_Lean_MessageData_ofConstName(v_declName_1393_, v___x_1408_);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1407_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__3, &l_Lean_addInheritedDocString___redArg___lam__3___closed__3_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = l_Lean_throwError___redArg(v_inst_1397_, v_inst_1398_, v___x_1412_);
v___x_1414_ = lean_apply_4(v_toBind_1394_, lean_box(0), lean_box(0), v___x_1413_, v___f_1399_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object* v_declName_1415_, lean_object* v_toBind_1416_, lean_object* v_getEnv_1417_, lean_object* v___f_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_, lean_object* v___f_1421_, lean_object* v_____do__lift_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1422_, v_declName_1415_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v___x_1424_; 
lean_dec(v___f_1421_);
lean_dec_ref(v_inst_1420_);
lean_dec_ref(v_inst_1419_);
lean_dec(v_declName_1415_);
v___x_1424_ = lean_apply_4(v_toBind_1416_, lean_box(0), lean_box(0), v_getEnv_1417_, v___f_1418_);
return v___x_1424_;
}
else
{
uint8_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v___x_1423_);
lean_dec(v___f_1418_);
lean_dec(v_getEnv_1417_);
v___x_1425_ = 0;
v___x_1426_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1427_ = l_Lean_MessageData_ofConstName(v_declName_1415_, v___x_1425_);
v___x_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1426_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1428_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = l_Lean_throwError___redArg(v_inst_1419_, v_inst_1420_, v___x_1430_);
v___x_1432_ = lean_apply_4(v_toBind_1416_, lean_box(0), lean_box(0), v___x_1431_, v___f_1421_);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object* v_declName_1433_, lean_object* v_toBind_1434_, lean_object* v_getEnv_1435_, lean_object* v___f_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v___f_1439_, lean_object* v_____do__lift_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_addInheritedDocString___redArg___lam__5(v_declName_1433_, v_toBind_1434_, v_getEnv_1435_, v___f_1436_, v_inst_1437_, v_inst_1438_, v___f_1439_, v_____do__lift_1440_);
lean_dec_ref(v_____do__lift_1440_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_inst_1445_, lean_object* v_declName_1446_, lean_object* v_target_1447_){
_start:
{
lean_object* v_toBind_1448_; lean_object* v_getEnv_1449_; lean_object* v_modifyEnv_1450_; lean_object* v___f_1451_; lean_object* v___f_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___f_1455_; lean_object* v___f_1456_; lean_object* v___f_1457_; lean_object* v___f_1458_; lean_object* v___f_1459_; lean_object* v___x_1460_; 
v_toBind_1448_ = lean_ctor_get(v_inst_1443_, 1);
lean_inc_n(v_toBind_1448_, 6);
v_getEnv_1449_ = lean_ctor_get(v_inst_1445_, 0);
lean_inc_n(v_getEnv_1449_, 5);
v_modifyEnv_1450_ = lean_ctor_get(v_inst_1445_, 1);
lean_inc_n(v_modifyEnv_1450_, 2);
lean_dec_ref(v_inst_1445_);
lean_inc(v_target_1447_);
lean_inc_n(v_declName_1446_, 3);
v___f_1451_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1451_, 0, v_declName_1446_);
lean_closure_set(v___f_1451_, 1, v_target_1447_);
lean_inc_ref(v___f_1451_);
v___f_1452_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1452_, 0, v_modifyEnv_1450_);
lean_closure_set(v___f_1452_, 1, v___f_1451_);
v___x_1453_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___closed__0));
v___x_1454_ = lean_box(0);
lean_inc_ref_n(v_inst_1444_, 2);
lean_inc_ref_n(v_inst_1443_, 2);
v___f_1455_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__2), 11, 10);
lean_closure_set(v___f_1455_, 0, v___x_1454_);
lean_closure_set(v___f_1455_, 1, v_target_1447_);
lean_closure_set(v___f_1455_, 2, v_declName_1446_);
lean_closure_set(v___f_1455_, 3, v___x_1453_);
lean_closure_set(v___f_1455_, 4, v_modifyEnv_1450_);
lean_closure_set(v___f_1455_, 5, v___f_1451_);
lean_closure_set(v___f_1455_, 6, v_inst_1443_);
lean_closure_set(v___f_1455_, 7, v_inst_1444_);
lean_closure_set(v___f_1455_, 8, v_toBind_1448_);
lean_closure_set(v___f_1455_, 9, v___f_1452_);
lean_inc_ref(v___f_1455_);
v___f_1456_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1456_, 0, v_toBind_1448_);
lean_closure_set(v___f_1456_, 1, v_getEnv_1449_);
lean_closure_set(v___f_1456_, 2, v___f_1455_);
v___f_1457_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__3), 9, 8);
lean_closure_set(v___f_1457_, 0, v___x_1454_);
lean_closure_set(v___f_1457_, 1, v_declName_1446_);
lean_closure_set(v___f_1457_, 2, v_toBind_1448_);
lean_closure_set(v___f_1457_, 3, v_getEnv_1449_);
lean_closure_set(v___f_1457_, 4, v___f_1455_);
lean_closure_set(v___f_1457_, 5, v_inst_1443_);
lean_closure_set(v___f_1457_, 6, v_inst_1444_);
lean_closure_set(v___f_1457_, 7, v___f_1456_);
lean_inc_ref(v___f_1457_);
v___f_1458_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1458_, 0, v_toBind_1448_);
lean_closure_set(v___f_1458_, 1, v_getEnv_1449_);
lean_closure_set(v___f_1458_, 2, v___f_1457_);
v___f_1459_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1459_, 0, v_declName_1446_);
lean_closure_set(v___f_1459_, 1, v_toBind_1448_);
lean_closure_set(v___f_1459_, 2, v_getEnv_1449_);
lean_closure_set(v___f_1459_, 3, v___f_1457_);
lean_closure_set(v___f_1459_, 4, v_inst_1443_);
lean_closure_set(v___f_1459_, 5, v_inst_1444_);
lean_closure_set(v___f_1459_, 6, v___f_1458_);
v___x_1460_ = lean_apply_4(v_toBind_1448_, lean_box(0), lean_box(0), v_getEnv_1449_, v___f_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object* v_m_1461_, lean_object* v_inst_1462_, lean_object* v_inst_1463_, lean_object* v_inst_1464_, lean_object* v_declName_1465_, lean_object* v_target_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_addInheritedDocString___redArg(v_inst_1462_, v_inst_1463_, v_inst_1464_, v_declName_1465_, v_target_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f(lean_object* v_env_1469_, lean_object* v_declName_1470_, uint8_t v_includeBuiltin_1471_){
_start:
{
lean_object* v___x_1476_; lean_object* v_toEnvExtension_1477_; lean_object* v_asyncMode_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; lean_object* v___x_1481_; 
v___x_1476_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1477_ = lean_ctor_get(v___x_1476_, 0);
v_asyncMode_1478_ = lean_ctor_get(v_toEnvExtension_1477_, 2);
v___x_1479_ = lean_box(0);
v___x_1480_ = 1;
lean_inc(v_declName_1470_);
lean_inc_ref(v_env_1469_);
v___x_1481_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1479_, v___x_1476_, v_env_1469_, v_declName_1470_, v_asyncMode_1478_, v___x_1480_);
if (lean_obj_tag(v___x_1481_) == 1)
{
lean_object* v_val_1482_; 
lean_dec(v_declName_1470_);
v_val_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_val_1482_);
lean_dec_ref(v___x_1481_);
v_declName_1470_ = v_val_1482_;
goto _start;
}
else
{
lean_object* v___x_1484_; lean_object* v_toEnvExtension_1485_; lean_object* v_asyncMode_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec(v___x_1481_);
v___x_1484_ = l_Lean_docStringExt;
v_toEnvExtension_1485_ = lean_ctor_get(v___x_1484_, 0);
v_asyncMode_1486_ = lean_ctor_get(v_toEnvExtension_1485_, 2);
v___x_1487_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
lean_inc(v_declName_1470_);
lean_inc_ref(v_env_1469_);
v___x_1488_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1487_, v___x_1484_, v_env_1469_, v_declName_1470_, v_asyncMode_1486_, v___x_1480_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1489_; lean_object* v_toEnvExtension_1490_; lean_object* v_asyncMode_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1489_ = l_Lean_versoDocStringExt;
v_toEnvExtension_1490_ = lean_ctor_get(v___x_1489_, 0);
v_asyncMode_1491_ = lean_ctor_get(v_toEnvExtension_1490_, 2);
v___x_1492_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default));
lean_inc(v_declName_1470_);
v___x_1493_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1492_, v___x_1489_, v_env_1469_, v_declName_1470_, v_asyncMode_1491_, v___x_1480_);
if (lean_obj_tag(v___x_1493_) == 0)
{
if (v_includeBuiltin_1471_ == 0)
{
lean_dec(v_declName_1470_);
goto v___jp_1473_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1494_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1495_ = lean_st_ref_get(v___x_1494_);
v___x_1496_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1495_, v_declName_1470_);
lean_dec(v___x_1495_);
if (lean_obj_tag(v___x_1496_) == 1)
{
lean_object* v_val_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_declName_1470_);
v_val_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1506_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_val_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1506_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_val_1497_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1501_);
v___x_1503_ = v___x_1499_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
}
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec(v___x_1496_);
v___x_1507_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1508_ = lean_st_ref_get(v___x_1507_);
v___x_1509_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1508_, v_declName_1470_);
lean_dec(v_declName_1470_);
lean_dec(v___x_1508_);
if (lean_obj_tag(v___x_1509_) == 1)
{
lean_object* v_val_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1519_; 
v_val_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1519_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_val_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1519_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_val_1510_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1514_);
v___x_1516_ = v___x_1512_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
return v___x_1517_;
}
}
}
else
{
lean_dec(v___x_1509_);
goto v___jp_1473_;
}
}
}
}
else
{
lean_object* v_val_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1529_; 
lean_dec(v_declName_1470_);
v_val_1520_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1522_ = v___x_1493_;
v_isShared_1523_ = v_isSharedCheck_1529_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_val_1520_);
lean_dec(v___x_1493_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1529_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v_val_1520_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1524_);
v___x_1526_ = v___x_1522_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_val_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_declName_1470_);
lean_dec_ref(v_env_1469_);
v_val_1530_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1532_ = v___x_1488_;
v_isShared_1533_ = v_isSharedCheck_1539_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_val_1530_);
lean_dec(v___x_1488_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1539_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_val_1530_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1534_);
v___x_1536_ = v___x_1532_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
}
}
}
v___jp_1473_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
return v___x_1475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object* v_env_1540_, lean_object* v_declName_1541_, lean_object* v_includeBuiltin_1542_, lean_object* v_a_1543_){
_start:
{
uint8_t v_includeBuiltin_boxed_1544_; lean_object* v_res_1545_; 
v_includeBuiltin_boxed_1544_ = lean_unbox(v_includeBuiltin_1542_);
v_res_1545_ = l_Lean_findInternalDocString_x3f(v_env_1540_, v_declName_1541_, v_includeBuiltin_boxed_1544_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(lean_object* v_s_1546_, lean_object* v_replacement_1547_, lean_object* v_a_1548_, lean_object* v_b_1549_){
_start:
{
lean_object* v_it_1551_; lean_object* v_startPos_1552_; lean_object* v_endPos_1553_; lean_object* v_it_1562_; 
switch(lean_obj_tag(v_a_1548_))
{
case 0:
{
lean_object* v_pos_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1580_; 
v_pos_1568_ = lean_ctor_get(v_a_1548_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_a_1548_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1570_ = v_a_1548_;
v_isShared_1571_ = v_isSharedCheck_1580_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_pos_1568_);
lean_dec(v_a_1548_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1580_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v_startInclusive_1572_; lean_object* v_endExclusive_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v_startInclusive_1572_ = lean_ctor_get(v_s_1546_, 1);
v_endExclusive_1573_ = lean_ctor_get(v_s_1546_, 2);
v___x_1574_ = lean_nat_sub(v_endExclusive_1573_, v_startInclusive_1572_);
v___x_1575_ = lean_nat_dec_eq(v_pos_1568_, v___x_1574_);
lean_dec(v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1577_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set_tag(v___x_1570_, 1);
v___x_1577_ = v___x_1570_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_pos_1568_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
v_it_1562_ = v___x_1577_;
goto v___jp_1561_;
}
}
else
{
lean_object* v___x_1579_; 
lean_del_object(v___x_1570_);
lean_dec(v_pos_1568_);
v___x_1579_ = lean_box(3);
v_it_1562_ = v___x_1579_;
goto v___jp_1561_;
}
}
}
case 1:
{
lean_object* v_pos_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1593_; 
v_pos_1581_ = lean_ctor_get(v_a_1548_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_a_1548_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1583_ = v_a_1548_;
v_isShared_1584_ = v_isSharedCheck_1593_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_pos_1581_);
lean_dec(v_a_1548_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1593_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_str_1585_; lean_object* v_startInclusive_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v_str_1585_ = lean_ctor_get(v_s_1546_, 0);
v_startInclusive_1586_ = lean_ctor_get(v_s_1546_, 1);
v___x_1587_ = lean_nat_add(v_startInclusive_1586_, v_pos_1581_);
v___x_1588_ = lean_string_utf8_next_fast(v_str_1585_, v___x_1587_);
lean_dec(v___x_1587_);
v___x_1589_ = lean_nat_sub(v___x_1588_, v_startInclusive_1586_);
lean_inc(v___x_1589_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set_tag(v___x_1583_, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1589_);
v___x_1591_ = v___x_1583_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
v_it_1551_ = v___x_1591_;
v_startPos_1552_ = v_pos_1581_;
v_endPos_1553_ = v___x_1589_;
goto v___jp_1550_;
}
}
}
case 2:
{
lean_object* v_needle_1594_; lean_object* v_table_1595_; lean_object* v_stackPos_1596_; lean_object* v_needlePos_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1656_; 
v_needle_1594_ = lean_ctor_get(v_a_1548_, 0);
v_table_1595_ = lean_ctor_get(v_a_1548_, 1);
v_stackPos_1596_ = lean_ctor_get(v_a_1548_, 2);
v_needlePos_1597_ = lean_ctor_get(v_a_1548_, 3);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_a_1548_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1599_ = v_a_1548_;
v_isShared_1600_ = v_isSharedCheck_1656_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_needlePos_1597_);
lean_inc(v_stackPos_1596_);
lean_inc(v_table_1595_);
lean_inc(v_needle_1594_);
lean_dec(v_a_1548_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1656_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_str_1601_; lean_object* v_startInclusive_1602_; lean_object* v_endExclusive_1603_; lean_object* v_str_1604_; lean_object* v_startInclusive_1605_; lean_object* v_endExclusive_1606_; lean_object* v_basePos_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v_str_1601_ = lean_ctor_get(v_needle_1594_, 0);
v_startInclusive_1602_ = lean_ctor_get(v_needle_1594_, 1);
v_endExclusive_1603_ = lean_ctor_get(v_needle_1594_, 2);
v_str_1604_ = lean_ctor_get(v_s_1546_, 0);
v_startInclusive_1605_ = lean_ctor_get(v_s_1546_, 1);
v_endExclusive_1606_ = lean_ctor_get(v_s_1546_, 2);
v_basePos_1607_ = lean_nat_sub(v_stackPos_1596_, v_needlePos_1597_);
v___x_1608_ = lean_nat_sub(v_endExclusive_1603_, v_startInclusive_1602_);
v___x_1609_ = lean_nat_add(v_basePos_1607_, v___x_1608_);
v___x_1610_ = lean_nat_sub(v_endExclusive_1606_, v_startInclusive_1605_);
v___x_1611_ = lean_nat_dec_le(v___x_1609_, v___x_1610_);
lean_dec(v___x_1609_);
if (v___x_1611_ == 0)
{
uint8_t v___x_1612_; 
lean_dec(v___x_1608_);
lean_del_object(v___x_1599_);
lean_dec(v_needlePos_1597_);
lean_dec(v_stackPos_1596_);
lean_dec_ref(v_table_1595_);
lean_dec_ref(v_needle_1594_);
v___x_1612_ = lean_nat_dec_lt(v_basePos_1607_, v___x_1610_);
if (v___x_1612_ == 0)
{
lean_dec(v___x_1610_);
lean_dec(v_basePos_1607_);
lean_dec_ref(v_s_1546_);
return v_b_1549_;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = l_String_Slice_pos_x21(v_s_1546_, v_basePos_1607_);
lean_dec(v_basePos_1607_);
v___x_1614_ = lean_box(3);
v_it_1551_ = v___x_1614_;
v_startPos_1552_ = v___x_1613_;
v_endPos_1553_ = v___x_1610_;
goto v___jp_1550_;
}
}
else
{
lean_object* v___x_1615_; uint8_t v_stackByte_1616_; lean_object* v___x_1617_; uint8_t v_patByte_1618_; uint8_t v___x_1619_; 
lean_dec(v___x_1610_);
v___x_1615_ = lean_nat_add(v_startInclusive_1605_, v_stackPos_1596_);
v_stackByte_1616_ = lean_string_get_byte_fast(v_str_1604_, v___x_1615_);
v___x_1617_ = lean_nat_add(v_startInclusive_1602_, v_needlePos_1597_);
v_patByte_1618_ = lean_string_get_byte_fast(v_str_1601_, v___x_1617_);
v___x_1619_ = lean_uint8_dec_eq(v_stackByte_1616_, v_patByte_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
lean_dec(v___x_1608_);
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = lean_nat_dec_eq(v_needlePos_1597_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v_newNeedlePos_1624_; uint8_t v___x_1625_; 
v___x_1622_ = lean_unsigned_to_nat(1u);
v___x_1623_ = lean_nat_sub(v_needlePos_1597_, v___x_1622_);
lean_dec(v_needlePos_1597_);
v_newNeedlePos_1624_ = lean_array_fget_borrowed(v_table_1595_, v___x_1623_);
lean_dec(v___x_1623_);
v___x_1625_ = lean_nat_dec_eq(v_newNeedlePos_1624_, v___x_1620_);
if (v___x_1625_ == 0)
{
lean_object* v_oldBasePos_1626_; lean_object* v___x_1627_; lean_object* v_newBasePos_1628_; lean_object* v___x_1630_; 
lean_inc(v_newNeedlePos_1624_);
v_oldBasePos_1626_ = l_String_Slice_pos_x21(v_s_1546_, v_basePos_1607_);
lean_dec(v_basePos_1607_);
v___x_1627_ = lean_nat_sub(v_stackPos_1596_, v_newNeedlePos_1624_);
v_newBasePos_1628_ = l_String_Slice_pos_x21(v_s_1546_, v___x_1627_);
lean_dec(v___x_1627_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 3, v_newNeedlePos_1624_);
v___x_1630_ = v___x_1599_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_needle_1594_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_table_1595_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_stackPos_1596_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_newNeedlePos_1624_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
v_it_1551_ = v___x_1630_;
v_startPos_1552_ = v_oldBasePos_1626_;
v_endPos_1553_ = v_newBasePos_1628_;
goto v___jp_1550_;
}
}
else
{
lean_object* v_basePos_1632_; lean_object* v_nextStackPos_1633_; lean_object* v___x_1635_; 
v_basePos_1632_ = l_String_Slice_pos_x21(v_s_1546_, v_basePos_1607_);
lean_dec(v_basePos_1607_);
v_nextStackPos_1633_ = l_String_Slice_posGE___redArg(v_s_1546_, v_stackPos_1596_);
lean_inc(v_nextStackPos_1633_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 3, v___x_1620_);
lean_ctor_set(v___x_1599_, 2, v_nextStackPos_1633_);
v___x_1635_ = v___x_1599_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_needle_1594_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_table_1595_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_nextStackPos_1633_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v___x_1620_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
v_it_1551_ = v___x_1635_;
v_startPos_1552_ = v_basePos_1632_;
v_endPos_1553_ = v_nextStackPos_1633_;
goto v___jp_1550_;
}
}
}
else
{
lean_object* v_basePos_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v_nextStackPos_1640_; lean_object* v___x_1642_; 
lean_dec(v_basePos_1607_);
lean_dec(v_needlePos_1597_);
v_basePos_1637_ = l_String_Slice_pos_x21(v_s_1546_, v_stackPos_1596_);
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_nat_add(v_stackPos_1596_, v___x_1638_);
lean_dec(v_stackPos_1596_);
v_nextStackPos_1640_ = l_String_Slice_posGE___redArg(v_s_1546_, v___x_1639_);
lean_inc(v_nextStackPos_1640_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 3, v___x_1620_);
lean_ctor_set(v___x_1599_, 2, v_nextStackPos_1640_);
v___x_1642_ = v___x_1599_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_needle_1594_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_table_1595_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_nextStackPos_1640_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v___x_1620_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
v_it_1551_ = v___x_1642_;
v_startPos_1552_ = v_basePos_1637_;
v_endPos_1553_ = v_nextStackPos_1640_;
goto v___jp_1550_;
}
}
}
else
{
lean_object* v___x_1644_; lean_object* v_nextStackPos_1645_; lean_object* v_nextNeedlePos_1646_; uint8_t v___x_1647_; 
lean_dec(v_basePos_1607_);
v___x_1644_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1645_ = lean_nat_add(v_stackPos_1596_, v___x_1644_);
lean_dec(v_stackPos_1596_);
v_nextNeedlePos_1646_ = lean_nat_add(v_needlePos_1597_, v___x_1644_);
lean_dec(v_needlePos_1597_);
v___x_1647_ = lean_nat_dec_eq(v_nextNeedlePos_1646_, v___x_1608_);
lean_dec(v___x_1608_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1649_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 3, v_nextNeedlePos_1646_);
lean_ctor_set(v___x_1599_, 2, v_nextStackPos_1645_);
v___x_1649_ = v___x_1599_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_needle_1594_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_table_1595_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_nextStackPos_1645_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v_nextNeedlePos_1646_);
v___x_1649_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
v_a_1548_ = v___x_1649_;
goto _start;
}
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
lean_dec(v_nextNeedlePos_1646_);
v___x_1652_ = lean_unsigned_to_nat(0u);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 3, v___x_1652_);
lean_ctor_set(v___x_1599_, 2, v_nextStackPos_1645_);
v___x_1654_ = v___x_1599_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_needle_1594_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_table_1595_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_nextStackPos_1645_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
v_it_1562_ = v___x_1654_;
goto v___jp_1561_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1546_);
return v_b_1549_;
}
}
v___jp_1550_:
{
lean_object* v___x_1554_; lean_object* v_str_1555_; lean_object* v_startInclusive_1556_; lean_object* v_endExclusive_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_inc_ref(v_s_1546_);
v___x_1554_ = l_String_Slice_slice_x21(v_s_1546_, v_startPos_1552_, v_endPos_1553_);
lean_dec(v_endPos_1553_);
lean_dec(v_startPos_1552_);
v_str_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc_ref(v_str_1555_);
v_startInclusive_1556_ = lean_ctor_get(v___x_1554_, 1);
lean_inc(v_startInclusive_1556_);
v_endExclusive_1557_ = lean_ctor_get(v___x_1554_, 2);
lean_inc(v_endExclusive_1557_);
lean_dec_ref(v___x_1554_);
v___x_1558_ = lean_string_utf8_extract(v_str_1555_, v_startInclusive_1556_, v_endExclusive_1557_);
lean_dec(v_endExclusive_1557_);
lean_dec(v_startInclusive_1556_);
lean_dec_ref(v_str_1555_);
v___x_1559_ = lean_string_append(v_b_1549_, v___x_1558_);
lean_dec_ref(v___x_1558_);
v_a_1548_ = v_it_1551_;
v_b_1549_ = v___x_1559_;
goto _start;
}
v___jp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_string_utf8_byte_size(v_replacement_1547_);
v___x_1565_ = lean_string_utf8_extract(v_replacement_1547_, v___x_1563_, v___x_1564_);
v___x_1566_ = lean_string_append(v_b_1549_, v___x_1565_);
lean_dec_ref(v___x_1565_);
v_a_1548_ = v_it_1562_;
v_b_1549_ = v___x_1566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_s_1657_, lean_object* v_replacement_1658_, lean_object* v_a_1659_, lean_object* v_b_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1657_, v_replacement_1658_, v_a_1659_, v_b_1660_);
lean_dec_ref(v_replacement_1658_);
return v_res_1661_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1664_ = lean_string_utf8_byte_size(v___x_1663_);
return v___x_1664_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1665_ = lean_unsigned_to_nat(0u);
v___x_1666_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1667_ = lean_nat_dec_eq(v___x_1666_, v___x_1665_);
return v___x_1667_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1668_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1669_);
lean_ctor_set(v___x_1671_, 2, v___x_1668_);
return v___x_1671_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1673_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1672_);
return v___x_1673_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4);
v___x_1676_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1677_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v___x_1675_);
lean_ctor_set(v___x_1677_, 2, v___x_1674_);
lean_ctor_set(v___x_1677_, 3, v___x_1674_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(lean_object* v_s_1680_, lean_object* v_replacement_1681_){
_start:
{
lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_1683_ = lean_uint8_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5);
v___x_1685_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1680_, v_replacement_1681_, v___x_1684_, v___x_1682_);
return v___x_1685_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__6));
v___x_1687_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1680_, v_replacement_1681_, v___x_1686_, v___x_1682_);
return v___x_1687_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_s_1688_, lean_object* v_replacement_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v_s_1688_, v_replacement_1689_);
lean_dec_ref(v_replacement_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(lean_object* v_as_1698_, size_t v_sz_1699_, size_t v_i_1700_, lean_object* v_b_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
uint8_t v___x_1704_; 
v___x_1704_ = lean_usize_dec_lt(v_i_1700_, v_sz_1699_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v_b_1701_);
lean_ctor_set(v___x_1705_, 1, v___y_1703_);
return v___x_1705_;
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1707_; lean_object* v_snd_1708_; lean_object* v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; 
v_a_1706_ = lean_array_uget_borrowed(v_as_1698_, v_i_1700_);
lean_inc(v_a_1706_);
v___x_1707_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_a_1706_, v___y_1702_, v___y_1703_);
v_snd_1708_ = lean_ctor_get(v___x_1707_, 1);
lean_inc(v_snd_1708_);
lean_dec_ref(v___x_1707_);
v___x_1709_ = lean_box(0);
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1700_, v___x_1710_);
v_i_1700_ = v___x_1711_;
v_b_1701_ = v___x_1709_;
v___y_1703_ = v_snd_1708_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(lean_object* v_x_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
switch(lean_obj_tag(v_x_1726_))
{
case 0:
{
lean_object* v_string_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_string_1729_ = lean_ctor_get(v_x_1726_, 0);
lean_inc_ref(v_string_1729_);
lean_dec_ref(v_x_1726_);
v___x_1730_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1729_);
lean_dec_ref(v_string_1729_);
v___x_1731_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1730_, v_a_1728_);
lean_dec_ref(v___x_1730_);
return v___x_1731_;
}
case 1:
{
lean_object* v_content_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1773_; 
v_content_1732_ = lean_ctor_get(v_x_1726_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_x_1726_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1734_ = v_x_1726_;
v_isShared_1735_ = v_isSharedCheck_1773_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_content_1732_);
lean_dec(v_x_1726_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1773_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set_tag(v___x_1734_, 9);
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_content_1732_);
v___x_1737_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; lean_object* v_snd_1739_; lean_object* v_fst_1740_; lean_object* v_fst_1741_; lean_object* v_snd_1742_; uint8_t v_inEmph_1744_; uint8_t v_inBold_1745_; uint8_t v_inLink_1746_; lean_object* v_linePrefix_1747_; lean_object* v___y_1748_; lean_object* v___x_1759_; uint8_t v_inEmph_1760_; 
v___x_1738_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1737_);
v_snd_1739_ = lean_ctor_get(v___x_1738_, 1);
lean_inc(v_snd_1739_);
v_fst_1740_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_fst_1740_);
lean_dec_ref(v___x_1738_);
v_fst_1741_ = lean_ctor_get(v_snd_1739_, 0);
lean_inc(v_fst_1741_);
v_snd_1742_ = lean_ctor_get(v_snd_1739_, 1);
lean_inc(v_snd_1742_);
lean_dec(v_snd_1739_);
v___x_1759_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_1740_, v_a_1728_);
lean_dec(v_fst_1740_);
v_inEmph_1760_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*1);
if (v_inEmph_1760_ == 0)
{
lean_object* v_snd_1761_; uint8_t v_inBold_1762_; uint8_t v_inLink_1763_; lean_object* v_linePrefix_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v_snd_1767_; 
v_snd_1761_ = lean_ctor_get(v___x_1759_, 1);
lean_inc(v_snd_1761_);
lean_dec_ref(v___x_1759_);
v_inBold_1762_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*1 + 1);
v_inLink_1763_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*1 + 2);
v_linePrefix_1764_ = lean_ctor_get(v_a_1727_, 0);
v___x_1765_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0));
v___x_1766_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1765_, v_snd_1761_);
v_snd_1767_ = lean_ctor_get(v___x_1766_, 1);
lean_inc(v_snd_1767_);
lean_dec_ref(v___x_1766_);
v_inEmph_1744_ = v_inEmph_1760_;
v_inBold_1745_ = v_inBold_1762_;
v_inLink_1746_ = v_inLink_1763_;
v_linePrefix_1747_ = v_linePrefix_1764_;
v___y_1748_ = v_snd_1767_;
goto v___jp_1743_;
}
else
{
lean_object* v_snd_1768_; uint8_t v_inBold_1769_; uint8_t v_inLink_1770_; lean_object* v_linePrefix_1771_; 
v_snd_1768_ = lean_ctor_get(v___x_1759_, 1);
lean_inc(v_snd_1768_);
lean_dec_ref(v___x_1759_);
v_inBold_1769_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*1 + 1);
v_inLink_1770_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*1 + 2);
v_linePrefix_1771_ = lean_ctor_get(v_a_1727_, 0);
v_inEmph_1744_ = v_inEmph_1760_;
v_inBold_1745_ = v_inBold_1769_;
v_inLink_1746_ = v_inLink_1770_;
v_linePrefix_1747_ = v_linePrefix_1771_;
v___y_1748_ = v_snd_1768_;
goto v___jp_1743_;
}
v___jp_1743_:
{
uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = 1;
lean_inc_ref(v_linePrefix_1747_);
v___x_1750_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1750_, 0, v_linePrefix_1747_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*1, v___x_1749_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*1 + 1, v_inBold_1745_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*1 + 2, v_inLink_1746_);
v___x_1751_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_fst_1741_, v___x_1750_, v___y_1748_);
lean_dec_ref(v___x_1750_);
if (v_inEmph_1744_ == 0)
{
lean_object* v_snd_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v_snd_1755_; lean_object* v___x_1756_; 
v_snd_1752_ = lean_ctor_get(v___x_1751_, 1);
lean_inc(v_snd_1752_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0));
v___x_1754_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1753_, v_snd_1752_);
v_snd_1755_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_snd_1755_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1742_, v_snd_1755_);
lean_dec(v_snd_1742_);
return v___x_1756_;
}
else
{
lean_object* v_snd_1757_; lean_object* v___x_1758_; 
v_snd_1757_ = lean_ctor_get(v___x_1751_, 1);
lean_inc(v_snd_1757_);
lean_dec_ref(v___x_1751_);
v___x_1758_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1742_, v_snd_1757_);
lean_dec(v_snd_1742_);
return v___x_1758_;
}
}
}
}
}
case 2:
{
lean_object* v_content_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1812_; 
v_content_1774_ = lean_ctor_get(v_x_1726_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_x_1726_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1776_ = v_x_1726_;
v_isShared_1777_ = v_isSharedCheck_1812_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_content_1774_);
lean_dec(v_x_1726_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1812_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set_tag(v___x_1776_, 9);
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_content_1774_);
v___x_1779_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; lean_object* v_snd_1781_; lean_object* v_fst_1782_; lean_object* v_fst_1783_; lean_object* v_snd_1784_; uint8_t v_inBold_1786_; uint8_t v_inLink_1787_; lean_object* v_linePrefix_1788_; lean_object* v___y_1789_; lean_object* v___x_1800_; uint8_t v_inBold_1801_; 
v___x_1780_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1779_);
v_snd_1781_ = lean_ctor_get(v___x_1780_, 1);
lean_inc(v_snd_1781_);
v_fst_1782_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_fst_1782_);
lean_dec_ref(v___x_1780_);
v_fst_1783_ = lean_ctor_get(v_snd_1781_, 0);
lean_inc(v_fst_1783_);
v_snd_1784_ = lean_ctor_get(v_snd_1781_, 1);
lean_inc(v_snd_1784_);
lean_dec(v_snd_1781_);
v___x_1800_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_1782_, v_a_1728_);
lean_dec(v_fst_1782_);
v_inBold_1801_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*1 + 1);
if (v_inBold_1801_ == 0)
{
lean_object* v_snd_1802_; uint8_t v_inLink_1803_; lean_object* v_linePrefix_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v_snd_1807_; 
v_snd_1802_ = lean_ctor_get(v___x_1800_, 1);
lean_inc(v_snd_1802_);
lean_dec_ref(v___x_1800_);
v_inLink_1803_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*1 + 2);
v_linePrefix_1804_ = lean_ctor_get(v_a_1727_, 0);
v___x_1805_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1));
v___x_1806_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1805_, v_snd_1802_);
v_snd_1807_ = lean_ctor_get(v___x_1806_, 1);
lean_inc(v_snd_1807_);
lean_dec_ref(v___x_1806_);
v_inBold_1786_ = v_inBold_1801_;
v_inLink_1787_ = v_inLink_1803_;
v_linePrefix_1788_ = v_linePrefix_1804_;
v___y_1789_ = v_snd_1807_;
goto v___jp_1785_;
}
else
{
lean_object* v_snd_1808_; uint8_t v_inLink_1809_; lean_object* v_linePrefix_1810_; 
v_snd_1808_ = lean_ctor_get(v___x_1800_, 1);
lean_inc(v_snd_1808_);
lean_dec_ref(v___x_1800_);
v_inLink_1809_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*1 + 2);
v_linePrefix_1810_ = lean_ctor_get(v_a_1727_, 0);
v_inBold_1786_ = v_inBold_1801_;
v_inLink_1787_ = v_inLink_1809_;
v_linePrefix_1788_ = v_linePrefix_1810_;
v___y_1789_ = v_snd_1808_;
goto v___jp_1785_;
}
v___jp_1785_:
{
uint8_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = 1;
lean_inc_ref(v_linePrefix_1788_);
v___x_1791_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1791_, 0, v_linePrefix_1788_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*1, v___x_1790_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*1 + 1, v_inBold_1786_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*1 + 2, v_inLink_1787_);
v___x_1792_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_fst_1783_, v___x_1791_, v___y_1789_);
lean_dec_ref(v___x_1791_);
if (v_inBold_1786_ == 0)
{
lean_object* v_snd_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v_snd_1796_; lean_object* v___x_1797_; 
v_snd_1793_ = lean_ctor_get(v___x_1792_, 1);
lean_inc(v_snd_1793_);
lean_dec_ref(v___x_1792_);
v___x_1794_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1));
v___x_1795_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1794_, v_snd_1793_);
v_snd_1796_ = lean_ctor_get(v___x_1795_, 1);
lean_inc(v_snd_1796_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1784_, v_snd_1796_);
lean_dec(v_snd_1784_);
return v___x_1797_;
}
else
{
lean_object* v_snd_1798_; lean_object* v___x_1799_; 
v_snd_1798_ = lean_ctor_get(v___x_1792_, 1);
lean_inc(v_snd_1798_);
lean_dec_ref(v___x_1792_);
v___x_1799_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1784_, v_snd_1798_);
lean_dec(v_snd_1784_);
return v___x_1799_;
}
}
}
}
}
case 3:
{
lean_object* v_string_1813_; lean_object* v___y_1815_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v_fst_1820_; uint8_t v___x_1821_; 
v_string_1813_ = lean_ctor_get(v_x_1726_, 0);
lean_inc_ref(v_string_1813_);
lean_dec_ref(v_x_1726_);
v___x_1818_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__2));
v___x_1819_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v___x_1818_, v_a_1728_);
v_fst_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_fst_1820_);
v___x_1821_ = lean_unbox(v_fst_1820_);
lean_dec(v_fst_1820_);
if (v___x_1821_ == 0)
{
lean_object* v_snd_1822_; 
v_snd_1822_ = lean_ctor_get(v___x_1819_, 1);
lean_inc(v_snd_1822_);
lean_dec_ref(v___x_1819_);
v___y_1815_ = v_snd_1822_;
goto v___jp_1814_;
}
else
{
lean_object* v_snd_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v_snd_1826_; 
v_snd_1823_ = lean_ctor_get(v___x_1819_, 1);
lean_inc(v_snd_1823_);
lean_dec_ref(v___x_1819_);
v___x_1824_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__3));
v___x_1825_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1824_, v_snd_1823_);
v_snd_1826_ = lean_ctor_get(v___x_1825_, 1);
lean_inc(v_snd_1826_);
lean_dec_ref(v___x_1825_);
v___y_1815_ = v_snd_1826_;
goto v___jp_1814_;
}
v___jp_1814_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1813_);
v___x_1817_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1816_, v___y_1815_);
lean_dec_ref(v___x_1816_);
return v___x_1817_;
}
}
case 4:
{
uint8_t v_mode_1827_; 
v_mode_1827_ = lean_ctor_get_uint8(v_x_1726_, sizeof(void*)*1);
if (v_mode_1827_ == 0)
{
lean_object* v_string_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_string_1828_ = lean_ctor_get(v_x_1726_, 0);
lean_inc_ref(v_string_1828_);
lean_dec_ref(v_x_1726_);
v___x_1829_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__4));
v___x_1830_ = lean_string_append(v___x_1829_, v_string_1828_);
lean_dec_ref(v_string_1828_);
v___x_1831_ = lean_string_append(v___x_1830_, v___x_1829_);
v___x_1832_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1831_, v_a_1728_);
lean_dec_ref(v___x_1831_);
return v___x_1832_;
}
else
{
lean_object* v_string_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_string_1833_ = lean_ctor_get(v_x_1726_, 0);
lean_inc_ref(v_string_1833_);
lean_dec_ref(v_x_1726_);
v___x_1834_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__5));
v___x_1835_ = lean_string_append(v___x_1834_, v_string_1833_);
lean_dec_ref(v_string_1833_);
v___x_1836_ = lean_string_append(v___x_1835_, v___x_1834_);
v___x_1837_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1836_, v_a_1728_);
lean_dec_ref(v___x_1836_);
return v___x_1837_;
}
}
case 5:
{
lean_object* v_string_1838_; lean_object* v_linePrefix_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_string_1838_ = lean_ctor_get(v_x_1726_, 0);
lean_inc_ref(v_string_1838_);
lean_dec_ref(v_x_1726_);
v_linePrefix_1839_ = lean_ctor_get(v_a_1727_, 0);
v___x_1840_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1841_ = lean_string_append(v___x_1840_, v_linePrefix_1839_);
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_string_utf8_byte_size(v_string_1838_);
v___x_1844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1844_, 0, v_string_1838_);
lean_ctor_set(v___x_1844_, 1, v___x_1842_);
lean_ctor_set(v___x_1844_, 2, v___x_1843_);
v___x_1845_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v___x_1844_, v___x_1841_);
lean_dec_ref(v___x_1841_);
v___x_1846_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1845_, v_a_1728_);
lean_dec_ref(v___x_1845_);
return v___x_1846_;
}
case 6:
{
uint8_t v_inLink_1847_; 
v_inLink_1847_ = lean_ctor_get_uint8(v_a_1727_, sizeof(void*)*1 + 2);
if (v_inLink_1847_ == 0)
{
lean_object* v_content_1848_; lean_object* v_url_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v_snd_1852_; lean_object* v___x_1853_; size_t v_sz_1854_; size_t v___x_1855_; lean_object* v___x_1856_; lean_object* v_snd_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v_snd_1860_; lean_object* v___x_1861_; lean_object* v_snd_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_content_1848_ = lean_ctor_get(v_x_1726_, 0);
lean_inc_ref(v_content_1848_);
v_url_1849_ = lean_ctor_get(v_x_1726_, 1);
lean_inc_ref(v_url_1849_);
lean_dec_ref(v_x_1726_);
v___x_1850_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__6));
v___x_1851_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1850_, v_a_1728_);
v_snd_1852_ = lean_ctor_get(v___x_1851_, 1);
lean_inc(v_snd_1852_);
lean_dec_ref(v___x_1851_);
v___x_1853_ = lean_box(0);
v_sz_1854_ = lean_array_size(v_content_1848_);
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1848_, v_sz_1854_, v___x_1855_, v___x_1853_, v_a_1727_, v_snd_1852_);
lean_dec_ref(v_content_1848_);
v_snd_1857_ = lean_ctor_get(v___x_1856_, 1);
lean_inc(v_snd_1857_);
lean_dec_ref(v___x_1856_);
v___x_1858_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7));
v___x_1859_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1858_, v_snd_1857_);
v_snd_1860_ = lean_ctor_get(v___x_1859_, 1);
lean_inc(v_snd_1860_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = l_Lean_Doc_MarkdownM_push___redArg(v_url_1849_, v_snd_1860_);
lean_dec_ref(v_url_1849_);
v_snd_1862_ = lean_ctor_get(v___x_1861_, 1);
lean_inc(v_snd_1862_);
lean_dec_ref(v___x_1861_);
v___x_1863_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_1864_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1863_, v_snd_1862_);
return v___x_1864_;
}
else
{
lean_object* v_content_1865_; lean_object* v___x_1866_; size_t v_sz_1867_; size_t v___x_1868_; lean_object* v___x_1869_; lean_object* v_snd_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_content_1865_ = lean_ctor_get(v_x_1726_, 0);
lean_inc_ref(v_content_1865_);
lean_dec_ref(v_x_1726_);
v___x_1866_ = lean_box(0);
v_sz_1867_ = lean_array_size(v_content_1865_);
v___x_1868_ = ((size_t)0ULL);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1865_, v_sz_1867_, v___x_1868_, v___x_1866_, v_a_1727_, v_a_1728_);
lean_dec_ref(v_content_1865_);
v_snd_1870_ = lean_ctor_get(v___x_1869_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1877_ == 0)
{
lean_object* v_unused_1878_; 
v_unused_1878_ = lean_ctor_get(v___x_1869_, 0);
lean_dec(v_unused_1878_);
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_snd_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1866_);
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_snd_1870_);
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
case 7:
{
lean_object* v_name_1879_; lean_object* v_content_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v_snd_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1925_; 
v_name_1879_ = lean_ctor_get(v_x_1726_, 0);
lean_inc_ref(v_name_1879_);
v_content_1880_ = lean_ctor_get(v_x_1726_, 1);
lean_inc_ref(v_content_1880_);
lean_dec_ref(v_x_1726_);
v___x_1881_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__9));
v___x_1882_ = lean_string_append(v___x_1881_, v_name_1879_);
v___x_1883_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10));
v___x_1884_ = lean_string_append(v___x_1882_, v___x_1883_);
v___x_1885_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1884_, v_a_1728_);
lean_dec_ref(v___x_1884_);
v_snd_1886_ = lean_ctor_get(v___x_1885_, 1);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; 
v_unused_1926_ = lean_ctor_get(v___x_1885_, 0);
lean_dec(v_unused_1926_);
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1925_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_snd_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1925_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v_snd_1891_; lean_object* v___y_1910_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1913_ = lean_array_get_size(v_content_1880_);
v___x_1914_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11));
v___x_1915_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13));
v___x_1916_ = lean_nat_dec_lt(v___x_1912_, v___x_1913_);
if (v___x_1916_ == 0)
{
lean_dec_ref(v_content_1880_);
v_snd_1891_ = v___x_1915_;
goto v___jp_1890_;
}
else
{
lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1917_ = lean_box(0);
v___x_1918_ = lean_nat_dec_le(v___x_1913_, v___x_1913_);
if (v___x_1918_ == 0)
{
if (v___x_1916_ == 0)
{
lean_dec_ref(v_content_1880_);
v_snd_1891_ = v___x_1915_;
goto v___jp_1890_;
}
else
{
size_t v___x_1919_; size_t v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = ((size_t)0ULL);
v___x_1920_ = lean_usize_of_nat(v___x_1913_);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1880_, v___x_1919_, v___x_1920_, v___x_1917_, v___x_1914_, v___x_1915_);
lean_dec_ref(v_content_1880_);
v___y_1910_ = v___x_1921_;
goto v___jp_1909_;
}
}
else
{
size_t v___x_1922_; size_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = ((size_t)0ULL);
v___x_1923_ = lean_usize_of_nat(v___x_1913_);
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1880_, v___x_1922_, v___x_1923_, v___x_1917_, v___x_1914_, v___x_1915_);
lean_dec_ref(v_content_1880_);
v___y_1910_ = v___x_1924_;
goto v___jp_1909_;
}
}
v___jp_1890_:
{
lean_object* v_priorBlocks_1892_; lean_object* v_currentBlock_1893_; lean_object* v_footnotes_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1908_; 
v_priorBlocks_1892_ = lean_ctor_get(v_snd_1886_, 0);
v_currentBlock_1893_ = lean_ctor_get(v_snd_1886_, 1);
v_footnotes_1894_ = lean_ctor_get(v_snd_1886_, 2);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_snd_1886_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1896_ = v_snd_1886_;
v_isShared_1897_ = v_isSharedCheck_1908_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_footnotes_1894_);
lean_inc(v_currentBlock_1893_);
lean_inc(v_priorBlocks_1892_);
lean_dec(v_snd_1886_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1908_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1898_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(v_snd_1891_);
v___x_1899_ = lean_box(0);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v___x_1898_);
lean_ctor_set(v___x_1888_, 0, v_name_1879_);
v___x_1901_ = v___x_1888_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_name_1879_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v___x_1898_);
v___x_1901_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1902_ = lean_array_push(v_footnotes_1894_, v___x_1901_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 2, v___x_1902_);
v___x_1904_ = v___x_1896_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_priorBlocks_1892_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_currentBlock_1893_);
lean_ctor_set(v_reuseFailAlloc_1906_, 2, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1899_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
return v___x_1905_;
}
}
}
}
v___jp_1909_:
{
lean_object* v_snd_1911_; 
v_snd_1911_ = lean_ctor_get(v___y_1910_, 1);
lean_inc(v_snd_1911_);
lean_dec_ref(v___y_1910_);
v_snd_1891_ = v_snd_1911_;
goto v___jp_1890_;
}
}
}
case 8:
{
lean_object* v_alt_1927_; lean_object* v_url_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_alt_1927_ = lean_ctor_get(v_x_1726_, 0);
lean_inc_ref(v_alt_1927_);
v_url_1928_ = lean_ctor_get(v_x_1726_, 1);
lean_inc_ref(v_url_1928_);
lean_dec_ref(v_x_1726_);
v___x_1929_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__14));
v___x_1930_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1927_);
lean_dec_ref(v_alt_1927_);
v___x_1931_ = lean_string_append(v___x_1929_, v___x_1930_);
lean_dec_ref(v___x_1930_);
v___x_1932_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7));
v___x_1933_ = lean_string_append(v___x_1931_, v___x_1932_);
v___x_1934_ = lean_string_append(v___x_1933_, v_url_1928_);
lean_dec_ref(v_url_1928_);
v___x_1935_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_1936_ = lean_string_append(v___x_1934_, v___x_1935_);
v___x_1937_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1936_, v_a_1728_);
lean_dec_ref(v___x_1936_);
return v___x_1937_;
}
case 9:
{
lean_object* v_content_1938_; lean_object* v___x_1939_; size_t v_sz_1940_; size_t v___x_1941_; lean_object* v___x_1942_; lean_object* v_snd_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_content_1938_ = lean_ctor_get(v_x_1726_, 0);
lean_inc_ref(v_content_1938_);
lean_dec_ref(v_x_1726_);
v___x_1939_ = lean_box(0);
v_sz_1940_ = lean_array_size(v_content_1938_);
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1938_, v_sz_1940_, v___x_1941_, v___x_1939_, v_a_1727_, v_a_1728_);
lean_dec_ref(v_content_1938_);
v_snd_1943_ = lean_ctor_get(v___x_1942_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v___x_1942_, 0);
lean_dec(v_unused_1951_);
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_snd_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1939_);
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_snd_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
default: 
{
lean_object* v_content_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v_content_1952_ = lean_ctor_get(v_x_1726_, 1);
lean_inc_ref(v_content_1952_);
lean_dec_ref(v_x_1726_);
v___x_1953_ = lean_unsigned_to_nat(0u);
v___x_1954_ = lean_array_get_size(v_content_1952_);
v___x_1955_ = lean_box(0);
v___x_1956_ = lean_nat_dec_lt(v___x_1953_, v___x_1954_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; 
lean_dec_ref(v_content_1952_);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v_a_1728_);
return v___x_1957_;
}
else
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_nat_dec_le(v___x_1954_, v___x_1954_);
if (v___x_1958_ == 0)
{
if (v___x_1956_ == 0)
{
lean_object* v___x_1959_; 
lean_dec_ref(v_content_1952_);
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1955_);
lean_ctor_set(v___x_1959_, 1, v_a_1728_);
return v___x_1959_;
}
else
{
size_t v___x_1960_; size_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = ((size_t)0ULL);
v___x_1961_ = lean_usize_of_nat(v___x_1954_);
v___x_1962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1952_, v___x_1960_, v___x_1961_, v___x_1955_, v_a_1727_, v_a_1728_);
lean_dec_ref(v_content_1952_);
return v___x_1962_;
}
}
else
{
size_t v___x_1963_; size_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = lean_usize_of_nat(v___x_1954_);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1952_, v___x_1963_, v___x_1964_, v___x_1955_, v_a_1727_, v_a_1728_);
lean_dec_ref(v_content_1952_);
return v___x_1965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(lean_object* v_as_1966_, size_t v_i_1967_, size_t v_stop_1968_, lean_object* v_b_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
uint8_t v___x_1972_; 
v___x_1972_ = lean_usize_dec_eq(v_i_1967_, v_stop_1968_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v_fst_1975_; lean_object* v_snd_1976_; size_t v___x_1977_; size_t v___x_1978_; 
v___x_1973_ = lean_array_uget_borrowed(v_as_1966_, v_i_1967_);
lean_inc(v___x_1973_);
v___x_1974_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_1973_, v___y_1970_, v___y_1971_);
v_fst_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_fst_1975_);
v_snd_1976_ = lean_ctor_get(v___x_1974_, 1);
lean_inc(v_snd_1976_);
lean_dec_ref(v___x_1974_);
v___x_1977_ = ((size_t)1ULL);
v___x_1978_ = lean_usize_add(v_i_1967_, v___x_1977_);
v_i_1967_ = v___x_1978_;
v_b_1969_ = v_fst_1975_;
v___y_1971_ = v_snd_1976_;
goto _start;
}
else
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v_b_1969_);
lean_ctor_set(v___x_1980_, 1, v___y_1971_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1981_, lean_object* v_i_1982_, lean_object* v_stop_1983_, lean_object* v_b_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
size_t v_i_boxed_1987_; size_t v_stop_boxed_1988_; lean_object* v_res_1989_; 
v_i_boxed_1987_ = lean_unbox_usize(v_i_1982_);
lean_dec(v_i_1982_);
v_stop_boxed_1988_ = lean_unbox_usize(v_stop_1983_);
lean_dec(v_stop_1983_);
v_res_1989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_as_1981_, v_i_boxed_1987_, v_stop_boxed_1988_, v_b_1984_, v___y_1985_, v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec_ref(v_as_1981_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2___boxed(lean_object* v_as_1990_, lean_object* v_sz_1991_, lean_object* v_i_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
size_t v_sz_boxed_1996_; size_t v_i_boxed_1997_; lean_object* v_res_1998_; 
v_sz_boxed_1996_ = lean_unbox_usize(v_sz_1991_);
lean_dec(v_sz_1991_);
v_i_boxed_1997_ = lean_unbox_usize(v_i_1992_);
lean_dec(v_i_1992_);
v_res_1998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_as_1990_, v_sz_boxed_1996_, v_i_boxed_1997_, v_b_1993_, v___y_1994_, v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec_ref(v_as_1990_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___boxed(lean_object* v_x_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_x_1999_, v_a_2000_, v_a_2001_);
lean_dec_ref(v_a_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(lean_object* v_as_2005_, size_t v_sz_2006_, size_t v_i_2007_, lean_object* v_b_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
uint8_t v___x_2011_; 
v___x_2011_ = lean_usize_dec_lt(v_i_2007_, v_sz_2006_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_b_2008_);
lean_ctor_set(v___x_2012_, 1, v___y_2010_);
return v___x_2012_;
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2014_; lean_object* v_snd_2015_; lean_object* v___x_2016_; size_t v___x_2017_; size_t v___x_2018_; 
v_a_2013_ = lean_array_uget_borrowed(v_as_2005_, v_i_2007_);
lean_inc(v_a_2013_);
v___x_2014_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v_a_2013_, v___y_2009_, v___y_2010_);
v_snd_2015_ = lean_ctor_get(v___x_2014_, 1);
lean_inc(v_snd_2015_);
lean_dec_ref(v___x_2014_);
v___x_2016_ = lean_box(0);
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_add(v_i_2007_, v___x_2017_);
v_i_2007_ = v___x_2018_;
v_b_2008_ = v___x_2016_;
v___y_2010_ = v_snd_2015_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(lean_object* v_as_2020_, size_t v_sz_2021_, size_t v_i_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_usize_dec_lt(v_i_2022_, v_sz_2021_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_b_2023_);
lean_ctor_set(v___x_2027_, 1, v___y_2025_);
return v___x_2027_;
}
else
{
uint8_t v_inEmph_2028_; uint8_t v_inBold_2029_; uint8_t v_inLink_2030_; lean_object* v_linePrefix_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v_snd_2035_; lean_object* v___x_2036_; lean_object* v_a_2037_; size_t v_sz_2038_; size_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v_snd_2044_; size_t v___x_2045_; size_t v___x_2046_; 
v_inEmph_2028_ = lean_ctor_get_uint8(v___y_2024_, sizeof(void*)*1);
v_inBold_2029_ = lean_ctor_get_uint8(v___y_2024_, sizeof(void*)*1 + 1);
v_inLink_2030_ = lean_ctor_get_uint8(v___y_2024_, sizeof(void*)*1 + 2);
v_linePrefix_2031_ = lean_ctor_get(v___y_2024_, 0);
v___x_2032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0));
lean_inc_ref_n(v_linePrefix_2031_, 2);
v___x_2033_ = lean_string_append(v_linePrefix_2031_, v___x_2032_);
v___x_2034_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2033_, v___y_2025_);
lean_dec_ref(v___x_2033_);
v_snd_2035_ = lean_ctor_get(v___x_2034_, 1);
lean_inc(v_snd_2035_);
lean_dec_ref(v___x_2034_);
v___x_2036_ = lean_box(0);
v_a_2037_ = lean_array_uget_borrowed(v_as_2020_, v_i_2022_);
v_sz_2038_ = lean_array_size(v_a_2037_);
v___x_2039_ = ((size_t)0ULL);
v___x_2040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
v___x_2041_ = lean_string_append(v_linePrefix_2031_, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*1, v_inEmph_2028_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*1 + 1, v_inBold_2029_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*1 + 2, v_inLink_2030_);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_a_2037_, v_sz_2038_, v___x_2039_, v___x_2036_, v___x_2042_, v_snd_2035_);
lean_dec_ref(v___x_2042_);
v_snd_2044_ = lean_ctor_get(v___x_2043_, 1);
lean_inc(v_snd_2044_);
lean_dec_ref(v___x_2043_);
v___x_2045_ = ((size_t)1ULL);
v___x_2046_ = lean_usize_add(v_i_2022_, v___x_2045_);
v_i_2022_ = v___x_2046_;
v_b_2023_ = v___x_2036_;
v___y_2025_ = v_snd_2044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(lean_object* v_as_2049_, size_t v_sz_2050_, size_t v_i_2051_, lean_object* v_b_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
uint8_t v___x_2055_; 
v___x_2055_ = lean_usize_dec_lt(v_i_2051_, v_sz_2050_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v_b_2052_);
lean_ctor_set(v___x_2056_, 1, v___y_2054_);
return v___x_2056_;
}
else
{
uint8_t v_inEmph_2057_; uint8_t v_inBold_2058_; uint8_t v_inLink_2059_; lean_object* v_linePrefix_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v_snd_2066_; lean_object* v_a_2067_; lean_object* v___x_2068_; size_t v_sz_2069_; size_t v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v_snd_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; size_t v___x_2078_; size_t v___x_2079_; 
v_inEmph_2057_ = lean_ctor_get_uint8(v___y_2053_, sizeof(void*)*1);
v_inBold_2058_ = lean_ctor_get_uint8(v___y_2053_, sizeof(void*)*1 + 1);
v_inLink_2059_ = lean_ctor_get_uint8(v___y_2053_, sizeof(void*)*1 + 2);
v_linePrefix_2060_ = lean_ctor_get(v___y_2053_, 0);
lean_inc(v_b_2052_);
v___x_2061_ = l_Nat_reprFast(v_b_2052_);
v___x_2062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0));
v___x_2063_ = lean_string_append(v___x_2061_, v___x_2062_);
lean_inc_ref_n(v_linePrefix_2060_, 2);
v___x_2064_ = lean_string_append(v_linePrefix_2060_, v___x_2063_);
lean_dec_ref(v___x_2063_);
v___x_2065_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2064_, v___y_2054_);
lean_dec_ref(v___x_2064_);
v_snd_2066_ = lean_ctor_get(v___x_2065_, 1);
lean_inc(v_snd_2066_);
lean_dec_ref(v___x_2065_);
v_a_2067_ = lean_array_uget_borrowed(v_as_2049_, v_i_2051_);
v___x_2068_ = lean_box(0);
v_sz_2069_ = lean_array_size(v_a_2067_);
v___x_2070_ = ((size_t)0ULL);
v___x_2071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
v___x_2072_ = lean_string_append(v_linePrefix_2060_, v___x_2071_);
v___x_2073_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*1, v_inEmph_2057_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*1 + 1, v_inBold_2058_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*1 + 2, v_inLink_2059_);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_a_2067_, v_sz_2069_, v___x_2070_, v___x_2068_, v___x_2073_, v_snd_2066_);
lean_dec_ref(v___x_2073_);
v_snd_2075_ = lean_ctor_get(v___x_2074_, 1);
lean_inc(v_snd_2075_);
lean_dec_ref(v___x_2074_);
v___x_2076_ = lean_unsigned_to_nat(1u);
v___x_2077_ = lean_nat_add(v_b_2052_, v___x_2076_);
lean_dec(v_b_2052_);
v___x_2078_ = ((size_t)1ULL);
v___x_2079_ = lean_usize_add(v_i_2051_, v___x_2078_);
v_i_2051_ = v___x_2079_;
v_b_2052_ = v___x_2077_;
v___y_2054_ = v_snd_2075_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(lean_object* v_as_2084_, size_t v_sz_2085_, size_t v_i_2086_, lean_object* v_b_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v___x_2090_; 
v___x_2090_ = lean_usize_dec_lt(v_i_2086_, v_sz_2085_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v_b_2087_);
lean_ctor_set(v___x_2091_, 1, v___y_2089_);
return v___x_2091_;
}
else
{
uint8_t v_inEmph_2092_; uint8_t v_inBold_2093_; uint8_t v_inLink_2094_; lean_object* v_linePrefix_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v_snd_2099_; lean_object* v_a_2100_; lean_object* v_term_2101_; lean_object* v_desc_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v_snd_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v_snd_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_snd_2114_; lean_object* v___x_2115_; lean_object* v_snd_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_snd_2119_; lean_object* v___x_2120_; size_t v___x_2121_; size_t v___x_2122_; 
v_inEmph_2092_ = lean_ctor_get_uint8(v___y_2088_, sizeof(void*)*1);
v_inBold_2093_ = lean_ctor_get_uint8(v___y_2088_, sizeof(void*)*1 + 1);
v_inLink_2094_ = lean_ctor_get_uint8(v___y_2088_, sizeof(void*)*1 + 2);
v_linePrefix_2095_ = lean_ctor_get(v___y_2088_, 0);
v___x_2096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0));
lean_inc_ref_n(v_linePrefix_2095_, 2);
v___x_2097_ = lean_string_append(v_linePrefix_2095_, v___x_2096_);
v___x_2098_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2097_, v___y_2089_);
lean_dec_ref(v___x_2097_);
v_snd_2099_ = lean_ctor_get(v___x_2098_, 1);
lean_inc(v_snd_2099_);
lean_dec_ref(v___x_2098_);
v_a_2100_ = lean_array_uget_borrowed(v_as_2084_, v_i_2086_);
v_term_2101_ = lean_ctor_get(v_a_2100_, 0);
v_desc_2102_ = lean_ctor_get(v_a_2100_, 1);
lean_inc_ref(v_term_2101_);
v___x_2103_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2103_, 0, v_term_2101_);
v___x_2104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
v___x_2105_ = lean_string_append(v_linePrefix_2095_, v___x_2104_);
lean_inc_ref(v___x_2105_);
v___x_2106_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set_uint8(v___x_2106_, sizeof(void*)*1, v_inEmph_2092_);
lean_ctor_set_uint8(v___x_2106_, sizeof(void*)*1 + 1, v_inBold_2093_);
lean_ctor_set_uint8(v___x_2106_, sizeof(void*)*1 + 2, v_inLink_2094_);
v___x_2107_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_2103_, v___x_2106_, v_snd_2099_);
v_snd_2108_ = lean_ctor_get(v___x_2107_, 1);
lean_inc(v_snd_2108_);
lean_dec_ref(v___x_2107_);
v___x_2109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__1));
v___x_2110_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_2109_, v___x_2106_, v_snd_2108_);
v_snd_2111_ = lean_ctor_get(v___x_2110_, 1);
lean_inc(v_snd_2111_);
lean_dec_ref(v___x_2110_);
v___x_2112_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2113_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2112_, v_snd_2111_);
v_snd_2114_ = lean_ctor_get(v___x_2113_, 1);
lean_inc(v_snd_2114_);
lean_dec_ref(v___x_2113_);
v___x_2115_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2105_, v_snd_2114_);
lean_dec_ref(v___x_2105_);
v_snd_2116_ = lean_ctor_get(v___x_2115_, 1);
lean_inc(v_snd_2116_);
lean_dec_ref(v___x_2115_);
lean_inc_ref(v_desc_2102_);
v___x_2117_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2117_, 0, v_desc_2102_);
v___x_2118_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v___x_2117_, v___x_2106_, v_snd_2116_);
lean_dec_ref(v___x_2106_);
v_snd_2119_ = lean_ctor_get(v___x_2118_, 1);
lean_inc(v_snd_2119_);
lean_dec_ref(v___x_2118_);
v___x_2120_ = lean_box(0);
v___x_2121_ = ((size_t)1ULL);
v___x_2122_ = lean_usize_add(v_i_2086_, v___x_2121_);
v_i_2086_ = v___x_2122_;
v_b_2087_ = v___x_2120_;
v___y_2089_ = v_snd_2119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(lean_object* v_x_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
switch(lean_obj_tag(v_x_2125_))
{
case 0:
{
lean_object* v_contents_2128_; lean_object* v___x_2129_; size_t v_sz_2130_; size_t v___x_2131_; lean_object* v___x_2132_; lean_object* v_snd_2133_; lean_object* v___x_2134_; 
v_contents_2128_ = lean_ctor_get(v_x_2125_, 0);
lean_inc_ref(v_contents_2128_);
lean_dec_ref(v_x_2125_);
v___x_2129_ = lean_box(0);
v_sz_2130_ = lean_array_size(v_contents_2128_);
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_contents_2128_, v_sz_2130_, v___x_2131_, v___x_2129_, v_a_2126_, v_a_2127_);
lean_dec_ref(v_contents_2128_);
v_snd_2133_ = lean_ctor_get(v___x_2132_, 1);
lean_inc(v_snd_2133_);
lean_dec_ref(v___x_2132_);
v___x_2134_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2133_);
return v___x_2134_;
}
case 1:
{
lean_object* v_content_2135_; lean_object* v___y_2137_; lean_object* v___y_2138_; uint8_t v___y_2146_; lean_object* v_currentBlock_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v_content_2135_ = lean_ctor_get(v_x_2125_, 0);
lean_inc_ref(v_content_2135_);
lean_dec_ref(v_x_2125_);
v_currentBlock_2150_ = lean_ctor_get(v_a_2127_, 1);
v___x_2151_ = lean_string_utf8_byte_size(v_currentBlock_2150_);
v___x_2152_ = lean_unsigned_to_nat(0u);
v___x_2153_ = lean_nat_dec_eq(v___x_2151_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2154_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2155_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_2156_ = lean_nat_dec_le(v___x_2155_, v___x_2151_);
if (v___x_2156_ == 0)
{
v___y_2146_ = v___x_2153_;
goto v___jp_2145_;
}
else
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = lean_nat_sub(v___x_2151_, v___x_2155_);
v___x_2158_ = lean_string_memcmp(v_currentBlock_2150_, v___x_2154_, v___x_2157_, v___x_2152_, v___x_2155_);
lean_dec(v___x_2157_);
v___y_2146_ = v___x_2158_;
goto v___jp_2145_;
}
}
else
{
v___y_2146_ = v___x_2153_;
goto v___jp_2145_;
}
v___jp_2136_:
{
lean_object* v_linePrefix_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v_snd_2143_; lean_object* v___x_2144_; 
v_linePrefix_2139_ = lean_ctor_get(v___y_2137_, 0);
v___x_2140_ = lean_string_length(v_linePrefix_2139_);
v___x_2141_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v___x_2140_, v_content_2135_);
lean_dec_ref(v_content_2135_);
v___x_2142_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2141_, v___y_2138_);
lean_dec_ref(v___x_2141_);
v_snd_2143_ = lean_ctor_get(v___x_2142_, 1);
lean_inc(v_snd_2143_);
lean_dec_ref(v___x_2142_);
v___x_2144_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2143_);
return v___x_2144_;
}
v___jp_2145_:
{
if (v___y_2146_ == 0)
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v_snd_2149_; 
v___x_2147_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2148_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2147_, v_a_2127_);
v_snd_2149_ = lean_ctor_get(v___x_2148_, 1);
lean_inc(v_snd_2149_);
lean_dec_ref(v___x_2148_);
v___y_2137_ = v_a_2126_;
v___y_2138_ = v_snd_2149_;
goto v___jp_2136_;
}
else
{
v___y_2137_ = v_a_2126_;
v___y_2138_ = v_a_2127_;
goto v___jp_2136_;
}
}
}
case 2:
{
lean_object* v_items_2159_; lean_object* v___x_2160_; size_t v_sz_2161_; size_t v___x_2162_; lean_object* v___x_2163_; lean_object* v_snd_2164_; lean_object* v___x_2165_; 
v_items_2159_ = lean_ctor_get(v_x_2125_, 0);
lean_inc_ref(v_items_2159_);
lean_dec_ref(v_x_2125_);
v___x_2160_ = lean_box(0);
v_sz_2161_ = lean_array_size(v_items_2159_);
v___x_2162_ = ((size_t)0ULL);
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_items_2159_, v_sz_2161_, v___x_2162_, v___x_2160_, v_a_2126_, v_a_2127_);
lean_dec_ref(v_items_2159_);
v_snd_2164_ = lean_ctor_get(v___x_2163_, 1);
lean_inc(v_snd_2164_);
lean_dec_ref(v___x_2163_);
v___x_2165_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2164_);
return v___x_2165_;
}
case 3:
{
lean_object* v_start_2166_; lean_object* v_items_2167_; lean_object* v___y_2169_; lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v_start_2166_ = lean_ctor_get(v_x_2125_, 0);
lean_inc(v_start_2166_);
v_items_2167_ = lean_ctor_get(v_x_2125_, 1);
lean_inc_ref(v_items_2167_);
lean_dec_ref(v_x_2125_);
v___x_2175_ = lean_unsigned_to_nat(1u);
v___x_2176_ = l_Int_toNat(v_start_2166_);
lean_dec(v_start_2166_);
v___x_2177_ = lean_nat_dec_le(v___x_2175_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_dec(v___x_2176_);
v___y_2169_ = v___x_2175_;
goto v___jp_2168_;
}
else
{
v___y_2169_ = v___x_2176_;
goto v___jp_2168_;
}
v___jp_2168_:
{
size_t v_sz_2170_; size_t v___x_2171_; lean_object* v___x_2172_; lean_object* v_snd_2173_; lean_object* v___x_2174_; 
v_sz_2170_ = lean_array_size(v_items_2167_);
v___x_2171_ = ((size_t)0ULL);
v___x_2172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_items_2167_, v_sz_2170_, v___x_2171_, v___y_2169_, v_a_2126_, v_a_2127_);
lean_dec_ref(v_items_2167_);
v_snd_2173_ = lean_ctor_get(v___x_2172_, 1);
lean_inc(v_snd_2173_);
lean_dec_ref(v___x_2172_);
v___x_2174_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2173_);
return v___x_2174_;
}
}
case 4:
{
lean_object* v_items_2178_; lean_object* v___x_2179_; size_t v_sz_2180_; size_t v___x_2181_; lean_object* v___x_2182_; lean_object* v_snd_2183_; lean_object* v___x_2184_; 
v_items_2178_ = lean_ctor_get(v_x_2125_, 0);
lean_inc_ref(v_items_2178_);
lean_dec_ref(v_x_2125_);
v___x_2179_ = lean_box(0);
v_sz_2180_ = lean_array_size(v_items_2178_);
v___x_2181_ = ((size_t)0ULL);
v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_items_2178_, v_sz_2180_, v___x_2181_, v___x_2179_, v_a_2126_, v_a_2127_);
lean_dec_ref(v_items_2178_);
v_snd_2183_ = lean_ctor_get(v___x_2182_, 1);
lean_inc(v_snd_2183_);
lean_dec_ref(v___x_2182_);
v___x_2184_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2183_);
return v___x_2184_;
}
case 5:
{
lean_object* v_items_2185_; uint8_t v_inEmph_2186_; uint8_t v_inBold_2187_; uint8_t v_inLink_2188_; lean_object* v_linePrefix_2189_; lean_object* v___x_2190_; size_t v_sz_2191_; size_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v_snd_2197_; lean_object* v___x_2198_; 
v_items_2185_ = lean_ctor_get(v_x_2125_, 0);
lean_inc_ref(v_items_2185_);
lean_dec_ref(v_x_2125_);
v_inEmph_2186_ = lean_ctor_get_uint8(v_a_2126_, sizeof(void*)*1);
v_inBold_2187_ = lean_ctor_get_uint8(v_a_2126_, sizeof(void*)*1 + 1);
v_inLink_2188_ = lean_ctor_get_uint8(v_a_2126_, sizeof(void*)*1 + 2);
v_linePrefix_2189_ = lean_ctor_get(v_a_2126_, 0);
v___x_2190_ = lean_box(0);
v_sz_2191_ = lean_array_size(v_items_2185_);
v___x_2192_ = ((size_t)0ULL);
v___x_2193_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0));
lean_inc_ref(v_linePrefix_2189_);
v___x_2194_ = lean_string_append(v_linePrefix_2189_, v___x_2193_);
v___x_2195_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set_uint8(v___x_2195_, sizeof(void*)*1, v_inEmph_2186_);
lean_ctor_set_uint8(v___x_2195_, sizeof(void*)*1 + 1, v_inBold_2187_);
lean_ctor_set_uint8(v___x_2195_, sizeof(void*)*1 + 2, v_inLink_2188_);
v___x_2196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_items_2185_, v_sz_2191_, v___x_2192_, v___x_2190_, v___x_2195_, v_a_2127_);
lean_dec_ref(v___x_2195_);
lean_dec_ref(v_items_2185_);
v_snd_2197_ = lean_ctor_get(v___x_2196_, 1);
lean_inc(v_snd_2197_);
lean_dec_ref(v___x_2196_);
v___x_2198_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2197_);
return v___x_2198_;
}
case 6:
{
lean_object* v_content_2199_; lean_object* v___x_2200_; size_t v_sz_2201_; size_t v___x_2202_; lean_object* v___x_2203_; lean_object* v_snd_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
v_content_2199_ = lean_ctor_get(v_x_2125_, 0);
lean_inc_ref(v_content_2199_);
lean_dec_ref(v_x_2125_);
v___x_2200_ = lean_box(0);
v_sz_2201_ = lean_array_size(v_content_2199_);
v___x_2202_ = ((size_t)0ULL);
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_content_2199_, v_sz_2201_, v___x_2202_, v___x_2200_, v_a_2126_, v_a_2127_);
lean_dec_ref(v_content_2199_);
v_snd_2204_ = lean_ctor_get(v___x_2203_, 1);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2211_ == 0)
{
lean_object* v_unused_2212_; 
v_unused_2212_ = lean_ctor_get(v___x_2203_, 0);
lean_dec(v_unused_2212_);
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_snd_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2200_);
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_snd_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
default: 
{
lean_object* v_content_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2234_; 
v_content_2213_ = lean_ctor_get(v_x_2125_, 1);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_x_2125_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; 
v_unused_2235_ = lean_ctor_get(v_x_2125_, 0);
lean_dec(v_unused_2235_);
v___x_2215_ = v_x_2125_;
v_isShared_2216_ = v_isSharedCheck_2234_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_content_2213_);
lean_dec(v_x_2125_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2234_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = lean_array_get_size(v_content_2213_);
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_nat_dec_lt(v___x_2217_, v___x_2218_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2222_; 
lean_dec_ref(v_content_2213_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set_tag(v___x_2215_, 0);
lean_ctor_set(v___x_2215_, 1, v_a_2127_);
lean_ctor_set(v___x_2215_, 0, v___x_2219_);
v___x_2222_ = v___x_2215_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_a_2127_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
else
{
uint8_t v___x_2224_; 
v___x_2224_ = lean_nat_dec_le(v___x_2218_, v___x_2218_);
if (v___x_2224_ == 0)
{
if (v___x_2220_ == 0)
{
lean_object* v___x_2226_; 
lean_dec_ref(v_content_2213_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set_tag(v___x_2215_, 0);
lean_ctor_set(v___x_2215_, 1, v_a_2127_);
lean_ctor_set(v___x_2215_, 0, v___x_2219_);
v___x_2226_ = v___x_2215_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_a_2127_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
else
{
size_t v___x_2228_; size_t v___x_2229_; lean_object* v___x_2230_; 
lean_del_object(v___x_2215_);
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = lean_usize_of_nat(v___x_2218_);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_content_2213_, v___x_2228_, v___x_2229_, v___x_2219_, v_a_2126_, v_a_2127_);
lean_dec_ref(v_content_2213_);
return v___x_2230_;
}
}
else
{
size_t v___x_2231_; size_t v___x_2232_; lean_object* v___x_2233_; 
lean_del_object(v___x_2215_);
v___x_2231_ = ((size_t)0ULL);
v___x_2232_ = lean_usize_of_nat(v___x_2218_);
v___x_2233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_content_2213_, v___x_2231_, v___x_2232_, v___x_2219_, v_a_2126_, v_a_2127_);
lean_dec_ref(v_content_2213_);
return v___x_2233_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(lean_object* v_as_2236_, size_t v_i_2237_, size_t v_stop_2238_, lean_object* v_b_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
uint8_t v___x_2242_; 
v___x_2242_ = lean_usize_dec_eq(v_i_2237_, v_stop_2238_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v_fst_2245_; lean_object* v_snd_2246_; size_t v___x_2247_; size_t v___x_2248_; 
v___x_2243_ = lean_array_uget_borrowed(v_as_2236_, v_i_2237_);
lean_inc(v___x_2243_);
v___x_2244_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v___x_2243_, v___y_2240_, v___y_2241_);
v_fst_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_fst_2245_);
v_snd_2246_ = lean_ctor_get(v___x_2244_, 1);
lean_inc(v_snd_2246_);
lean_dec_ref(v___x_2244_);
v___x_2247_ = ((size_t)1ULL);
v___x_2248_ = lean_usize_add(v_i_2237_, v___x_2247_);
v_i_2237_ = v___x_2248_;
v_b_2239_ = v_fst_2245_;
v___y_2241_ = v_snd_2246_;
goto _start;
}
else
{
lean_object* v___x_2250_; 
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v_b_2239_);
lean_ctor_set(v___x_2250_, 1, v___y_2241_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___boxed(lean_object* v_as_2251_, lean_object* v_i_2252_, lean_object* v_stop_2253_, lean_object* v_b_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
size_t v_i_boxed_2257_; size_t v_stop_boxed_2258_; lean_object* v_res_2259_; 
v_i_boxed_2257_ = lean_unbox_usize(v_i_2252_);
lean_dec(v_i_2252_);
v_stop_boxed_2258_ = lean_unbox_usize(v_stop_2253_);
lean_dec(v_stop_2253_);
v_res_2259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_as_2251_, v_i_boxed_2257_, v_stop_boxed_2258_, v_b_2254_, v___y_2255_, v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec_ref(v_as_2251_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2___boxed(lean_object* v_as_2260_, lean_object* v_sz_2261_, lean_object* v_i_2262_, lean_object* v_b_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
size_t v_sz_boxed_2266_; size_t v_i_boxed_2267_; lean_object* v_res_2268_; 
v_sz_boxed_2266_ = lean_unbox_usize(v_sz_2261_);
lean_dec(v_sz_2261_);
v_i_boxed_2267_ = lean_unbox_usize(v_i_2262_);
lean_dec(v_i_2262_);
v_res_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_as_2260_, v_sz_boxed_2266_, v_i_boxed_2267_, v_b_2263_, v___y_2264_, v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_as_2260_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___boxed(lean_object* v_as_2269_, lean_object* v_sz_2270_, lean_object* v_i_2271_, lean_object* v_b_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
size_t v_sz_boxed_2275_; size_t v_i_boxed_2276_; lean_object* v_res_2277_; 
v_sz_boxed_2275_ = lean_unbox_usize(v_sz_2270_);
lean_dec(v_sz_2270_);
v_i_boxed_2276_ = lean_unbox_usize(v_i_2271_);
lean_dec(v_i_2271_);
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_as_2269_, v_sz_boxed_2275_, v_i_boxed_2276_, v_b_2272_, v___y_2273_, v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v_as_2269_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___boxed(lean_object* v_as_2278_, lean_object* v_sz_2279_, lean_object* v_i_2280_, lean_object* v_b_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
size_t v_sz_boxed_2284_; size_t v_i_boxed_2285_; lean_object* v_res_2286_; 
v_sz_boxed_2284_ = lean_unbox_usize(v_sz_2279_);
lean_dec(v_sz_2279_);
v_i_boxed_2285_ = lean_unbox_usize(v_i_2280_);
lean_dec(v_i_2280_);
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_as_2278_, v_sz_boxed_2284_, v_i_boxed_2285_, v_b_2281_, v___y_2282_, v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec_ref(v_as_2278_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___boxed(lean_object* v_as_2287_, lean_object* v_sz_2288_, lean_object* v_i_2289_, lean_object* v_b_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
size_t v_sz_boxed_2293_; size_t v_i_boxed_2294_; lean_object* v_res_2295_; 
v_sz_boxed_2293_ = lean_unbox_usize(v_sz_2288_);
lean_dec(v_sz_2288_);
v_i_boxed_2294_ = lean_unbox_usize(v_i_2289_);
lean_dec(v_i_2289_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_as_2287_, v_sz_boxed_2293_, v_i_boxed_2294_, v_b_2290_, v___y_2291_, v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec_ref(v_as_2287_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___boxed(lean_object* v_x_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v_x_2296_, v_a_2297_, v_a_2298_);
lean_dec_ref(v_a_2297_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(lean_object* v_x_2300_, lean_object* v_x_2301_){
_start:
{
lean_object* v_zero_2302_; uint8_t v_isZero_2303_; 
v_zero_2302_ = lean_unsigned_to_nat(0u);
v_isZero_2303_ = lean_nat_dec_eq(v_x_2300_, v_zero_2302_);
if (v_isZero_2303_ == 1)
{
lean_dec(v_x_2300_);
return v_x_2301_;
}
else
{
uint32_t v___x_2304_; lean_object* v_one_2305_; lean_object* v_n_2306_; lean_object* v___x_2307_; 
v___x_2304_ = 35;
v_one_2305_ = lean_unsigned_to_nat(1u);
v_n_2306_ = lean_nat_sub(v_x_2300_, v_one_2305_);
lean_dec(v_x_2300_);
v___x_2307_ = lean_string_push(v_x_2301_, v___x_2304_);
v_x_2300_ = v_n_2306_;
v_x_2301_ = v___x_2307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(lean_object* v_level_2310_, lean_object* v_part_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v_snd_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v_snd_2322_; lean_object* v_title_2323_; lean_object* v_content_2324_; lean_object* v_subParts_2325_; lean_object* v___x_2326_; size_t v_sz_2327_; size_t v___x_2328_; lean_object* v___x_2329_; lean_object* v_snd_2330_; lean_object* v___x_2331_; lean_object* v_snd_2332_; size_t v_sz_2333_; lean_object* v___x_2334_; lean_object* v_snd_2335_; lean_object* v___x_2336_; lean_object* v_snd_2337_; size_t v_sz_2338_; lean_object* v___x_2339_; lean_object* v_snd_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
v___x_2314_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_2315_ = lean_unsigned_to_nat(1u);
v___x_2316_ = lean_nat_add(v_level_2310_, v___x_2315_);
lean_inc(v___x_2316_);
v___x_2317_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v___x_2316_, v___x_2314_);
v___x_2318_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2317_, v_a_2313_);
lean_dec_ref(v___x_2317_);
v_snd_2319_ = lean_ctor_get(v___x_2318_, 1);
lean_inc(v_snd_2319_);
lean_dec_ref(v___x_2318_);
v___x_2320_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0));
v___x_2321_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2320_, v_snd_2319_);
v_snd_2322_ = lean_ctor_get(v___x_2321_, 1);
lean_inc(v_snd_2322_);
lean_dec_ref(v___x_2321_);
v_title_2323_ = lean_ctor_get(v_part_2311_, 0);
v_content_2324_ = lean_ctor_get(v_part_2311_, 3);
v_subParts_2325_ = lean_ctor_get(v_part_2311_, 4);
v___x_2326_ = lean_box(0);
v_sz_2327_ = lean_array_size(v_title_2323_);
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_title_2323_, v_sz_2327_, v___x_2328_, v___x_2326_, v_a_2312_, v_snd_2322_);
v_snd_2330_ = lean_ctor_get(v___x_2329_, 1);
lean_inc(v_snd_2330_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2330_);
v_snd_2332_ = lean_ctor_get(v___x_2331_, 1);
lean_inc(v_snd_2332_);
lean_dec_ref(v___x_2331_);
v_sz_2333_ = lean_array_size(v_content_2324_);
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_content_2324_, v_sz_2333_, v___x_2328_, v___x_2326_, v_a_2312_, v_snd_2332_);
v_snd_2335_ = lean_ctor_get(v___x_2334_, 1);
lean_inc(v_snd_2335_);
lean_dec_ref(v___x_2334_);
v___x_2336_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2335_);
v_snd_2337_ = lean_ctor_get(v___x_2336_, 1);
lean_inc(v_snd_2337_);
lean_dec_ref(v___x_2336_);
v_sz_2338_ = lean_array_size(v_subParts_2325_);
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2316_, v_subParts_2325_, v_sz_2338_, v___x_2328_, v___x_2326_, v_a_2312_, v_snd_2337_);
lean_dec(v___x_2316_);
v_snd_2340_ = lean_ctor_get(v___x_2339_, 1);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v___x_2339_, 0);
lean_dec(v_unused_2348_);
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_snd_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2326_);
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_snd_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(lean_object* v___x_2349_, lean_object* v_as_2350_, size_t v_sz_2351_, size_t v_i_2352_, lean_object* v_b_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
uint8_t v___x_2356_; 
v___x_2356_ = lean_usize_dec_lt(v_i_2352_, v_sz_2351_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v_b_2353_);
lean_ctor_set(v___x_2357_, 1, v___y_2355_);
return v___x_2357_;
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2359_; lean_object* v_snd_2360_; lean_object* v___x_2361_; size_t v___x_2362_; size_t v___x_2363_; 
v_a_2358_ = lean_array_uget_borrowed(v_as_2350_, v_i_2352_);
v___x_2359_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v___x_2349_, v_a_2358_, v___y_2354_, v___y_2355_);
v_snd_2360_ = lean_ctor_get(v___x_2359_, 1);
lean_inc(v_snd_2360_);
lean_dec_ref(v___x_2359_);
v___x_2361_ = lean_box(0);
v___x_2362_ = ((size_t)1ULL);
v___x_2363_ = lean_usize_add(v_i_2352_, v___x_2362_);
v_i_2352_ = v___x_2363_;
v_b_2353_ = v___x_2361_;
v___y_2355_ = v_snd_2360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg___boxed(lean_object* v___x_2365_, lean_object* v_as_2366_, lean_object* v_sz_2367_, lean_object* v_i_2368_, lean_object* v_b_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
size_t v_sz_boxed_2372_; size_t v_i_boxed_2373_; lean_object* v_res_2374_; 
v_sz_boxed_2372_ = lean_unbox_usize(v_sz_2367_);
lean_dec(v_sz_2367_);
v_i_boxed_2373_ = lean_unbox_usize(v_i_2368_);
lean_dec(v_i_2368_);
v_res_2374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2365_, v_as_2366_, v_sz_boxed_2372_, v_i_boxed_2373_, v_b_2369_, v___y_2370_, v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec_ref(v_as_2366_);
lean_dec(v___x_2365_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___boxed(lean_object* v_level_2375_, lean_object* v_part_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_level_2375_, v_part_2376_, v_a_2377_, v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec_ref(v_part_2376_);
lean_dec(v_level_2375_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(lean_object* v_as_2380_, size_t v_sz_2381_, size_t v_i_2382_, lean_object* v_b_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
uint8_t v___x_2386_; 
v___x_2386_ = lean_usize_dec_lt(v_i_2382_, v_sz_2381_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v_b_2383_);
lean_ctor_set(v___x_2387_, 1, v___y_2385_);
return v___x_2387_;
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v_snd_2391_; lean_object* v___x_2392_; size_t v___x_2393_; size_t v___x_2394_; 
v_a_2388_ = lean_array_uget_borrowed(v_as_2380_, v_i_2382_);
v___x_2389_ = lean_unsigned_to_nat(0u);
v___x_2390_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v___x_2389_, v_a_2388_, v___y_2384_, v___y_2385_);
v_snd_2391_ = lean_ctor_get(v___x_2390_, 1);
lean_inc(v_snd_2391_);
lean_dec_ref(v___x_2390_);
v___x_2392_ = lean_box(0);
v___x_2393_ = ((size_t)1ULL);
v___x_2394_ = lean_usize_add(v_i_2382_, v___x_2393_);
v_i_2382_ = v___x_2394_;
v_b_2383_ = v___x_2392_;
v___y_2385_ = v_snd_2391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3___boxed(lean_object* v_as_2396_, lean_object* v_sz_2397_, lean_object* v_i_2398_, lean_object* v_b_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
size_t v_sz_boxed_2402_; size_t v_i_boxed_2403_; lean_object* v_res_2404_; 
v_sz_boxed_2402_ = lean_unbox_usize(v_sz_2397_);
lean_dec(v_sz_2397_);
v_i_boxed_2403_ = lean_unbox_usize(v_i_2398_);
lean_dec(v_i_2398_);
v_res_2404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(v_as_2396_, v_sz_boxed_2402_, v_i_boxed_2403_, v_b_2399_, v___y_2400_, v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec_ref(v_as_2396_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(lean_object* v_text_2405_, size_t v_sz_2406_, size_t v___x_2407_, lean_object* v___x_2408_, lean_object* v_subsections_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2412_; lean_object* v_snd_2413_; size_t v_sz_2414_; lean_object* v___x_2415_; lean_object* v_snd_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
v___x_2412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_text_2405_, v_sz_2406_, v___x_2407_, v___x_2408_, v___y_2410_, v___y_2411_);
v_snd_2413_ = lean_ctor_get(v___x_2412_, 1);
lean_inc(v_snd_2413_);
lean_dec_ref(v___x_2412_);
v_sz_2414_ = lean_array_size(v_subsections_2409_);
v___x_2415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(v_subsections_2409_, v_sz_2414_, v___x_2407_, v___x_2408_, v___y_2410_, v_snd_2413_);
v_snd_2416_ = lean_ctor_get(v___x_2415_, 1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2423_ == 0)
{
lean_object* v_unused_2424_; 
v_unused_2424_ = lean_ctor_get(v___x_2415_, 0);
lean_dec(v_unused_2424_);
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_snd_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2408_);
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2408_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_snd_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed(lean_object* v_text_2425_, lean_object* v_sz_2426_, lean_object* v___x_2427_, lean_object* v___x_2428_, lean_object* v_subsections_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
size_t v_sz_boxed_2432_; size_t v___x_10664__boxed_2433_; lean_object* v_res_2434_; 
v_sz_boxed_2432_ = lean_unbox_usize(v_sz_2426_);
lean_dec(v_sz_2426_);
v___x_10664__boxed_2433_ = lean_unbox_usize(v___x_2427_);
lean_dec(v___x_2427_);
v_res_2434_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(v_text_2425_, v_sz_boxed_2432_, v___x_10664__boxed_2433_, v___x_2428_, v_subsections_2429_, v___y_2430_, v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec_ref(v_subsections_2429_);
lean_dec_ref(v_text_2425_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(lean_object* v_a_2437_){
_start:
{
lean_object* v_text_2438_; lean_object* v_subsections_2439_; lean_object* v___x_2440_; size_t v_sz_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___f_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_text_2438_ = lean_ctor_get(v_a_2437_, 0);
lean_inc_ref(v_text_2438_);
v_subsections_2439_ = lean_ctor_get(v_a_2437_, 1);
lean_inc_ref(v_subsections_2439_);
lean_dec_ref(v_a_2437_);
v___x_2440_ = lean_box(0);
v_sz_2441_ = lean_array_size(v_text_2438_);
v___x_2442_ = lean_box_usize(v_sz_2441_);
v___x_2443_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1));
v___f_2444_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2444_, 0, v_text_2438_);
lean_closure_set(v___f_2444_, 1, v___x_2442_);
lean_closure_set(v___f_2444_, 2, v___x_2443_);
lean_closure_set(v___f_2444_, 3, v___x_2440_);
lean_closure_set(v___f_2444_, 4, v_subsections_2439_);
v___x_2445_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11));
v___x_2446_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13));
v___x_2447_ = l_Lean_Doc_MarkdownM_run_x27(v___f_2444_, v___x_2445_, v___x_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(lean_object* v_p_2448_, lean_object* v_level_2449_, lean_object* v_part_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_level_2449_, v_part_2450_, v_a_2451_, v_a_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___boxed(lean_object* v_p_2454_, lean_object* v_level_2455_, lean_object* v_part_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(v_p_2454_, v_level_2455_, v_part_2456_, v_a_2457_, v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec_ref(v_part_2456_);
lean_dec(v_level_2455_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(lean_object* v_p_2460_, lean_object* v___x_2461_, lean_object* v_as_2462_, size_t v_sz_2463_, size_t v_i_2464_, lean_object* v_b_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2461_, v_as_2462_, v_sz_2463_, v_i_2464_, v_b_2465_, v___y_2466_, v___y_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___boxed(lean_object* v_p_2469_, lean_object* v___x_2470_, lean_object* v_as_2471_, lean_object* v_sz_2472_, lean_object* v_i_2473_, lean_object* v_b_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
size_t v_sz_boxed_2477_; size_t v_i_boxed_2478_; lean_object* v_res_2479_; 
v_sz_boxed_2477_ = lean_unbox_usize(v_sz_2472_);
lean_dec(v_sz_2472_);
v_i_boxed_2478_ = lean_unbox_usize(v_i_2473_);
lean_dec(v_i_2473_);
v_res_2479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(v_p_2469_, v___x_2470_, v_as_2471_, v_sz_boxed_2477_, v_i_boxed_2478_, v_b_2474_, v___y_2475_, v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec_ref(v_as_2471_);
lean_dec(v___x_2470_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2(lean_object* v_s_2480_, lean_object* v_pattern_2481_, lean_object* v_replacement_2482_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v_s_2480_, v_replacement_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___boxed(lean_object* v_s_2484_, lean_object* v_pattern_2485_, lean_object* v_replacement_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2(v_s_2484_, v_pattern_2485_, v_replacement_2486_);
lean_dec_ref(v_replacement_2486_);
lean_dec_ref(v_pattern_2485_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6(lean_object* v_s_2488_, lean_object* v_replacement_2489_, lean_object* v_inst_2490_, lean_object* v_R_2491_, lean_object* v_a_2492_, lean_object* v_b_2493_, lean_object* v_c_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_2488_, v_replacement_2489_, v_a_2492_, v_b_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___boxed(lean_object* v_s_2496_, lean_object* v_replacement_2497_, lean_object* v_inst_2498_, lean_object* v_R_2499_, lean_object* v_a_2500_, lean_object* v_b_2501_, lean_object* v_c_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6(v_s_2496_, v_replacement_2497_, v_inst_2498_, v_R_2499_, v_a_2500_, v_b_2501_, v_c_2502_);
lean_dec_ref(v_replacement_2497_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_2504_, lean_object* v_declName_2505_, uint8_t v_includeBuiltin_2506_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_findInternalDocString_x3f(v_env_2504_, v_declName_2505_, v_includeBuiltin_2506_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2537_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2537_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2537_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
if (lean_obj_tag(v_a_2509_) == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2513_ = lean_box(0);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v___x_2513_);
v___x_2515_ = v___x_2511_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
else
{
lean_object* v_val_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2536_; 
v_val_2517_ = lean_ctor_get(v_a_2509_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_a_2509_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2519_ = v_a_2509_;
v_isShared_2520_ = v_isSharedCheck_2536_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_val_2517_);
lean_dec(v_a_2509_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2536_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
if (lean_obj_tag(v_val_2517_) == 0)
{
lean_object* v_val_2521_; lean_object* v___x_2523_; 
v_val_2521_ = lean_ctor_get(v_val_2517_, 0);
lean_inc(v_val_2521_);
lean_dec_ref(v_val_2517_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 0, v_val_2521_);
v___x_2523_ = v___x_2519_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_val_2521_);
v___x_2523_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2525_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v___x_2523_);
v___x_2525_ = v___x_2511_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
else
{
lean_object* v_val_2528_; lean_object* v___x_2529_; lean_object* v___x_2531_; 
v_val_2528_ = lean_ctor_get(v_val_2517_, 0);
lean_inc(v_val_2528_);
lean_dec_ref(v_val_2517_);
v___x_2529_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(v_val_2528_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 0, v___x_2529_);
v___x_2531_ = v___x_2519_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2533_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v___x_2531_);
v___x_2533_ = v___x_2511_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v_a_2538_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2508_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2508_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_2546_, lean_object* v_declName_2547_, lean_object* v_includeBuiltin_2548_, lean_object* v_a_2549_){
_start:
{
uint8_t v_includeBuiltin_boxed_2550_; lean_object* v_res_2551_; 
v_includeBuiltin_boxed_2550_ = lean_unbox(v_includeBuiltin_2548_);
v_res_2551_ = l_Lean_findSimpleDocString_x3f(v_env_2546_, v_declName_2547_, v_includeBuiltin_boxed_2550_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_es_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_array_mk(v_es_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_x_2556_, lean_object* v_x_2557_, lean_object* v_es_2558_){
_start:
{
lean_object* v_ents_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v_ents_2559_ = lean_array_mk(v_es_2558_);
v___x_2560_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
lean_inc_ref(v_ents_2559_);
v___x_2561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
lean_ctor_set(v___x_2561_, 1, v_ents_2559_);
lean_ctor_set(v___x_2561_, 2, v_ents_2559_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_x_2562_, lean_object* v_x_2563_, lean_object* v_es_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v_x_2562_, v_x_2563_, v_es_2564_);
lean_dec_ref(v_x_2563_);
lean_dec_ref(v_x_2562_);
return v_res_2565_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = lean_unsigned_to_nat(32u);
v___x_2567_ = lean_mk_empty_array_with_capacity(v___x_2566_);
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v___x_2569_, lean_object* v_x_2570_){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v___x_2571_ = lean_unsigned_to_nat(32u);
v___x_2572_ = lean_mk_empty_array_with_capacity(v___x_2571_);
v___x_2573_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_);
v___x_2574_ = ((size_t)5ULL);
lean_inc(v___x_2569_);
v___x_2575_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v___x_2572_);
lean_ctor_set(v___x_2575_, 2, v___x_2569_);
lean_ctor_set(v___x_2575_, 3, v___x_2569_);
lean_ctor_set_usize(v___x_2575_, 4, v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v___x_2576_, lean_object* v_x_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v___x_2576_, v_x_2577_);
lean_dec_ref(v_x_2577_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
v___x_2600_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object* v_env_2603_, lean_object* v_doc_2604_){
_start:
{
lean_object* v___x_2605_; lean_object* v_toEnvExtension_2606_; lean_object* v_asyncMode_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2605_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2606_ = lean_ctor_get(v___x_2605_, 0);
v_asyncMode_2607_ = lean_ctor_get(v_toEnvExtension_2606_, 2);
v___x_2608_ = lean_box(0);
v___x_2609_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2605_, v_env_2603_, v_doc_2604_, v_asyncMode_2607_, v___x_2608_);
return v___x_2609_;
}
}
static lean_object* _init_l_Lean_getMainModuleDoc___closed__0(void){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object* v_env_2611_){
_start:
{
lean_object* v___x_2612_; lean_object* v_toEnvExtension_2613_; lean_object* v_asyncMode_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2612_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2613_ = lean_ctor_get(v___x_2612_, 0);
v_asyncMode_2614_ = lean_ctor_get(v_toEnvExtension_2613_, 2);
v___x_2615_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2616_ = lean_box(0);
v___x_2617_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2615_, v___x_2612_, v_env_2611_, v_asyncMode_2614_, v___x_2616_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_getModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2619_ = lean_box(0);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v___x_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object* v_env_2621_, lean_object* v_moduleName_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_Environment_getModuleIdx_x3f(v_env_2621_, v_moduleName_2622_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_box(0);
return v___x_2624_;
}
else
{
lean_object* v_val_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2636_; 
v_val_2625_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2627_ = v___x_2623_;
v_isShared_2628_ = v_isSharedCheck_2636_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_val_2625_);
lean_dec(v___x_2623_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2636_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2629_ = lean_obj_once(&l_Lean_getModuleDoc_x3f___closed__0, &l_Lean_getModuleDoc_x3f___closed__0_once, _init_l_Lean_getModuleDoc_x3f___closed__0);
v___x_2630_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v___x_2631_ = 1;
v___x_2632_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2629_, v___x_2630_, v_env_2621_, v_val_2625_, v___x_2631_);
lean_dec(v_val_2625_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2632_);
v___x_2634_ = v___x_2627_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object* v_env_2637_, lean_object* v_moduleName_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Lean_getModuleDoc_x3f(v_env_2637_, v_moduleName_2638_);
lean_dec(v_moduleName_2638_);
lean_dec_ref(v_env_2637_);
return v_res_2639_;
}
}
static lean_object* _init_l_Lean_getDocStringText___redArg___closed__1(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__0));
v___x_2642_ = l_Lean_stringToMessageData(v___x_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object* v_inst_2646_, lean_object* v_inst_2647_, lean_object* v_stx_2648_){
_start:
{
lean_object* v_toApplicative_2655_; lean_object* v_toPure_2656_; lean_object* v_val_2658_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_toApplicative_2655_ = lean_ctor_get(v_inst_2646_, 0);
v_toPure_2656_ = lean_ctor_get(v_toApplicative_2655_, 1);
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = l_Lean_Syntax_getArg(v_stx_2648_, v___x_2665_);
switch(lean_obj_tag(v___x_2666_))
{
case 2:
{
lean_object* v_val_2667_; 
lean_inc(v_toPure_2656_);
lean_dec(v_stx_2648_);
lean_dec_ref(v_inst_2647_);
lean_dec_ref(v_inst_2646_);
v_val_2667_ = lean_ctor_get(v___x_2666_, 1);
lean_inc_ref(v_val_2667_);
lean_dec_ref(v___x_2666_);
v_val_2658_ = v_val_2667_;
goto v___jp_2657_;
}
case 1:
{
lean_object* v_kind_2668_; 
v_kind_2668_ = lean_ctor_get(v___x_2666_, 1);
lean_inc(v_kind_2668_);
if (lean_obj_tag(v_kind_2668_) == 1)
{
lean_object* v_pre_2669_; 
v_pre_2669_ = lean_ctor_get(v_kind_2668_, 0);
lean_inc(v_pre_2669_);
if (lean_obj_tag(v_pre_2669_) == 1)
{
lean_object* v_pre_2670_; 
v_pre_2670_ = lean_ctor_get(v_pre_2669_, 0);
lean_inc(v_pre_2670_);
if (lean_obj_tag(v_pre_2670_) == 1)
{
lean_object* v_pre_2671_; 
v_pre_2671_ = lean_ctor_get(v_pre_2670_, 0);
lean_inc(v_pre_2671_);
if (lean_obj_tag(v_pre_2671_) == 1)
{
lean_object* v_pre_2672_; 
v_pre_2672_ = lean_ctor_get(v_pre_2671_, 0);
if (lean_obj_tag(v_pre_2672_) == 0)
{
lean_object* v_str_2673_; lean_object* v_str_2674_; lean_object* v_str_2675_; lean_object* v_str_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_str_2673_ = lean_ctor_get(v_kind_2668_, 1);
lean_inc_ref(v_str_2673_);
lean_dec_ref(v_kind_2668_);
v_str_2674_ = lean_ctor_get(v_pre_2669_, 1);
lean_inc_ref(v_str_2674_);
lean_dec_ref(v_pre_2669_);
v_str_2675_ = lean_ctor_get(v_pre_2670_, 1);
lean_inc_ref(v_str_2675_);
lean_dec_ref(v_pre_2670_);
v_str_2676_ = lean_ctor_get(v_pre_2671_, 1);
lean_inc_ref(v_str_2676_);
lean_dec_ref(v_pre_2671_);
v___x_2677_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_2678_ = lean_string_dec_eq(v_str_2676_, v___x_2677_);
lean_dec_ref(v_str_2676_);
if (v___x_2678_ == 0)
{
lean_dec_ref(v_str_2675_);
lean_dec_ref(v_str_2674_);
lean_dec_ref(v_str_2673_);
lean_dec_ref(v___x_2666_);
goto v___jp_2649_;
}
else
{
lean_object* v___x_2679_; uint8_t v___x_2680_; 
v___x_2679_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__2));
v___x_2680_ = lean_string_dec_eq(v_str_2675_, v___x_2679_);
lean_dec_ref(v_str_2675_);
if (v___x_2680_ == 0)
{
lean_dec_ref(v_str_2674_);
lean_dec_ref(v_str_2673_);
lean_dec_ref(v___x_2666_);
goto v___jp_2649_;
}
else
{
lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2681_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__3));
v___x_2682_ = lean_string_dec_eq(v_str_2674_, v___x_2681_);
lean_dec_ref(v_str_2674_);
if (v___x_2682_ == 0)
{
lean_dec_ref(v_str_2673_);
lean_dec_ref(v___x_2666_);
goto v___jp_2649_;
}
else
{
lean_object* v___x_2683_; uint8_t v___x_2684_; 
v___x_2683_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__4));
v___x_2684_ = lean_string_dec_eq(v_str_2673_, v___x_2683_);
lean_dec_ref(v_str_2673_);
if (v___x_2684_ == 0)
{
lean_dec_ref(v___x_2666_);
goto v___jp_2649_;
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = lean_unsigned_to_nat(0u);
v___x_2686_ = l_Lean_Syntax_getArg(v___x_2666_, v___x_2685_);
lean_dec_ref(v___x_2666_);
if (lean_obj_tag(v___x_2686_) == 2)
{
lean_object* v_val_2687_; 
lean_inc(v_toPure_2656_);
lean_dec(v_stx_2648_);
lean_dec_ref(v_inst_2647_);
lean_dec_ref(v_inst_2646_);
v_val_2687_ = lean_ctor_get(v___x_2686_, 1);
lean_inc_ref(v_val_2687_);
lean_dec_ref(v___x_2686_);
v_val_2658_ = v_val_2687_;
goto v___jp_2657_;
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_dec(v___x_2686_);
v___x_2688_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2648_);
v___x_2689_ = l_Lean_MessageData_ofSyntax(v_stx_2648_);
v___x_2690_ = l_Lean_indentD(v___x_2689_);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2688_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = l_Lean_throwErrorAt___redArg(v_inst_2646_, v_inst_2647_, v_stx_2648_, v___x_2691_);
return v___x_2692_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2671_);
lean_dec_ref(v_pre_2670_);
lean_dec_ref(v_pre_2669_);
lean_dec_ref(v_kind_2668_);
lean_dec_ref(v___x_2666_);
goto v___jp_2649_;
}
}
else
{
lean_dec(v_pre_2671_);
lean_dec_ref(v_pre_2670_);
lean_dec_ref(v_pre_2669_);
lean_dec_ref(v_kind_2668_);
lean_dec_ref(v___x_2666_);
goto v___jp_2649_;
}
}
else
{
lean_dec_ref(v_pre_2669_);
lean_dec(v_pre_2670_);
lean_dec_ref(v_kind_2668_);
lean_dec_ref(v___x_2666_);
goto v___jp_2649_;
}
}
else
{
lean_dec(v_pre_2669_);
lean_dec_ref(v_kind_2668_);
lean_dec_ref(v___x_2666_);
goto v___jp_2649_;
}
}
else
{
lean_dec(v_kind_2668_);
lean_dec_ref(v___x_2666_);
goto v___jp_2649_;
}
}
default: 
{
lean_dec(v___x_2666_);
goto v___jp_2649_;
}
}
v___jp_2649_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2650_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2648_);
v___x_2651_ = l_Lean_MessageData_ofSyntax(v_stx_2648_);
v___x_2652_ = l_Lean_indentD(v___x_2651_);
v___x_2653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2650_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = l_Lean_throwErrorAt___redArg(v_inst_2646_, v_inst_2647_, v_stx_2648_, v___x_2653_);
return v___x_2654_;
}
v___jp_2657_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2659_ = lean_unsigned_to_nat(0u);
v___x_2660_ = lean_string_utf8_byte_size(v_val_2658_);
v___x_2661_ = lean_unsigned_to_nat(2u);
v___x_2662_ = lean_nat_sub(v___x_2660_, v___x_2661_);
v___x_2663_ = lean_string_utf8_extract(v_val_2658_, v___x_2659_, v___x_2662_);
lean_dec(v___x_2662_);
lean_dec_ref(v_val_2658_);
v___x_2664_ = lean_apply_2(v_toPure_2656_, lean_box(0), v___x_2663_);
return v___x_2664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object* v_m_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_stx_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_getDocStringText___redArg(v_inst_2694_, v_inst_2695_, v_stx_2696_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2700_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_2701_ = ((lean_object*)(l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0));
v___x_2702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
lean_ctor_set(v___x_2702_, 2, v___x_2700_);
return v___x_2702_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default(void){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_obj_once(&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1, &l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1_once, _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1);
return v___x_2703_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet(void){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object* v_a_2705_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = lean_nat_to_int(v_a_2705_);
return v___x_2706_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_unsigned_to_nat(2u);
v___x_2714_ = lean_nat_to_int(v___x_2713_);
return v___x_2714_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = lean_unsigned_to_nat(1u);
v___x_2716_ = lean_nat_to_int(v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object* v_x_2729_, lean_object* v_x_2730_, lean_object* v_x_2731_){
_start:
{
if (lean_obj_tag(v_x_2731_) == 0)
{
lean_dec(v_x_2729_);
return v_x_2730_;
}
else
{
lean_object* v_head_2732_; lean_object* v_tail_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2744_; 
v_head_2732_ = lean_ctor_get(v_x_2731_, 0);
v_tail_2733_ = lean_ctor_get(v_x_2731_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_x_2731_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2735_ = v_x_2731_;
v_isShared_2736_ = v_isSharedCheck_2744_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_tail_2733_);
lean_inc(v_head_2732_);
lean_dec(v_x_2731_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2744_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
lean_inc(v_x_2729_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set_tag(v___x_2735_, 5);
lean_ctor_set(v___x_2735_, 1, v_x_2729_);
lean_ctor_set(v___x_2735_, 0, v_x_2730_);
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_x_2730_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_x_2729_);
v___x_2738_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2739_ = lean_unsigned_to_nat(0u);
v___x_2740_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2732_, v___x_2739_);
v___x_2741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2738_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v_x_2730_ = v___x_2741_;
v_x_2731_ = v_tail_2733_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object* v_x_2745_, lean_object* v_x_2746_, lean_object* v_x_2747_){
_start:
{
if (lean_obj_tag(v_x_2747_) == 0)
{
lean_dec(v_x_2745_);
return v_x_2746_;
}
else
{
lean_object* v_head_2748_; lean_object* v_tail_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2760_; 
v_head_2748_ = lean_ctor_get(v_x_2747_, 0);
v_tail_2749_ = lean_ctor_get(v_x_2747_, 1);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_x_2747_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2751_ = v_x_2747_;
v_isShared_2752_ = v_isSharedCheck_2760_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_tail_2749_);
lean_inc(v_head_2748_);
lean_dec(v_x_2747_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2760_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
lean_inc(v_x_2745_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set_tag(v___x_2751_, 5);
lean_ctor_set(v___x_2751_, 1, v_x_2745_);
lean_ctor_set(v___x_2751_, 0, v_x_2746_);
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_x_2746_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_x_2745_);
v___x_2754_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2755_ = lean_unsigned_to_nat(0u);
v___x_2756_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2748_, v___x_2755_);
v___x_2757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2754_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(v_x_2745_, v___x_2757_, v_tail_2749_);
return v___x_2758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2761_, lean_object* v_x_2762_){
_start:
{
if (lean_obj_tag(v_x_2761_) == 0)
{
lean_object* v___x_2763_; 
lean_dec(v_x_2762_);
v___x_2763_ = lean_box(0);
return v___x_2763_;
}
else
{
lean_object* v_tail_2764_; 
v_tail_2764_ = lean_ctor_get(v_x_2761_, 1);
if (lean_obj_tag(v_tail_2764_) == 0)
{
lean_object* v_head_2765_; lean_object* v___x_2766_; 
lean_dec(v_x_2762_);
v_head_2765_ = lean_ctor_get(v_x_2761_, 0);
lean_inc(v_head_2765_);
lean_dec_ref(v_x_2761_);
v___x_2766_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2765_);
return v___x_2766_;
}
else
{
lean_object* v_head_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_inc(v_tail_2764_);
v_head_2767_ = lean_ctor_get(v_x_2761_, 0);
lean_inc(v_head_2767_);
lean_dec_ref(v_x_2761_);
v___x_2768_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2767_);
v___x_2769_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(v_x_2762_, v___x_2768_, v_tail_2764_);
return v___x_2769_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0));
v___x_2772_ = lean_string_length(v___x_2771_);
return v___x_2772_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5(void){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4);
v___x_2774_ = lean_nat_to_int(v___x_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_xs_2782_){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; uint8_t v___x_2785_; 
v___x_2783_ = lean_array_get_size(v_xs_2782_);
v___x_2784_ = lean_unsigned_to_nat(0u);
v___x_2785_ = lean_nat_dec_eq(v___x_2783_, v___x_2784_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2786_ = lean_array_to_list(v_xs_2782_);
v___x_2787_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2788_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_2786_, v___x_2787_);
v___x_2789_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_2790_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_2791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
lean_ctor_set(v___x_2791_, 1, v___x_2788_);
v___x_2792_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2789_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = l_Std_Format_fill(v___x_2794_);
return v___x_2795_;
}
else
{
lean_object* v___x_2796_; 
lean_dec_ref(v_xs_2782_);
v___x_2796_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_2796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_2851_, lean_object* v_prec_2852_){
_start:
{
switch(lean_obj_tag(v_x_2851_))
{
case 0:
{
lean_object* v_string_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2873_; 
v_string_2853_ = lean_ctor_get(v_x_2851_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_x_2851_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2855_ = v_x_2851_;
v_isShared_2856_ = v_isSharedCheck_2873_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_string_2853_);
lean_dec(v_x_2851_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2873_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___y_2858_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2869_ = lean_unsigned_to_nat(1024u);
v___x_2870_ = lean_nat_dec_le(v___x_2869_, v_prec_2852_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; 
v___x_2871_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2858_ = v___x_2871_;
goto v___jp_2857_;
}
else
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2858_ = v___x_2872_;
goto v___jp_2857_;
}
v___jp_2857_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
v___x_2859_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_2860_ = l_String_quote(v_string_2853_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set_tag(v___x_2855_, 3);
lean_ctor_set(v___x_2855_, 0, v___x_2860_);
v___x_2862_ = v___x_2855_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2860_);
v___x_2862_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2859_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
lean_inc(v___y_2858_);
v___x_2864_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___y_2858_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = 0;
v___x_2866_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*1, v___x_2865_);
v___x_2867_ = l_Repr_addAppParen(v___x_2866_, v_prec_2852_);
return v___x_2867_;
}
}
}
}
case 1:
{
lean_object* v_content_2874_; lean_object* v___y_2876_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v_content_2874_ = lean_ctor_get(v_x_2851_, 0);
lean_inc_ref(v_content_2874_);
lean_dec_ref(v_x_2851_);
v___x_2884_ = lean_unsigned_to_nat(1024u);
v___x_2885_ = lean_nat_dec_le(v___x_2884_, v_prec_2852_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; 
v___x_2886_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2876_ = v___x_2886_;
goto v___jp_2875_;
}
else
{
lean_object* v___x_2887_; 
v___x_2887_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2876_ = v___x_2887_;
goto v___jp_2875_;
}
v___jp_2875_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2877_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7));
v___x_2878_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2874_);
v___x_2879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
lean_inc(v___y_2876_);
v___x_2880_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___y_2876_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
v___x_2881_ = 0;
v___x_2882_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*1, v___x_2881_);
v___x_2883_ = l_Repr_addAppParen(v___x_2882_, v_prec_2852_);
return v___x_2883_;
}
}
case 2:
{
lean_object* v_content_2888_; lean_object* v___y_2890_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v_content_2888_ = lean_ctor_get(v_x_2851_, 0);
lean_inc_ref(v_content_2888_);
lean_dec_ref(v_x_2851_);
v___x_2898_ = lean_unsigned_to_nat(1024u);
v___x_2899_ = lean_nat_dec_le(v___x_2898_, v_prec_2852_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2890_ = v___x_2900_;
goto v___jp_2889_;
}
else
{
lean_object* v___x_2901_; 
v___x_2901_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2890_ = v___x_2901_;
goto v___jp_2889_;
}
v___jp_2889_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2891_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10));
v___x_2892_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2888_);
v___x_2893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2891_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
lean_inc(v___y_2890_);
v___x_2894_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___y_2890_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = 0;
v___x_2896_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*1, v___x_2895_);
v___x_2897_ = l_Repr_addAppParen(v___x_2896_, v_prec_2852_);
return v___x_2897_;
}
}
case 3:
{
lean_object* v_string_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2922_; 
v_string_2902_ = lean_ctor_get(v_x_2851_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_x_2851_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2904_ = v_x_2851_;
v_isShared_2905_ = v_isSharedCheck_2922_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_string_2902_);
lean_dec(v_x_2851_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2922_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___y_2907_; lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = lean_unsigned_to_nat(1024u);
v___x_2919_ = lean_nat_dec_le(v___x_2918_, v_prec_2852_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2907_ = v___x_2920_;
goto v___jp_2906_;
}
else
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2907_ = v___x_2921_;
goto v___jp_2906_;
}
v___jp_2906_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2908_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13));
v___x_2909_ = l_String_quote(v_string_2902_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 0, v___x_2909_);
v___x_2911_ = v___x_2904_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; uint8_t v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2908_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
lean_inc(v___y_2907_);
v___x_2913_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___y_2907_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = 0;
v___x_2915_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2915_, 0, v___x_2913_);
lean_ctor_set_uint8(v___x_2915_, sizeof(void*)*1, v___x_2914_);
v___x_2916_ = l_Repr_addAppParen(v___x_2915_, v_prec_2852_);
return v___x_2916_;
}
}
}
}
case 4:
{
uint8_t v_mode_2923_; lean_object* v_string_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2949_; 
v_mode_2923_ = lean_ctor_get_uint8(v_x_2851_, sizeof(void*)*1);
v_string_2924_ = lean_ctor_get(v_x_2851_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_x_2851_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2926_ = v_x_2851_;
v_isShared_2927_ = v_isSharedCheck_2949_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_string_2924_);
lean_dec(v_x_2851_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2949_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___y_2929_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v___x_2945_ = lean_unsigned_to_nat(1024u);
v___x_2946_ = lean_nat_dec_le(v___x_2945_, v_prec_2852_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2929_ = v___x_2947_;
goto v___jp_2928_;
}
else
{
lean_object* v___x_2948_; 
v___x_2948_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2929_ = v___x_2948_;
goto v___jp_2928_;
}
v___jp_2928_:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; lean_object* v___x_2942_; 
v___x_2930_ = lean_box(1);
v___x_2931_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16));
v___x_2932_ = lean_unsigned_to_nat(1024u);
v___x_2933_ = l_Lean_Doc_instReprMathMode_repr(v_mode_2923_, v___x_2932_);
v___x_2934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2931_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
lean_ctor_set(v___x_2935_, 1, v___x_2930_);
v___x_2936_ = l_String_quote(v_string_2924_);
v___x_2937_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
v___x_2938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2935_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
lean_inc(v___y_2929_);
v___x_2939_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___y_2929_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
v___x_2940_ = 0;
if (v_isShared_2927_ == 0)
{
lean_ctor_set_tag(v___x_2926_, 6);
lean_ctor_set(v___x_2926_, 0, v___x_2939_);
v___x_2942_ = v___x_2926_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2939_);
v___x_2942_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2943_; 
lean_ctor_set_uint8(v___x_2942_, sizeof(void*)*1, v___x_2940_);
v___x_2943_ = l_Repr_addAppParen(v___x_2942_, v_prec_2852_);
return v___x_2943_;
}
}
}
}
case 5:
{
lean_object* v_string_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2970_; 
v_string_2950_ = lean_ctor_get(v_x_2851_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_x_2851_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2952_ = v_x_2851_;
v_isShared_2953_ = v_isSharedCheck_2970_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_string_2950_);
lean_dec(v_x_2851_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2970_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___y_2955_; lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = lean_unsigned_to_nat(1024u);
v___x_2967_ = lean_nat_dec_le(v___x_2966_, v_prec_2852_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; 
v___x_2968_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2955_ = v___x_2968_;
goto v___jp_2954_;
}
else
{
lean_object* v___x_2969_; 
v___x_2969_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2955_ = v___x_2969_;
goto v___jp_2954_;
}
v___jp_2954_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2956_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19));
v___x_2957_ = l_String_quote(v_string_2950_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set_tag(v___x_2952_, 3);
lean_ctor_set(v___x_2952_, 0, v___x_2957_);
v___x_2959_ = v___x_2952_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2956_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
lean_inc(v___y_2955_);
v___x_2961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___y_2955_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = 0;
v___x_2963_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*1, v___x_2962_);
v___x_2964_ = l_Repr_addAppParen(v___x_2963_, v_prec_2852_);
return v___x_2964_;
}
}
}
}
case 6:
{
lean_object* v_content_2971_; lean_object* v_url_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2996_; 
v_content_2971_ = lean_ctor_get(v_x_2851_, 0);
v_url_2972_ = lean_ctor_get(v_x_2851_, 1);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_x_2851_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2974_ = v_x_2851_;
v_isShared_2975_ = v_isSharedCheck_2996_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_url_2972_);
lean_inc(v_content_2971_);
lean_dec(v_x_2851_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2996_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___y_2977_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v___x_2992_ = lean_unsigned_to_nat(1024u);
v___x_2993_ = lean_nat_dec_le(v___x_2992_, v_prec_2852_);
if (v___x_2993_ == 0)
{
lean_object* v___x_2994_; 
v___x_2994_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2977_ = v___x_2994_;
goto v___jp_2976_;
}
else
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2977_ = v___x_2995_;
goto v___jp_2976_;
}
v___jp_2976_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2978_ = lean_box(1);
v___x_2979_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22));
v___x_2980_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2971_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set_tag(v___x_2974_, 5);
lean_ctor_set(v___x_2974_, 1, v___x_2980_);
lean_ctor_set(v___x_2974_, 0, v___x_2979_);
v___x_2982_ = v___x_2974_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
lean_ctor_set(v___x_2983_, 1, v___x_2978_);
v___x_2984_ = l_String_quote(v_url_2972_);
v___x_2985_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
v___x_2986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2983_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
lean_inc(v___y_2977_);
v___x_2987_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___y_2977_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = 0;
v___x_2989_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2989_, 0, v___x_2987_);
lean_ctor_set_uint8(v___x_2989_, sizeof(void*)*1, v___x_2988_);
v___x_2990_ = l_Repr_addAppParen(v___x_2989_, v_prec_2852_);
return v___x_2990_;
}
}
}
}
case 7:
{
lean_object* v_name_2997_; lean_object* v_content_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3022_; 
v_name_2997_ = lean_ctor_get(v_x_2851_, 0);
v_content_2998_ = lean_ctor_get(v_x_2851_, 1);
v_isSharedCheck_3022_ = !lean_is_exclusive(v_x_2851_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3000_ = v_x_2851_;
v_isShared_3001_ = v_isSharedCheck_3022_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_content_2998_);
lean_inc(v_name_2997_);
lean_dec(v_x_2851_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3022_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___y_3003_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3018_ = lean_unsigned_to_nat(1024u);
v___x_3019_ = lean_nat_dec_le(v___x_3018_, v_prec_2852_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; 
v___x_3020_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3003_ = v___x_3020_;
goto v___jp_3002_;
}
else
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3003_ = v___x_3021_;
goto v___jp_3002_;
}
v___jp_3002_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3004_ = lean_box(1);
v___x_3005_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25));
v___x_3006_ = l_String_quote(v_name_2997_);
v___x_3007_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set_tag(v___x_3000_, 5);
lean_ctor_set(v___x_3000_, 1, v___x_3007_);
lean_ctor_set(v___x_3000_, 0, v___x_3005_);
v___x_3009_ = v___x_3000_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v___x_3004_);
v___x_3011_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2998_);
v___x_3012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
lean_inc(v___y_3003_);
v___x_3013_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___y_3003_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
v___x_3014_ = 0;
v___x_3015_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*1, v___x_3014_);
v___x_3016_ = l_Repr_addAppParen(v___x_3015_, v_prec_2852_);
return v___x_3016_;
}
}
}
}
case 8:
{
lean_object* v_alt_3023_; lean_object* v_url_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3049_; 
v_alt_3023_ = lean_ctor_get(v_x_2851_, 0);
v_url_3024_ = lean_ctor_get(v_x_2851_, 1);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_x_2851_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3026_ = v_x_2851_;
v_isShared_3027_ = v_isSharedCheck_3049_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_url_3024_);
lean_inc(v_alt_3023_);
lean_dec(v_x_2851_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3049_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___y_3029_; lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = lean_unsigned_to_nat(1024u);
v___x_3046_ = lean_nat_dec_le(v___x_3045_, v_prec_2852_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3029_ = v___x_3047_;
goto v___jp_3028_;
}
else
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3029_ = v___x_3048_;
goto v___jp_3028_;
}
v___jp_3028_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v___x_3030_ = lean_box(1);
v___x_3031_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28));
v___x_3032_ = l_String_quote(v_alt_3023_);
v___x_3033_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set_tag(v___x_3026_, 5);
lean_ctor_set(v___x_3026_, 1, v___x_3033_);
lean_ctor_set(v___x_3026_, 0, v___x_3031_);
v___x_3035_ = v___x_3026_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
lean_ctor_set(v___x_3036_, 1, v___x_3030_);
v___x_3037_ = l_String_quote(v_url_3024_);
v___x_3038_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
v___x_3039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3036_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
lean_inc(v___y_3029_);
v___x_3040_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___y_3029_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = 0;
v___x_3042_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*1, v___x_3041_);
v___x_3043_ = l_Repr_addAppParen(v___x_3042_, v_prec_2852_);
return v___x_3043_;
}
}
}
}
case 9:
{
lean_object* v_content_3050_; lean_object* v___y_3052_; lean_object* v___x_3060_; uint8_t v___x_3061_; 
v_content_3050_ = lean_ctor_get(v_x_2851_, 0);
lean_inc_ref(v_content_3050_);
lean_dec_ref(v_x_2851_);
v___x_3060_ = lean_unsigned_to_nat(1024u);
v___x_3061_ = lean_nat_dec_le(v___x_3060_, v_prec_2852_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3052_ = v___x_3062_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3052_ = v___x_3063_;
goto v___jp_3051_;
}
v___jp_3051_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3053_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31));
v___x_3054_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3050_);
v___x_3055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3053_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
lean_inc(v___y_3052_);
v___x_3056_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___y_3052_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = 0;
v___x_3058_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3058_, 0, v___x_3056_);
lean_ctor_set_uint8(v___x_3058_, sizeof(void*)*1, v___x_3057_);
v___x_3059_ = l_Repr_addAppParen(v___x_3058_, v_prec_2852_);
return v___x_3059_;
}
}
default: 
{
lean_object* v_container_3064_; lean_object* v_content_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3113_; 
v_container_3064_ = lean_ctor_get(v_x_2851_, 0);
v_content_3065_ = lean_ctor_get(v_x_2851_, 1);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_x_2851_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3067_ = v_x_2851_;
v_isShared_3068_ = v_isSharedCheck_3113_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_content_3065_);
lean_inc(v_container_3064_);
lean_dec(v_x_2851_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3113_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___y_3070_; lean_object* v___x_3109_; uint8_t v___x_3110_; 
v___x_3109_ = lean_unsigned_to_nat(1024u);
v___x_3110_ = lean_nat_dec_le(v___x_3109_, v_prec_2852_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; 
v___x_3111_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3070_ = v___x_3111_;
goto v___jp_3069_;
}
else
{
lean_object* v___x_3112_; 
v___x_3112_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3070_ = v___x_3112_;
goto v___jp_3069_;
}
v___jp_3069_:
{
lean_object* v_name_3071_; lean_object* v_val_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3108_; 
v_name_3071_ = lean_ctor_get(v_container_3064_, 0);
v_val_3072_ = lean_ctor_get(v_container_3064_, 1);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_container_3064_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3074_ = v_container_3064_;
v_isShared_3075_ = v_isSharedCheck_3108_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_val_3072_);
lean_inc(v_name_3071_);
lean_dec(v_container_3064_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3108_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3076_ = lean_box(1);
v___x_3077_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34));
v___x_3078_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3079_ = lean_unsigned_to_nat(0u);
v___x_3080_ = l_Lean_Name_reprPrec(v_name_3071_, v___x_3079_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set_tag(v___x_3074_, 5);
lean_ctor_set(v___x_3074_, 1, v___x_3080_);
lean_ctor_set(v___x_3074_, 0, v___x_3078_);
v___x_3082_ = v___x_3074_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3078_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; uint8_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3083_ = l_Std_Format_nestD(v___x_3082_);
v___x_3084_ = 0;
v___x_3085_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3085_, 0, v___x_3083_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*1, v___x_3084_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 5);
lean_ctor_set(v___x_3067_, 1, v___x_3076_);
lean_ctor_set(v___x_3067_, 0, v___x_3085_);
v___x_3087_ = v___x_3067_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v___x_3076_);
v___x_3087_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3088_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3089_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3072_);
lean_dec(v_val_3072_);
v___x_3090_ = l_Lean_Name_reprPrec(v___x_3089_, v___x_3079_);
v___x_3091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3088_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3091_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = l_Std_Format_nestD(v___x_3093_);
v___x_3095_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*1, v___x_3084_);
v___x_3096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3087_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = l_Std_Format_nestD(v___x_3096_);
v___x_3098_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3098_, 0, v___x_3097_);
lean_ctor_set_uint8(v___x_3098_, sizeof(void*)*1, v___x_3084_);
v___x_3099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3077_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
lean_ctor_set(v___x_3100_, 1, v___x_3076_);
v___x_3101_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3065_);
v___x_3102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3100_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
lean_inc(v___y_3070_);
v___x_3103_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___y_3070_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
lean_ctor_set_uint8(v___x_3104_, sizeof(void*)*1, v___x_3084_);
v___x_3105_ = l_Repr_addAppParen(v___x_3104_, v_prec_2852_);
return v___x_3105_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_3114_){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = lean_unsigned_to_nat(0u);
v___x_3116_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v___y_3114_, v___x_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_3117_, lean_object* v_prec_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_x_3117_, v_prec_3118_);
lean_dec(v_prec_3118_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object* v_xs_3120_){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3121_ = lean_array_get_size(v_xs_3120_);
v___x_3122_ = lean_unsigned_to_nat(0u);
v___x_3123_ = lean_nat_dec_eq(v___x_3121_, v___x_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3124_ = lean_array_to_list(v_xs_3120_);
v___x_3125_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3126_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_3124_, v___x_3125_);
v___x_3127_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3128_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
lean_ctor_set(v___x_3129_, 1, v___x_3126_);
v___x_3130_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3129_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3127_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = l_Std_Format_fill(v___x_3132_);
return v___x_3133_;
}
else
{
lean_object* v___x_3134_; 
lean_dec_ref(v_xs_3120_);
v___x_3134_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3134_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = lean_unsigned_to_nat(12u);
v___x_3166_ = lean_nat_to_int(v___x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object* v_x_3167_, lean_object* v_x_3168_, lean_object* v_x_3169_){
_start:
{
if (lean_obj_tag(v_x_3169_) == 0)
{
lean_dec(v_x_3167_);
return v_x_3168_;
}
else
{
lean_object* v_head_3170_; lean_object* v_tail_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3182_; 
v_head_3170_ = lean_ctor_get(v_x_3169_, 0);
v_tail_3171_ = lean_ctor_get(v_x_3169_, 1);
v_isSharedCheck_3182_ = !lean_is_exclusive(v_x_3169_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3173_ = v_x_3169_;
v_isShared_3174_ = v_isSharedCheck_3182_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_tail_3171_);
lean_inc(v_head_3170_);
lean_dec(v_x_3169_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3182_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
lean_inc(v_x_3167_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set_tag(v___x_3173_, 5);
lean_ctor_set(v___x_3173_, 1, v_x_3167_);
lean_ctor_set(v___x_3173_, 0, v_x_3168_);
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_x_3168_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_x_3167_);
v___x_3176_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = lean_unsigned_to_nat(0u);
v___x_3178_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_3170_, v___x_3177_);
v___x_3179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3176_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v_x_3168_ = v___x_3179_;
v_x_3169_ = v_tail_3171_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object* v_x_3183_, lean_object* v_x_3184_, lean_object* v_x_3185_){
_start:
{
if (lean_obj_tag(v_x_3185_) == 0)
{
lean_dec(v_x_3183_);
return v_x_3184_;
}
else
{
lean_object* v_head_3186_; lean_object* v_tail_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3198_; 
v_head_3186_ = lean_ctor_get(v_x_3185_, 0);
v_tail_3187_ = lean_ctor_get(v_x_3185_, 1);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_x_3185_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3189_ = v_x_3185_;
v_isShared_3190_ = v_isSharedCheck_3198_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_tail_3187_);
lean_inc(v_head_3186_);
lean_dec(v_x_3185_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3198_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
lean_inc(v_x_3183_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set_tag(v___x_3189_, 5);
lean_ctor_set(v___x_3189_, 1, v_x_3183_);
lean_ctor_set(v___x_3189_, 0, v_x_3184_);
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_x_3184_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v_x_3183_);
v___x_3192_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3193_ = lean_unsigned_to_nat(0u);
v___x_3194_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_3186_, v___x_3193_);
v___x_3195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3192_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(v_x_3183_, v___x_3195_, v_tail_3187_);
return v___x_3196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object* v_x_3199_, lean_object* v_x_3200_){
_start:
{
if (lean_obj_tag(v_x_3199_) == 0)
{
lean_object* v___x_3201_; 
lean_dec(v_x_3200_);
v___x_3201_ = lean_box(0);
return v___x_3201_;
}
else
{
lean_object* v_tail_3202_; 
v_tail_3202_ = lean_ctor_get(v_x_3199_, 1);
if (lean_obj_tag(v_tail_3202_) == 0)
{
lean_object* v_head_3203_; lean_object* v___x_3204_; 
lean_dec(v_x_3200_);
v_head_3203_ = lean_ctor_get(v_x_3199_, 0);
lean_inc(v_head_3203_);
lean_dec_ref(v_x_3199_);
v___x_3204_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3203_);
return v___x_3204_;
}
else
{
lean_object* v_head_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
lean_inc(v_tail_3202_);
v_head_3205_ = lean_ctor_get(v_x_3199_, 0);
lean_inc(v_head_3205_);
lean_dec_ref(v_x_3199_);
v___x_3206_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3205_);
v___x_3207_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(v_x_3200_, v___x_3206_, v_tail_3202_);
return v___x_3207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object* v_xs_3208_){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; 
v___x_3209_ = lean_array_get_size(v_xs_3208_);
v___x_3210_ = lean_unsigned_to_nat(0u);
v___x_3211_ = lean_nat_dec_eq(v___x_3209_, v___x_3210_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3212_ = lean_array_to_list(v_xs_3208_);
v___x_3213_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3214_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3212_, v___x_3213_);
v___x_3215_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3216_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
lean_ctor_set(v___x_3217_, 1, v___x_3214_);
v___x_3218_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3217_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3215_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = l_Std_Format_fill(v___x_3220_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; 
lean_dec_ref(v_xs_3208_);
v___x_3222_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3222_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_3225_ = lean_string_length(v___x_3224_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9);
v___x_3227_ = lean_nat_to_int(v___x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_x_3233_){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; uint8_t v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3234_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6));
v___x_3235_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3236_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_x_3233_);
v___x_3237_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3235_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v___x_3238_ = 0;
v___x_3239_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3239_, 0, v___x_3237_);
lean_ctor_set_uint8(v___x_3239_, sizeof(void*)*1, v___x_3238_);
v___x_3240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3234_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
v___x_3241_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3242_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3242_);
lean_ctor_set(v___x_3243_, 1, v___x_3240_);
v___x_3244_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3241_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
lean_ctor_set_uint8(v___x_3247_, sizeof(void*)*1, v___x_3238_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object* v_x_3248_, lean_object* v_x_3249_, lean_object* v_x_3250_){
_start:
{
if (lean_obj_tag(v_x_3250_) == 0)
{
lean_dec(v_x_3248_);
return v_x_3249_;
}
else
{
lean_object* v_head_3251_; lean_object* v_tail_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3262_; 
v_head_3251_ = lean_ctor_get(v_x_3250_, 0);
v_tail_3252_ = lean_ctor_get(v_x_3250_, 1);
v_isSharedCheck_3262_ = !lean_is_exclusive(v_x_3250_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3254_ = v_x_3250_;
v_isShared_3255_ = v_isSharedCheck_3262_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_tail_3252_);
lean_inc(v_head_3251_);
lean_dec(v_x_3250_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3262_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
lean_inc(v_x_3248_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set_tag(v___x_3254_, 5);
lean_ctor_set(v___x_3254_, 1, v_x_3248_);
lean_ctor_set(v___x_3254_, 0, v_x_3249_);
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_x_3249_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v_x_3248_);
v___x_3257_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3251_);
v___x_3259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v_x_3249_ = v___x_3259_;
v_x_3250_ = v_tail_3252_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object* v_x_3263_, lean_object* v_x_3264_, lean_object* v_x_3265_){
_start:
{
if (lean_obj_tag(v_x_3265_) == 0)
{
lean_dec(v_x_3263_);
return v_x_3264_;
}
else
{
lean_object* v_head_3266_; lean_object* v_tail_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3277_; 
v_head_3266_ = lean_ctor_get(v_x_3265_, 0);
v_tail_3267_ = lean_ctor_get(v_x_3265_, 1);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_x_3265_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3269_ = v_x_3265_;
v_isShared_3270_ = v_isSharedCheck_3277_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_tail_3267_);
lean_inc(v_head_3266_);
lean_dec(v_x_3265_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3277_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
lean_inc(v_x_3263_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set_tag(v___x_3269_, 5);
lean_ctor_set(v___x_3269_, 1, v_x_3263_);
lean_ctor_set(v___x_3269_, 0, v_x_3264_);
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_x_3264_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_x_3263_);
v___x_3272_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3266_);
v___x_3274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(v_x_3263_, v___x_3274_, v_tail_3267_);
return v___x_3275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object* v_x_3278_, lean_object* v_x_3279_){
_start:
{
if (lean_obj_tag(v_x_3278_) == 0)
{
lean_object* v___x_3280_; 
lean_dec(v_x_3279_);
v___x_3280_ = lean_box(0);
return v___x_3280_;
}
else
{
lean_object* v_tail_3281_; 
v_tail_3281_ = lean_ctor_get(v_x_3278_, 1);
if (lean_obj_tag(v_tail_3281_) == 0)
{
lean_object* v_head_3282_; lean_object* v___x_3283_; 
lean_dec(v_x_3279_);
v_head_3282_ = lean_ctor_get(v_x_3278_, 0);
lean_inc(v_head_3282_);
lean_dec_ref(v_x_3278_);
v___x_3283_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3282_);
return v___x_3283_;
}
else
{
lean_object* v_head_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
lean_inc(v_tail_3281_);
v_head_3284_ = lean_ctor_get(v_x_3278_, 0);
lean_inc(v_head_3284_);
lean_dec_ref(v_x_3278_);
v___x_3285_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3284_);
v___x_3286_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(v_x_3279_, v___x_3285_, v_tail_3281_);
return v___x_3286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object* v_xs_3287_){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3288_ = lean_array_get_size(v_xs_3287_);
v___x_3289_ = lean_unsigned_to_nat(0u);
v___x_3290_ = lean_nat_dec_eq(v___x_3288_, v___x_3289_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3291_ = lean_array_to_list(v_xs_3287_);
v___x_3292_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3293_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(v___x_3291_, v___x_3292_);
v___x_3294_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3295_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
lean_ctor_set(v___x_3296_, 1, v___x_3293_);
v___x_3297_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3296_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
v___x_3299_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3294_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = l_Std_Format_fill(v___x_3299_);
return v___x_3300_;
}
else
{
lean_object* v___x_3301_; 
lean_dec_ref(v_xs_3287_);
v___x_3301_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3301_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = lean_unsigned_to_nat(0u);
v___x_3309_ = lean_nat_to_int(v___x_3308_);
return v___x_3309_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = lean_unsigned_to_nat(8u);
v___x_3326_ = lean_nat_to_int(v___x_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_x_3330_){
_start:
{
lean_object* v_term_3331_; lean_object* v_desc_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3364_; 
v_term_3331_ = lean_ctor_get(v_x_3330_, 0);
v_desc_3332_ = lean_ctor_get(v_x_3330_, 1);
v_isSharedCheck_3364_ = !lean_is_exclusive(v_x_3330_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3334_ = v_x_3330_;
v_isShared_3335_ = v_isSharedCheck_3364_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_desc_3332_);
lean_inc(v_term_3331_);
lean_dec(v_x_3330_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3364_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3341_; 
v___x_3336_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3337_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3));
v___x_3338_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3339_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_term_3331_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set_tag(v___x_3334_, 4);
lean_ctor_set(v___x_3334_, 1, v___x_3339_);
lean_ctor_set(v___x_3334_, 0, v___x_3338_);
v___x_3341_ = v___x_3334_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v___x_3339_);
v___x_3341_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
uint8_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3342_ = 0;
v___x_3343_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3343_, 0, v___x_3341_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*1, v___x_3342_);
v___x_3344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3337_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3344_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = lean_box(1);
v___x_3348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3346_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6));
v___x_3350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
lean_ctor_set(v___x_3351_, 1, v___x_3336_);
v___x_3352_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_desc_3332_);
v___x_3353_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3338_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
lean_ctor_set_uint8(v___x_3354_, sizeof(void*)*1, v___x_3342_);
v___x_3355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3351_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3357_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
lean_ctor_set(v___x_3358_, 1, v___x_3355_);
v___x_3359_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3358_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3356_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
lean_ctor_set_uint8(v___x_3362_, sizeof(void*)*1, v___x_3342_);
return v___x_3362_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object* v_x_3365_, lean_object* v_x_3366_, lean_object* v_x_3367_){
_start:
{
if (lean_obj_tag(v_x_3367_) == 0)
{
lean_dec(v_x_3365_);
return v_x_3366_;
}
else
{
lean_object* v_head_3368_; lean_object* v_tail_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3379_; 
v_head_3368_ = lean_ctor_get(v_x_3367_, 0);
v_tail_3369_ = lean_ctor_get(v_x_3367_, 1);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_x_3367_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3371_ = v_x_3367_;
v_isShared_3372_ = v_isSharedCheck_3379_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_tail_3369_);
lean_inc(v_head_3368_);
lean_dec(v_x_3367_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3379_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
lean_inc(v_x_3365_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set_tag(v___x_3371_, 5);
lean_ctor_set(v___x_3371_, 1, v_x_3365_);
lean_ctor_set(v___x_3371_, 0, v_x_3366_);
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_x_3366_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_x_3365_);
v___x_3374_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3368_);
v___x_3376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3374_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v_x_3366_ = v___x_3376_;
v_x_3367_ = v_tail_3369_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object* v_x_3380_, lean_object* v_x_3381_, lean_object* v_x_3382_){
_start:
{
if (lean_obj_tag(v_x_3382_) == 0)
{
lean_dec(v_x_3380_);
return v_x_3381_;
}
else
{
lean_object* v_head_3383_; lean_object* v_tail_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3394_; 
v_head_3383_ = lean_ctor_get(v_x_3382_, 0);
v_tail_3384_ = lean_ctor_get(v_x_3382_, 1);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_x_3382_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3386_ = v_x_3382_;
v_isShared_3387_ = v_isSharedCheck_3394_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_tail_3384_);
lean_inc(v_head_3383_);
lean_dec(v_x_3382_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3394_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
lean_inc(v_x_3380_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set_tag(v___x_3386_, 5);
lean_ctor_set(v___x_3386_, 1, v_x_3380_);
lean_ctor_set(v___x_3386_, 0, v_x_3381_);
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_x_3381_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_x_3380_);
v___x_3389_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3383_);
v___x_3391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3389_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_3392_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(v_x_3380_, v___x_3391_, v_tail_3384_);
return v___x_3392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object* v_x_3395_, lean_object* v_x_3396_){
_start:
{
if (lean_obj_tag(v_x_3395_) == 0)
{
lean_object* v___x_3397_; 
lean_dec(v_x_3396_);
v___x_3397_ = lean_box(0);
return v___x_3397_;
}
else
{
lean_object* v_tail_3398_; 
v_tail_3398_ = lean_ctor_get(v_x_3395_, 1);
if (lean_obj_tag(v_tail_3398_) == 0)
{
lean_object* v_head_3399_; lean_object* v___x_3400_; 
lean_dec(v_x_3396_);
v_head_3399_ = lean_ctor_get(v_x_3395_, 0);
lean_inc(v_head_3399_);
lean_dec_ref(v_x_3395_);
v___x_3400_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3399_);
return v___x_3400_;
}
else
{
lean_object* v_head_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_inc(v_tail_3398_);
v_head_3401_ = lean_ctor_get(v_x_3395_, 0);
lean_inc(v_head_3401_);
lean_dec_ref(v_x_3395_);
v___x_3402_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3401_);
v___x_3403_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(v_x_3396_, v___x_3402_, v_tail_3398_);
return v___x_3403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object* v_xs_3404_){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3405_ = lean_array_get_size(v_xs_3404_);
v___x_3406_ = lean_unsigned_to_nat(0u);
v___x_3407_ = lean_nat_dec_eq(v___x_3405_, v___x_3406_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3408_ = lean_array_to_list(v_xs_3404_);
v___x_3409_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3410_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(v___x_3408_, v___x_3409_);
v___x_3411_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3412_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v___x_3410_);
v___x_3414_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3413_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3411_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = l_Std_Format_fill(v___x_3416_);
return v___x_3417_;
}
else
{
lean_object* v___x_3418_; 
lean_dec_ref(v_xs_3404_);
v___x_3418_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object* v_x_3437_, lean_object* v_prec_3438_){
_start:
{
switch(lean_obj_tag(v_x_3437_))
{
case 0:
{
lean_object* v_contents_3439_; lean_object* v___y_3441_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
v_contents_3439_ = lean_ctor_get(v_x_3437_, 0);
lean_inc_ref(v_contents_3439_);
lean_dec_ref(v_x_3437_);
v___x_3449_ = lean_unsigned_to_nat(1024u);
v___x_3450_ = lean_nat_dec_le(v___x_3449_, v_prec_3438_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3441_ = v___x_3451_;
goto v___jp_3440_;
}
else
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3441_ = v___x_3452_;
goto v___jp_3440_;
}
v___jp_3440_:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3442_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2));
v___x_3443_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_contents_3439_);
v___x_3444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3442_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
lean_inc(v___y_3441_);
v___x_3445_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___y_3441_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
v___x_3446_ = 0;
v___x_3447_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3447_, 0, v___x_3445_);
lean_ctor_set_uint8(v___x_3447_, sizeof(void*)*1, v___x_3446_);
v___x_3448_ = l_Repr_addAppParen(v___x_3447_, v_prec_3438_);
return v___x_3448_;
}
}
case 1:
{
lean_object* v_content_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3473_; 
v_content_3453_ = lean_ctor_get(v_x_3437_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_x_3437_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3455_ = v_x_3437_;
v_isShared_3456_ = v_isSharedCheck_3473_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_content_3453_);
lean_dec(v_x_3437_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3473_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___y_3458_; lean_object* v___x_3469_; uint8_t v___x_3470_; 
v___x_3469_ = lean_unsigned_to_nat(1024u);
v___x_3470_ = lean_nat_dec_le(v___x_3469_, v_prec_3438_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3471_; 
v___x_3471_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3458_ = v___x_3471_;
goto v___jp_3457_;
}
else
{
lean_object* v___x_3472_; 
v___x_3472_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3458_ = v___x_3472_;
goto v___jp_3457_;
}
v___jp_3457_:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3459_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5));
v___x_3460_ = l_String_quote(v_content_3453_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set_tag(v___x_3455_, 3);
lean_ctor_set(v___x_3455_, 0, v___x_3460_);
v___x_3462_ = v___x_3455_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; uint8_t v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3459_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
lean_inc(v___y_3458_);
v___x_3464_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___y_3458_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = 0;
v___x_3466_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set_uint8(v___x_3466_, sizeof(void*)*1, v___x_3465_);
v___x_3467_ = l_Repr_addAppParen(v___x_3466_, v_prec_3438_);
return v___x_3467_;
}
}
}
}
case 2:
{
lean_object* v_items_3474_; lean_object* v___y_3476_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v_items_3474_ = lean_ctor_get(v_x_3437_, 0);
lean_inc_ref(v_items_3474_);
lean_dec_ref(v_x_3437_);
v___x_3484_ = lean_unsigned_to_nat(1024u);
v___x_3485_ = lean_nat_dec_le(v___x_3484_, v_prec_3438_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; 
v___x_3486_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3476_ = v___x_3486_;
goto v___jp_3475_;
}
else
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3476_ = v___x_3487_;
goto v___jp_3475_;
}
v___jp_3475_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3477_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8));
v___x_3478_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3474_);
v___x_3479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3477_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
lean_inc(v___y_3476_);
v___x_3480_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___y_3476_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = 0;
v___x_3482_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3482_, 0, v___x_3480_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*1, v___x_3481_);
v___x_3483_ = l_Repr_addAppParen(v___x_3482_, v_prec_3438_);
return v___x_3483_;
}
}
case 3:
{
lean_object* v_start_3488_; lean_object* v_items_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3524_; 
v_start_3488_ = lean_ctor_get(v_x_3437_, 0);
v_items_3489_ = lean_ctor_get(v_x_3437_, 1);
v_isSharedCheck_3524_ = !lean_is_exclusive(v_x_3437_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3491_ = v_x_3437_;
v_isShared_3492_ = v_isSharedCheck_3524_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_items_3489_);
lean_inc(v_start_3488_);
lean_dec(v_x_3437_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3524_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3509_; lean_object* v___x_3520_; uint8_t v___x_3521_; 
v___x_3520_ = lean_unsigned_to_nat(1024u);
v___x_3521_ = lean_nat_dec_le(v___x_3520_, v_prec_3438_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; 
v___x_3522_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3509_ = v___x_3522_;
goto v___jp_3508_;
}
else
{
lean_object* v___x_3523_; 
v___x_3523_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3509_ = v___x_3523_;
goto v___jp_3508_;
}
v___jp_3493_:
{
lean_object* v___x_3499_; 
lean_inc(v___y_3496_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set_tag(v___x_3491_, 5);
lean_ctor_set(v___x_3491_, 1, v___y_3497_);
lean_ctor_set(v___x_3491_, 0, v___y_3496_);
v___x_3499_ = v___x_3491_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___y_3496_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v___y_3497_);
v___x_3499_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
lean_inc(v___y_3494_);
v___x_3500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v___y_3494_);
v___x_3501_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3489_);
v___x_3502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3500_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
lean_inc(v___y_3495_);
v___x_3503_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___y_3495_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
v___x_3504_ = 0;
v___x_3505_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3505_, 0, v___x_3503_);
lean_ctor_set_uint8(v___x_3505_, sizeof(void*)*1, v___x_3504_);
v___x_3506_ = l_Repr_addAppParen(v___x_3505_, v_prec_3438_);
return v___x_3506_;
}
}
v___jp_3508_:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; 
v___x_3510_ = lean_box(1);
v___x_3511_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11));
v___x_3512_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12, &l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12);
v___x_3513_ = lean_int_dec_lt(v_start_3488_, v___x_3512_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = l_Int_repr(v_start_3488_);
lean_dec(v_start_3488_);
v___x_3515_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3514_);
v___y_3494_ = v___x_3510_;
v___y_3495_ = v___y_3509_;
v___y_3496_ = v___x_3511_;
v___y_3497_ = v___x_3515_;
goto v___jp_3493_;
}
else
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3516_ = lean_unsigned_to_nat(1024u);
v___x_3517_ = l_Int_repr(v_start_3488_);
lean_dec(v_start_3488_);
v___x_3518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
v___x_3519_ = l_Repr_addAppParen(v___x_3518_, v___x_3516_);
v___y_3494_ = v___x_3510_;
v___y_3495_ = v___y_3509_;
v___y_3496_ = v___x_3511_;
v___y_3497_ = v___x_3519_;
goto v___jp_3493_;
}
}
}
}
case 4:
{
lean_object* v_items_3525_; lean_object* v___y_3527_; lean_object* v___x_3535_; uint8_t v___x_3536_; 
v_items_3525_ = lean_ctor_get(v_x_3437_, 0);
lean_inc_ref(v_items_3525_);
lean_dec_ref(v_x_3437_);
v___x_3535_ = lean_unsigned_to_nat(1024u);
v___x_3536_ = lean_nat_dec_le(v___x_3535_, v_prec_3438_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
v___x_3537_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3527_ = v___x_3537_;
goto v___jp_3526_;
}
else
{
lean_object* v___x_3538_; 
v___x_3538_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3527_ = v___x_3538_;
goto v___jp_3526_;
}
v___jp_3526_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3528_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15));
v___x_3529_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(v_items_3525_);
v___x_3530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3528_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
lean_inc(v___y_3527_);
v___x_3531_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___y_3527_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = 0;
v___x_3533_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3533_, 0, v___x_3531_);
lean_ctor_set_uint8(v___x_3533_, sizeof(void*)*1, v___x_3532_);
v___x_3534_ = l_Repr_addAppParen(v___x_3533_, v_prec_3438_);
return v___x_3534_;
}
}
case 5:
{
lean_object* v_items_3539_; lean_object* v___y_3541_; lean_object* v___x_3549_; uint8_t v___x_3550_; 
v_items_3539_ = lean_ctor_get(v_x_3437_, 0);
lean_inc_ref(v_items_3539_);
lean_dec_ref(v_x_3437_);
v___x_3549_ = lean_unsigned_to_nat(1024u);
v___x_3550_ = lean_nat_dec_le(v___x_3549_, v_prec_3438_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; 
v___x_3551_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3541_ = v___x_3551_;
goto v___jp_3540_;
}
else
{
lean_object* v___x_3552_; 
v___x_3552_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3541_ = v___x_3552_;
goto v___jp_3540_;
}
v___jp_3540_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; uint8_t v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3542_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18));
v___x_3543_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_items_3539_);
v___x_3544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3542_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
lean_inc(v___y_3541_);
v___x_3545_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___y_3541_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = 0;
v___x_3547_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3547_, 0, v___x_3545_);
lean_ctor_set_uint8(v___x_3547_, sizeof(void*)*1, v___x_3546_);
v___x_3548_ = l_Repr_addAppParen(v___x_3547_, v_prec_3438_);
return v___x_3548_;
}
}
case 6:
{
lean_object* v_content_3553_; lean_object* v___y_3555_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v_content_3553_ = lean_ctor_get(v_x_3437_, 0);
lean_inc_ref(v_content_3553_);
lean_dec_ref(v_x_3437_);
v___x_3563_ = lean_unsigned_to_nat(1024u);
v___x_3564_ = lean_nat_dec_le(v___x_3563_, v_prec_3438_);
if (v___x_3564_ == 0)
{
lean_object* v___x_3565_; 
v___x_3565_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3555_ = v___x_3565_;
goto v___jp_3554_;
}
else
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3555_ = v___x_3566_;
goto v___jp_3554_;
}
v___jp_3554_:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3556_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21));
v___x_3557_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3553_);
v___x_3558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3556_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
lean_inc(v___y_3555_);
v___x_3559_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___y_3555_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = 0;
v___x_3561_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3561_, 0, v___x_3559_);
lean_ctor_set_uint8(v___x_3561_, sizeof(void*)*1, v___x_3560_);
v___x_3562_ = l_Repr_addAppParen(v___x_3561_, v_prec_3438_);
return v___x_3562_;
}
}
default: 
{
lean_object* v_container_3567_; lean_object* v_content_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3616_; 
v_container_3567_ = lean_ctor_get(v_x_3437_, 0);
v_content_3568_ = lean_ctor_get(v_x_3437_, 1);
v_isSharedCheck_3616_ = !lean_is_exclusive(v_x_3437_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3570_ = v_x_3437_;
v_isShared_3571_ = v_isSharedCheck_3616_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_content_3568_);
lean_inc(v_container_3567_);
lean_dec(v_x_3437_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3616_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___y_3573_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v___x_3612_ = lean_unsigned_to_nat(1024u);
v___x_3613_ = lean_nat_dec_le(v___x_3612_, v_prec_3438_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3614_; 
v___x_3614_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3573_ = v___x_3614_;
goto v___jp_3572_;
}
else
{
lean_object* v___x_3615_; 
v___x_3615_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3573_ = v___x_3615_;
goto v___jp_3572_;
}
v___jp_3572_:
{
lean_object* v_name_3574_; lean_object* v_val_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3611_; 
v_name_3574_ = lean_ctor_get(v_container_3567_, 0);
v_val_3575_ = lean_ctor_get(v_container_3567_, 1);
v_isSharedCheck_3611_ = !lean_is_exclusive(v_container_3567_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3577_ = v_container_3567_;
v_isShared_3578_ = v_isSharedCheck_3611_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_val_3575_);
lean_inc(v_name_3574_);
lean_dec(v_container_3567_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3611_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3579_ = lean_box(1);
v___x_3580_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24));
v___x_3581_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3582_ = lean_unsigned_to_nat(0u);
v___x_3583_ = l_Lean_Name_reprPrec(v_name_3574_, v___x_3582_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set_tag(v___x_3577_, 5);
lean_ctor_set(v___x_3577_, 1, v___x_3583_);
lean_ctor_set(v___x_3577_, 0, v___x_3581_);
v___x_3585_ = v___x_3577_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3586_; uint8_t v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3590_; 
v___x_3586_ = l_Std_Format_nestD(v___x_3585_);
v___x_3587_ = 0;
v___x_3588_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3588_, 0, v___x_3586_);
lean_ctor_set_uint8(v___x_3588_, sizeof(void*)*1, v___x_3587_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set_tag(v___x_3570_, 5);
lean_ctor_set(v___x_3570_, 1, v___x_3579_);
lean_ctor_set(v___x_3570_, 0, v___x_3588_);
v___x_3590_ = v___x_3570_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v___x_3579_);
v___x_3590_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3591_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3592_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3575_);
lean_dec(v_val_3575_);
v___x_3593_ = l_Lean_Name_reprPrec(v___x_3592_, v___x_3582_);
v___x_3594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3591_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v___x_3595_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3594_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = l_Std_Format_nestD(v___x_3596_);
v___x_3598_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
lean_ctor_set_uint8(v___x_3598_, sizeof(void*)*1, v___x_3587_);
v___x_3599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3590_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = l_Std_Format_nestD(v___x_3599_);
v___x_3601_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
lean_ctor_set_uint8(v___x_3601_, sizeof(void*)*1, v___x_3587_);
v___x_3602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3580_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
lean_ctor_set(v___x_3603_, 1, v___x_3579_);
v___x_3604_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3568_);
v___x_3605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3603_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
lean_inc(v___y_3573_);
v___x_3606_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___y_3573_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
lean_ctor_set_uint8(v___x_3607_, sizeof(void*)*1, v___x_3587_);
v___x_3608_ = l_Repr_addAppParen(v___x_3607_, v_prec_3438_);
return v___x_3608_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3618_ = lean_unsigned_to_nat(0u);
v___x_3619_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v___y_3617_, v___x_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object* v_x_3620_, lean_object* v_prec_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_x_3620_, v_prec_3621_);
lean_dec(v_prec_3621_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object* v_xs_3623_){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; 
v___x_3624_ = lean_array_get_size(v_xs_3623_);
v___x_3625_ = lean_unsigned_to_nat(0u);
v___x_3626_ = lean_nat_dec_eq(v___x_3624_, v___x_3625_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3627_ = lean_array_to_list(v_xs_3623_);
v___x_3628_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3629_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3627_, v___x_3628_);
v___x_3630_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3631_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
lean_ctor_set(v___x_3632_, 1, v___x_3629_);
v___x_3633_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3632_);
lean_ctor_set(v___x_3634_, 1, v___x_3633_);
v___x_3635_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3630_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = l_Std_Format_fill(v___x_3635_);
return v___x_3636_;
}
else
{
lean_object* v___x_3637_; 
lean_dec_ref(v_xs_3623_);
v___x_3637_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3637_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object* v_x_3641_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = ((lean_object*)(l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1));
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object* v_x_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3643_);
lean_dec(v_x_3643_);
return v_res_3644_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_unsigned_to_nat(9u);
v___x_3655_ = lean_nat_to_int(v___x_3654_);
return v___x_3655_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = lean_unsigned_to_nat(15u);
v___x_3660_ = lean_nat_to_int(v___x_3659_);
return v___x_3660_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12(void){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = lean_unsigned_to_nat(11u);
v___x_3668_ = lean_nat_to_int(v___x_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object* v_x_3672_, lean_object* v_x_3673_, lean_object* v_x_3674_){
_start:
{
if (lean_obj_tag(v_x_3674_) == 0)
{
lean_dec(v_x_3672_);
return v_x_3673_;
}
else
{
lean_object* v_head_3675_; lean_object* v_tail_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3686_; 
v_head_3675_ = lean_ctor_get(v_x_3674_, 0);
v_tail_3676_ = lean_ctor_get(v_x_3674_, 1);
v_isSharedCheck_3686_ = !lean_is_exclusive(v_x_3674_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3678_ = v_x_3674_;
v_isShared_3679_ = v_isSharedCheck_3686_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_tail_3676_);
lean_inc(v_head_3675_);
lean_dec(v_x_3674_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3686_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
lean_inc(v_x_3672_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set_tag(v___x_3678_, 5);
lean_ctor_set(v___x_3678_, 1, v_x_3672_);
lean_ctor_set(v___x_3678_, 0, v_x_3673_);
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_x_3673_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_x_3672_);
v___x_3681_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3682_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3675_);
v___x_3683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3681_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(v_x_3672_, v___x_3683_, v_tail_3676_);
return v___x_3684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object* v_x_3687_, lean_object* v_x_3688_){
_start:
{
if (lean_obj_tag(v_x_3687_) == 0)
{
lean_object* v___x_3689_; 
lean_dec(v_x_3688_);
v___x_3689_ = lean_box(0);
return v___x_3689_;
}
else
{
lean_object* v_tail_3690_; 
v_tail_3690_ = lean_ctor_get(v_x_3687_, 1);
if (lean_obj_tag(v_tail_3690_) == 0)
{
lean_object* v_head_3691_; lean_object* v___x_3692_; 
lean_dec(v_x_3688_);
v_head_3691_ = lean_ctor_get(v_x_3687_, 0);
lean_inc(v_head_3691_);
lean_dec_ref(v_x_3687_);
v___x_3692_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3691_);
return v___x_3692_;
}
else
{
lean_object* v_head_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
lean_inc(v_tail_3690_);
v_head_3693_ = lean_ctor_get(v_x_3687_, 0);
lean_inc(v_head_3693_);
lean_dec_ref(v_x_3687_);
v___x_3694_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3693_);
v___x_3695_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(v_x_3688_, v___x_3694_, v_tail_3690_);
return v___x_3695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object* v_xs_3696_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; 
v___x_3697_ = lean_array_get_size(v_xs_3696_);
v___x_3698_ = lean_unsigned_to_nat(0u);
v___x_3699_ = lean_nat_dec_eq(v___x_3697_, v___x_3698_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3700_ = lean_array_to_list(v_xs_3696_);
v___x_3701_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3702_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(v___x_3700_, v___x_3701_);
v___x_3703_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3704_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
lean_ctor_set(v___x_3705_, 1, v___x_3702_);
v___x_3706_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3705_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
v___x_3708_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3703_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
v___x_3709_ = l_Std_Format_fill(v___x_3708_);
return v___x_3709_;
}
else
{
lean_object* v___x_3710_; 
lean_dec_ref(v_xs_3696_);
v___x_3710_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object* v_x_3711_){
_start:
{
lean_object* v_title_3712_; lean_object* v_titleString_3713_; lean_object* v_metadata_3714_; lean_object* v_content_3715_; lean_object* v_subParts_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; uint8_t v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v_title_3712_ = lean_ctor_get(v_x_3711_, 0);
lean_inc_ref(v_title_3712_);
v_titleString_3713_ = lean_ctor_get(v_x_3711_, 1);
lean_inc_ref(v_titleString_3713_);
v_metadata_3714_ = lean_ctor_get(v_x_3711_, 2);
lean_inc(v_metadata_3714_);
v_content_3715_ = lean_ctor_get(v_x_3711_, 3);
lean_inc_ref(v_content_3715_);
v_subParts_3716_ = lean_ctor_get(v_x_3711_, 4);
lean_inc_ref(v_subParts_3716_);
lean_dec_ref(v_x_3711_);
v___x_3717_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3718_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3));
v___x_3719_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4);
v___x_3720_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_title_3712_);
v___x_3721_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3719_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = 0;
v___x_3723_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3723_, 0, v___x_3721_);
lean_ctor_set_uint8(v___x_3723_, sizeof(void*)*1, v___x_3722_);
v___x_3724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3718_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3724_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v___x_3727_ = lean_box(1);
v___x_3728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3726_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6));
v___x_3730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
lean_ctor_set(v___x_3731_, 1, v___x_3717_);
v___x_3732_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7);
v___x_3733_ = l_String_quote(v_titleString_3713_);
v___x_3734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
v___x_3735_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3732_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set_uint8(v___x_3736_, sizeof(void*)*1, v___x_3722_);
v___x_3737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3731_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
lean_ctor_set(v___x_3738_, 1, v___x_3725_);
v___x_3739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
lean_ctor_set(v___x_3739_, 1, v___x_3727_);
v___x_3740_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9));
v___x_3741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
lean_ctor_set(v___x_3742_, 1, v___x_3717_);
v___x_3743_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3744_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_metadata_3714_);
lean_dec(v_metadata_3714_);
v___x_3745_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3743_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
lean_ctor_set_uint8(v___x_3746_, sizeof(void*)*1, v___x_3722_);
v___x_3747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3742_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
lean_ctor_set(v___x_3748_, 1, v___x_3725_);
v___x_3749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
lean_ctor_set(v___x_3749_, 1, v___x_3727_);
v___x_3750_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11));
v___x_3751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3749_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
lean_ctor_set(v___x_3752_, 1, v___x_3717_);
v___x_3753_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12);
v___x_3754_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_content_3715_);
v___x_3755_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3753_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
lean_ctor_set_uint8(v___x_3756_, sizeof(void*)*1, v___x_3722_);
v___x_3757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3752_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3757_);
lean_ctor_set(v___x_3758_, 1, v___x_3725_);
v___x_3759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
lean_ctor_set(v___x_3759_, 1, v___x_3727_);
v___x_3760_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14));
v___x_3761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
lean_ctor_set(v___x_3762_, 1, v___x_3717_);
v___x_3763_ = l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(v_subParts_3716_);
v___x_3764_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3743_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
lean_ctor_set_uint8(v___x_3765_, sizeof(void*)*1, v___x_3722_);
v___x_3766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3762_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3768_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
lean_ctor_set(v___x_3769_, 1, v___x_3766_);
v___x_3770_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3771_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3769_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3767_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
lean_ctor_set_uint8(v___x_3773_, sizeof(void*)*1, v___x_3722_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object* v_x_3774_, lean_object* v_x_3775_, lean_object* v_x_3776_){
_start:
{
if (lean_obj_tag(v_x_3776_) == 0)
{
lean_dec(v_x_3774_);
return v_x_3775_;
}
else
{
lean_object* v_head_3777_; lean_object* v_tail_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3788_; 
v_head_3777_ = lean_ctor_get(v_x_3776_, 0);
v_tail_3778_ = lean_ctor_get(v_x_3776_, 1);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_x_3776_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3780_ = v_x_3776_;
v_isShared_3781_ = v_isSharedCheck_3788_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_tail_3778_);
lean_inc(v_head_3777_);
lean_dec(v_x_3776_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3788_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
lean_inc(v_x_3774_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set_tag(v___x_3780_, 5);
lean_ctor_set(v___x_3780_, 1, v_x_3774_);
lean_ctor_set(v___x_3780_, 0, v_x_3775_);
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_x_3775_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v_x_3774_);
v___x_3783_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3784_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3777_);
v___x_3785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v_x_3775_ = v___x_3785_;
v_x_3776_ = v_tail_3778_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object* v_x_3789_, lean_object* v_x_3790_){
_start:
{
lean_object* v_fst_3791_; lean_object* v_snd_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3802_; 
v_fst_3791_ = lean_ctor_get(v_x_3789_, 0);
v_snd_3792_ = lean_ctor_get(v_x_3789_, 1);
v_isSharedCheck_3802_ = !lean_is_exclusive(v_x_3789_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3794_ = v_x_3789_;
v_isShared_3795_ = v_isSharedCheck_3802_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_snd_3792_);
lean_inc(v_fst_3791_);
lean_dec(v_x_3789_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3802_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3796_ = l_Lean_instReprDeclarationRange_repr___redArg(v_fst_3791_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set_tag(v___x_3794_, 1);
lean_ctor_set(v___x_3794_, 1, v_x_3790_);
lean_ctor_set(v___x_3794_, 0, v___x_3796_);
v___x_3798_ = v___x_3794_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3796_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_x_3790_);
v___x_3798_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_snd_3792_);
v___x_3800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3799_);
lean_ctor_set(v___x_3800_, 1, v___x_3798_);
return v___x_3800_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object* v_x_3803_, lean_object* v_x_3804_, lean_object* v_x_3805_){
_start:
{
if (lean_obj_tag(v_x_3805_) == 0)
{
lean_dec(v_x_3803_);
return v_x_3804_;
}
else
{
lean_object* v_head_3806_; lean_object* v_tail_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3816_; 
v_head_3806_ = lean_ctor_get(v_x_3805_, 0);
v_tail_3807_ = lean_ctor_get(v_x_3805_, 1);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_x_3805_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3809_ = v_x_3805_;
v_isShared_3810_ = v_isSharedCheck_3816_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_tail_3807_);
lean_inc(v_head_3806_);
lean_dec(v_x_3805_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3816_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
lean_inc(v_x_3803_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set_tag(v___x_3809_, 5);
lean_ctor_set(v___x_3809_, 1, v_x_3803_);
lean_ctor_set(v___x_3809_, 0, v_x_3804_);
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_x_3804_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_x_3803_);
v___x_3812_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3813_; 
v___x_3813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
lean_ctor_set(v___x_3813_, 1, v_head_3806_);
v_x_3804_ = v___x_3813_;
v_x_3805_ = v_tail_3807_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object* v_x_3817_, lean_object* v_x_3818_){
_start:
{
if (lean_obj_tag(v_x_3817_) == 0)
{
lean_object* v___x_3819_; 
lean_dec(v_x_3818_);
v___x_3819_ = lean_box(0);
return v___x_3819_;
}
else
{
lean_object* v_tail_3820_; 
v_tail_3820_ = lean_ctor_get(v_x_3817_, 1);
if (lean_obj_tag(v_tail_3820_) == 0)
{
lean_object* v_head_3821_; 
lean_dec(v_x_3818_);
v_head_3821_ = lean_ctor_get(v_x_3817_, 0);
lean_inc(v_head_3821_);
lean_dec_ref(v_x_3817_);
return v_head_3821_;
}
else
{
lean_object* v_head_3822_; lean_object* v___x_3823_; 
lean_inc(v_tail_3820_);
v_head_3822_ = lean_ctor_get(v_x_3817_, 0);
lean_inc(v_head_3822_);
lean_dec_ref(v_x_3817_);
v___x_3823_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(v_x_3818_, v_head_3822_, v_tail_3820_);
return v___x_3823_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3825_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0));
v___x_3826_ = lean_string_length(v___x_3825_);
return v___x_3826_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3827_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1);
v___x_3828_ = lean_nat_to_int(v___x_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object* v_x_3833_){
_start:
{
lean_object* v_fst_3834_; lean_object* v_snd_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3857_; 
v_fst_3834_ = lean_ctor_get(v_x_3833_, 0);
v_snd_3835_ = lean_ctor_get(v_x_3833_, 1);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_x_3833_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3837_ = v_x_3833_;
v_isShared_3838_ = v_isSharedCheck_3857_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_snd_3835_);
lean_inc(v_fst_3834_);
lean_dec(v_x_3833_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3857_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3843_; 
v___x_3839_ = l_Nat_reprFast(v_fst_3834_);
v___x_3840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
v___x_3841_ = lean_box(0);
if (v_isShared_3838_ == 0)
{
lean_ctor_set_tag(v___x_3837_, 1);
lean_ctor_set(v___x_3837_, 1, v___x_3841_);
lean_ctor_set(v___x_3837_, 0, v___x_3840_);
v___x_3843_ = v___x_3837_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3840_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v___x_3841_);
v___x_3843_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; uint8_t v___x_3854_; lean_object* v___x_3855_; 
v___x_3844_ = l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(v_snd_3835_, v___x_3843_);
v___x_3845_ = l_List_reverse___redArg(v___x_3844_);
v___x_3846_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3847_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(v___x_3845_, v___x_3846_);
v___x_3848_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2);
v___x_3849_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3));
v___x_3850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
lean_ctor_set(v___x_3850_, 1, v___x_3847_);
v___x_3851_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4));
v___x_3852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3850_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v___x_3853_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3848_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v___x_3854_ = 0;
v___x_3855_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3855_, 0, v___x_3853_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*1, v___x_3854_);
return v___x_3855_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object* v_x_3858_, lean_object* v_x_3859_, lean_object* v_x_3860_){
_start:
{
if (lean_obj_tag(v_x_3860_) == 0)
{
lean_dec(v_x_3858_);
return v_x_3859_;
}
else
{
lean_object* v_head_3861_; lean_object* v_tail_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3872_; 
v_head_3861_ = lean_ctor_get(v_x_3860_, 0);
v_tail_3862_ = lean_ctor_get(v_x_3860_, 1);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_x_3860_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3864_ = v_x_3860_;
v_isShared_3865_ = v_isSharedCheck_3872_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_tail_3862_);
lean_inc(v_head_3861_);
lean_dec(v_x_3860_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3872_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
lean_inc(v_x_3858_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set_tag(v___x_3864_, 5);
lean_ctor_set(v___x_3864_, 1, v_x_3858_);
lean_ctor_set(v___x_3864_, 0, v_x_3859_);
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_x_3859_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_x_3858_);
v___x_3867_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3861_);
v___x_3869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3867_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v_x_3859_ = v___x_3869_;
v_x_3860_ = v_tail_3862_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object* v_x_3873_, lean_object* v_x_3874_, lean_object* v_x_3875_){
_start:
{
if (lean_obj_tag(v_x_3875_) == 0)
{
lean_dec(v_x_3873_);
return v_x_3874_;
}
else
{
lean_object* v_head_3876_; lean_object* v_tail_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3887_; 
v_head_3876_ = lean_ctor_get(v_x_3875_, 0);
v_tail_3877_ = lean_ctor_get(v_x_3875_, 1);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_x_3875_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3879_ = v_x_3875_;
v_isShared_3880_ = v_isSharedCheck_3887_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_tail_3877_);
lean_inc(v_head_3876_);
lean_dec(v_x_3875_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3887_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
lean_inc(v_x_3873_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set_tag(v___x_3879_, 5);
lean_ctor_set(v___x_3879_, 1, v_x_3873_);
lean_ctor_set(v___x_3879_, 0, v_x_3874_);
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_x_3874_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v_x_3873_);
v___x_3882_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3883_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3876_);
v___x_3884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3882_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v___x_3885_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(v_x_3873_, v___x_3884_, v_tail_3877_);
return v___x_3885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object* v_x_3888_, lean_object* v_x_3889_){
_start:
{
if (lean_obj_tag(v_x_3888_) == 0)
{
lean_object* v___x_3890_; 
lean_dec(v_x_3889_);
v___x_3890_ = lean_box(0);
return v___x_3890_;
}
else
{
lean_object* v_tail_3891_; 
v_tail_3891_ = lean_ctor_get(v_x_3888_, 1);
if (lean_obj_tag(v_tail_3891_) == 0)
{
lean_object* v_head_3892_; lean_object* v___x_3893_; 
lean_dec(v_x_3889_);
v_head_3892_ = lean_ctor_get(v_x_3888_, 0);
lean_inc(v_head_3892_);
lean_dec_ref(v_x_3888_);
v___x_3893_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3892_);
return v___x_3893_;
}
else
{
lean_object* v_head_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
lean_inc(v_tail_3891_);
v_head_3894_ = lean_ctor_get(v_x_3888_, 0);
lean_inc(v_head_3894_);
lean_dec_ref(v_x_3888_);
v___x_3895_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3894_);
v___x_3896_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(v_x_3889_, v___x_3895_, v_tail_3891_);
return v___x_3896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object* v_xs_3897_){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___x_3898_ = lean_array_get_size(v_xs_3897_);
v___x_3899_ = lean_unsigned_to_nat(0u);
v___x_3900_ = lean_nat_dec_eq(v___x_3898_, v___x_3899_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3901_ = lean_array_to_list(v_xs_3897_);
v___x_3902_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3903_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(v___x_3901_, v___x_3902_);
v___x_3904_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3905_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
lean_ctor_set(v___x_3906_, 1, v___x_3903_);
v___x_3907_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3906_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
v___x_3909_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3904_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = l_Std_Format_fill(v___x_3909_);
return v___x_3910_;
}
else
{
lean_object* v___x_3911_; 
lean_dec_ref(v_xs_3897_);
v___x_3911_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3911_;
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3927_ = lean_unsigned_to_nat(20u);
v___x_3928_ = lean_nat_to_int(v___x_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object* v_x_3929_){
_start:
{
lean_object* v_text_3930_; lean_object* v_sections_3931_; lean_object* v_declarationRange_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; uint8_t v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v_text_3930_ = lean_ctor_get(v_x_3929_, 0);
lean_inc_ref(v_text_3930_);
v_sections_3931_ = lean_ctor_get(v_x_3929_, 1);
lean_inc_ref(v_sections_3931_);
v_declarationRange_3932_ = lean_ctor_get(v_x_3929_, 2);
lean_inc_ref(v_declarationRange_3932_);
lean_dec_ref(v_x_3929_);
v___x_3933_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3934_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3));
v___x_3935_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3936_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_text_3930_);
v___x_3937_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3935_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = 0;
v___x_3939_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3939_, 0, v___x_3937_);
lean_ctor_set_uint8(v___x_3939_, sizeof(void*)*1, v___x_3938_);
v___x_3940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3934_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
v___x_3941_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3940_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
v___x_3943_ = lean_box(1);
v___x_3944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3942_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
v___x_3945_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5));
v___x_3946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3944_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
v___x_3947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
lean_ctor_set(v___x_3947_, 1, v___x_3933_);
v___x_3948_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3949_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(v_sections_3931_);
v___x_3950_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3948_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
v___x_3951_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
lean_ctor_set_uint8(v___x_3951_, sizeof(void*)*1, v___x_3938_);
v___x_3952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3947_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
lean_ctor_set(v___x_3953_, 1, v___x_3941_);
v___x_3954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
lean_ctor_set(v___x_3954_, 1, v___x_3943_);
v___x_3955_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7));
v___x_3956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3954_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
v___x_3957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3956_);
lean_ctor_set(v___x_3957_, 1, v___x_3933_);
v___x_3958_ = lean_obj_once(&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8, &l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once, _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8);
v___x_3959_ = l_Lean_instReprDeclarationRange_repr___redArg(v_declarationRange_3932_);
v___x_3960_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3958_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
v___x_3961_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
lean_ctor_set_uint8(v___x_3961_, sizeof(void*)*1, v___x_3938_);
v___x_3962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3957_);
lean_ctor_set(v___x_3962_, 1, v___x_3961_);
v___x_3963_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3964_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
lean_ctor_set(v___x_3965_, 1, v___x_3962_);
v___x_3966_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3965_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3963_);
lean_ctor_set(v___x_3968_, 1, v___x_3967_);
v___x_3969_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
lean_ctor_set_uint8(v___x_3969_, sizeof(void*)*1, v___x_3938_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object* v_x_3970_, lean_object* v_prec_3971_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(v_x_3970_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object* v_x_3973_, lean_object* v_prec_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_VersoModuleDocs_instReprSnippet_repr(v_x_3973_, v_prec_3974_);
lean_dec(v_prec_3974_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object* v_x_3976_, lean_object* v_x_3977_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_x_3976_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object* v_x_3979_, lean_object* v_x_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(v_x_3979_, v_x_3980_);
lean_dec(v_x_3980_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_3982_, lean_object* v_prec_3983_){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_x_3982_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_x_3985_, lean_object* v_prec_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(v_x_3985_, v_prec_3986_);
lean_dec(v_prec_3986_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object* v_x_3988_, lean_object* v_prec_3989_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_x_3988_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_x_3991_, lean_object* v_prec_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(v_x_3991_, v_prec_3992_);
lean_dec(v_prec_3992_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object* v_x_3994_, lean_object* v_x_3995_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3994_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object* v_x_3997_, lean_object* v_x_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(v_x_3997_, v_x_3998_);
lean_dec(v_x_3998_);
lean_dec(v_x_3997_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object* v_x_4000_, lean_object* v_prec_4001_){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_x_4000_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object* v_x_4003_, lean_object* v_prec_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(v_x_4003_, v_prec_4004_);
lean_dec(v_prec_4004_);
return v_res_4005_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object* v_level_4008_, lean_object* v_snippet_4009_){
_start:
{
lean_object* v_sections_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v_sections_4010_ = lean_ctor_get(v_snippet_4009_, 1);
v___x_4011_ = lean_unsigned_to_nat(0u);
v___x_4012_ = lean_array_get_size(v_sections_4010_);
v___x_4013_ = lean_nat_dec_lt(v___x_4011_, v___x_4012_);
if (v___x_4013_ == 0)
{
uint8_t v___x_4014_; 
v___x_4014_ = 1;
return v___x_4014_;
}
else
{
lean_object* v___x_4015_; lean_object* v_fst_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; uint8_t v___x_4019_; 
v___x_4015_ = lean_array_fget_borrowed(v_sections_4010_, v___x_4011_);
v_fst_4016_ = lean_ctor_get(v___x_4015_, 0);
v___x_4017_ = lean_unsigned_to_nat(1u);
v___x_4018_ = lean_nat_add(v_level_4008_, v___x_4017_);
v___x_4019_ = lean_nat_dec_le(v_fst_4016_, v___x_4018_);
lean_dec(v___x_4018_);
return v___x_4019_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object* v_level_4020_, lean_object* v_snippet_4021_){
_start:
{
uint8_t v_res_4022_; lean_object* v_r_4023_; 
v_res_4022_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_level_4020_, v_snippet_4021_);
lean_dec_ref(v_snippet_4021_);
lean_dec(v_level_4020_);
v_r_4023_ = lean_box(v_res_4022_);
return v_r_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object* v_snippet_4024_){
_start:
{
lean_object* v_sections_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; 
v_sections_4025_ = lean_ctor_get(v_snippet_4024_, 1);
v___x_4026_ = lean_array_get_size(v_sections_4025_);
v___x_4027_ = lean_unsigned_to_nat(1u);
v___x_4028_ = lean_nat_sub(v___x_4026_, v___x_4027_);
v___x_4029_ = lean_nat_dec_lt(v___x_4028_, v___x_4026_);
if (v___x_4029_ == 0)
{
lean_object* v___x_4030_; 
lean_dec(v___x_4028_);
v___x_4030_ = lean_box(0);
return v___x_4030_;
}
else
{
lean_object* v___x_4031_; lean_object* v_fst_4032_; lean_object* v___x_4033_; 
v___x_4031_ = lean_array_fget_borrowed(v_sections_4025_, v___x_4028_);
lean_dec(v___x_4028_);
v_fst_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_fst_4032_);
v___x_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4033_, 0, v_fst_4032_);
return v___x_4033_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object* v_snippet_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4034_);
lean_dec_ref(v_snippet_4034_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object* v_snippet_4036_, lean_object* v_block_4037_){
_start:
{
lean_object* v_text_4038_; lean_object* v_sections_4039_; lean_object* v_declarationRange_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; 
v_text_4038_ = lean_ctor_get(v_snippet_4036_, 0);
v_sections_4039_ = lean_ctor_get(v_snippet_4036_, 1);
v_declarationRange_4040_ = lean_ctor_get(v_snippet_4036_, 2);
v___x_4041_ = lean_array_get_size(v_sections_4039_);
v___x_4042_ = lean_unsigned_to_nat(0u);
v___x_4043_ = lean_nat_dec_eq(v___x_4041_, v___x_4042_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; 
v___x_4044_ = lean_unsigned_to_nat(1u);
v___x_4045_ = lean_nat_sub(v___x_4041_, v___x_4044_);
v___x_4046_ = lean_nat_dec_lt(v___x_4045_, v___x_4041_);
if (v___x_4046_ == 0)
{
lean_dec(v___x_4045_);
lean_dec_ref(v_block_4037_);
return v_snippet_4036_;
}
else
{
lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4090_; 
lean_inc_ref(v_declarationRange_4040_);
lean_inc_ref(v_sections_4039_);
lean_inc_ref(v_text_4038_);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_snippet_4036_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; lean_object* v_unused_4092_; lean_object* v_unused_4093_; 
v_unused_4091_ = lean_ctor_get(v_snippet_4036_, 2);
lean_dec(v_unused_4091_);
v_unused_4092_ = lean_ctor_get(v_snippet_4036_, 1);
lean_dec(v_unused_4092_);
v_unused_4093_ = lean_ctor_get(v_snippet_4036_, 0);
lean_dec(v_unused_4093_);
v___x_4048_ = v_snippet_4036_;
v_isShared_4049_ = v_isSharedCheck_4090_;
goto v_resetjp_4047_;
}
else
{
lean_dec(v_snippet_4036_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4090_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v_v_4050_; lean_object* v_snd_4051_; lean_object* v_snd_4052_; lean_object* v_fst_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4088_; 
v_v_4050_ = lean_array_fget(v_sections_4039_, v___x_4045_);
v_snd_4051_ = lean_ctor_get(v_v_4050_, 1);
lean_inc(v_snd_4051_);
v_snd_4052_ = lean_ctor_get(v_snd_4051_, 1);
lean_inc(v_snd_4052_);
v_fst_4053_ = lean_ctor_get(v_v_4050_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v_v_4050_);
if (v_isSharedCheck_4088_ == 0)
{
lean_object* v_unused_4089_; 
v_unused_4089_ = lean_ctor_get(v_v_4050_, 1);
lean_dec(v_unused_4089_);
v___x_4055_ = v_v_4050_;
v_isShared_4056_ = v_isSharedCheck_4088_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_fst_4053_);
lean_dec(v_v_4050_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4088_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v_fst_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4086_; 
v_fst_4057_ = lean_ctor_get(v_snd_4051_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v_snd_4051_);
if (v_isSharedCheck_4086_ == 0)
{
lean_object* v_unused_4087_; 
v_unused_4087_ = lean_ctor_get(v_snd_4051_, 1);
lean_dec(v_unused_4087_);
v___x_4059_ = v_snd_4051_;
v_isShared_4060_ = v_isSharedCheck_4086_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_fst_4057_);
lean_dec(v_snd_4051_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4086_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v_title_4061_; lean_object* v_titleString_4062_; lean_object* v_metadata_4063_; lean_object* v_content_4064_; lean_object* v_subParts_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4085_; 
v_title_4061_ = lean_ctor_get(v_snd_4052_, 0);
v_titleString_4062_ = lean_ctor_get(v_snd_4052_, 1);
v_metadata_4063_ = lean_ctor_get(v_snd_4052_, 2);
v_content_4064_ = lean_ctor_get(v_snd_4052_, 3);
v_subParts_4065_ = lean_ctor_get(v_snd_4052_, 4);
v_isSharedCheck_4085_ = !lean_is_exclusive(v_snd_4052_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4067_ = v_snd_4052_;
v_isShared_4068_ = v_isSharedCheck_4085_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_subParts_4065_);
lean_inc(v_content_4064_);
lean_inc(v_metadata_4063_);
lean_inc(v_titleString_4062_);
lean_inc(v_title_4061_);
lean_dec(v_snd_4052_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4085_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; lean_object* v_xs_x27_4070_; lean_object* v___x_4071_; lean_object* v___x_4073_; 
v___x_4069_ = lean_box(0);
v_xs_x27_4070_ = lean_array_fset(v_sections_4039_, v___x_4045_, v___x_4069_);
v___x_4071_ = lean_array_push(v_content_4064_, v_block_4037_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 3, v___x_4071_);
v___x_4073_ = v___x_4067_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_title_4061_);
lean_ctor_set(v_reuseFailAlloc_4084_, 1, v_titleString_4062_);
lean_ctor_set(v_reuseFailAlloc_4084_, 2, v_metadata_4063_);
lean_ctor_set(v_reuseFailAlloc_4084_, 3, v___x_4071_);
lean_ctor_set(v_reuseFailAlloc_4084_, 4, v_subParts_4065_);
v___x_4073_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_object* v___x_4075_; 
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 1, v___x_4073_);
v___x_4075_ = v___x_4059_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_fst_4057_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v___x_4073_);
v___x_4075_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4077_; 
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 1, v___x_4075_);
v___x_4077_ = v___x_4055_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_fst_4053_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v___x_4075_);
v___x_4077_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
lean_object* v___x_4078_; lean_object* v___x_4080_; 
v___x_4078_ = lean_array_fset(v_xs_x27_4070_, v___x_4045_, v___x_4077_);
lean_dec(v___x_4045_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 1, v___x_4078_);
v___x_4080_ = v___x_4048_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_text_4038_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v___x_4078_);
lean_ctor_set(v_reuseFailAlloc_4081_, 2, v_declarationRange_4040_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
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
lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4101_; 
lean_inc_ref(v_declarationRange_4040_);
lean_inc_ref(v_sections_4039_);
lean_inc_ref(v_text_4038_);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_snippet_4036_);
if (v_isSharedCheck_4101_ == 0)
{
lean_object* v_unused_4102_; lean_object* v_unused_4103_; lean_object* v_unused_4104_; 
v_unused_4102_ = lean_ctor_get(v_snippet_4036_, 2);
lean_dec(v_unused_4102_);
v_unused_4103_ = lean_ctor_get(v_snippet_4036_, 1);
lean_dec(v_unused_4103_);
v_unused_4104_ = lean_ctor_get(v_snippet_4036_, 0);
lean_dec(v_unused_4104_);
v___x_4095_ = v_snippet_4036_;
v_isShared_4096_ = v_isSharedCheck_4101_;
goto v_resetjp_4094_;
}
else
{
lean_dec(v_snippet_4036_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4101_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4097_; lean_object* v___x_4099_; 
v___x_4097_ = lean_array_push(v_text_4038_, v_block_4037_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_4097_);
v___x_4099_ = v___x_4095_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4097_);
lean_ctor_set(v_reuseFailAlloc_4100_, 1, v_sections_4039_);
lean_ctor_set(v_reuseFailAlloc_4100_, 2, v_declarationRange_4040_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object* v_snippet_4105_, lean_object* v_level_4106_, lean_object* v_range_4107_, lean_object* v_part_4108_){
_start:
{
lean_object* v_text_4109_; lean_object* v_sections_4110_; lean_object* v_declarationRange_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4121_; 
v_text_4109_ = lean_ctor_get(v_snippet_4105_, 0);
v_sections_4110_ = lean_ctor_get(v_snippet_4105_, 1);
v_declarationRange_4111_ = lean_ctor_get(v_snippet_4105_, 2);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_snippet_4105_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4113_ = v_snippet_4105_;
v_isShared_4114_ = v_isSharedCheck_4121_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_declarationRange_4111_);
lean_inc(v_sections_4110_);
lean_inc(v_text_4109_);
lean_dec(v_snippet_4105_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4121_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4119_; 
v___x_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4115_, 0, v_range_4107_);
lean_ctor_set(v___x_4115_, 1, v_part_4108_);
v___x_4116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4116_, 0, v_level_4106_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
v___x_4117_ = lean_array_push(v_sections_4110_, v___x_4116_);
if (v_isShared_4114_ == 0)
{
lean_ctor_set(v___x_4113_, 1, v___x_4117_);
v___x_4119_ = v___x_4113_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_text_4109_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v___x_4117_);
lean_ctor_set(v_reuseFailAlloc_4120_, 2, v_declarationRange_4111_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0(lean_object* v___x_4122_, lean_object* v___x_4123_, lean_object* v_x_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v___x_4128_; 
v___x_4128_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v___x_4122_, v___x_4123_, v___y_4125_, v___y_4126_, v___y_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_4129_, lean_object* v___x_4130_, lean_object* v_x_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_Lean_instToMarkdownSnippet___lam__0(v___x_4129_, v___x_4130_, v_x_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
lean_dec_ref(v___y_4133_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1(lean_object* v___x_4136_, lean_object* v___x_4137_, lean_object* v___x_4138_, lean_object* v_a_4139_, lean_object* v_x_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v___x_4144_; lean_object* v_snd_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4153_; 
v___x_4144_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v___x_4136_, v___x_4137_, v_a_4139_, v___y_4142_, v___y_4143_);
v_snd_4145_ = lean_ctor_get(v___x_4144_, 1);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4153_ == 0)
{
lean_object* v_unused_4154_; 
v_unused_4154_ = lean_ctor_get(v___x_4144_, 0);
lean_dec(v_unused_4154_);
v___x_4147_ = v___x_4144_;
v_isShared_4148_ = v_isSharedCheck_4153_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_snd_4145_);
lean_dec(v___x_4144_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4153_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4149_; lean_object* v___x_4151_; 
v___x_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4138_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 0, v___x_4149_);
v___x_4151_ = v___x_4147_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4149_);
lean_ctor_set(v_reuseFailAlloc_4152_, 1, v_snd_4145_);
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
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_4155_, lean_object* v___x_4156_, lean_object* v___x_4157_, lean_object* v_a_4158_, lean_object* v_x_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Lean_instToMarkdownSnippet___lam__1(v___x_4155_, v___x_4156_, v___x_4157_, v_a_4158_, v_x_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec_ref(v___y_4161_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2(lean_object* v___x_4164_, lean_object* v___x_4165_, lean_object* v_a_4166_, lean_object* v_x_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v___x_4171_; lean_object* v_snd_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4180_; 
v___x_4171_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_box(0), v___x_4164_, v_a_4166_, v___y_4169_, v___y_4170_);
v_snd_4172_ = lean_ctor_get(v___x_4171_, 1);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4180_ == 0)
{
lean_object* v_unused_4181_; 
v_unused_4181_ = lean_ctor_get(v___x_4171_, 0);
lean_dec(v_unused_4181_);
v___x_4174_ = v___x_4171_;
v_isShared_4175_ = v_isSharedCheck_4180_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_snd_4172_);
lean_dec(v___x_4171_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4180_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4176_; lean_object* v___x_4178_; 
v___x_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4165_);
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v___x_4176_);
v___x_4178_ = v___x_4174_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4179_, 1, v_snd_4172_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2___boxed(lean_object* v___x_4182_, lean_object* v___x_4183_, lean_object* v_a_4184_, lean_object* v_x_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_instToMarkdownSnippet___lam__2(v___x_4182_, v___x_4183_, v_a_4184_, v_x_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
lean_dec_ref(v___y_4187_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3(uint32_t v___x_4190_, lean_object* v_s_4191_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = lean_string_push(v_s_4191_, v___x_4190_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3___boxed(lean_object* v___x_4193_, lean_object* v_s_4194_){
_start:
{
uint32_t v___x_5743__boxed_4195_; lean_object* v_res_4196_; 
v___x_5743__boxed_4195_ = lean_unbox_uint32(v___x_4193_);
lean_dec(v___x_4193_);
v_res_4196_ = l_Lean_instToMarkdownSnippet___lam__3(v___x_5743__boxed_4195_, v_s_4194_);
return v_res_4196_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_4197_; lean_object* v___x_4198_; 
v___x_4197_ = 35;
v___x_4198_ = lean_box_uint32(v___x_4197_);
return v___x_4198_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___f_4200_; 
v___x_4199_ = l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1;
v___f_4200_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__3___boxed), 2, 1);
lean_closure_set(v___f_4200_, 0, v___x_4199_);
return v___f_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4(lean_object* v___x_4201_, lean_object* v___f_4202_, lean_object* v___x_4203_, lean_object* v___f_4204_, lean_object* v_a_4205_, lean_object* v_x_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v_snd_4210_; lean_object* v_fst_4211_; lean_object* v_snd_4212_; lean_object* v___x_4213_; lean_object* v___f_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v_snd_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v_snd_4222_; lean_object* v_title_4223_; lean_object* v_content_4224_; size_t v_sz_4225_; size_t v___x_4226_; lean_object* v___x_5585__overap_4227_; lean_object* v___x_4228_; lean_object* v_snd_4229_; lean_object* v___x_4230_; lean_object* v_snd_4231_; size_t v_sz_4232_; lean_object* v___x_5591__overap_4233_; lean_object* v___x_4234_; lean_object* v_snd_4235_; lean_object* v___x_4236_; lean_object* v_snd_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4245_; 
v_snd_4210_ = lean_ctor_get(v_a_4205_, 1);
lean_inc(v_snd_4210_);
v_fst_4211_ = lean_ctor_get(v_a_4205_, 0);
lean_inc(v_fst_4211_);
lean_dec_ref(v_a_4205_);
v_snd_4212_ = lean_ctor_get(v_snd_4210_, 1);
lean_inc(v_snd_4212_);
lean_dec(v_snd_4210_);
v___x_4213_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___f_4214_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___lam__4___closed__0, &l_Lean_instToMarkdownSnippet___lam__4___closed__0_once, _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0);
v___x_4215_ = lean_unsigned_to_nat(1u);
v___x_4216_ = lean_nat_add(v_fst_4211_, v___x_4215_);
lean_dec(v_fst_4211_);
v___x_4217_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_4214_, v___x_4216_, v___x_4213_);
v___x_4218_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_4217_, v___y_4209_);
lean_dec(v___x_4217_);
v_snd_4219_ = lean_ctor_get(v___x_4218_, 1);
lean_inc(v_snd_4219_);
lean_dec_ref(v___x_4218_);
v___x_4220_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0));
v___x_4221_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_4220_, v_snd_4219_);
v_snd_4222_ = lean_ctor_get(v___x_4221_, 1);
lean_inc(v_snd_4222_);
lean_dec_ref(v___x_4221_);
v_title_4223_ = lean_ctor_get(v_snd_4212_, 0);
lean_inc_ref(v_title_4223_);
v_content_4224_ = lean_ctor_get(v_snd_4212_, 3);
lean_inc_ref(v_content_4224_);
lean_dec(v_snd_4212_);
v_sz_4225_ = lean_array_size(v_title_4223_);
v___x_4226_ = ((size_t)0ULL);
lean_inc_ref(v___x_4201_);
v___x_5585__overap_4227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4201_, v_title_4223_, v___f_4202_, v_sz_4225_, v___x_4226_, v___x_4203_);
lean_inc_ref_n(v___y_4208_, 2);
v___x_4228_ = lean_apply_2(v___x_5585__overap_4227_, v___y_4208_, v_snd_4222_);
v_snd_4229_ = lean_ctor_get(v___x_4228_, 1);
lean_inc(v_snd_4229_);
lean_dec_ref(v___x_4228_);
v___x_4230_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4229_);
v_snd_4231_ = lean_ctor_get(v___x_4230_, 1);
lean_inc(v_snd_4231_);
lean_dec_ref(v___x_4230_);
v_sz_4232_ = lean_array_size(v_content_4224_);
v___x_5591__overap_4233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4201_, v_content_4224_, v___f_4204_, v_sz_4232_, v___x_4226_, v___x_4203_);
v___x_4234_ = lean_apply_2(v___x_5591__overap_4233_, v___y_4208_, v_snd_4231_);
v_snd_4235_ = lean_ctor_get(v___x_4234_, 1);
lean_inc(v_snd_4235_);
lean_dec_ref(v___x_4234_);
v___x_4236_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4235_);
v_snd_4237_ = lean_ctor_get(v___x_4236_, 1);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4245_ == 0)
{
lean_object* v_unused_4246_; 
v_unused_4246_ = lean_ctor_get(v___x_4236_, 0);
lean_dec(v_unused_4246_);
v___x_4239_ = v___x_4236_;
v_isShared_4240_ = v_isSharedCheck_4245_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_snd_4237_);
lean_dec(v___x_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4245_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4203_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v___x_4241_);
v___x_4243_ = v___x_4239_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v_snd_4237_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4___boxed(lean_object* v___x_4247_, lean_object* v___f_4248_, lean_object* v___x_4249_, lean_object* v___f_4250_, lean_object* v_a_4251_, lean_object* v_x_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Lean_instToMarkdownSnippet___lam__4(v___x_4247_, v___f_4248_, v___x_4249_, v___f_4250_, v_a_4251_, v_x_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
lean_dec_ref(v___y_4254_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5(lean_object* v___x_4257_, lean_object* v___x_4258_, lean_object* v___x_4259_, lean_object* v___f_4260_, lean_object* v_x_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_text_4264_; lean_object* v_sections_4265_; lean_object* v_snd_4267_; lean_object* v___y_4288_; lean_object* v___x_4290_; lean_object* v___x_4291_; uint8_t v___x_4292_; 
v_text_4264_ = lean_ctor_get(v_x_4261_, 0);
lean_inc_ref(v_text_4264_);
v_sections_4265_ = lean_ctor_get(v_x_4261_, 1);
lean_inc_ref(v_sections_4265_);
lean_dec_ref(v_x_4261_);
v___x_4290_ = lean_unsigned_to_nat(0u);
v___x_4291_ = lean_array_get_size(v_text_4264_);
v___x_4292_ = lean_nat_dec_lt(v___x_4290_, v___x_4291_);
if (v___x_4292_ == 0)
{
lean_dec_ref(v_text_4264_);
lean_dec_ref(v___f_4260_);
v_snd_4267_ = v___y_4263_;
goto v___jp_4266_;
}
else
{
lean_object* v___x_4293_; uint8_t v___x_4294_; 
v___x_4293_ = lean_box(0);
v___x_4294_ = lean_nat_dec_le(v___x_4291_, v___x_4291_);
if (v___x_4294_ == 0)
{
if (v___x_4292_ == 0)
{
lean_dec_ref(v_text_4264_);
lean_dec_ref(v___f_4260_);
v_snd_4267_ = v___y_4263_;
goto v___jp_4266_;
}
else
{
size_t v___x_4295_; size_t v___x_4296_; lean_object* v___x_5634__overap_4297_; lean_object* v___x_4298_; 
v___x_4295_ = ((size_t)0ULL);
v___x_4296_ = lean_usize_of_nat(v___x_4291_);
lean_inc_ref(v___x_4259_);
v___x_5634__overap_4297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4259_, v___f_4260_, v_text_4264_, v___x_4295_, v___x_4296_, v___x_4293_);
lean_inc_ref(v___y_4262_);
v___x_4298_ = lean_apply_2(v___x_5634__overap_4297_, v___y_4262_, v___y_4263_);
v___y_4288_ = v___x_4298_;
goto v___jp_4287_;
}
}
else
{
size_t v___x_4299_; size_t v___x_4300_; lean_object* v___x_5637__overap_4301_; lean_object* v___x_4302_; 
v___x_4299_ = ((size_t)0ULL);
v___x_4300_ = lean_usize_of_nat(v___x_4291_);
lean_inc_ref(v___x_4259_);
v___x_5637__overap_4301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4259_, v___f_4260_, v_text_4264_, v___x_4299_, v___x_4300_, v___x_4293_);
lean_inc_ref(v___y_4262_);
v___x_4302_ = lean_apply_2(v___x_5637__overap_4301_, v___y_4262_, v___y_4263_);
v___y_4288_ = v___x_4302_;
goto v___jp_4287_;
}
}
v___jp_4266_:
{
lean_object* v___x_4268_; lean_object* v_snd_4269_; lean_object* v___x_4270_; lean_object* v___f_4271_; lean_object* v___f_4272_; lean_object* v___f_4273_; size_t v_sz_4274_; size_t v___x_4275_; lean_object* v___x_5619__overap_4276_; lean_object* v___x_4277_; lean_object* v_snd_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
v___x_4268_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4267_);
v_snd_4269_ = lean_ctor_get(v___x_4268_, 1);
lean_inc(v_snd_4269_);
lean_dec_ref(v___x_4268_);
v___x_4270_ = lean_box(0);
lean_inc_ref(v___x_4257_);
v___f_4271_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__1___boxed), 8, 3);
lean_closure_set(v___f_4271_, 0, v___x_4257_);
lean_closure_set(v___f_4271_, 1, v___x_4258_);
lean_closure_set(v___f_4271_, 2, v___x_4270_);
v___f_4272_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_4272_, 0, v___x_4257_);
lean_closure_set(v___f_4272_, 1, v___x_4270_);
lean_inc_ref(v___x_4259_);
v___f_4273_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__4___boxed), 9, 4);
lean_closure_set(v___f_4273_, 0, v___x_4259_);
lean_closure_set(v___f_4273_, 1, v___f_4272_);
lean_closure_set(v___f_4273_, 2, v___x_4270_);
lean_closure_set(v___f_4273_, 3, v___f_4271_);
v_sz_4274_ = lean_array_size(v_sections_4265_);
v___x_4275_ = ((size_t)0ULL);
v___x_5619__overap_4276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4259_, v_sections_4265_, v___f_4273_, v_sz_4274_, v___x_4275_, v___x_4270_);
lean_inc_ref(v___y_4262_);
v___x_4277_ = lean_apply_2(v___x_5619__overap_4276_, v___y_4262_, v_snd_4269_);
v_snd_4278_ = lean_ctor_get(v___x_4277_, 1);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4285_ == 0)
{
lean_object* v_unused_4286_; 
v_unused_4286_ = lean_ctor_get(v___x_4277_, 0);
lean_dec(v_unused_4286_);
v___x_4280_ = v___x_4277_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_snd_4278_);
lean_dec(v___x_4277_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 0, v___x_4270_);
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4270_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_snd_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
v___jp_4287_:
{
lean_object* v_snd_4289_; 
v_snd_4289_ = lean_ctor_get(v___y_4288_, 1);
lean_inc(v_snd_4289_);
lean_dec_ref(v___y_4288_);
v_snd_4267_ = v_snd_4289_;
goto v___jp_4266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5___boxed(lean_object* v___x_4303_, lean_object* v___x_4304_, lean_object* v___x_4305_, lean_object* v___f_4306_, lean_object* v_x_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l_Lean_instToMarkdownSnippet___lam__5(v___x_4303_, v___x_4304_, v___x_4305_, v___f_4306_, v_x_4307_, v___y_4308_, v___y_4309_);
lean_dec_ref(v___y_4308_);
return v_res_4310_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___f_4313_; 
v___x_4311_ = l_Lean_instMarkdownBlockElabInlineElabBlock;
v___x_4312_ = l_Lean_instMarkdownInlineElabInline;
v___f_4313_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__0___boxed), 6, 2);
lean_closure_set(v___f_4313_, 0, v___x_4312_);
lean_closure_set(v___f_4313_, 1, v___x_4311_);
return v___f_4313_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___closed__1(void){
_start:
{
lean_object* v___f_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___f_4318_; 
v___f_4314_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___closed__0, &l_Lean_instToMarkdownSnippet___closed__0_once, _init_l_Lean_instToMarkdownSnippet___closed__0);
v___x_4315_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__20, &l_Lean_instMarkdownInlineElabInline___closed__20_once, _init_l_Lean_instMarkdownInlineElabInline___closed__20);
v___x_4316_ = l_Lean_instMarkdownBlockElabInlineElabBlock;
v___x_4317_ = l_Lean_instMarkdownInlineElabInline;
v___f_4318_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__5___boxed), 7, 4);
lean_closure_set(v___f_4318_, 0, v___x_4317_);
lean_closure_set(v___f_4318_, 1, v___x_4316_);
lean_closure_set(v___f_4318_, 2, v___x_4315_);
lean_closure_set(v___f_4318_, 3, v___f_4314_);
return v___f_4318_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet(void){
_start:
{
lean_object* v___f_4319_; 
v___f_4319_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___closed__1, &l_Lean_instToMarkdownSnippet___closed__1_once, _init_l_Lean_instToMarkdownSnippet___closed__1);
return v___f_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0___redArg(lean_object* v_as_4320_, lean_object* v_i_4321_){
_start:
{
lean_object* v_zero_4322_; uint8_t v_isZero_4323_; 
v_zero_4322_ = lean_unsigned_to_nat(0u);
v_isZero_4323_ = lean_nat_dec_eq(v_i_4321_, v_zero_4322_);
if (v_isZero_4323_ == 1)
{
lean_object* v___x_4324_; 
lean_dec(v_i_4321_);
v___x_4324_ = lean_box(0);
return v___x_4324_;
}
else
{
lean_object* v_one_4325_; lean_object* v_n_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v_one_4325_ = lean_unsigned_to_nat(1u);
v_n_4326_ = lean_nat_sub(v_i_4321_, v_one_4325_);
lean_dec(v_i_4321_);
v___x_4327_ = lean_array_fget_borrowed(v_as_4320_, v_n_4326_);
v___x_4328_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v___x_4327_);
if (lean_obj_tag(v___x_4328_) == 0)
{
v_i_4321_ = v_n_4326_;
goto _start;
}
else
{
lean_dec(v_n_4326_);
return v___x_4328_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0___redArg___boxed(lean_object* v_as_4330_, lean_object* v_i_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0___redArg(v_as_4330_, v_i_4331_);
lean_dec_ref(v_as_4330_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1_spec__2___redArg(lean_object* v_as_4333_, lean_object* v_i_4334_){
_start:
{
lean_object* v_zero_4335_; uint8_t v_isZero_4336_; 
v_zero_4335_ = lean_unsigned_to_nat(0u);
v_isZero_4336_ = lean_nat_dec_eq(v_i_4334_, v_zero_4335_);
if (v_isZero_4336_ == 1)
{
lean_object* v___x_4337_; 
lean_dec(v_i_4334_);
v___x_4337_ = lean_box(0);
return v___x_4337_;
}
else
{
lean_object* v_one_4338_; lean_object* v_n_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v_one_4338_ = lean_unsigned_to_nat(1u);
v_n_4339_ = lean_nat_sub(v_i_4334_, v_one_4338_);
lean_dec(v_i_4334_);
v___x_4340_ = lean_array_fget_borrowed(v_as_4333_, v_n_4339_);
v___x_4341_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1(v___x_4340_);
if (lean_obj_tag(v___x_4341_) == 0)
{
v_i_4334_ = v_n_4339_;
goto _start;
}
else
{
lean_dec(v_n_4339_);
return v___x_4341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1(lean_object* v_x_4343_){
_start:
{
if (lean_obj_tag(v_x_4343_) == 0)
{
lean_object* v_cs_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_cs_4344_ = lean_ctor_get(v_x_4343_, 0);
v___x_4345_ = lean_array_get_size(v_cs_4344_);
v___x_4346_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1_spec__2___redArg(v_cs_4344_, v___x_4345_);
return v___x_4346_;
}
else
{
lean_object* v_vs_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v_vs_4347_ = lean_ctor_get(v_x_4343_, 0);
v___x_4348_ = lean_array_get_size(v_vs_4347_);
v___x_4349_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0___redArg(v_vs_4347_, v___x_4348_);
return v___x_4349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1___boxed(lean_object* v_x_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1(v_x_4350_);
lean_dec_ref(v_x_4350_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_4352_, lean_object* v_i_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1_spec__2___redArg(v_as_4352_, v_i_4353_);
lean_dec_ref(v_as_4352_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0(lean_object* v_t_4355_){
_start:
{
lean_object* v_root_4356_; lean_object* v_tail_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v_root_4356_ = lean_ctor_get(v_t_4355_, 0);
v_tail_4357_ = lean_ctor_get(v_t_4355_, 1);
v___x_4358_ = lean_array_get_size(v_tail_4357_);
v___x_4359_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0___redArg(v_tail_4357_, v___x_4358_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v___x_4360_; 
v___x_4360_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1(v_root_4356_);
return v___x_4360_;
}
else
{
return v___x_4359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0___boxed(lean_object* v_t_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0(v_t_4361_);
lean_dec_ref(v_t_4361_);
return v_res_4362_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0(void){
_start:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4363_ = lean_unsigned_to_nat(32u);
v___x_4364_ = lean_mk_empty_array_with_capacity(v___x_4363_);
v___x_4365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4364_);
return v___x_4365_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1(void){
_start:
{
size_t v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4366_ = ((size_t)5ULL);
v___x_4367_ = lean_unsigned_to_nat(0u);
v___x_4368_ = lean_unsigned_to_nat(32u);
v___x_4369_ = lean_mk_empty_array_with_capacity(v___x_4368_);
v___x_4370_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_4371_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4371_, 0, v___x_4370_);
lean_ctor_set(v___x_4371_, 1, v___x_4369_);
lean_ctor_set(v___x_4371_, 2, v___x_4367_);
lean_ctor_set(v___x_4371_, 3, v___x_4367_);
lean_ctor_set_usize(v___x_4371_, 4, v___x_4366_);
return v___x_4371_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__2(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4372_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__1, &l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1);
v___x_4373_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0(v___x_4372_);
return v___x_4373_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__3(void){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4374_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__2, &l_Lean_instInhabitedVersoModuleDocs_default___closed__2_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__2);
v___x_4375_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__1, &l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1);
v___x_4376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
lean_ctor_set(v___x_4376_, 1, v___x_4374_);
return v___x_4376_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default(void){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__3, &l_Lean_instInhabitedVersoModuleDocs_default___closed__3_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__3);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0(lean_object* v_as_4378_, lean_object* v_i_4379_, lean_object* v_a_4380_){
_start:
{
lean_object* v___x_4381_; 
v___x_4381_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0___redArg(v_as_4378_, v_i_4379_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0___boxed(lean_object* v_as_4382_, lean_object* v_i_4383_, lean_object* v_a_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__0(v_as_4382_, v_i_4383_, v_a_4384_);
lean_dec_ref(v_as_4382_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1_spec__2(lean_object* v_as_4386_, lean_object* v_i_4387_, lean_object* v_a_4388_){
_start:
{
lean_object* v___x_4389_; 
v___x_4389_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1_spec__2___redArg(v_as_4386_, v_i_4387_);
return v___x_4389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1_spec__2___boxed(lean_object* v_as_4390_, lean_object* v_i_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0_spec__1_spec__2(v_as_4390_, v_i_4391_, v_a_4392_);
lean_dec_ref(v_as_4390_);
return v_res_4393_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs(void){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l_Lean_instInhabitedVersoModuleDocs_default;
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object* v___x_4401_, lean_object* v_v_4402_, lean_object* v_x_4403_){
_start:
{
lean_object* v_snippets_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4427_; 
v_snippets_4404_ = lean_ctor_get(v_v_4402_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_v_4402_);
if (v_isSharedCheck_4427_ == 0)
{
lean_object* v_unused_4428_; 
v_unused_4428_ = lean_ctor_get(v_v_4402_, 1);
lean_dec(v_unused_4428_);
v___x_4406_ = v_v_4402_;
v_isShared_4407_ = v_isSharedCheck_4427_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_snippets_4404_);
lean_dec(v_v_4402_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4427_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4415_; 
v___x_4408_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___x_4409_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_4410_ = lean_box(1);
v___x_4411_ = ((lean_object*)(l_Lean_instReprVersoModuleDocs___lam__0___closed__2));
v___x_4412_ = l_Lean_PersistentArray_toArray___redArg(v_snippets_4404_);
lean_dec_ref(v_snippets_4404_);
v___x_4413_ = l_Array_repr___redArg(v___x_4401_, v___x_4412_);
if (v_isShared_4407_ == 0)
{
lean_ctor_set_tag(v___x_4406_, 5);
lean_ctor_set(v___x_4406_, 1, v___x_4413_);
lean_ctor_set(v___x_4406_, 0, v___x_4411_);
v___x_4415_ = v___x_4406_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4411_);
lean_ctor_set(v_reuseFailAlloc_4426_, 1, v___x_4413_);
v___x_4415_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v___x_4416_; uint8_t v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4416_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4408_);
lean_ctor_set(v___x_4416_, 1, v___x_4415_);
v___x_4417_ = 0;
v___x_4418_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4418_, 0, v___x_4416_);
lean_ctor_set_uint8(v___x_4418_, sizeof(void*)*1, v___x_4417_);
lean_inc_ref(v___x_4418_);
v___x_4419_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4409_);
lean_ctor_set(v___x_4419_, 1, v___x_4418_);
v___x_4420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4419_);
lean_ctor_set(v___x_4420_, 1, v___x_4410_);
v___x_4421_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4420_);
lean_ctor_set(v___x_4421_, 1, v___x_4418_);
v___x_4422_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_4423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4421_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
v___x_4424_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4408_);
lean_ctor_set(v___x_4424_, 1, v___x_4423_);
v___x_4425_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
lean_ctor_set_uint8(v___x_4425_, sizeof(void*)*1, v___x_4417_);
return v___x_4425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object* v___x_4429_, lean_object* v_v_4430_, lean_object* v_x_4431_){
_start:
{
lean_object* v_res_4432_; 
v_res_4432_ = l_Lean_instReprVersoModuleDocs___lam__0(v___x_4429_, v_v_4430_, v_x_4431_);
lean_dec(v_x_4431_);
return v_res_4432_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object* v_docs_4436_){
_start:
{
lean_object* v_snippets_4437_; uint8_t v___x_4438_; 
v_snippets_4437_ = lean_ctor_get(v_docs_4436_, 0);
v___x_4438_ = l_Lean_PersistentArray_isEmpty___redArg(v_snippets_4437_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object* v_docs_4439_){
_start:
{
uint8_t v_res_4440_; lean_object* v_r_4441_; 
v_res_4440_ = l_Lean_VersoModuleDocs_isEmpty(v_docs_4439_);
lean_dec_ref(v_docs_4439_);
v_r_4441_ = lean_box(v_res_4440_);
return v_r_4441_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object* v_docs_4442_, lean_object* v_snippet_4443_){
_start:
{
lean_object* v_terminalNesting_4444_; 
v_terminalNesting_4444_ = lean_ctor_get(v_docs_4442_, 1);
if (lean_obj_tag(v_terminalNesting_4444_) == 1)
{
lean_object* v_val_4445_; uint8_t v___x_4446_; 
v_val_4445_ = lean_ctor_get(v_terminalNesting_4444_, 0);
v___x_4446_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4445_, v_snippet_4443_);
return v___x_4446_;
}
else
{
uint8_t v___x_4447_; 
v___x_4447_ = 1;
return v___x_4447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object* v_docs_4448_, lean_object* v_snippet_4449_){
_start:
{
uint8_t v_res_4450_; lean_object* v_r_4451_; 
v_res_4450_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4448_, v_snippet_4449_);
lean_dec_ref(v_snippet_4449_);
lean_dec_ref(v_docs_4448_);
v_r_4451_ = lean_box(v_res_4450_);
return v_r_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object* v_docs_4455_, lean_object* v_snippet_4456_){
_start:
{
uint8_t v___x_4457_; 
v___x_4457_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4455_, v_snippet_4456_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; 
lean_dec_ref(v_snippet_4456_);
lean_dec_ref(v_docs_4455_);
v___x_4458_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__1));
return v___x_4458_;
}
else
{
lean_object* v_snippets_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4469_; 
v_snippets_4459_ = lean_ctor_get(v_docs_4455_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v_docs_4455_);
if (v_isSharedCheck_4469_ == 0)
{
lean_object* v_unused_4470_; 
v_unused_4470_ = lean_ctor_get(v_docs_4455_, 1);
lean_dec(v_unused_4470_);
v___x_4461_ = v_docs_4455_;
v_isShared_4462_ = v_isSharedCheck_4469_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_snippets_4459_);
lean_dec(v_docs_4455_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4469_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4466_; 
lean_inc_ref(v_snippet_4456_);
v___x_4463_ = l_Lean_PersistentArray_push___redArg(v_snippets_4459_, v_snippet_4456_);
v___x_4464_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4456_);
lean_dec_ref(v_snippet_4456_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 1, v___x_4464_);
lean_ctor_set(v___x_4461_, 0, v___x_4463_);
v___x_4466_ = v___x_4461_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4463_);
lean_ctor_set(v_reuseFailAlloc_4468_, 1, v___x_4464_);
v___x_4466_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
lean_object* v___x_4467_; 
v___x_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4466_);
return v___x_4467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object* v_msg_4471_){
_start:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4472_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_4473_ = lean_panic_fn_borrowed(v___x_4472_, v_msg_4471_);
return v___x_4473_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_add_x21___closed__2(void){
_start:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4476_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__0));
v___x_4477_ = lean_unsigned_to_nat(4u);
v___x_4478_ = lean_unsigned_to_nat(328u);
v___x_4479_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__1));
v___x_4480_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__0));
v___x_4481_ = l_mkPanicMessageWithDecl(v___x_4480_, v___x_4479_, v___x_4478_, v___x_4477_, v___x_4476_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object* v_docs_4482_, lean_object* v_snippet_4483_){
_start:
{
lean_object* v_snippets_4484_; lean_object* v_terminalNesting_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4499_; 
v_snippets_4484_ = lean_ctor_get(v_docs_4482_, 0);
v_terminalNesting_4485_ = lean_ctor_get(v_docs_4482_, 1);
v_isSharedCheck_4499_ = !lean_is_exclusive(v_docs_4482_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4487_ = v_docs_4482_;
v_isShared_4488_ = v_isSharedCheck_4499_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_terminalNesting_4485_);
lean_inc(v_snippets_4484_);
lean_dec(v_docs_4482_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4499_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
if (lean_obj_tag(v_terminalNesting_4485_) == 1)
{
lean_object* v_val_4495_; uint8_t v___x_4496_; 
v_val_4495_ = lean_ctor_get(v_terminalNesting_4485_, 0);
lean_inc(v_val_4495_);
lean_dec_ref(v_terminalNesting_4485_);
v___x_4496_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4495_, v_snippet_4483_);
lean_dec(v_val_4495_);
if (v___x_4496_ == 0)
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
lean_del_object(v___x_4487_);
lean_dec_ref(v_snippets_4484_);
lean_dec_ref(v_snippet_4483_);
v___x_4497_ = lean_obj_once(&l_Lean_VersoModuleDocs_add_x21___closed__2, &l_Lean_VersoModuleDocs_add_x21___closed__2_once, _init_l_Lean_VersoModuleDocs_add_x21___closed__2);
v___x_4498_ = l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(v___x_4497_);
return v___x_4498_;
}
else
{
goto v___jp_4489_;
}
}
else
{
lean_dec(v_terminalNesting_4485_);
goto v___jp_4489_;
}
v___jp_4489_:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4493_; 
lean_inc_ref(v_snippet_4483_);
v___x_4490_ = l_Lean_PersistentArray_push___redArg(v_snippets_4484_, v_snippet_4483_);
v___x_4491_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4483_);
lean_dec_ref(v_snippet_4483_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 1, v___x_4491_);
lean_ctor_set(v___x_4487_, 0, v___x_4490_);
v___x_4493_ = v___x_4487_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4490_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v___x_4491_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object* v_ctx_4500_){
_start:
{
lean_object* v_context_4501_; lean_object* v___x_4502_; 
v_context_4501_ = lean_ctor_get(v_ctx_4500_, 2);
v___x_4502_ = lean_array_get_size(v_context_4501_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object* v_ctx_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4503_);
lean_dec_ref(v_ctx_4503_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object* v_ctx_4508_){
_start:
{
lean_object* v_content_4509_; lean_object* v_priorParts_4510_; lean_object* v_context_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4534_; 
v_content_4509_ = lean_ctor_get(v_ctx_4508_, 0);
v_priorParts_4510_ = lean_ctor_get(v_ctx_4508_, 1);
v_context_4511_ = lean_ctor_get(v_ctx_4508_, 2);
v_isSharedCheck_4534_ = !lean_is_exclusive(v_ctx_4508_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4513_ = v_ctx_4508_;
v_isShared_4514_ = v_isSharedCheck_4534_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_context_4511_);
lean_inc(v_priorParts_4510_);
lean_inc(v_content_4509_);
lean_dec(v_ctx_4508_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4534_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4515_ = lean_array_get_size(v_context_4511_);
v___x_4516_ = lean_unsigned_to_nat(0u);
v___x_4517_ = lean_nat_dec_eq(v___x_4515_, v___x_4516_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v_last_4520_; lean_object* v_content_4521_; lean_object* v_priorParts_4522_; lean_object* v_titleString_4523_; lean_object* v_title_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4530_; 
v___x_4518_ = lean_unsigned_to_nat(1u);
v___x_4519_ = lean_nat_sub(v___x_4515_, v___x_4518_);
v_last_4520_ = lean_array_fget_borrowed(v_context_4511_, v___x_4519_);
lean_dec(v___x_4519_);
v_content_4521_ = lean_ctor_get(v_last_4520_, 0);
lean_inc_ref(v_content_4521_);
v_priorParts_4522_ = lean_ctor_get(v_last_4520_, 1);
v_titleString_4523_ = lean_ctor_get(v_last_4520_, 2);
v_title_4524_ = lean_ctor_get(v_last_4520_, 3);
v___x_4525_ = lean_box(0);
lean_inc_ref(v_titleString_4523_);
lean_inc_ref(v_title_4524_);
v___x_4526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4526_, 0, v_title_4524_);
lean_ctor_set(v___x_4526_, 1, v_titleString_4523_);
lean_ctor_set(v___x_4526_, 2, v___x_4525_);
lean_ctor_set(v___x_4526_, 3, v_content_4509_);
lean_ctor_set(v___x_4526_, 4, v_priorParts_4510_);
lean_inc_ref(v_priorParts_4522_);
v___x_4527_ = lean_array_push(v_priorParts_4522_, v___x_4526_);
v___x_4528_ = lean_array_pop(v_context_4511_);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 2, v___x_4528_);
lean_ctor_set(v___x_4513_, 1, v___x_4527_);
lean_ctor_set(v___x_4513_, 0, v_content_4521_);
v___x_4530_ = v___x_4513_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_content_4521_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v___x_4527_);
lean_ctor_set(v_reuseFailAlloc_4532_, 2, v___x_4528_);
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
else
{
lean_object* v___x_4533_; 
lean_del_object(v___x_4513_);
lean_dec_ref(v_context_4511_);
lean_dec_ref(v_priorParts_4510_);
lean_dec_ref(v_content_4509_);
v___x_4533_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1));
return v___x_4533_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object* v_ctx_4535_){
_start:
{
lean_object* v_context_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
v_context_4536_ = lean_ctor_get(v_ctx_4535_, 2);
v___x_4537_ = lean_array_get_size(v_context_4536_);
v___x_4538_ = lean_unsigned_to_nat(0u);
v___x_4539_ = lean_nat_dec_eq(v___x_4537_, v___x_4538_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; 
v___x_4540_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4535_);
if (lean_obj_tag(v___x_4540_) == 0)
{
return v___x_4540_;
}
else
{
lean_object* v_a_4541_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
lean_inc(v_a_4541_);
lean_dec_ref(v___x_4540_);
v_ctx_4535_ = v_a_4541_;
goto _start;
}
}
else
{
lean_object* v___x_4543_; 
v___x_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4543_, 0, v_ctx_4535_);
return v___x_4543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object* v_ctx_4546_, lean_object* v_partLevel_4547_, lean_object* v_part_4548_){
_start:
{
lean_object* v___x_4549_; uint8_t v___x_4550_; 
v___x_4549_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4546_);
v___x_4550_ = lean_nat_dec_lt(v___x_4549_, v_partLevel_4547_);
if (v___x_4550_ == 0)
{
uint8_t v___x_4551_; 
v___x_4551_ = lean_nat_dec_eq(v_partLevel_4547_, v___x_4549_);
lean_dec(v___x_4549_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; 
v___x_4552_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4546_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_dec_ref(v_part_4548_);
lean_dec(v_partLevel_4547_);
return v___x_4552_;
}
else
{
lean_object* v_a_4553_; 
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
lean_inc(v_a_4553_);
lean_dec_ref(v___x_4552_);
v_ctx_4546_ = v_a_4553_;
goto _start;
}
}
else
{
lean_object* v_content_4555_; lean_object* v_priorParts_4556_; lean_object* v_context_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4566_; 
lean_dec(v_partLevel_4547_);
v_content_4555_ = lean_ctor_get(v_ctx_4546_, 0);
v_priorParts_4556_ = lean_ctor_get(v_ctx_4546_, 1);
v_context_4557_ = lean_ctor_get(v_ctx_4546_, 2);
v_isSharedCheck_4566_ = !lean_is_exclusive(v_ctx_4546_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4559_ = v_ctx_4546_;
v_isShared_4560_ = v_isSharedCheck_4566_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_context_4557_);
lean_inc(v_priorParts_4556_);
lean_inc(v_content_4555_);
lean_dec(v_ctx_4546_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4566_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4561_; lean_object* v___x_4563_; 
v___x_4561_ = lean_array_push(v_priorParts_4556_, v_part_4548_);
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 1, v___x_4561_);
v___x_4563_ = v___x_4559_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_content_4555_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v___x_4561_);
lean_ctor_set(v_reuseFailAlloc_4565_, 2, v_context_4557_);
v___x_4563_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
lean_object* v___x_4564_; 
v___x_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4563_);
return v___x_4564_;
}
}
}
}
else
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
lean_dec_ref(v_part_4548_);
lean_dec_ref(v_ctx_4546_);
v___x_4567_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0));
v___x_4568_ = l_Nat_reprFast(v___x_4549_);
v___x_4569_ = lean_string_append(v___x_4567_, v___x_4568_);
lean_dec_ref(v___x_4568_);
v___x_4570_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1));
v___x_4571_ = lean_string_append(v___x_4569_, v___x_4570_);
v___x_4572_ = l_Nat_reprFast(v_partLevel_4547_);
v___x_4573_ = lean_string_append(v___x_4571_, v___x_4572_);
lean_dec_ref(v___x_4572_);
v___x_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4573_);
return v___x_4574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object* v_ctx_4578_, lean_object* v_blocks_4579_){
_start:
{
lean_object* v_content_4580_; lean_object* v_priorParts_4581_; lean_object* v_context_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4595_; 
v_content_4580_ = lean_ctor_get(v_ctx_4578_, 0);
v_priorParts_4581_ = lean_ctor_get(v_ctx_4578_, 1);
v_context_4582_ = lean_ctor_get(v_ctx_4578_, 2);
v_isSharedCheck_4595_ = !lean_is_exclusive(v_ctx_4578_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4584_ = v_ctx_4578_;
v_isShared_4585_ = v_isSharedCheck_4595_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_context_4582_);
lean_inc(v_priorParts_4581_);
lean_inc(v_content_4580_);
lean_dec(v_ctx_4578_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4595_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; uint8_t v___x_4588_; 
v___x_4586_ = lean_array_get_size(v_priorParts_4581_);
v___x_4587_ = lean_unsigned_to_nat(0u);
v___x_4588_ = lean_nat_dec_eq(v___x_4586_, v___x_4587_);
if (v___x_4588_ == 0)
{
lean_object* v___x_4589_; 
lean_del_object(v___x_4584_);
lean_dec_ref(v_context_4582_);
lean_dec_ref(v_priorParts_4581_);
lean_dec_ref(v_content_4580_);
v___x_4589_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1));
return v___x_4589_;
}
else
{
lean_object* v___x_4590_; lean_object* v___x_4592_; 
v___x_4590_ = l_Array_append___redArg(v_content_4580_, v_blocks_4579_);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v___x_4590_);
v___x_4592_ = v___x_4584_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4590_);
lean_ctor_set(v_reuseFailAlloc_4594_, 1, v_priorParts_4581_);
lean_ctor_set(v_reuseFailAlloc_4594_, 2, v_context_4582_);
v___x_4592_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
lean_object* v___x_4593_; 
v___x_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4592_);
return v___x_4593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object* v_ctx_4596_, lean_object* v_blocks_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4596_, v_blocks_4597_);
lean_dec_ref(v_blocks_4597_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object* v_as_4599_, size_t v_sz_4600_, size_t v_i_4601_, lean_object* v_b_4602_){
_start:
{
uint8_t v___x_4603_; 
v___x_4603_ = lean_usize_dec_lt(v_i_4601_, v_sz_4600_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; 
v___x_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4604_, 0, v_b_4602_);
return v___x_4604_;
}
else
{
lean_object* v_a_4605_; lean_object* v_snd_4606_; lean_object* v_fst_4607_; lean_object* v_snd_4608_; lean_object* v___x_4609_; 
v_a_4605_ = lean_array_uget_borrowed(v_as_4599_, v_i_4601_);
v_snd_4606_ = lean_ctor_get(v_a_4605_, 1);
v_fst_4607_ = lean_ctor_get(v_a_4605_, 0);
v_snd_4608_ = lean_ctor_get(v_snd_4606_, 1);
lean_inc(v_snd_4608_);
lean_inc(v_fst_4607_);
v___x_4609_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(v_b_4602_, v_fst_4607_, v_snd_4608_);
if (lean_obj_tag(v___x_4609_) == 0)
{
return v___x_4609_;
}
else
{
lean_object* v_a_4610_; size_t v___x_4611_; size_t v___x_4612_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc(v_a_4610_);
lean_dec_ref(v___x_4609_);
v___x_4611_ = ((size_t)1ULL);
v___x_4612_ = lean_usize_add(v_i_4601_, v___x_4611_);
v_i_4601_ = v___x_4612_;
v_b_4602_ = v_a_4610_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object* v_as_4614_, lean_object* v_sz_4615_, lean_object* v_i_4616_, lean_object* v_b_4617_){
_start:
{
size_t v_sz_boxed_4618_; size_t v_i_boxed_4619_; lean_object* v_res_4620_; 
v_sz_boxed_4618_ = lean_unbox_usize(v_sz_4615_);
lean_dec(v_sz_4615_);
v_i_boxed_4619_ = lean_unbox_usize(v_i_4616_);
lean_dec(v_i_4616_);
v_res_4620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_as_4614_, v_sz_boxed_4618_, v_i_boxed_4619_, v_b_4617_);
lean_dec_ref(v_as_4614_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object* v_ctx_4621_, lean_object* v_snippet_4622_){
_start:
{
lean_object* v_text_4623_; lean_object* v_sections_4624_; lean_object* v___x_4625_; 
v_text_4623_ = lean_ctor_get(v_snippet_4622_, 0);
v_sections_4624_ = lean_ctor_get(v_snippet_4622_, 1);
v___x_4625_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4621_, v_text_4623_);
if (lean_obj_tag(v___x_4625_) == 0)
{
return v___x_4625_;
}
else
{
lean_object* v_a_4626_; size_t v_sz_4627_; size_t v___x_4628_; lean_object* v___x_4629_; 
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
lean_inc(v_a_4626_);
lean_dec_ref(v___x_4625_);
v_sz_4627_ = lean_array_size(v_sections_4624_);
v___x_4628_ = ((size_t)0ULL);
v___x_4629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_sections_4624_, v_sz_4627_, v___x_4628_, v_a_4626_);
return v___x_4629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object* v_ctx_4630_, lean_object* v_snippet_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_ctx_4630_, v_snippet_4631_);
lean_dec_ref(v_snippet_4631_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object* v_as_4633_, size_t v_sz_4634_, size_t v_i_4635_, lean_object* v_b_4636_){
_start:
{
uint8_t v___x_4637_; 
v___x_4637_ = lean_usize_dec_lt(v_i_4635_, v_sz_4634_);
if (v___x_4637_ == 0)
{
lean_object* v___x_4638_; 
v___x_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4638_, 0, v_b_4636_);
return v___x_4638_;
}
else
{
lean_object* v_snd_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4661_; 
v_snd_4639_ = lean_ctor_get(v_b_4636_, 1);
v_isSharedCheck_4661_ = !lean_is_exclusive(v_b_4636_);
if (v_isSharedCheck_4661_ == 0)
{
lean_object* v_unused_4662_; 
v_unused_4662_ = lean_ctor_get(v_b_4636_, 0);
lean_dec(v_unused_4662_);
v___x_4641_ = v_b_4636_;
v_isShared_4642_ = v_isSharedCheck_4661_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_snd_4639_);
lean_dec(v_b_4636_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4661_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v_a_4643_; lean_object* v___x_4644_; 
v_a_4643_ = lean_array_uget_borrowed(v_as_4633_, v_i_4635_);
v___x_4644_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4639_, v_a_4643_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
lean_del_object(v___x_4641_);
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4647_ = v___x_4644_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4644_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
else
{
lean_object* v_a_4653_; lean_object* v___x_4654_; lean_object* v___x_4656_; 
v_a_4653_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4653_);
lean_dec_ref(v___x_4644_);
v___x_4654_ = lean_box(0);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 1, v_a_4653_);
lean_ctor_set(v___x_4641_, 0, v___x_4654_);
v___x_4656_ = v___x_4641_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4654_);
lean_ctor_set(v_reuseFailAlloc_4660_, 1, v_a_4653_);
v___x_4656_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
size_t v___x_4657_; size_t v___x_4658_; 
v___x_4657_ = ((size_t)1ULL);
v___x_4658_ = lean_usize_add(v_i_4635_, v___x_4657_);
v_i_4635_ = v___x_4658_;
v_b_4636_ = v___x_4656_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4663_, lean_object* v_sz_4664_, lean_object* v_i_4665_, lean_object* v_b_4666_){
_start:
{
size_t v_sz_boxed_4667_; size_t v_i_boxed_4668_; lean_object* v_res_4669_; 
v_sz_boxed_4667_ = lean_unbox_usize(v_sz_4664_);
lean_dec(v_sz_4664_);
v_i_boxed_4668_ = lean_unbox_usize(v_i_4665_);
lean_dec(v_i_4665_);
v_res_4669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4663_, v_sz_boxed_4667_, v_i_boxed_4668_, v_b_4666_);
lean_dec_ref(v_as_4663_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object* v_as_4670_, size_t v_sz_4671_, size_t v_i_4672_, lean_object* v_b_4673_){
_start:
{
uint8_t v___x_4674_; 
v___x_4674_ = lean_usize_dec_lt(v_i_4672_, v_sz_4671_);
if (v___x_4674_ == 0)
{
lean_object* v___x_4675_; 
v___x_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4675_, 0, v_b_4673_);
return v___x_4675_;
}
else
{
lean_object* v_snd_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4698_; 
v_snd_4676_ = lean_ctor_get(v_b_4673_, 1);
v_isSharedCheck_4698_ = !lean_is_exclusive(v_b_4673_);
if (v_isSharedCheck_4698_ == 0)
{
lean_object* v_unused_4699_; 
v_unused_4699_ = lean_ctor_get(v_b_4673_, 0);
lean_dec(v_unused_4699_);
v___x_4678_ = v_b_4673_;
v_isShared_4679_ = v_isSharedCheck_4698_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_snd_4676_);
lean_dec(v_b_4673_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4698_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v_a_4680_; lean_object* v___x_4681_; 
v_a_4680_ = lean_array_uget_borrowed(v_as_4670_, v_i_4672_);
v___x_4681_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4676_, v_a_4680_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4689_; 
lean_del_object(v___x_4678_);
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4684_ = v___x_4681_;
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4681_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
else
{
lean_object* v_a_4690_; lean_object* v___x_4691_; lean_object* v___x_4693_; 
v_a_4690_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4690_);
lean_dec_ref(v___x_4681_);
v___x_4691_ = lean_box(0);
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 1, v_a_4690_);
lean_ctor_set(v___x_4678_, 0, v___x_4691_);
v___x_4693_ = v___x_4678_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4691_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v_a_4690_);
v___x_4693_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
size_t v___x_4694_; size_t v___x_4695_; lean_object* v___x_4696_; 
v___x_4694_ = ((size_t)1ULL);
v___x_4695_ = lean_usize_add(v_i_4672_, v___x_4694_);
v___x_4696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4670_, v_sz_4671_, v___x_4695_, v___x_4693_);
return v___x_4696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object* v_as_4700_, lean_object* v_sz_4701_, lean_object* v_i_4702_, lean_object* v_b_4703_){
_start:
{
size_t v_sz_boxed_4704_; size_t v_i_boxed_4705_; lean_object* v_res_4706_; 
v_sz_boxed_4704_ = lean_unbox_usize(v_sz_4701_);
lean_dec(v_sz_4701_);
v_i_boxed_4705_ = lean_unbox_usize(v_i_4702_);
lean_dec(v_i_4702_);
v_res_4706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_as_4700_, v_sz_boxed_4704_, v_i_boxed_4705_, v_b_4703_);
lean_dec_ref(v_as_4700_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_4707_, size_t v_sz_4708_, size_t v_i_4709_, lean_object* v_b_4710_){
_start:
{
uint8_t v___x_4711_; 
v___x_4711_ = lean_usize_dec_lt(v_i_4709_, v_sz_4708_);
if (v___x_4711_ == 0)
{
lean_object* v___x_4712_; 
v___x_4712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4712_, 0, v_b_4710_);
return v___x_4712_;
}
else
{
lean_object* v_snd_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4735_; 
v_snd_4713_ = lean_ctor_get(v_b_4710_, 1);
v_isSharedCheck_4735_ = !lean_is_exclusive(v_b_4710_);
if (v_isSharedCheck_4735_ == 0)
{
lean_object* v_unused_4736_; 
v_unused_4736_ = lean_ctor_get(v_b_4710_, 0);
lean_dec(v_unused_4736_);
v___x_4715_ = v_b_4710_;
v_isShared_4716_ = v_isSharedCheck_4735_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_snd_4713_);
lean_dec(v_b_4710_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4735_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v_a_4717_; lean_object* v___x_4718_; 
v_a_4717_ = lean_array_uget_borrowed(v_as_4707_, v_i_4709_);
v___x_4718_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4713_, v_a_4717_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4726_; 
lean_del_object(v___x_4715_);
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4721_ = v___x_4718_;
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4718_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4724_; 
if (v_isShared_4722_ == 0)
{
v___x_4724_ = v___x_4721_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4719_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
else
{
lean_object* v_a_4727_; lean_object* v___x_4728_; lean_object* v___x_4730_; 
v_a_4727_ = lean_ctor_get(v___x_4718_, 0);
lean_inc(v_a_4727_);
lean_dec_ref(v___x_4718_);
v___x_4728_ = lean_box(0);
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 1, v_a_4727_);
lean_ctor_set(v___x_4715_, 0, v___x_4728_);
v___x_4730_ = v___x_4715_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4728_);
lean_ctor_set(v_reuseFailAlloc_4734_, 1, v_a_4727_);
v___x_4730_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
size_t v___x_4731_; size_t v___x_4732_; 
v___x_4731_ = ((size_t)1ULL);
v___x_4732_ = lean_usize_add(v_i_4709_, v___x_4731_);
v_i_4709_ = v___x_4732_;
v_b_4710_ = v___x_4730_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_4737_, lean_object* v_sz_4738_, lean_object* v_i_4739_, lean_object* v_b_4740_){
_start:
{
size_t v_sz_boxed_4741_; size_t v_i_boxed_4742_; lean_object* v_res_4743_; 
v_sz_boxed_4741_ = lean_unbox_usize(v_sz_4738_);
lean_dec(v_sz_4738_);
v_i_boxed_4742_ = lean_unbox_usize(v_i_4739_);
lean_dec(v_i_4739_);
v_res_4743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4737_, v_sz_boxed_4741_, v_i_boxed_4742_, v_b_4740_);
lean_dec_ref(v_as_4737_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object* v_as_4744_, size_t v_sz_4745_, size_t v_i_4746_, lean_object* v_b_4747_){
_start:
{
uint8_t v___x_4748_; 
v___x_4748_ = lean_usize_dec_lt(v_i_4746_, v_sz_4745_);
if (v___x_4748_ == 0)
{
lean_object* v___x_4749_; 
v___x_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4749_, 0, v_b_4747_);
return v___x_4749_;
}
else
{
lean_object* v_snd_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4772_; 
v_snd_4750_ = lean_ctor_get(v_b_4747_, 1);
v_isSharedCheck_4772_ = !lean_is_exclusive(v_b_4747_);
if (v_isSharedCheck_4772_ == 0)
{
lean_object* v_unused_4773_; 
v_unused_4773_ = lean_ctor_get(v_b_4747_, 0);
lean_dec(v_unused_4773_);
v___x_4752_ = v_b_4747_;
v_isShared_4753_ = v_isSharedCheck_4772_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_snd_4750_);
lean_dec(v_b_4747_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4772_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v_a_4754_; lean_object* v___x_4755_; 
v_a_4754_ = lean_array_uget_borrowed(v_as_4744_, v_i_4746_);
v___x_4755_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4750_, v_a_4754_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_del_object(v___x_4752_);
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4755_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4755_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4765_; lean_object* v___x_4767_; 
v_a_4764_ = lean_ctor_get(v___x_4755_, 0);
lean_inc(v_a_4764_);
lean_dec_ref(v___x_4755_);
v___x_4765_ = lean_box(0);
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 1, v_a_4764_);
lean_ctor_set(v___x_4752_, 0, v___x_4765_);
v___x_4767_ = v___x_4752_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v___x_4765_);
lean_ctor_set(v_reuseFailAlloc_4771_, 1, v_a_4764_);
v___x_4767_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
size_t v___x_4768_; size_t v___x_4769_; lean_object* v___x_4770_; 
v___x_4768_ = ((size_t)1ULL);
v___x_4769_ = lean_usize_add(v_i_4746_, v___x_4768_);
v___x_4770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4744_, v_sz_4745_, v___x_4769_, v___x_4767_);
return v___x_4770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4774_, lean_object* v_sz_4775_, lean_object* v_i_4776_, lean_object* v_b_4777_){
_start:
{
size_t v_sz_boxed_4778_; size_t v_i_boxed_4779_; lean_object* v_res_4780_; 
v_sz_boxed_4778_ = lean_unbox_usize(v_sz_4775_);
lean_dec(v_sz_4775_);
v_i_boxed_4779_ = lean_unbox_usize(v_i_4776_);
lean_dec(v_i_4776_);
v_res_4780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_as_4774_, v_sz_boxed_4778_, v_i_boxed_4779_, v_b_4777_);
lean_dec_ref(v_as_4774_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object* v_init_4781_, lean_object* v_n_4782_, lean_object* v_b_4783_){
_start:
{
if (lean_obj_tag(v_n_4782_) == 0)
{
lean_object* v_cs_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4818_; 
v_cs_4784_ = lean_ctor_get(v_n_4782_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v_n_4782_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4786_ = v_n_4782_;
v_isShared_4787_ = v_isSharedCheck_4818_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_cs_4784_);
lean_dec(v_n_4782_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4818_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; size_t v_sz_4790_; size_t v___x_4791_; lean_object* v___x_4792_; 
v___x_4788_ = lean_box(0);
v___x_4789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4788_);
lean_ctor_set(v___x_4789_, 1, v_b_4783_);
v_sz_4790_ = lean_array_size(v_cs_4784_);
v___x_4791_ = ((size_t)0ULL);
v___x_4792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_4781_, v_cs_4784_, v_sz_4790_, v___x_4791_, v___x_4789_);
lean_dec_ref(v_cs_4784_);
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
lean_del_object(v___x_4786_);
v_a_4793_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4792_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4792_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4817_; 
v_a_4801_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4803_ = v___x_4792_;
v_isShared_4804_ = v_isSharedCheck_4817_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4792_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4817_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v_fst_4805_; 
v_fst_4805_ = lean_ctor_get(v_a_4801_, 0);
if (lean_obj_tag(v_fst_4805_) == 0)
{
lean_object* v_snd_4806_; lean_object* v___x_4808_; 
v_snd_4806_ = lean_ctor_get(v_a_4801_, 1);
lean_inc(v_snd_4806_);
lean_dec(v_a_4801_);
if (v_isShared_4787_ == 0)
{
lean_ctor_set_tag(v___x_4786_, 1);
lean_ctor_set(v___x_4786_, 0, v_snd_4806_);
v___x_4808_ = v___x_4786_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_snd_4806_);
v___x_4808_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
lean_object* v___x_4810_; 
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 0, v___x_4808_);
v___x_4810_ = v___x_4803_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v___x_4808_);
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
lean_object* v_val_4813_; lean_object* v___x_4815_; 
lean_inc_ref(v_fst_4805_);
lean_dec(v_a_4801_);
lean_del_object(v___x_4786_);
v_val_4813_ = lean_ctor_get(v_fst_4805_, 0);
lean_inc(v_val_4813_);
lean_dec_ref(v_fst_4805_);
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 0, v_val_4813_);
v___x_4815_ = v___x_4803_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_val_4813_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
}
}
}
else
{
lean_object* v_vs_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4853_; 
v_vs_4819_ = lean_ctor_get(v_n_4782_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v_n_4782_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4821_ = v_n_4782_;
v_isShared_4822_ = v_isSharedCheck_4853_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_vs_4819_);
lean_dec(v_n_4782_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4853_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4823_; lean_object* v___x_4824_; size_t v_sz_4825_; size_t v___x_4826_; lean_object* v___x_4827_; 
v___x_4823_ = lean_box(0);
v___x_4824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4823_);
lean_ctor_set(v___x_4824_, 1, v_b_4783_);
v_sz_4825_ = lean_array_size(v_vs_4819_);
v___x_4826_ = ((size_t)0ULL);
v___x_4827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_vs_4819_, v_sz_4825_, v___x_4826_, v___x_4824_);
lean_dec_ref(v_vs_4819_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
lean_del_object(v___x_4821_);
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4827_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4827_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
else
{
lean_object* v_a_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4852_; 
v_a_4836_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4838_ = v___x_4827_;
v_isShared_4839_ = v_isSharedCheck_4852_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_a_4836_);
lean_dec(v___x_4827_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4852_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v_fst_4840_; 
v_fst_4840_ = lean_ctor_get(v_a_4836_, 0);
if (lean_obj_tag(v_fst_4840_) == 0)
{
lean_object* v_snd_4841_; lean_object* v___x_4843_; 
v_snd_4841_ = lean_ctor_get(v_a_4836_, 1);
lean_inc(v_snd_4841_);
lean_dec(v_a_4836_);
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 0, v_snd_4841_);
v___x_4843_ = v___x_4821_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_snd_4841_);
v___x_4843_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
lean_object* v___x_4845_; 
if (v_isShared_4839_ == 0)
{
lean_ctor_set(v___x_4838_, 0, v___x_4843_);
v___x_4845_ = v___x_4838_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4843_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
else
{
lean_object* v_val_4848_; lean_object* v___x_4850_; 
lean_inc_ref(v_fst_4840_);
lean_dec(v_a_4836_);
lean_del_object(v___x_4821_);
v_val_4848_ = lean_ctor_get(v_fst_4840_, 0);
lean_inc(v_val_4848_);
lean_dec_ref(v_fst_4840_);
if (v_isShared_4839_ == 0)
{
lean_ctor_set(v___x_4838_, 0, v_val_4848_);
v___x_4850_ = v___x_4838_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_val_4848_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object* v_init_4854_, lean_object* v_as_4855_, size_t v_sz_4856_, size_t v_i_4857_, lean_object* v_b_4858_){
_start:
{
uint8_t v___x_4859_; 
v___x_4859_ = lean_usize_dec_lt(v_i_4857_, v_sz_4856_);
if (v___x_4859_ == 0)
{
lean_object* v___x_4860_; 
v___x_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4860_, 0, v_b_4858_);
return v___x_4860_;
}
else
{
lean_object* v_snd_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4895_; 
v_snd_4861_ = lean_ctor_get(v_b_4858_, 1);
v_isSharedCheck_4895_ = !lean_is_exclusive(v_b_4858_);
if (v_isSharedCheck_4895_ == 0)
{
lean_object* v_unused_4896_; 
v_unused_4896_ = lean_ctor_get(v_b_4858_, 0);
lean_dec(v_unused_4896_);
v___x_4863_ = v_b_4858_;
v_isShared_4864_ = v_isSharedCheck_4895_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_snd_4861_);
lean_dec(v_b_4858_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4895_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v_a_4865_; lean_object* v___x_4866_; 
v_a_4865_ = lean_array_uget_borrowed(v_as_4855_, v_i_4857_);
lean_inc(v_snd_4861_);
lean_inc(v_a_4865_);
v___x_4866_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4854_, v_a_4865_, v_snd_4861_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4874_; 
lean_del_object(v___x_4863_);
lean_dec(v_snd_4861_);
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4869_ = v___x_4866_;
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4866_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4872_; 
if (v_isShared_4870_ == 0)
{
v___x_4872_ = v___x_4869_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4867_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
else
{
lean_object* v_a_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4894_; 
v_a_4875_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4877_ = v___x_4866_;
v_isShared_4878_ = v_isSharedCheck_4894_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_a_4875_);
lean_dec(v___x_4866_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4894_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
if (lean_obj_tag(v_a_4875_) == 0)
{
lean_object* v___x_4879_; lean_object* v___x_4881_; 
v___x_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4879_, 0, v_a_4875_);
if (v_isShared_4864_ == 0)
{
lean_ctor_set(v___x_4863_, 0, v___x_4879_);
v___x_4881_ = v___x_4863_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v___x_4879_);
lean_ctor_set(v_reuseFailAlloc_4885_, 1, v_snd_4861_);
v___x_4881_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
lean_object* v___x_4883_; 
if (v_isShared_4878_ == 0)
{
lean_ctor_set(v___x_4877_, 0, v___x_4881_);
v___x_4883_ = v___x_4877_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4881_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
else
{
lean_object* v_a_4886_; lean_object* v___x_4887_; lean_object* v___x_4889_; 
lean_del_object(v___x_4877_);
lean_dec(v_snd_4861_);
v_a_4886_ = lean_ctor_get(v_a_4875_, 0);
lean_inc(v_a_4886_);
lean_dec_ref(v_a_4875_);
v___x_4887_ = lean_box(0);
if (v_isShared_4864_ == 0)
{
lean_ctor_set(v___x_4863_, 1, v_a_4886_);
lean_ctor_set(v___x_4863_, 0, v___x_4887_);
v___x_4889_ = v___x_4863_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4887_);
lean_ctor_set(v_reuseFailAlloc_4893_, 1, v_a_4886_);
v___x_4889_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
size_t v___x_4890_; size_t v___x_4891_; 
v___x_4890_ = ((size_t)1ULL);
v___x_4891_ = lean_usize_add(v_i_4857_, v___x_4890_);
v_i_4857_ = v___x_4891_;
v_b_4858_ = v___x_4889_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4897_, lean_object* v_as_4898_, lean_object* v_sz_4899_, lean_object* v_i_4900_, lean_object* v_b_4901_){
_start:
{
size_t v_sz_boxed_4902_; size_t v_i_boxed_4903_; lean_object* v_res_4904_; 
v_sz_boxed_4902_ = lean_unbox_usize(v_sz_4899_);
lean_dec(v_sz_4899_);
v_i_boxed_4903_ = lean_unbox_usize(v_i_4900_);
lean_dec(v_i_4900_);
v_res_4904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_4897_, v_as_4898_, v_sz_boxed_4902_, v_i_boxed_4903_, v_b_4901_);
lean_dec_ref(v_as_4898_);
lean_dec_ref(v_init_4897_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object* v_init_4905_, lean_object* v_n_4906_, lean_object* v_b_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4905_, v_n_4906_, v_b_4907_);
lean_dec_ref(v_init_4905_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object* v_t_4909_, lean_object* v_init_4910_){
_start:
{
lean_object* v_root_4911_; lean_object* v_tail_4912_; lean_object* v___x_4913_; 
v_root_4911_ = lean_ctor_get(v_t_4909_, 0);
lean_inc_ref(v_root_4911_);
v_tail_4912_ = lean_ctor_get(v_t_4909_, 1);
lean_inc_ref(v_tail_4912_);
lean_dec_ref(v_t_4909_);
lean_inc_ref(v_init_4910_);
v___x_4913_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4910_, v_root_4911_, v_init_4910_);
lean_dec_ref(v_init_4910_);
if (lean_obj_tag(v___x_4913_) == 0)
{
lean_object* v_a_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4921_; 
lean_dec_ref(v_tail_4912_);
v_a_4914_ = lean_ctor_get(v___x_4913_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4916_ = v___x_4913_;
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___x_4913_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4919_; 
if (v_isShared_4917_ == 0)
{
v___x_4919_ = v___x_4916_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4914_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
else
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4958_; 
v_a_4922_ = lean_ctor_get(v___x_4913_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4924_ = v___x_4913_;
v_isShared_4925_ = v_isSharedCheck_4958_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4913_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4958_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
if (lean_obj_tag(v_a_4922_) == 0)
{
lean_object* v_a_4926_; lean_object* v___x_4928_; 
lean_dec_ref(v_tail_4912_);
v_a_4926_ = lean_ctor_get(v_a_4922_, 0);
lean_inc(v_a_4926_);
lean_dec_ref(v_a_4922_);
if (v_isShared_4925_ == 0)
{
lean_ctor_set(v___x_4924_, 0, v_a_4926_);
v___x_4928_ = v___x_4924_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4926_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
else
{
lean_object* v_a_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; size_t v_sz_4933_; size_t v___x_4934_; lean_object* v___x_4935_; 
lean_del_object(v___x_4924_);
v_a_4930_ = lean_ctor_get(v_a_4922_, 0);
lean_inc(v_a_4930_);
lean_dec_ref(v_a_4922_);
v___x_4931_ = lean_box(0);
v___x_4932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4932_, 0, v___x_4931_);
lean_ctor_set(v___x_4932_, 1, v_a_4930_);
v_sz_4933_ = lean_array_size(v_tail_4912_);
v___x_4934_ = ((size_t)0ULL);
v___x_4935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_tail_4912_, v_sz_4933_, v___x_4934_, v___x_4932_);
lean_dec_ref(v_tail_4912_);
if (lean_obj_tag(v___x_4935_) == 0)
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
v_a_4936_ = lean_ctor_get(v___x_4935_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4935_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4938_ = v___x_4935_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___x_4935_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4941_; 
if (v_isShared_4939_ == 0)
{
v___x_4941_ = v___x_4938_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4936_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
else
{
lean_object* v_a_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4957_; 
v_a_4944_ = lean_ctor_get(v___x_4935_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4935_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4946_ = v___x_4935_;
v_isShared_4947_ = v_isSharedCheck_4957_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_a_4944_);
lean_dec(v___x_4935_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4957_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v_fst_4948_; 
v_fst_4948_ = lean_ctor_get(v_a_4944_, 0);
if (lean_obj_tag(v_fst_4948_) == 0)
{
lean_object* v_snd_4949_; lean_object* v___x_4951_; 
v_snd_4949_ = lean_ctor_get(v_a_4944_, 1);
lean_inc(v_snd_4949_);
lean_dec(v_a_4944_);
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 0, v_snd_4949_);
v___x_4951_ = v___x_4946_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_snd_4949_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
else
{
lean_object* v_val_4953_; lean_object* v___x_4955_; 
lean_inc_ref(v_fst_4948_);
lean_dec(v_a_4944_);
v_val_4953_ = lean_ctor_get(v_fst_4948_, 0);
lean_inc(v_val_4953_);
lean_dec_ref(v_fst_4948_);
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 0, v_val_4953_);
v___x_4955_ = v___x_4946_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_val_4953_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object* v_docs_4961_){
_start:
{
lean_object* v_snippets_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_4999_; 
v_snippets_4962_ = lean_ctor_get(v_docs_4961_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v_docs_4961_);
if (v_isSharedCheck_4999_ == 0)
{
lean_object* v_unused_5000_; 
v_unused_5000_ = lean_ctor_get(v_docs_4961_, 1);
lean_dec(v_unused_5000_);
v___x_4964_ = v_docs_4961_;
v_isShared_4965_ = v_isSharedCheck_4999_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_snippets_4962_);
lean_dec(v_docs_4961_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_4999_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v_ctx_4966_; lean_object* v___x_4967_; 
v_ctx_4966_ = ((lean_object*)(l_Lean_VersoModuleDocs_assemble___closed__0));
v___x_4967_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_snippets_4962_, v_ctx_4966_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4975_; 
lean_del_object(v___x_4964_);
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4970_ = v___x_4967_;
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4967_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4973_; 
if (v_isShared_4971_ == 0)
{
v___x_4973_ = v___x_4970_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4968_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4977_; 
v_a_4976_ = lean_ctor_get(v___x_4967_, 0);
lean_inc(v_a_4976_);
lean_dec_ref(v___x_4967_);
v___x_4977_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(v_a_4976_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_a_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4985_; 
lean_del_object(v___x_4964_);
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4980_ = v___x_4977_;
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_a_4978_);
lean_dec(v___x_4977_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4983_; 
if (v_isShared_4981_ == 0)
{
v___x_4983_ = v___x_4980_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_a_4978_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
else
{
lean_object* v_a_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_4998_; 
v_a_4986_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4988_ = v___x_4977_;
v_isShared_4989_ = v_isSharedCheck_4998_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_a_4986_);
lean_dec(v___x_4977_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_4998_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v_content_4990_; lean_object* v_priorParts_4991_; lean_object* v___x_4993_; 
v_content_4990_ = lean_ctor_get(v_a_4986_, 0);
lean_inc_ref(v_content_4990_);
v_priorParts_4991_ = lean_ctor_get(v_a_4986_, 1);
lean_inc_ref(v_priorParts_4991_);
lean_dec(v_a_4986_);
if (v_isShared_4965_ == 0)
{
lean_ctor_set(v___x_4964_, 1, v_priorParts_4991_);
lean_ctor_set(v___x_4964_, 0, v_content_4990_);
v___x_4993_ = v___x_4964_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_content_4990_);
lean_ctor_set(v_reuseFailAlloc_4997_, 1, v_priorParts_4991_);
v___x_4993_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
lean_object* v___x_4995_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 0, v___x_4993_);
v___x_4995_ = v___x_4988_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4993_);
v___x_4995_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
return v___x_4995_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_es_5001_){
_start:
{
lean_object* v___x_5002_; 
v___x_5002_ = lean_array_mk(v_es_5001_);
return v___x_5002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_x_5005_, lean_object* v_x_5006_, lean_object* v_es_5007_){
_start:
{
lean_object* v_ents_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v_ents_5008_ = lean_array_mk(v_es_5007_);
v___x_5009_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
lean_inc_ref(v_ents_5008_);
v___x_5010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5009_);
lean_ctor_set(v___x_5010_, 1, v_ents_5008_);
lean_ctor_set(v___x_5010_, 2, v_ents_5008_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_x_5011_, lean_object* v_x_5012_, lean_object* v_es_5013_){
_start:
{
lean_object* v_res_5014_; 
v_res_5014_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v_x_5011_, v_x_5012_, v_es_5013_);
lean_dec_ref(v_x_5012_);
lean_dec_ref(v_x_5011_);
return v_res_5014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v___x_5015_, lean_object* v_x_5016_){
_start:
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; size_t v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; 
v___x_5017_ = lean_unsigned_to_nat(32u);
v___x_5018_ = lean_mk_empty_array_with_capacity(v___x_5017_);
v___x_5019_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_5020_ = ((size_t)5ULL);
lean_inc(v___x_5015_);
v___x_5021_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5021_, 0, v___x_5019_);
lean_ctor_set(v___x_5021_, 1, v___x_5018_);
lean_ctor_set(v___x_5021_, 2, v___x_5015_);
lean_ctor_set(v___x_5021_, 3, v___x_5015_);
lean_ctor_set_usize(v___x_5021_, 4, v___x_5020_);
v___x_5022_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_instInhabitedVersoModuleDocs_default_spec__0(v___x_5021_);
v___x_5023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5023_, 0, v___x_5021_);
lean_ctor_set(v___x_5023_, 1, v___x_5022_);
return v___x_5023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v___x_5024_, lean_object* v_x_5025_){
_start:
{
lean_object* v_res_5026_; 
v_res_5026_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v___x_5024_, v_x_5025_);
lean_dec_ref(v_x_5025_);
return v_res_5026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5047_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
v___x_5048_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5047_);
return v___x_5048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_a_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
return v_res_5050_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object* v_env_5051_){
_start:
{
lean_object* v___x_5052_; lean_object* v_toEnvExtension_5053_; lean_object* v_asyncMode_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5052_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_5053_ = lean_ctor_get(v___x_5052_, 0);
v_asyncMode_5054_ = lean_ctor_get(v_toEnvExtension_5053_, 2);
v___x_5055_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_5056_ = lean_box(0);
v___x_5057_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5055_, v___x_5052_, v_env_5051_, v_asyncMode_5054_, v___x_5056_);
return v___x_5057_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object* v_env_5058_){
_start:
{
lean_object* v___x_5059_; 
v___x_5059_ = l_Lean_getMainVersoModuleDocs(v_env_5058_);
return v___x_5059_;
}
}
static lean_object* _init_l_Lean_getVersoModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
v___x_5060_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_5061_ = lean_box(0);
v___x_5062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5061_);
lean_ctor_set(v___x_5062_, 1, v___x_5060_);
return v___x_5062_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object* v_env_5063_, lean_object* v_moduleName_5064_){
_start:
{
lean_object* v___x_5065_; 
v___x_5065_ = l_Lean_Environment_getModuleIdx_x3f(v_env_5063_, v_moduleName_5064_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v___x_5066_; 
v___x_5066_ = lean_box(0);
return v___x_5066_;
}
else
{
lean_object* v_val_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5078_; 
v_val_5067_ = lean_ctor_get(v___x_5065_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5069_ = v___x_5065_;
v_isShared_5070_ = v_isSharedCheck_5078_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_val_5067_);
lean_dec(v___x_5065_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5078_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; uint8_t v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5076_; 
v___x_5071_ = lean_obj_once(&l_Lean_getVersoModuleDoc_x3f___closed__0, &l_Lean_getVersoModuleDoc_x3f___closed__0_once, _init_l_Lean_getVersoModuleDoc_x3f___closed__0);
v___x_5072_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v___x_5073_ = 1;
v___x_5074_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_5071_, v___x_5072_, v_env_5063_, v_val_5067_, v___x_5073_);
lean_dec(v_val_5067_);
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 0, v___x_5074_);
v___x_5076_ = v___x_5069_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v___x_5074_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object* v_env_5079_, lean_object* v_moduleName_5080_){
_start:
{
lean_object* v_res_5081_; 
v_res_5081_ = l_Lean_getVersoModuleDoc_x3f(v_env_5079_, v_moduleName_5080_);
lean_dec(v_moduleName_5080_);
lean_dec_ref(v_env_5079_);
return v_res_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object* v_env_5084_, lean_object* v_snippet_5085_){
_start:
{
lean_object* v_docs_5086_; uint8_t v___x_5087_; 
lean_inc_ref(v_env_5084_);
v_docs_5086_ = l_Lean_getMainVersoModuleDocs(v_env_5084_);
v___x_5087_ = l_Lean_VersoModuleDocs_canAdd(v_docs_5086_, v_snippet_5085_);
if (v___x_5087_ == 0)
{
lean_object* v_terminalNesting_5088_; lean_object* v___x_5089_; lean_object* v___y_5091_; 
lean_dec_ref(v_snippet_5085_);
lean_dec_ref(v_env_5084_);
v_terminalNesting_5088_ = lean_ctor_get(v_docs_5086_, 1);
lean_inc(v_terminalNesting_5088_);
lean_dec_ref(v_docs_5086_);
v___x_5089_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__0));
if (lean_obj_tag(v_terminalNesting_5088_) == 0)
{
lean_object* v___x_5096_; 
v___x_5096_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___y_5091_ = v___x_5096_;
goto v___jp_5090_;
}
else
{
lean_object* v_val_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; 
v_val_5097_ = lean_ctor_get(v_terminalNesting_5088_, 0);
lean_inc(v_val_5097_);
lean_dec_ref(v_terminalNesting_5088_);
v___x_5098_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__1));
v___x_5099_ = l_Nat_reprFast(v_val_5097_);
v___x_5100_ = lean_string_append(v___x_5098_, v___x_5099_);
lean_dec_ref(v___x_5099_);
v___x_5101_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_5102_ = lean_string_append(v___x_5100_, v___x_5101_);
v___y_5091_ = v___x_5102_;
goto v___jp_5090_;
}
v___jp_5090_:
{
lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; 
v___x_5092_ = lean_string_append(v___x_5089_, v___y_5091_);
lean_dec_ref(v___y_5091_);
v___x_5093_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_5094_ = lean_string_append(v___x_5092_, v___x_5093_);
v___x_5095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5095_, 0, v___x_5094_);
return v___x_5095_;
}
}
else
{
lean_object* v___x_5103_; lean_object* v_toEnvExtension_5104_; lean_object* v_asyncMode_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
lean_dec_ref(v_docs_5086_);
v___x_5103_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_5104_ = lean_ctor_get(v___x_5103_, 0);
v_asyncMode_5105_ = lean_ctor_get(v_toEnvExtension_5104_, 2);
v___x_5106_ = lean_box(0);
v___x_5107_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5103_, v_env_5084_, v_snippet_5085_, v_asyncMode_5105_, v___x_5106_);
v___x_5108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5108_, 0, v___x_5107_);
return v___x_5108_;
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
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_doc_verso = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_doc_verso);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_doc_verso_module = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_doc_verso_module);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings);
lean_dec_ref(res);
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
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
res = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
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
