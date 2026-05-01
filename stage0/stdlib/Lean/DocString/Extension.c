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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoModuleDocs_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedVersoModuleDocs_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoModuleDocs_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedVersoModuleDocs;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_VersoModuleDocs_assemble___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value),((lean_object*)&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value),((lean_object*)&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_value)}};
static const lean_object* l_Lean_VersoModuleDocs_assemble___closed__0 = (const lean_object*)&l_Lean_VersoModuleDocs_assemble___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble___boxed(lean_object*);
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
v___x_543_ = lean_nat_add(v___y_540_, v___y_542_);
lean_dec(v___y_542_);
lean_dec(v___y_540_);
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
lean_ctor_set(v___x_523_, 3, v___y_541_);
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
lean_ctor_set(v_reuseFailAlloc_548_, 3, v___y_541_);
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
v___y_540_ = v___x_555_;
v___y_541_ = v___x_554_;
v___y_542_ = v_size_556_;
goto v___jp_539_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = lean_unsigned_to_nat(0u);
v___y_540_ = v___x_555_;
v___y_541_ = v___x_554_;
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
v___x_729_ = lean_nat_add(v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec(v___y_727_);
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
lean_ctor_set(v___x_709_, 3, v___y_726_);
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
lean_ctor_set(v_reuseFailAlloc_734_, 3, v___y_726_);
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
v___y_726_ = v___x_740_;
v___y_727_ = v___x_741_;
v___y_728_ = v_size_742_;
goto v___jp_725_;
}
else
{
lean_object* v___x_743_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___y_726_ = v___x_740_;
v___y_727_ = v___x_741_;
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
v___x_870_ = lean_nat_add(v___y_867_, v___y_869_);
lean_dec(v___y_869_);
lean_dec(v___y_867_);
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
lean_ctor_set(v___x_874_, 3, v___y_868_);
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
lean_ctor_set(v_reuseFailAlloc_878_, 3, v___y_868_);
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
v___y_867_ = v___x_892_;
v___y_868_ = v___x_891_;
v___y_869_ = v_size_893_;
goto v___jp_866_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v___y_867_ = v___x_892_;
v___y_868_ = v___x_891_;
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
v___x_1028_ = lean_nat_add(v___y_1025_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec(v___y_1025_);
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
lean_ctor_set(v___x_1008_, 3, v___y_1026_);
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
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v___y_1026_);
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
v___y_1025_ = v___x_1041_;
v___y_1026_ = v___x_1040_;
v___y_1027_ = v_size_1042_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_unsigned_to_nat(0u);
v___y_1025_ = v___x_1041_;
v___y_1026_ = v___x_1040_;
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
lean_object* v_md_1474_; lean_object* v_v_1479_; lean_object* v___x_1486_; lean_object* v_toEnvExtension_1487_; lean_object* v_asyncMode_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; 
v___x_1486_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1487_ = lean_ctor_get(v___x_1486_, 0);
v_asyncMode_1488_ = lean_ctor_get(v_toEnvExtension_1487_, 2);
v___x_1489_ = lean_box(0);
v___x_1490_ = 1;
lean_inc(v_declName_1470_);
lean_inc_ref(v_env_1469_);
v___x_1491_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1489_, v___x_1486_, v_env_1469_, v_declName_1470_, v_asyncMode_1488_, v___x_1490_);
if (lean_obj_tag(v___x_1491_) == 1)
{
lean_object* v_val_1492_; 
lean_dec(v_declName_1470_);
v_val_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_val_1492_);
lean_dec_ref(v___x_1491_);
v_declName_1470_ = v_val_1492_;
goto _start;
}
else
{
lean_object* v___x_1494_; lean_object* v_toEnvExtension_1495_; lean_object* v_asyncMode_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_dec(v___x_1491_);
v___x_1494_ = l_Lean_docStringExt;
v_toEnvExtension_1495_ = lean_ctor_get(v___x_1494_, 0);
v_asyncMode_1496_ = lean_ctor_get(v_toEnvExtension_1495_, 2);
v___x_1497_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
lean_inc(v_declName_1470_);
lean_inc_ref(v_env_1469_);
v___x_1498_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1497_, v___x_1494_, v_env_1469_, v_declName_1470_, v_asyncMode_1496_, v___x_1490_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v___x_1499_; lean_object* v_toEnvExtension_1500_; lean_object* v_asyncMode_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1499_ = l_Lean_versoDocStringExt;
v_toEnvExtension_1500_ = lean_ctor_get(v___x_1499_, 0);
v_asyncMode_1501_ = lean_ctor_get(v_toEnvExtension_1500_, 2);
v___x_1502_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default));
lean_inc(v_declName_1470_);
v___x_1503_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1502_, v___x_1499_, v_env_1469_, v_declName_1470_, v_asyncMode_1501_, v___x_1490_);
if (lean_obj_tag(v___x_1503_) == 0)
{
if (v_includeBuiltin_1471_ == 0)
{
lean_dec(v_declName_1470_);
goto v___jp_1483_;
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1505_ = lean_st_ref_get(v___x_1504_);
v___x_1506_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1505_, v_declName_1470_);
lean_dec(v___x_1505_);
if (lean_obj_tag(v___x_1506_) == 1)
{
lean_object* v_val_1507_; 
lean_dec(v_declName_1470_);
v_val_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_val_1507_);
lean_dec_ref(v___x_1506_);
v_md_1474_ = v_val_1507_;
goto v___jp_1473_;
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_dec(v___x_1506_);
v___x_1508_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1509_ = lean_st_ref_get(v___x_1508_);
v___x_1510_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1509_, v_declName_1470_);
lean_dec(v_declName_1470_);
lean_dec(v___x_1509_);
if (lean_obj_tag(v___x_1510_) == 1)
{
lean_object* v_val_1511_; 
v_val_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_val_1511_);
lean_dec_ref(v___x_1510_);
v_v_1479_ = v_val_1511_;
goto v___jp_1478_;
}
else
{
lean_dec(v___x_1510_);
goto v___jp_1483_;
}
}
}
}
else
{
lean_object* v_val_1512_; 
lean_dec(v_declName_1470_);
v_val_1512_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_val_1512_);
lean_dec_ref(v___x_1503_);
v_v_1479_ = v_val_1512_;
goto v___jp_1478_;
}
}
else
{
lean_object* v_val_1513_; 
lean_dec(v_declName_1470_);
lean_dec_ref(v_env_1469_);
v_val_1513_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_val_1513_);
lean_dec_ref(v___x_1498_);
v_md_1474_ = v_val_1513_;
goto v___jp_1473_;
}
}
v___jp_1473_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_md_1474_);
v___x_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
return v___x_1477_;
}
v___jp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_v_1479_);
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
v___jp_1483_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_box(0);
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
return v___x_1485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object* v_env_1514_, lean_object* v_declName_1515_, lean_object* v_includeBuiltin_1516_, lean_object* v_a_1517_){
_start:
{
uint8_t v_includeBuiltin_boxed_1518_; lean_object* v_res_1519_; 
v_includeBuiltin_boxed_1518_ = lean_unbox(v_includeBuiltin_1516_);
v_res_1519_ = l_Lean_findInternalDocString_x3f(v_env_1514_, v_declName_1515_, v_includeBuiltin_boxed_1518_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(lean_object* v_s_1520_, lean_object* v_replacement_1521_, lean_object* v_a_1522_, lean_object* v_b_1523_){
_start:
{
lean_object* v_it_1525_; lean_object* v_startPos_1526_; lean_object* v_endPos_1527_; lean_object* v_it_1536_; 
switch(lean_obj_tag(v_a_1522_))
{
case 0:
{
lean_object* v_pos_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1554_; 
v_pos_1542_ = lean_ctor_get(v_a_1522_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_a_1522_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1544_ = v_a_1522_;
v_isShared_1545_ = v_isSharedCheck_1554_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_pos_1542_);
lean_dec(v_a_1522_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1554_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_startInclusive_1546_; lean_object* v_endExclusive_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v_startInclusive_1546_ = lean_ctor_get(v_s_1520_, 1);
v_endExclusive_1547_ = lean_ctor_get(v_s_1520_, 2);
v___x_1548_ = lean_nat_sub(v_endExclusive_1547_, v_startInclusive_1546_);
v___x_1549_ = lean_nat_dec_eq(v_pos_1542_, v___x_1548_);
lean_dec(v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1551_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 1);
v___x_1551_ = v___x_1544_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_pos_1542_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
v_it_1536_ = v___x_1551_;
goto v___jp_1535_;
}
}
else
{
lean_object* v___x_1553_; 
lean_del_object(v___x_1544_);
lean_dec(v_pos_1542_);
v___x_1553_ = lean_box(3);
v_it_1536_ = v___x_1553_;
goto v___jp_1535_;
}
}
}
case 1:
{
lean_object* v_pos_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1567_; 
v_pos_1555_ = lean_ctor_get(v_a_1522_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_a_1522_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1557_ = v_a_1522_;
v_isShared_1558_ = v_isSharedCheck_1567_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_pos_1555_);
lean_dec(v_a_1522_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1567_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v_str_1559_; lean_object* v_startInclusive_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v_str_1559_ = lean_ctor_get(v_s_1520_, 0);
v_startInclusive_1560_ = lean_ctor_get(v_s_1520_, 1);
v___x_1561_ = lean_nat_add(v_startInclusive_1560_, v_pos_1555_);
v___x_1562_ = lean_string_utf8_next_fast(v_str_1559_, v___x_1561_);
lean_dec(v___x_1561_);
v___x_1563_ = lean_nat_sub(v___x_1562_, v_startInclusive_1560_);
lean_inc(v___x_1563_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set_tag(v___x_1557_, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1563_);
v___x_1565_ = v___x_1557_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
v_it_1525_ = v___x_1565_;
v_startPos_1526_ = v_pos_1555_;
v_endPos_1527_ = v___x_1563_;
goto v___jp_1524_;
}
}
}
case 2:
{
lean_object* v_needle_1568_; lean_object* v_table_1569_; lean_object* v_stackPos_1570_; lean_object* v_needlePos_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1630_; 
v_needle_1568_ = lean_ctor_get(v_a_1522_, 0);
v_table_1569_ = lean_ctor_get(v_a_1522_, 1);
v_stackPos_1570_ = lean_ctor_get(v_a_1522_, 2);
v_needlePos_1571_ = lean_ctor_get(v_a_1522_, 3);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_a_1522_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1573_ = v_a_1522_;
v_isShared_1574_ = v_isSharedCheck_1630_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_needlePos_1571_);
lean_inc(v_stackPos_1570_);
lean_inc(v_table_1569_);
lean_inc(v_needle_1568_);
lean_dec(v_a_1522_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1630_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_str_1575_; lean_object* v_startInclusive_1576_; lean_object* v_endExclusive_1577_; lean_object* v_str_1578_; lean_object* v_startInclusive_1579_; lean_object* v_endExclusive_1580_; lean_object* v_basePos_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v_str_1575_ = lean_ctor_get(v_needle_1568_, 0);
v_startInclusive_1576_ = lean_ctor_get(v_needle_1568_, 1);
v_endExclusive_1577_ = lean_ctor_get(v_needle_1568_, 2);
v_str_1578_ = lean_ctor_get(v_s_1520_, 0);
v_startInclusive_1579_ = lean_ctor_get(v_s_1520_, 1);
v_endExclusive_1580_ = lean_ctor_get(v_s_1520_, 2);
v_basePos_1581_ = lean_nat_sub(v_stackPos_1570_, v_needlePos_1571_);
v___x_1582_ = lean_nat_sub(v_endExclusive_1577_, v_startInclusive_1576_);
v___x_1583_ = lean_nat_add(v_basePos_1581_, v___x_1582_);
v___x_1584_ = lean_nat_sub(v_endExclusive_1580_, v_startInclusive_1579_);
v___x_1585_ = lean_nat_dec_le(v___x_1583_, v___x_1584_);
lean_dec(v___x_1583_);
if (v___x_1585_ == 0)
{
uint8_t v___x_1586_; 
lean_dec(v___x_1582_);
lean_del_object(v___x_1573_);
lean_dec(v_needlePos_1571_);
lean_dec(v_stackPos_1570_);
lean_dec_ref(v_table_1569_);
lean_dec_ref(v_needle_1568_);
v___x_1586_ = lean_nat_dec_lt(v_basePos_1581_, v___x_1584_);
if (v___x_1586_ == 0)
{
lean_dec(v___x_1584_);
lean_dec(v_basePos_1581_);
lean_dec_ref(v_s_1520_);
return v_b_1523_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = l_String_Slice_pos_x21(v_s_1520_, v_basePos_1581_);
lean_dec(v_basePos_1581_);
v___x_1588_ = lean_box(3);
v_it_1525_ = v___x_1588_;
v_startPos_1526_ = v___x_1587_;
v_endPos_1527_ = v___x_1584_;
goto v___jp_1524_;
}
}
else
{
lean_object* v___x_1589_; uint8_t v_stackByte_1590_; lean_object* v___x_1591_; uint8_t v_patByte_1592_; uint8_t v___x_1593_; 
lean_dec(v___x_1584_);
v___x_1589_ = lean_nat_add(v_startInclusive_1579_, v_stackPos_1570_);
v_stackByte_1590_ = lean_string_get_byte_fast(v_str_1578_, v___x_1589_);
v___x_1591_ = lean_nat_add(v_startInclusive_1576_, v_needlePos_1571_);
v_patByte_1592_ = lean_string_get_byte_fast(v_str_1575_, v___x_1591_);
v___x_1593_ = lean_uint8_dec_eq(v_stackByte_1590_, v_patByte_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; uint8_t v___x_1595_; 
lean_dec(v___x_1582_);
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = lean_nat_dec_eq(v_needlePos_1571_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v_newNeedlePos_1598_; uint8_t v___x_1599_; 
v___x_1596_ = lean_unsigned_to_nat(1u);
v___x_1597_ = lean_nat_sub(v_needlePos_1571_, v___x_1596_);
lean_dec(v_needlePos_1571_);
v_newNeedlePos_1598_ = lean_array_fget_borrowed(v_table_1569_, v___x_1597_);
lean_dec(v___x_1597_);
v___x_1599_ = lean_nat_dec_eq(v_newNeedlePos_1598_, v___x_1594_);
if (v___x_1599_ == 0)
{
lean_object* v_oldBasePos_1600_; lean_object* v___x_1601_; lean_object* v_newBasePos_1602_; lean_object* v___x_1604_; 
lean_inc(v_newNeedlePos_1598_);
v_oldBasePos_1600_ = l_String_Slice_pos_x21(v_s_1520_, v_basePos_1581_);
lean_dec(v_basePos_1581_);
v___x_1601_ = lean_nat_sub(v_stackPos_1570_, v_newNeedlePos_1598_);
v_newBasePos_1602_ = l_String_Slice_pos_x21(v_s_1520_, v___x_1601_);
lean_dec(v___x_1601_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 3, v_newNeedlePos_1598_);
v___x_1604_ = v___x_1573_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_needle_1568_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_table_1569_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_stackPos_1570_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_newNeedlePos_1598_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
v_it_1525_ = v___x_1604_;
v_startPos_1526_ = v_oldBasePos_1600_;
v_endPos_1527_ = v_newBasePos_1602_;
goto v___jp_1524_;
}
}
else
{
lean_object* v_basePos_1606_; lean_object* v_nextStackPos_1607_; lean_object* v___x_1609_; 
v_basePos_1606_ = l_String_Slice_pos_x21(v_s_1520_, v_basePos_1581_);
lean_dec(v_basePos_1581_);
v_nextStackPos_1607_ = l_String_Slice_posGE___redArg(v_s_1520_, v_stackPos_1570_);
lean_inc(v_nextStackPos_1607_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 3, v___x_1594_);
lean_ctor_set(v___x_1573_, 2, v_nextStackPos_1607_);
v___x_1609_ = v___x_1573_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_needle_1568_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_table_1569_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_nextStackPos_1607_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v___x_1594_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
v_it_1525_ = v___x_1609_;
v_startPos_1526_ = v_basePos_1606_;
v_endPos_1527_ = v_nextStackPos_1607_;
goto v___jp_1524_;
}
}
}
else
{
lean_object* v_basePos_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v_nextStackPos_1614_; lean_object* v___x_1616_; 
lean_dec(v_basePos_1581_);
lean_dec(v_needlePos_1571_);
v_basePos_1611_ = l_String_Slice_pos_x21(v_s_1520_, v_stackPos_1570_);
v___x_1612_ = lean_unsigned_to_nat(1u);
v___x_1613_ = lean_nat_add(v_stackPos_1570_, v___x_1612_);
lean_dec(v_stackPos_1570_);
v_nextStackPos_1614_ = l_String_Slice_posGE___redArg(v_s_1520_, v___x_1613_);
lean_inc(v_nextStackPos_1614_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 3, v___x_1594_);
lean_ctor_set(v___x_1573_, 2, v_nextStackPos_1614_);
v___x_1616_ = v___x_1573_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_needle_1568_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_table_1569_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_nextStackPos_1614_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v___x_1594_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
v_it_1525_ = v___x_1616_;
v_startPos_1526_ = v_basePos_1611_;
v_endPos_1527_ = v_nextStackPos_1614_;
goto v___jp_1524_;
}
}
}
else
{
lean_object* v___x_1618_; lean_object* v_nextStackPos_1619_; lean_object* v_nextNeedlePos_1620_; uint8_t v___x_1621_; 
lean_dec(v_basePos_1581_);
v___x_1618_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1619_ = lean_nat_add(v_stackPos_1570_, v___x_1618_);
lean_dec(v_stackPos_1570_);
v_nextNeedlePos_1620_ = lean_nat_add(v_needlePos_1571_, v___x_1618_);
lean_dec(v_needlePos_1571_);
v___x_1621_ = lean_nat_dec_eq(v_nextNeedlePos_1620_, v___x_1582_);
lean_dec(v___x_1582_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1623_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 3, v_nextNeedlePos_1620_);
lean_ctor_set(v___x_1573_, 2, v_nextStackPos_1619_);
v___x_1623_ = v___x_1573_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_needle_1568_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_table_1569_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_nextStackPos_1619_);
lean_ctor_set(v_reuseFailAlloc_1625_, 3, v_nextNeedlePos_1620_);
v___x_1623_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
v_a_1522_ = v___x_1623_;
goto _start;
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
lean_dec(v_nextNeedlePos_1620_);
v___x_1626_ = lean_unsigned_to_nat(0u);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 3, v___x_1626_);
lean_ctor_set(v___x_1573_, 2, v_nextStackPos_1619_);
v___x_1628_ = v___x_1573_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_needle_1568_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_table_1569_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v_nextStackPos_1619_);
lean_ctor_set(v_reuseFailAlloc_1629_, 3, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
v_it_1536_ = v___x_1628_;
goto v___jp_1535_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1520_);
return v_b_1523_;
}
}
v___jp_1524_:
{
lean_object* v___x_1528_; lean_object* v_str_1529_; lean_object* v_startInclusive_1530_; lean_object* v_endExclusive_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_inc_ref(v_s_1520_);
v___x_1528_ = l_String_Slice_slice_x21(v_s_1520_, v_startPos_1526_, v_endPos_1527_);
lean_dec(v_endPos_1527_);
lean_dec(v_startPos_1526_);
v_str_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc_ref(v_str_1529_);
v_startInclusive_1530_ = lean_ctor_get(v___x_1528_, 1);
lean_inc(v_startInclusive_1530_);
v_endExclusive_1531_ = lean_ctor_get(v___x_1528_, 2);
lean_inc(v_endExclusive_1531_);
lean_dec_ref(v___x_1528_);
v___x_1532_ = lean_string_utf8_extract(v_str_1529_, v_startInclusive_1530_, v_endExclusive_1531_);
lean_dec(v_endExclusive_1531_);
lean_dec(v_startInclusive_1530_);
lean_dec_ref(v_str_1529_);
v___x_1533_ = lean_string_append(v_b_1523_, v___x_1532_);
lean_dec_ref(v___x_1532_);
v_a_1522_ = v_it_1525_;
v_b_1523_ = v___x_1533_;
goto _start;
}
v___jp_1535_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_string_utf8_byte_size(v_replacement_1521_);
v___x_1539_ = lean_string_utf8_extract(v_replacement_1521_, v___x_1537_, v___x_1538_);
v___x_1540_ = lean_string_append(v_b_1523_, v___x_1539_);
lean_dec_ref(v___x_1539_);
v_a_1522_ = v_it_1536_;
v_b_1523_ = v___x_1540_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_s_1631_, lean_object* v_replacement_1632_, lean_object* v_a_1633_, lean_object* v_b_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1631_, v_replacement_1632_, v_a_1633_, v_b_1634_);
lean_dec_ref(v_replacement_1632_);
return v_res_1635_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1638_ = lean_string_utf8_byte_size(v___x_1637_);
return v___x_1638_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1641_ = lean_nat_dec_eq(v___x_1640_, v___x_1639_);
return v___x_1641_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1642_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v___x_1643_);
lean_ctor_set(v___x_1645_, 2, v___x_1642_);
return v___x_1645_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1647_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1646_);
return v___x_1647_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__4);
v___x_1650_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1651_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v___x_1649_);
lean_ctor_set(v___x_1651_, 2, v___x_1648_);
lean_ctor_set(v___x_1651_, 3, v___x_1648_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(lean_object* v_s_1654_, lean_object* v_replacement_1655_){
_start:
{
lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_1657_ = lean_uint8_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__2);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__5);
v___x_1659_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1654_, v_replacement_1655_, v___x_1658_, v___x_1656_);
return v___x_1659_;
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__6));
v___x_1661_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_1654_, v_replacement_1655_, v___x_1660_, v___x_1656_);
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_s_1662_, lean_object* v_replacement_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v_s_1662_, v_replacement_1663_);
lean_dec_ref(v_replacement_1663_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(lean_object* v_as_1672_, size_t v_sz_1673_, size_t v_i_1674_, lean_object* v_b_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
uint8_t v___x_1678_; 
v___x_1678_ = lean_usize_dec_lt(v_i_1674_, v_sz_1673_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1679_, 0, v_b_1675_);
lean_ctor_set(v___x_1679_, 1, v___y_1677_);
return v___x_1679_;
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1681_; lean_object* v_snd_1682_; lean_object* v___x_1683_; size_t v___x_1684_; size_t v___x_1685_; 
v_a_1680_ = lean_array_uget_borrowed(v_as_1672_, v_i_1674_);
lean_inc(v_a_1680_);
v___x_1681_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_a_1680_, v___y_1676_, v___y_1677_);
v_snd_1682_ = lean_ctor_get(v___x_1681_, 1);
lean_inc(v_snd_1682_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = lean_box(0);
v___x_1684_ = ((size_t)1ULL);
v___x_1685_ = lean_usize_add(v_i_1674_, v___x_1684_);
v_i_1674_ = v___x_1685_;
v_b_1675_ = v___x_1683_;
v___y_1677_ = v_snd_1682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(lean_object* v_x_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
switch(lean_obj_tag(v_x_1700_))
{
case 0:
{
lean_object* v_string_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_string_1703_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_string_1703_);
lean_dec_ref(v_x_1700_);
v___x_1704_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1703_);
lean_dec_ref(v_string_1703_);
v___x_1705_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1704_, v_a_1702_);
lean_dec_ref(v___x_1704_);
return v___x_1705_;
}
case 1:
{
lean_object* v_content_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1747_; 
v_content_1706_ = lean_ctor_get(v_x_1700_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_x_1700_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1708_ = v_x_1700_;
v_isShared_1709_ = v_isSharedCheck_1747_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_content_1706_);
lean_dec(v_x_1700_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1747_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set_tag(v___x_1708_, 9);
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_content_1706_);
v___x_1711_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1712_; lean_object* v_snd_1713_; lean_object* v_fst_1714_; lean_object* v_fst_1715_; lean_object* v_snd_1716_; uint8_t v_inEmph_1718_; uint8_t v_inBold_1719_; uint8_t v_inLink_1720_; lean_object* v_linePrefix_1721_; lean_object* v___y_1722_; lean_object* v___x_1733_; uint8_t v_inEmph_1734_; 
v___x_1712_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1711_);
v_snd_1713_ = lean_ctor_get(v___x_1712_, 1);
lean_inc(v_snd_1713_);
v_fst_1714_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_fst_1714_);
lean_dec_ref(v___x_1712_);
v_fst_1715_ = lean_ctor_get(v_snd_1713_, 0);
lean_inc(v_fst_1715_);
v_snd_1716_ = lean_ctor_get(v_snd_1713_, 1);
lean_inc(v_snd_1716_);
lean_dec(v_snd_1713_);
v___x_1733_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_1714_, v_a_1702_);
lean_dec(v_fst_1714_);
v_inEmph_1734_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*1);
if (v_inEmph_1734_ == 0)
{
lean_object* v_snd_1735_; uint8_t v_inBold_1736_; uint8_t v_inLink_1737_; lean_object* v_linePrefix_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v_snd_1741_; 
v_snd_1735_ = lean_ctor_get(v___x_1733_, 1);
lean_inc(v_snd_1735_);
lean_dec_ref(v___x_1733_);
v_inBold_1736_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*1 + 1);
v_inLink_1737_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*1 + 2);
v_linePrefix_1738_ = lean_ctor_get(v_a_1701_, 0);
v___x_1739_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0));
v___x_1740_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1739_, v_snd_1735_);
v_snd_1741_ = lean_ctor_get(v___x_1740_, 1);
lean_inc(v_snd_1741_);
lean_dec_ref(v___x_1740_);
v_inEmph_1718_ = v_inEmph_1734_;
v_inBold_1719_ = v_inBold_1736_;
v_inLink_1720_ = v_inLink_1737_;
v_linePrefix_1721_ = v_linePrefix_1738_;
v___y_1722_ = v_snd_1741_;
goto v___jp_1717_;
}
else
{
lean_object* v_snd_1742_; uint8_t v_inBold_1743_; uint8_t v_inLink_1744_; lean_object* v_linePrefix_1745_; 
v_snd_1742_ = lean_ctor_get(v___x_1733_, 1);
lean_inc(v_snd_1742_);
lean_dec_ref(v___x_1733_);
v_inBold_1743_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*1 + 1);
v_inLink_1744_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*1 + 2);
v_linePrefix_1745_ = lean_ctor_get(v_a_1701_, 0);
v_inEmph_1718_ = v_inEmph_1734_;
v_inBold_1719_ = v_inBold_1743_;
v_inLink_1720_ = v_inLink_1744_;
v_linePrefix_1721_ = v_linePrefix_1745_;
v___y_1722_ = v_snd_1742_;
goto v___jp_1717_;
}
v___jp_1717_:
{
uint8_t v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1723_ = 1;
lean_inc_ref(v_linePrefix_1721_);
v___x_1724_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1724_, 0, v_linePrefix_1721_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*1, v___x_1723_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*1 + 1, v_inBold_1719_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*1 + 2, v_inLink_1720_);
v___x_1725_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_fst_1715_, v___x_1724_, v___y_1722_);
lean_dec_ref(v___x_1724_);
if (v_inEmph_1718_ == 0)
{
lean_object* v_snd_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v_snd_1729_; lean_object* v___x_1730_; 
v_snd_1726_ = lean_ctor_get(v___x_1725_, 1);
lean_inc(v_snd_1726_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__0));
v___x_1728_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1727_, v_snd_1726_);
v_snd_1729_ = lean_ctor_get(v___x_1728_, 1);
lean_inc(v_snd_1729_);
lean_dec_ref(v___x_1728_);
v___x_1730_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1716_, v_snd_1729_);
lean_dec(v_snd_1716_);
return v___x_1730_;
}
else
{
lean_object* v_snd_1731_; lean_object* v___x_1732_; 
v_snd_1731_ = lean_ctor_get(v___x_1725_, 1);
lean_inc(v_snd_1731_);
lean_dec_ref(v___x_1725_);
v___x_1732_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1716_, v_snd_1731_);
lean_dec(v_snd_1716_);
return v___x_1732_;
}
}
}
}
}
case 2:
{
lean_object* v_content_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1786_; 
v_content_1748_ = lean_ctor_get(v_x_1700_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_x_1700_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1750_ = v_x_1700_;
v_isShared_1751_ = v_isSharedCheck_1786_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_content_1748_);
lean_dec(v_x_1700_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1786_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set_tag(v___x_1750_, 9);
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_content_1748_);
v___x_1753_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1754_; lean_object* v_snd_1755_; lean_object* v_fst_1756_; lean_object* v_fst_1757_; lean_object* v_snd_1758_; uint8_t v_inBold_1760_; uint8_t v_inLink_1761_; lean_object* v_linePrefix_1762_; lean_object* v___y_1763_; lean_object* v___x_1774_; uint8_t v_inBold_1775_; 
v___x_1754_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1753_);
v_snd_1755_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_snd_1755_);
v_fst_1756_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_fst_1756_);
lean_dec_ref(v___x_1754_);
v_fst_1757_ = lean_ctor_get(v_snd_1755_, 0);
lean_inc(v_fst_1757_);
v_snd_1758_ = lean_ctor_get(v_snd_1755_, 1);
lean_inc(v_snd_1758_);
lean_dec(v_snd_1755_);
v___x_1774_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_1756_, v_a_1702_);
lean_dec(v_fst_1756_);
v_inBold_1775_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*1 + 1);
if (v_inBold_1775_ == 0)
{
lean_object* v_snd_1776_; uint8_t v_inLink_1777_; lean_object* v_linePrefix_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v_snd_1781_; 
v_snd_1776_ = lean_ctor_get(v___x_1774_, 1);
lean_inc(v_snd_1776_);
lean_dec_ref(v___x_1774_);
v_inLink_1777_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*1 + 2);
v_linePrefix_1778_ = lean_ctor_get(v_a_1701_, 0);
v___x_1779_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1));
v___x_1780_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1779_, v_snd_1776_);
v_snd_1781_ = lean_ctor_get(v___x_1780_, 1);
lean_inc(v_snd_1781_);
lean_dec_ref(v___x_1780_);
v_inBold_1760_ = v_inBold_1775_;
v_inLink_1761_ = v_inLink_1777_;
v_linePrefix_1762_ = v_linePrefix_1778_;
v___y_1763_ = v_snd_1781_;
goto v___jp_1759_;
}
else
{
lean_object* v_snd_1782_; uint8_t v_inLink_1783_; lean_object* v_linePrefix_1784_; 
v_snd_1782_ = lean_ctor_get(v___x_1774_, 1);
lean_inc(v_snd_1782_);
lean_dec_ref(v___x_1774_);
v_inLink_1783_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*1 + 2);
v_linePrefix_1784_ = lean_ctor_get(v_a_1701_, 0);
v_inBold_1760_ = v_inBold_1775_;
v_inLink_1761_ = v_inLink_1783_;
v_linePrefix_1762_ = v_linePrefix_1784_;
v___y_1763_ = v_snd_1782_;
goto v___jp_1759_;
}
v___jp_1759_:
{
uint8_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = 1;
lean_inc_ref(v_linePrefix_1762_);
v___x_1765_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1765_, 0, v_linePrefix_1762_);
lean_ctor_set_uint8(v___x_1765_, sizeof(void*)*1, v___x_1764_);
lean_ctor_set_uint8(v___x_1765_, sizeof(void*)*1 + 1, v_inBold_1760_);
lean_ctor_set_uint8(v___x_1765_, sizeof(void*)*1 + 2, v_inLink_1761_);
v___x_1766_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_fst_1757_, v___x_1765_, v___y_1763_);
lean_dec_ref(v___x_1765_);
if (v_inBold_1760_ == 0)
{
lean_object* v_snd_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v_snd_1770_; lean_object* v___x_1771_; 
v_snd_1767_ = lean_ctor_get(v___x_1766_, 1);
lean_inc(v_snd_1767_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__1));
v___x_1769_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1768_, v_snd_1767_);
v_snd_1770_ = lean_ctor_get(v___x_1769_, 1);
lean_inc(v_snd_1770_);
lean_dec_ref(v___x_1769_);
v___x_1771_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1758_, v_snd_1770_);
lean_dec(v_snd_1758_);
return v___x_1771_;
}
else
{
lean_object* v_snd_1772_; lean_object* v___x_1773_; 
v_snd_1772_ = lean_ctor_get(v___x_1766_, 1);
lean_inc(v_snd_1772_);
lean_dec_ref(v___x_1766_);
v___x_1773_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1758_, v_snd_1772_);
lean_dec(v_snd_1758_);
return v___x_1773_;
}
}
}
}
}
case 3:
{
lean_object* v_string_1787_; lean_object* v___y_1789_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v_fst_1794_; uint8_t v___x_1795_; 
v_string_1787_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_string_1787_);
lean_dec_ref(v_x_1700_);
v___x_1792_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__2));
v___x_1793_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v___x_1792_, v_a_1702_);
v_fst_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_fst_1794_);
v___x_1795_ = lean_unbox(v_fst_1794_);
lean_dec(v_fst_1794_);
if (v___x_1795_ == 0)
{
lean_object* v_snd_1796_; 
v_snd_1796_ = lean_ctor_get(v___x_1793_, 1);
lean_inc(v_snd_1796_);
lean_dec_ref(v___x_1793_);
v___y_1789_ = v_snd_1796_;
goto v___jp_1788_;
}
else
{
lean_object* v_snd_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v_snd_1800_; 
v_snd_1797_ = lean_ctor_get(v___x_1793_, 1);
lean_inc(v_snd_1797_);
lean_dec_ref(v___x_1793_);
v___x_1798_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__3));
v___x_1799_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1798_, v_snd_1797_);
v_snd_1800_ = lean_ctor_get(v___x_1799_, 1);
lean_inc(v_snd_1800_);
lean_dec_ref(v___x_1799_);
v___y_1789_ = v_snd_1800_;
goto v___jp_1788_;
}
v___jp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1787_);
v___x_1791_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1790_, v___y_1789_);
lean_dec_ref(v___x_1790_);
return v___x_1791_;
}
}
case 4:
{
uint8_t v_mode_1801_; 
v_mode_1801_ = lean_ctor_get_uint8(v_x_1700_, sizeof(void*)*1);
if (v_mode_1801_ == 0)
{
lean_object* v_string_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_string_1802_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_string_1802_);
lean_dec_ref(v_x_1700_);
v___x_1803_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__4));
v___x_1804_ = lean_string_append(v___x_1803_, v_string_1802_);
lean_dec_ref(v_string_1802_);
v___x_1805_ = lean_string_append(v___x_1804_, v___x_1803_);
v___x_1806_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1805_, v_a_1702_);
lean_dec_ref(v___x_1805_);
return v___x_1806_;
}
else
{
lean_object* v_string_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_string_1807_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_string_1807_);
lean_dec_ref(v_x_1700_);
v___x_1808_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__5));
v___x_1809_ = lean_string_append(v___x_1808_, v_string_1807_);
lean_dec_ref(v_string_1807_);
v___x_1810_ = lean_string_append(v___x_1809_, v___x_1808_);
v___x_1811_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1810_, v_a_1702_);
lean_dec_ref(v___x_1810_);
return v___x_1811_;
}
}
case 5:
{
lean_object* v_string_1812_; lean_object* v_linePrefix_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v_string_1812_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_string_1812_);
lean_dec_ref(v_x_1700_);
v_linePrefix_1813_ = lean_ctor_get(v_a_1701_, 0);
v___x_1814_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1815_ = lean_string_append(v___x_1814_, v_linePrefix_1813_);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_string_utf8_byte_size(v_string_1812_);
v___x_1818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1818_, 0, v_string_1812_);
lean_ctor_set(v___x_1818_, 1, v___x_1816_);
lean_ctor_set(v___x_1818_, 2, v___x_1817_);
v___x_1819_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v___x_1818_, v___x_1815_);
lean_dec_ref(v___x_1815_);
v___x_1820_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1819_, v_a_1702_);
lean_dec_ref(v___x_1819_);
return v___x_1820_;
}
case 6:
{
uint8_t v_inLink_1821_; 
v_inLink_1821_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*1 + 2);
if (v_inLink_1821_ == 0)
{
lean_object* v_content_1822_; lean_object* v_url_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v_snd_1826_; lean_object* v___x_1827_; size_t v_sz_1828_; size_t v___x_1829_; lean_object* v___x_1830_; lean_object* v_snd_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v_snd_1834_; lean_object* v___x_1835_; lean_object* v_snd_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v_content_1822_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_content_1822_);
v_url_1823_ = lean_ctor_get(v_x_1700_, 1);
lean_inc_ref(v_url_1823_);
lean_dec_ref(v_x_1700_);
v___x_1824_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__6));
v___x_1825_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1824_, v_a_1702_);
v_snd_1826_ = lean_ctor_get(v___x_1825_, 1);
lean_inc(v_snd_1826_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = lean_box(0);
v_sz_1828_ = lean_array_size(v_content_1822_);
v___x_1829_ = ((size_t)0ULL);
v___x_1830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1822_, v_sz_1828_, v___x_1829_, v___x_1827_, v_a_1701_, v_snd_1826_);
lean_dec_ref(v_content_1822_);
v_snd_1831_ = lean_ctor_get(v___x_1830_, 1);
lean_inc(v_snd_1831_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7));
v___x_1833_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1832_, v_snd_1831_);
v_snd_1834_ = lean_ctor_get(v___x_1833_, 1);
lean_inc(v_snd_1834_);
lean_dec_ref(v___x_1833_);
v___x_1835_ = l_Lean_Doc_MarkdownM_push___redArg(v_url_1823_, v_snd_1834_);
lean_dec_ref(v_url_1823_);
v_snd_1836_ = lean_ctor_get(v___x_1835_, 1);
lean_inc(v_snd_1836_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_1838_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1837_, v_snd_1836_);
return v___x_1838_;
}
else
{
lean_object* v_content_1839_; lean_object* v___x_1840_; size_t v_sz_1841_; size_t v___x_1842_; lean_object* v___x_1843_; lean_object* v_snd_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
v_content_1839_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_content_1839_);
lean_dec_ref(v_x_1700_);
v___x_1840_ = lean_box(0);
v_sz_1841_ = lean_array_size(v_content_1839_);
v___x_1842_ = ((size_t)0ULL);
v___x_1843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1839_, v_sz_1841_, v___x_1842_, v___x_1840_, v_a_1701_, v_a_1702_);
lean_dec_ref(v_content_1839_);
v_snd_1844_ = lean_ctor_get(v___x_1843_, 1);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; 
v_unused_1852_ = lean_ctor_get(v___x_1843_, 0);
lean_dec(v_unused_1852_);
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_snd_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1840_);
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_snd_1844_);
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
case 7:
{
lean_object* v_name_1853_; lean_object* v_content_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v_snd_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1899_; 
v_name_1853_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_name_1853_);
v_content_1854_ = lean_ctor_get(v_x_1700_, 1);
lean_inc_ref(v_content_1854_);
lean_dec_ref(v_x_1700_);
v___x_1855_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__9));
v___x_1856_ = lean_string_append(v___x_1855_, v_name_1853_);
v___x_1857_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__10));
v___x_1858_ = lean_string_append(v___x_1856_, v___x_1857_);
v___x_1859_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1858_, v_a_1702_);
lean_dec_ref(v___x_1858_);
v_snd_1860_ = lean_ctor_get(v___x_1859_, 1);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v___x_1859_, 0);
lean_dec(v_unused_1900_);
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1899_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_snd_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1899_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_snd_1865_; lean_object* v___y_1884_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = lean_array_get_size(v_content_1854_);
v___x_1888_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11));
v___x_1889_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13));
v___x_1890_ = lean_nat_dec_lt(v___x_1886_, v___x_1887_);
if (v___x_1890_ == 0)
{
lean_dec_ref(v_content_1854_);
v_snd_1865_ = v___x_1889_;
goto v___jp_1864_;
}
else
{
lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = lean_box(0);
v___x_1892_ = lean_nat_dec_le(v___x_1887_, v___x_1887_);
if (v___x_1892_ == 0)
{
if (v___x_1890_ == 0)
{
lean_dec_ref(v_content_1854_);
v_snd_1865_ = v___x_1889_;
goto v___jp_1864_;
}
else
{
size_t v___x_1893_; size_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = ((size_t)0ULL);
v___x_1894_ = lean_usize_of_nat(v___x_1887_);
v___x_1895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1854_, v___x_1893_, v___x_1894_, v___x_1891_, v___x_1888_, v___x_1889_);
lean_dec_ref(v_content_1854_);
v___y_1884_ = v___x_1895_;
goto v___jp_1883_;
}
}
else
{
size_t v___x_1896_; size_t v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = ((size_t)0ULL);
v___x_1897_ = lean_usize_of_nat(v___x_1887_);
v___x_1898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1854_, v___x_1896_, v___x_1897_, v___x_1891_, v___x_1888_, v___x_1889_);
lean_dec_ref(v_content_1854_);
v___y_1884_ = v___x_1898_;
goto v___jp_1883_;
}
}
v___jp_1864_:
{
lean_object* v_priorBlocks_1866_; lean_object* v_currentBlock_1867_; lean_object* v_footnotes_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1882_; 
v_priorBlocks_1866_ = lean_ctor_get(v_snd_1860_, 0);
v_currentBlock_1867_ = lean_ctor_get(v_snd_1860_, 1);
v_footnotes_1868_ = lean_ctor_get(v_snd_1860_, 2);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_snd_1860_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1870_ = v_snd_1860_;
v_isShared_1871_ = v_isSharedCheck_1882_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_footnotes_1868_);
lean_inc(v_currentBlock_1867_);
lean_inc(v_priorBlocks_1866_);
lean_dec(v_snd_1860_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1882_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1872_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(v_snd_1865_);
v___x_1873_ = lean_box(0);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 1, v___x_1872_);
lean_ctor_set(v___x_1862_, 0, v_name_1853_);
v___x_1875_ = v___x_1862_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_name_1853_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v___x_1872_);
v___x_1875_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = lean_array_push(v_footnotes_1868_, v___x_1875_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 2, v___x_1876_);
v___x_1878_ = v___x_1870_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_priorBlocks_1866_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_currentBlock_1867_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1873_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
return v___x_1879_;
}
}
}
}
v___jp_1883_:
{
lean_object* v_snd_1885_; 
v_snd_1885_ = lean_ctor_get(v___y_1884_, 1);
lean_inc(v_snd_1885_);
lean_dec_ref(v___y_1884_);
v_snd_1865_ = v_snd_1885_;
goto v___jp_1864_;
}
}
}
case 8:
{
lean_object* v_alt_1901_; lean_object* v_url_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_alt_1901_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_alt_1901_);
v_url_1902_ = lean_ctor_get(v_x_1700_, 1);
lean_inc_ref(v_url_1902_);
lean_dec_ref(v_x_1700_);
v___x_1903_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__14));
v___x_1904_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1901_);
lean_dec_ref(v_alt_1901_);
v___x_1905_ = lean_string_append(v___x_1903_, v___x_1904_);
lean_dec_ref(v___x_1904_);
v___x_1906_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__7));
v___x_1907_ = lean_string_append(v___x_1905_, v___x_1906_);
v___x_1908_ = lean_string_append(v___x_1907_, v_url_1902_);
lean_dec_ref(v_url_1902_);
v___x_1909_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_1910_ = lean_string_append(v___x_1908_, v___x_1909_);
v___x_1911_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1910_, v_a_1702_);
lean_dec_ref(v___x_1910_);
return v___x_1911_;
}
case 9:
{
lean_object* v_content_1912_; lean_object* v___x_1913_; size_t v_sz_1914_; size_t v___x_1915_; lean_object* v___x_1916_; lean_object* v_snd_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
v_content_1912_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_content_1912_);
lean_dec_ref(v_x_1700_);
v___x_1913_ = lean_box(0);
v_sz_1914_ = lean_array_size(v_content_1912_);
v___x_1915_ = ((size_t)0ULL);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_content_1912_, v_sz_1914_, v___x_1915_, v___x_1913_, v_a_1701_, v_a_1702_);
lean_dec_ref(v_content_1912_);
v_snd_1917_ = lean_ctor_get(v___x_1916_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v___x_1916_, 0);
lean_dec(v_unused_1925_);
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_snd_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1913_);
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_snd_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
default: 
{
lean_object* v_content_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v_content_1926_ = lean_ctor_get(v_x_1700_, 1);
lean_inc_ref(v_content_1926_);
lean_dec_ref(v_x_1700_);
v___x_1927_ = lean_unsigned_to_nat(0u);
v___x_1928_ = lean_array_get_size(v_content_1926_);
v___x_1929_ = lean_box(0);
v___x_1930_ = lean_nat_dec_lt(v___x_1927_, v___x_1928_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
lean_dec_ref(v_content_1926_);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v_a_1702_);
return v___x_1931_;
}
else
{
uint8_t v___x_1932_; 
v___x_1932_ = lean_nat_dec_le(v___x_1928_, v___x_1928_);
if (v___x_1932_ == 0)
{
if (v___x_1930_ == 0)
{
lean_object* v___x_1933_; 
lean_dec_ref(v_content_1926_);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1929_);
lean_ctor_set(v___x_1933_, 1, v_a_1702_);
return v___x_1933_;
}
else
{
size_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = ((size_t)0ULL);
v___x_1935_ = lean_usize_of_nat(v___x_1928_);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1926_, v___x_1934_, v___x_1935_, v___x_1929_, v_a_1701_, v_a_1702_);
lean_dec_ref(v_content_1926_);
return v___x_1936_;
}
}
else
{
size_t v___x_1937_; size_t v___x_1938_; lean_object* v___x_1939_; 
v___x_1937_ = ((size_t)0ULL);
v___x_1938_ = lean_usize_of_nat(v___x_1928_);
v___x_1939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_content_1926_, v___x_1937_, v___x_1938_, v___x_1929_, v_a_1701_, v_a_1702_);
lean_dec_ref(v_content_1926_);
return v___x_1939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(lean_object* v_as_1940_, size_t v_i_1941_, size_t v_stop_1942_, lean_object* v_b_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_usize_dec_eq(v_i_1941_, v_stop_1942_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v_fst_1949_; lean_object* v_snd_1950_; size_t v___x_1951_; size_t v___x_1952_; 
v___x_1947_ = lean_array_uget_borrowed(v_as_1940_, v_i_1941_);
lean_inc(v___x_1947_);
v___x_1948_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_1947_, v___y_1944_, v___y_1945_);
v_fst_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_fst_1949_);
v_snd_1950_ = lean_ctor_get(v___x_1948_, 1);
lean_inc(v_snd_1950_);
lean_dec_ref(v___x_1948_);
v___x_1951_ = ((size_t)1ULL);
v___x_1952_ = lean_usize_add(v_i_1941_, v___x_1951_);
v_i_1941_ = v___x_1952_;
v_b_1943_ = v_fst_1949_;
v___y_1945_ = v_snd_1950_;
goto _start;
}
else
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v_b_1943_);
lean_ctor_set(v___x_1954_, 1, v___y_1945_);
return v___x_1954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1955_, lean_object* v_i_1956_, lean_object* v_stop_1957_, lean_object* v_b_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
size_t v_i_boxed_1961_; size_t v_stop_boxed_1962_; lean_object* v_res_1963_; 
v_i_boxed_1961_ = lean_unbox_usize(v_i_1956_);
lean_dec(v_i_1956_);
v_stop_boxed_1962_ = lean_unbox_usize(v_stop_1957_);
lean_dec(v_stop_1957_);
v_res_1963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__3(v_as_1955_, v_i_boxed_1961_, v_stop_boxed_1962_, v_b_1958_, v___y_1959_, v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec_ref(v_as_1955_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2___boxed(lean_object* v_as_1964_, lean_object* v_sz_1965_, lean_object* v_i_1966_, lean_object* v_b_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
size_t v_sz_boxed_1970_; size_t v_i_boxed_1971_; lean_object* v_res_1972_; 
v_sz_boxed_1970_ = lean_unbox_usize(v_sz_1965_);
lean_dec(v_sz_1965_);
v_i_boxed_1971_ = lean_unbox_usize(v_i_1966_);
lean_dec(v_i_1966_);
v_res_1972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_as_1964_, v_sz_boxed_1970_, v_i_boxed_1971_, v_b_1967_, v___y_1968_, v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec_ref(v_as_1964_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___boxed(lean_object* v_x_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_x_1973_, v_a_1974_, v_a_1975_);
lean_dec_ref(v_a_1974_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(lean_object* v_as_1979_, size_t v_sz_1980_, size_t v_i_1981_, lean_object* v_b_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
uint8_t v___x_1985_; 
v___x_1985_ = lean_usize_dec_lt(v_i_1981_, v_sz_1980_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; 
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v_b_1982_);
lean_ctor_set(v___x_1986_, 1, v___y_1984_);
return v___x_1986_;
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1988_; lean_object* v_snd_1989_; lean_object* v___x_1990_; size_t v___x_1991_; size_t v___x_1992_; 
v_a_1987_ = lean_array_uget_borrowed(v_as_1979_, v_i_1981_);
lean_inc(v_a_1987_);
v___x_1988_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v_a_1987_, v___y_1983_, v___y_1984_);
v_snd_1989_ = lean_ctor_get(v___x_1988_, 1);
lean_inc(v_snd_1989_);
lean_dec_ref(v___x_1988_);
v___x_1990_ = lean_box(0);
v___x_1991_ = ((size_t)1ULL);
v___x_1992_ = lean_usize_add(v_i_1981_, v___x_1991_);
v_i_1981_ = v___x_1992_;
v_b_1982_ = v___x_1990_;
v___y_1984_ = v_snd_1989_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(lean_object* v_as_1994_, size_t v_sz_1995_, size_t v_i_1996_, lean_object* v_b_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = lean_usize_dec_lt(v_i_1996_, v_sz_1995_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v_b_1997_);
lean_ctor_set(v___x_2001_, 1, v___y_1999_);
return v___x_2001_;
}
else
{
uint8_t v_inEmph_2002_; uint8_t v_inBold_2003_; uint8_t v_inLink_2004_; lean_object* v_linePrefix_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v_snd_2009_; lean_object* v___x_2010_; lean_object* v_a_2011_; size_t v_sz_2012_; size_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v_snd_2018_; size_t v___x_2019_; size_t v___x_2020_; 
v_inEmph_2002_ = lean_ctor_get_uint8(v___y_1998_, sizeof(void*)*1);
v_inBold_2003_ = lean_ctor_get_uint8(v___y_1998_, sizeof(void*)*1 + 1);
v_inLink_2004_ = lean_ctor_get_uint8(v___y_1998_, sizeof(void*)*1 + 2);
v_linePrefix_2005_ = lean_ctor_get(v___y_1998_, 0);
v___x_2006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0));
lean_inc_ref_n(v_linePrefix_2005_, 2);
v___x_2007_ = lean_string_append(v_linePrefix_2005_, v___x_2006_);
v___x_2008_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2007_, v___y_1999_);
lean_dec_ref(v___x_2007_);
v_snd_2009_ = lean_ctor_get(v___x_2008_, 1);
lean_inc(v_snd_2009_);
lean_dec_ref(v___x_2008_);
v___x_2010_ = lean_box(0);
v_a_2011_ = lean_array_uget_borrowed(v_as_1994_, v_i_1996_);
v_sz_2012_ = lean_array_size(v_a_2011_);
v___x_2013_ = ((size_t)0ULL);
v___x_2014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
v___x_2015_ = lean_string_append(v_linePrefix_2005_, v___x_2014_);
v___x_2016_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*1, v_inEmph_2002_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*1 + 1, v_inBold_2003_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*1 + 2, v_inLink_2004_);
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_a_2011_, v_sz_2012_, v___x_2013_, v___x_2010_, v___x_2016_, v_snd_2009_);
lean_dec_ref(v___x_2016_);
v_snd_2018_ = lean_ctor_get(v___x_2017_, 1);
lean_inc(v_snd_2018_);
lean_dec_ref(v___x_2017_);
v___x_2019_ = ((size_t)1ULL);
v___x_2020_ = lean_usize_add(v_i_1996_, v___x_2019_);
v_i_1996_ = v___x_2020_;
v_b_1997_ = v___x_2010_;
v___y_1999_ = v_snd_2018_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(lean_object* v_as_2023_, size_t v_sz_2024_, size_t v_i_2025_, lean_object* v_b_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
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
uint8_t v_inEmph_2031_; uint8_t v_inBold_2032_; uint8_t v_inLink_2033_; lean_object* v_linePrefix_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v_snd_2040_; lean_object* v_a_2041_; lean_object* v___x_2042_; size_t v_sz_2043_; size_t v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v_snd_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; size_t v___x_2052_; size_t v___x_2053_; 
v_inEmph_2031_ = lean_ctor_get_uint8(v___y_2027_, sizeof(void*)*1);
v_inBold_2032_ = lean_ctor_get_uint8(v___y_2027_, sizeof(void*)*1 + 1);
v_inLink_2033_ = lean_ctor_get_uint8(v___y_2027_, sizeof(void*)*1 + 2);
v_linePrefix_2034_ = lean_ctor_get(v___y_2027_, 0);
lean_inc(v_b_2026_);
v___x_2035_ = l_Nat_reprFast(v_b_2026_);
v___x_2036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0));
v___x_2037_ = lean_string_append(v___x_2035_, v___x_2036_);
lean_inc_ref_n(v_linePrefix_2034_, 2);
v___x_2038_ = lean_string_append(v_linePrefix_2034_, v___x_2037_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2038_, v___y_2028_);
lean_dec_ref(v___x_2038_);
v_snd_2040_ = lean_ctor_get(v___x_2039_, 1);
lean_inc(v_snd_2040_);
lean_dec_ref(v___x_2039_);
v_a_2041_ = lean_array_uget_borrowed(v_as_2023_, v_i_2025_);
v___x_2042_ = lean_box(0);
v_sz_2043_ = lean_array_size(v_a_2041_);
v___x_2044_ = ((size_t)0ULL);
v___x_2045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
v___x_2046_ = lean_string_append(v_linePrefix_2034_, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*1, v_inEmph_2031_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*1 + 1, v_inBold_2032_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*1 + 2, v_inLink_2033_);
v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_a_2041_, v_sz_2043_, v___x_2044_, v___x_2042_, v___x_2047_, v_snd_2040_);
lean_dec_ref(v___x_2047_);
v_snd_2049_ = lean_ctor_get(v___x_2048_, 1);
lean_inc(v_snd_2049_);
lean_dec_ref(v___x_2048_);
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = lean_nat_add(v_b_2026_, v___x_2050_);
lean_dec(v_b_2026_);
v___x_2052_ = ((size_t)1ULL);
v___x_2053_ = lean_usize_add(v_i_2025_, v___x_2052_);
v_i_2025_ = v___x_2053_;
v_b_2026_ = v___x_2051_;
v___y_2028_ = v_snd_2049_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(lean_object* v_as_2058_, size_t v_sz_2059_, size_t v_i_2060_, lean_object* v_b_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
uint8_t v___x_2064_; 
v___x_2064_ = lean_usize_dec_lt(v_i_2060_, v_sz_2059_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v_b_2061_);
lean_ctor_set(v___x_2065_, 1, v___y_2063_);
return v___x_2065_;
}
else
{
uint8_t v_inEmph_2066_; uint8_t v_inBold_2067_; uint8_t v_inLink_2068_; lean_object* v_linePrefix_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_snd_2073_; lean_object* v_a_2074_; lean_object* v_term_2075_; lean_object* v_desc_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v_snd_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v_snd_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v_snd_2088_; lean_object* v___x_2089_; lean_object* v_snd_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v_snd_2093_; lean_object* v___x_2094_; size_t v___x_2095_; size_t v___x_2096_; 
v_inEmph_2066_ = lean_ctor_get_uint8(v___y_2062_, sizeof(void*)*1);
v_inBold_2067_ = lean_ctor_get_uint8(v___y_2062_, sizeof(void*)*1 + 1);
v_inLink_2068_ = lean_ctor_get_uint8(v___y_2062_, sizeof(void*)*1 + 2);
v_linePrefix_2069_ = lean_ctor_get(v___y_2062_, 0);
v___x_2070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0));
lean_inc_ref_n(v_linePrefix_2069_, 2);
v___x_2071_ = lean_string_append(v_linePrefix_2069_, v___x_2070_);
v___x_2072_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2071_, v___y_2063_);
lean_dec_ref(v___x_2071_);
v_snd_2073_ = lean_ctor_get(v___x_2072_, 1);
lean_inc(v_snd_2073_);
lean_dec_ref(v___x_2072_);
v_a_2074_ = lean_array_uget_borrowed(v_as_2058_, v_i_2060_);
v_term_2075_ = lean_ctor_get(v_a_2074_, 0);
v_desc_2076_ = lean_ctor_get(v_a_2074_, 1);
lean_inc_ref(v_term_2075_);
v___x_2077_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2077_, 0, v_term_2075_);
v___x_2078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__1));
v___x_2079_ = lean_string_append(v_linePrefix_2069_, v___x_2078_);
lean_inc_ref(v___x_2079_);
v___x_2080_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*1, v_inEmph_2066_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*1 + 1, v_inBold_2067_);
lean_ctor_set_uint8(v___x_2080_, sizeof(void*)*1 + 2, v_inLink_2068_);
v___x_2081_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_2077_, v___x_2080_, v_snd_2073_);
v_snd_2082_ = lean_ctor_get(v___x_2081_, 1);
lean_inc(v_snd_2082_);
lean_dec_ref(v___x_2081_);
v___x_2083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___closed__1));
v___x_2084_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v___x_2083_, v___x_2080_, v_snd_2082_);
v_snd_2085_ = lean_ctor_get(v___x_2084_, 1);
lean_inc(v_snd_2085_);
lean_dec_ref(v___x_2084_);
v___x_2086_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2087_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2086_, v_snd_2085_);
v_snd_2088_ = lean_ctor_get(v___x_2087_, 1);
lean_inc(v_snd_2088_);
lean_dec_ref(v___x_2087_);
v___x_2089_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2079_, v_snd_2088_);
lean_dec_ref(v___x_2079_);
v_snd_2090_ = lean_ctor_get(v___x_2089_, 1);
lean_inc(v_snd_2090_);
lean_dec_ref(v___x_2089_);
lean_inc_ref(v_desc_2076_);
v___x_2091_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_desc_2076_);
v___x_2092_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v___x_2091_, v___x_2080_, v_snd_2090_);
lean_dec_ref(v___x_2080_);
v_snd_2093_ = lean_ctor_get(v___x_2092_, 1);
lean_inc(v_snd_2093_);
lean_dec_ref(v___x_2092_);
v___x_2094_ = lean_box(0);
v___x_2095_ = ((size_t)1ULL);
v___x_2096_ = lean_usize_add(v_i_2060_, v___x_2095_);
v_i_2060_ = v___x_2096_;
v_b_2061_ = v___x_2094_;
v___y_2063_ = v_snd_2093_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(lean_object* v_x_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
switch(lean_obj_tag(v_x_2099_))
{
case 0:
{
lean_object* v_contents_2102_; lean_object* v___x_2103_; size_t v_sz_2104_; size_t v___x_2105_; lean_object* v___x_2106_; lean_object* v_snd_2107_; lean_object* v___x_2108_; 
v_contents_2102_ = lean_ctor_get(v_x_2099_, 0);
lean_inc_ref(v_contents_2102_);
lean_dec_ref(v_x_2099_);
v___x_2103_ = lean_box(0);
v_sz_2104_ = lean_array_size(v_contents_2102_);
v___x_2105_ = ((size_t)0ULL);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_contents_2102_, v_sz_2104_, v___x_2105_, v___x_2103_, v_a_2100_, v_a_2101_);
lean_dec_ref(v_contents_2102_);
v_snd_2107_ = lean_ctor_get(v___x_2106_, 1);
lean_inc(v_snd_2107_);
lean_dec_ref(v___x_2106_);
v___x_2108_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2107_);
return v___x_2108_;
}
case 1:
{
lean_object* v_content_2109_; lean_object* v___y_2111_; lean_object* v___y_2112_; uint8_t v___y_2120_; lean_object* v_currentBlock_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v_content_2109_ = lean_ctor_get(v_x_2099_, 0);
lean_inc_ref(v_content_2109_);
lean_dec_ref(v_x_2099_);
v_currentBlock_2124_ = lean_ctor_get(v_a_2101_, 1);
v___x_2125_ = lean_string_utf8_byte_size(v_currentBlock_2124_);
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = lean_nat_dec_eq(v___x_2125_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2128_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2129_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_2130_ = lean_nat_dec_le(v___x_2129_, v___x_2125_);
if (v___x_2130_ == 0)
{
v___y_2120_ = v___x_2127_;
goto v___jp_2119_;
}
else
{
lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2131_ = lean_nat_sub(v___x_2125_, v___x_2129_);
v___x_2132_ = lean_string_memcmp(v_currentBlock_2124_, v___x_2128_, v___x_2131_, v___x_2126_, v___x_2129_);
lean_dec(v___x_2131_);
v___y_2120_ = v___x_2132_;
goto v___jp_2119_;
}
}
else
{
v___y_2120_ = v___x_2127_;
goto v___jp_2119_;
}
v___jp_2110_:
{
lean_object* v_linePrefix_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v_snd_2117_; lean_object* v___x_2118_; 
v_linePrefix_2113_ = lean_ctor_get(v___y_2111_, 0);
v___x_2114_ = lean_string_length(v_linePrefix_2113_);
v___x_2115_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v___x_2114_, v_content_2109_);
lean_dec_ref(v_content_2109_);
v___x_2116_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2115_, v___y_2112_);
lean_dec_ref(v___x_2115_);
v_snd_2117_ = lean_ctor_get(v___x_2116_, 1);
lean_inc(v_snd_2117_);
lean_dec_ref(v___x_2116_);
v___x_2118_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2117_);
return v___x_2118_;
}
v___jp_2119_:
{
if (v___y_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v_snd_2123_; 
v___x_2121_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_2122_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2121_, v_a_2101_);
v_snd_2123_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_snd_2123_);
lean_dec_ref(v___x_2122_);
v___y_2111_ = v_a_2100_;
v___y_2112_ = v_snd_2123_;
goto v___jp_2110_;
}
else
{
v___y_2111_ = v_a_2100_;
v___y_2112_ = v_a_2101_;
goto v___jp_2110_;
}
}
}
case 2:
{
lean_object* v_items_2133_; lean_object* v___x_2134_; size_t v_sz_2135_; size_t v___x_2136_; lean_object* v___x_2137_; lean_object* v_snd_2138_; lean_object* v___x_2139_; 
v_items_2133_ = lean_ctor_get(v_x_2099_, 0);
lean_inc_ref(v_items_2133_);
lean_dec_ref(v_x_2099_);
v___x_2134_ = lean_box(0);
v_sz_2135_ = lean_array_size(v_items_2133_);
v___x_2136_ = ((size_t)0ULL);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_items_2133_, v_sz_2135_, v___x_2136_, v___x_2134_, v_a_2100_, v_a_2101_);
lean_dec_ref(v_items_2133_);
v_snd_2138_ = lean_ctor_get(v___x_2137_, 1);
lean_inc(v_snd_2138_);
lean_dec_ref(v___x_2137_);
v___x_2139_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2138_);
return v___x_2139_;
}
case 3:
{
lean_object* v_start_2140_; lean_object* v_items_2141_; lean_object* v___y_2143_; lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v_start_2140_ = lean_ctor_get(v_x_2099_, 0);
lean_inc(v_start_2140_);
v_items_2141_ = lean_ctor_get(v_x_2099_, 1);
lean_inc_ref(v_items_2141_);
lean_dec_ref(v_x_2099_);
v___x_2149_ = lean_unsigned_to_nat(1u);
v___x_2150_ = l_Int_toNat(v_start_2140_);
lean_dec(v_start_2140_);
v___x_2151_ = lean_nat_dec_le(v___x_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_dec(v___x_2150_);
v___y_2143_ = v___x_2149_;
goto v___jp_2142_;
}
else
{
v___y_2143_ = v___x_2150_;
goto v___jp_2142_;
}
v___jp_2142_:
{
size_t v_sz_2144_; size_t v___x_2145_; lean_object* v___x_2146_; lean_object* v_snd_2147_; lean_object* v___x_2148_; 
v_sz_2144_ = lean_array_size(v_items_2141_);
v___x_2145_ = ((size_t)0ULL);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_items_2141_, v_sz_2144_, v___x_2145_, v___y_2143_, v_a_2100_, v_a_2101_);
lean_dec_ref(v_items_2141_);
v_snd_2147_ = lean_ctor_get(v___x_2146_, 1);
lean_inc(v_snd_2147_);
lean_dec_ref(v___x_2146_);
v___x_2148_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2147_);
return v___x_2148_;
}
}
case 4:
{
lean_object* v_items_2152_; lean_object* v___x_2153_; size_t v_sz_2154_; size_t v___x_2155_; lean_object* v___x_2156_; lean_object* v_snd_2157_; lean_object* v___x_2158_; 
v_items_2152_ = lean_ctor_get(v_x_2099_, 0);
lean_inc_ref(v_items_2152_);
lean_dec_ref(v_x_2099_);
v___x_2153_ = lean_box(0);
v_sz_2154_ = lean_array_size(v_items_2152_);
v___x_2155_ = ((size_t)0ULL);
v___x_2156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_items_2152_, v_sz_2154_, v___x_2155_, v___x_2153_, v_a_2100_, v_a_2101_);
lean_dec_ref(v_items_2152_);
v_snd_2157_ = lean_ctor_get(v___x_2156_, 1);
lean_inc(v_snd_2157_);
lean_dec_ref(v___x_2156_);
v___x_2158_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2157_);
return v___x_2158_;
}
case 5:
{
lean_object* v_items_2159_; uint8_t v_inEmph_2160_; uint8_t v_inBold_2161_; uint8_t v_inLink_2162_; lean_object* v_linePrefix_2163_; lean_object* v___x_2164_; size_t v_sz_2165_; size_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v_snd_2171_; lean_object* v___x_2172_; 
v_items_2159_ = lean_ctor_get(v_x_2099_, 0);
lean_inc_ref(v_items_2159_);
lean_dec_ref(v_x_2099_);
v_inEmph_2160_ = lean_ctor_get_uint8(v_a_2100_, sizeof(void*)*1);
v_inBold_2161_ = lean_ctor_get_uint8(v_a_2100_, sizeof(void*)*1 + 1);
v_inLink_2162_ = lean_ctor_get_uint8(v_a_2100_, sizeof(void*)*1 + 2);
v_linePrefix_2163_ = lean_ctor_get(v_a_2100_, 0);
v___x_2164_ = lean_box(0);
v_sz_2165_ = lean_array_size(v_items_2159_);
v___x_2166_ = ((size_t)0ULL);
v___x_2167_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0));
lean_inc_ref(v_linePrefix_2163_);
v___x_2168_ = lean_string_append(v_linePrefix_2163_, v___x_2167_);
v___x_2169_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*1, v_inEmph_2160_);
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*1 + 1, v_inBold_2161_);
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*1 + 2, v_inLink_2162_);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_items_2159_, v_sz_2165_, v___x_2166_, v___x_2164_, v___x_2169_, v_a_2101_);
lean_dec_ref(v___x_2169_);
lean_dec_ref(v_items_2159_);
v_snd_2171_ = lean_ctor_get(v___x_2170_, 1);
lean_inc(v_snd_2171_);
lean_dec_ref(v___x_2170_);
v___x_2172_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2171_);
return v___x_2172_;
}
case 6:
{
lean_object* v_content_2173_; lean_object* v___x_2174_; size_t v_sz_2175_; size_t v___x_2176_; lean_object* v___x_2177_; lean_object* v_snd_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
v_content_2173_ = lean_ctor_get(v_x_2099_, 0);
lean_inc_ref(v_content_2173_);
lean_dec_ref(v_x_2099_);
v___x_2174_ = lean_box(0);
v_sz_2175_ = lean_array_size(v_content_2173_);
v___x_2176_ = ((size_t)0ULL);
v___x_2177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_content_2173_, v_sz_2175_, v___x_2176_, v___x_2174_, v_a_2100_, v_a_2101_);
lean_dec_ref(v_content_2173_);
v_snd_2178_ = lean_ctor_get(v___x_2177_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; 
v_unused_2186_ = lean_ctor_get(v___x_2177_, 0);
lean_dec(v_unused_2186_);
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_snd_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2174_);
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_snd_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
default: 
{
lean_object* v_content_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2208_; 
v_content_2187_ = lean_ctor_get(v_x_2099_, 1);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_x_2099_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; 
v_unused_2209_ = lean_ctor_get(v_x_2099_, 0);
lean_dec(v_unused_2209_);
v___x_2189_ = v_x_2099_;
v_isShared_2190_ = v_isSharedCheck_2208_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_content_2187_);
lean_dec(v_x_2099_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2208_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_array_get_size(v_content_2187_);
v___x_2193_ = lean_box(0);
v___x_2194_ = lean_nat_dec_lt(v___x_2191_, v___x_2192_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2196_; 
lean_dec_ref(v_content_2187_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set_tag(v___x_2189_, 0);
lean_ctor_set(v___x_2189_, 1, v_a_2101_);
lean_ctor_set(v___x_2189_, 0, v___x_2193_);
v___x_2196_ = v___x_2189_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_a_2101_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
else
{
uint8_t v___x_2198_; 
v___x_2198_ = lean_nat_dec_le(v___x_2192_, v___x_2192_);
if (v___x_2198_ == 0)
{
if (v___x_2194_ == 0)
{
lean_object* v___x_2200_; 
lean_dec_ref(v_content_2187_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set_tag(v___x_2189_, 0);
lean_ctor_set(v___x_2189_, 1, v_a_2101_);
lean_ctor_set(v___x_2189_, 0, v___x_2193_);
v___x_2200_ = v___x_2189_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_a_2101_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
else
{
size_t v___x_2202_; size_t v___x_2203_; lean_object* v___x_2204_; 
lean_del_object(v___x_2189_);
v___x_2202_ = ((size_t)0ULL);
v___x_2203_ = lean_usize_of_nat(v___x_2192_);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_content_2187_, v___x_2202_, v___x_2203_, v___x_2193_, v_a_2100_, v_a_2101_);
lean_dec_ref(v_content_2187_);
return v___x_2204_;
}
}
else
{
size_t v___x_2205_; size_t v___x_2206_; lean_object* v___x_2207_; 
lean_del_object(v___x_2189_);
v___x_2205_ = ((size_t)0ULL);
v___x_2206_ = lean_usize_of_nat(v___x_2192_);
v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_content_2187_, v___x_2205_, v___x_2206_, v___x_2193_, v_a_2100_, v_a_2101_);
lean_dec_ref(v_content_2187_);
return v___x_2207_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(lean_object* v_as_2210_, size_t v_i_2211_, size_t v_stop_2212_, lean_object* v_b_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
uint8_t v___x_2216_; 
v___x_2216_ = lean_usize_dec_eq(v_i_2211_, v_stop_2212_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v_fst_2219_; lean_object* v_snd_2220_; size_t v___x_2221_; size_t v___x_2222_; 
v___x_2217_ = lean_array_uget_borrowed(v_as_2210_, v_i_2211_);
lean_inc(v___x_2217_);
v___x_2218_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v___x_2217_, v___y_2214_, v___y_2215_);
v_fst_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_fst_2219_);
v_snd_2220_ = lean_ctor_get(v___x_2218_, 1);
lean_inc(v_snd_2220_);
lean_dec_ref(v___x_2218_);
v___x_2221_ = ((size_t)1ULL);
v___x_2222_ = lean_usize_add(v_i_2211_, v___x_2221_);
v_i_2211_ = v___x_2222_;
v_b_2213_ = v_fst_2219_;
v___y_2215_ = v_snd_2220_;
goto _start;
}
else
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2224_, 0, v_b_2213_);
lean_ctor_set(v___x_2224_, 1, v___y_2215_);
return v___x_2224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___boxed(lean_object* v_as_2225_, lean_object* v_i_2226_, lean_object* v_stop_2227_, lean_object* v_b_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
size_t v_i_boxed_2231_; size_t v_stop_boxed_2232_; lean_object* v_res_2233_; 
v_i_boxed_2231_ = lean_unbox_usize(v_i_2226_);
lean_dec(v_i_2226_);
v_stop_boxed_2232_ = lean_unbox_usize(v_stop_2227_);
lean_dec(v_stop_2227_);
v_res_2233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_as_2225_, v_i_boxed_2231_, v_stop_boxed_2232_, v_b_2228_, v___y_2229_, v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec_ref(v_as_2225_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2___boxed(lean_object* v_as_2234_, lean_object* v_sz_2235_, lean_object* v_i_2236_, lean_object* v_b_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
size_t v_sz_boxed_2240_; size_t v_i_boxed_2241_; lean_object* v_res_2242_; 
v_sz_boxed_2240_ = lean_unbox_usize(v_sz_2235_);
lean_dec(v_sz_2235_);
v_i_boxed_2241_ = lean_unbox_usize(v_i_2236_);
lean_dec(v_i_2236_);
v_res_2242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_as_2234_, v_sz_boxed_2240_, v_i_boxed_2241_, v_b_2237_, v___y_2238_, v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec_ref(v_as_2234_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___boxed(lean_object* v_as_2243_, lean_object* v_sz_2244_, lean_object* v_i_2245_, lean_object* v_b_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
size_t v_sz_boxed_2249_; size_t v_i_boxed_2250_; lean_object* v_res_2251_; 
v_sz_boxed_2249_ = lean_unbox_usize(v_sz_2244_);
lean_dec(v_sz_2244_);
v_i_boxed_2250_ = lean_unbox_usize(v_i_2245_);
lean_dec(v_i_2245_);
v_res_2251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_as_2243_, v_sz_boxed_2249_, v_i_boxed_2250_, v_b_2246_, v___y_2247_, v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec_ref(v_as_2243_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___boxed(lean_object* v_as_2252_, lean_object* v_sz_2253_, lean_object* v_i_2254_, lean_object* v_b_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
size_t v_sz_boxed_2258_; size_t v_i_boxed_2259_; lean_object* v_res_2260_; 
v_sz_boxed_2258_ = lean_unbox_usize(v_sz_2253_);
lean_dec(v_sz_2253_);
v_i_boxed_2259_ = lean_unbox_usize(v_i_2254_);
lean_dec(v_i_2254_);
v_res_2260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_as_2252_, v_sz_boxed_2258_, v_i_boxed_2259_, v_b_2255_, v___y_2256_, v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v_as_2252_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___boxed(lean_object* v_as_2261_, lean_object* v_sz_2262_, lean_object* v_i_2263_, lean_object* v_b_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
size_t v_sz_boxed_2267_; size_t v_i_boxed_2268_; lean_object* v_res_2269_; 
v_sz_boxed_2267_ = lean_unbox_usize(v_sz_2262_);
lean_dec(v_sz_2262_);
v_i_boxed_2268_ = lean_unbox_usize(v_i_2263_);
lean_dec(v_i_2263_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_as_2261_, v_sz_boxed_2267_, v_i_boxed_2268_, v_b_2264_, v___y_2265_, v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v_as_2261_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___boxed(lean_object* v_x_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v_x_2270_, v_a_2271_, v_a_2272_);
lean_dec_ref(v_a_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(lean_object* v_x_2274_, lean_object* v_x_2275_){
_start:
{
lean_object* v_zero_2276_; uint8_t v_isZero_2277_; 
v_zero_2276_ = lean_unsigned_to_nat(0u);
v_isZero_2277_ = lean_nat_dec_eq(v_x_2274_, v_zero_2276_);
if (v_isZero_2277_ == 1)
{
lean_dec(v_x_2274_);
return v_x_2275_;
}
else
{
uint32_t v___x_2278_; lean_object* v_one_2279_; lean_object* v_n_2280_; lean_object* v___x_2281_; 
v___x_2278_ = 35;
v_one_2279_ = lean_unsigned_to_nat(1u);
v_n_2280_ = lean_nat_sub(v_x_2274_, v_one_2279_);
lean_dec(v_x_2274_);
v___x_2281_ = lean_string_push(v_x_2275_, v___x_2278_);
v_x_2274_ = v_n_2280_;
v_x_2275_ = v___x_2281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(lean_object* v_level_2284_, lean_object* v_part_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v_snd_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v_snd_2296_; lean_object* v_title_2297_; lean_object* v_content_2298_; lean_object* v_subParts_2299_; lean_object* v___x_2300_; size_t v_sz_2301_; size_t v___x_2302_; lean_object* v___x_2303_; lean_object* v_snd_2304_; lean_object* v___x_2305_; lean_object* v_snd_2306_; size_t v_sz_2307_; lean_object* v___x_2308_; lean_object* v_snd_2309_; lean_object* v___x_2310_; lean_object* v_snd_2311_; size_t v_sz_2312_; lean_object* v___x_2313_; lean_object* v_snd_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v___x_2288_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_2289_ = lean_unsigned_to_nat(1u);
v___x_2290_ = lean_nat_add(v_level_2284_, v___x_2289_);
lean_inc(v___x_2290_);
v___x_2291_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v___x_2290_, v___x_2288_);
v___x_2292_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2291_, v_a_2287_);
lean_dec_ref(v___x_2291_);
v_snd_2293_ = lean_ctor_get(v___x_2292_, 1);
lean_inc(v_snd_2293_);
lean_dec_ref(v___x_2292_);
v___x_2294_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0));
v___x_2295_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2294_, v_snd_2293_);
v_snd_2296_ = lean_ctor_get(v___x_2295_, 1);
lean_inc(v_snd_2296_);
lean_dec_ref(v___x_2295_);
v_title_2297_ = lean_ctor_get(v_part_2285_, 0);
v_content_2298_ = lean_ctor_get(v_part_2285_, 3);
v_subParts_2299_ = lean_ctor_get(v_part_2285_, 4);
v___x_2300_ = lean_box(0);
v_sz_2301_ = lean_array_size(v_title_2297_);
v___x_2302_ = ((size_t)0ULL);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v_title_2297_, v_sz_2301_, v___x_2302_, v___x_2300_, v_a_2286_, v_snd_2296_);
v_snd_2304_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_snd_2304_);
lean_dec_ref(v___x_2303_);
v___x_2305_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2304_);
v_snd_2306_ = lean_ctor_get(v___x_2305_, 1);
lean_inc(v_snd_2306_);
lean_dec_ref(v___x_2305_);
v_sz_2307_ = lean_array_size(v_content_2298_);
v___x_2308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_content_2298_, v_sz_2307_, v___x_2302_, v___x_2300_, v_a_2286_, v_snd_2306_);
v_snd_2309_ = lean_ctor_get(v___x_2308_, 1);
lean_inc(v_snd_2309_);
lean_dec_ref(v___x_2308_);
v___x_2310_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2309_);
v_snd_2311_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_snd_2311_);
lean_dec_ref(v___x_2310_);
v_sz_2312_ = lean_array_size(v_subParts_2299_);
v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2290_, v_subParts_2299_, v_sz_2312_, v___x_2302_, v___x_2300_, v_a_2286_, v_snd_2311_);
lean_dec(v___x_2290_);
v_snd_2314_ = lean_ctor_get(v___x_2313_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v___x_2313_, 0);
lean_dec(v_unused_2322_);
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_snd_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2300_);
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_snd_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(lean_object* v___x_2323_, lean_object* v_as_2324_, size_t v_sz_2325_, size_t v_i_2326_, lean_object* v_b_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
uint8_t v___x_2330_; 
v___x_2330_ = lean_usize_dec_lt(v_i_2326_, v_sz_2325_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2331_, 0, v_b_2327_);
lean_ctor_set(v___x_2331_, 1, v___y_2329_);
return v___x_2331_;
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2333_; lean_object* v_snd_2334_; lean_object* v___x_2335_; size_t v___x_2336_; size_t v___x_2337_; 
v_a_2332_ = lean_array_uget_borrowed(v_as_2324_, v_i_2326_);
v___x_2333_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v___x_2323_, v_a_2332_, v___y_2328_, v___y_2329_);
v_snd_2334_ = lean_ctor_get(v___x_2333_, 1);
lean_inc(v_snd_2334_);
lean_dec_ref(v___x_2333_);
v___x_2335_ = lean_box(0);
v___x_2336_ = ((size_t)1ULL);
v___x_2337_ = lean_usize_add(v_i_2326_, v___x_2336_);
v_i_2326_ = v___x_2337_;
v_b_2327_ = v___x_2335_;
v___y_2329_ = v_snd_2334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg___boxed(lean_object* v___x_2339_, lean_object* v_as_2340_, lean_object* v_sz_2341_, lean_object* v_i_2342_, lean_object* v_b_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
size_t v_sz_boxed_2346_; size_t v_i_boxed_2347_; lean_object* v_res_2348_; 
v_sz_boxed_2346_ = lean_unbox_usize(v_sz_2341_);
lean_dec(v_sz_2341_);
v_i_boxed_2347_ = lean_unbox_usize(v_i_2342_);
lean_dec(v_i_2342_);
v_res_2348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2339_, v_as_2340_, v_sz_boxed_2346_, v_i_boxed_2347_, v_b_2343_, v___y_2344_, v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec_ref(v_as_2340_);
lean_dec(v___x_2339_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___boxed(lean_object* v_level_2349_, lean_object* v_part_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_level_2349_, v_part_2350_, v_a_2351_, v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec_ref(v_part_2350_);
lean_dec(v_level_2349_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(lean_object* v_as_2354_, size_t v_sz_2355_, size_t v_i_2356_, lean_object* v_b_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
uint8_t v___x_2360_; 
v___x_2360_ = lean_usize_dec_lt(v_i_2356_, v_sz_2355_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2361_, 0, v_b_2357_);
lean_ctor_set(v___x_2361_, 1, v___y_2359_);
return v___x_2361_;
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v_snd_2365_; lean_object* v___x_2366_; size_t v___x_2367_; size_t v___x_2368_; 
v_a_2362_ = lean_array_uget_borrowed(v_as_2354_, v_i_2356_);
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v___x_2363_, v_a_2362_, v___y_2358_, v___y_2359_);
v_snd_2365_ = lean_ctor_get(v___x_2364_, 1);
lean_inc(v_snd_2365_);
lean_dec_ref(v___x_2364_);
v___x_2366_ = lean_box(0);
v___x_2367_ = ((size_t)1ULL);
v___x_2368_ = lean_usize_add(v_i_2356_, v___x_2367_);
v_i_2356_ = v___x_2368_;
v_b_2357_ = v___x_2366_;
v___y_2359_ = v_snd_2365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3___boxed(lean_object* v_as_2370_, lean_object* v_sz_2371_, lean_object* v_i_2372_, lean_object* v_b_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
size_t v_sz_boxed_2376_; size_t v_i_boxed_2377_; lean_object* v_res_2378_; 
v_sz_boxed_2376_ = lean_unbox_usize(v_sz_2371_);
lean_dec(v_sz_2371_);
v_i_boxed_2377_ = lean_unbox_usize(v_i_2372_);
lean_dec(v_i_2372_);
v_res_2378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(v_as_2370_, v_sz_boxed_2376_, v_i_boxed_2377_, v_b_2373_, v___y_2374_, v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec_ref(v_as_2370_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(lean_object* v_text_2379_, size_t v_sz_2380_, size_t v___x_2381_, lean_object* v___x_2382_, lean_object* v_subsections_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___x_2386_; lean_object* v_snd_2387_; size_t v_sz_2388_; lean_object* v___x_2389_; lean_object* v_snd_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_text_2379_, v_sz_2380_, v___x_2381_, v___x_2382_, v___y_2384_, v___y_2385_);
v_snd_2387_ = lean_ctor_get(v___x_2386_, 1);
lean_inc(v_snd_2387_);
lean_dec_ref(v___x_2386_);
v_sz_2388_ = lean_array_size(v_subsections_2383_);
v___x_2389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(v_subsections_2383_, v_sz_2388_, v___x_2381_, v___x_2382_, v___y_2384_, v_snd_2387_);
v_snd_2390_ = lean_ctor_get(v___x_2389_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; 
v_unused_2398_ = lean_ctor_get(v___x_2389_, 0);
lean_dec(v_unused_2398_);
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_snd_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2382_);
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_snd_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed(lean_object* v_text_2399_, lean_object* v_sz_2400_, lean_object* v___x_2401_, lean_object* v___x_2402_, lean_object* v_subsections_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
size_t v_sz_boxed_2406_; size_t v___x_10664__boxed_2407_; lean_object* v_res_2408_; 
v_sz_boxed_2406_ = lean_unbox_usize(v_sz_2400_);
lean_dec(v_sz_2400_);
v___x_10664__boxed_2407_ = lean_unbox_usize(v___x_2401_);
lean_dec(v___x_2401_);
v_res_2408_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(v_text_2399_, v_sz_boxed_2406_, v___x_10664__boxed_2407_, v___x_2402_, v_subsections_2403_, v___y_2404_, v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec_ref(v_subsections_2403_);
lean_dec_ref(v_text_2399_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(lean_object* v_a_2411_){
_start:
{
lean_object* v_text_2412_; lean_object* v_subsections_2413_; lean_object* v___x_2414_; size_t v_sz_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___f_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_text_2412_ = lean_ctor_get(v_a_2411_, 0);
lean_inc_ref(v_text_2412_);
v_subsections_2413_ = lean_ctor_get(v_a_2411_, 1);
lean_inc_ref(v_subsections_2413_);
lean_dec_ref(v_a_2411_);
v___x_2414_ = lean_box(0);
v_sz_2415_ = lean_array_size(v_text_2412_);
v___x_2416_ = lean_box_usize(v_sz_2415_);
v___x_2417_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1));
v___f_2418_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed), 7, 5);
lean_closure_set(v___f_2418_, 0, v_text_2412_);
lean_closure_set(v___f_2418_, 1, v___x_2416_);
lean_closure_set(v___f_2418_, 2, v___x_2417_);
lean_closure_set(v___f_2418_, 3, v___x_2414_);
lean_closure_set(v___f_2418_, 4, v_subsections_2413_);
v___x_2419_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__11));
v___x_2420_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__13));
v___x_2421_ = l_Lean_Doc_MarkdownM_run_x27(v___f_2418_, v___x_2419_, v___x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(lean_object* v_p_2422_, lean_object* v_level_2423_, lean_object* v_part_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_level_2423_, v_part_2424_, v_a_2425_, v_a_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___boxed(lean_object* v_p_2428_, lean_object* v_level_2429_, lean_object* v_part_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(v_p_2428_, v_level_2429_, v_part_2430_, v_a_2431_, v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec_ref(v_part_2430_);
lean_dec(v_level_2429_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(lean_object* v_p_2434_, lean_object* v___x_2435_, lean_object* v_as_2436_, size_t v_sz_2437_, size_t v_i_2438_, lean_object* v_b_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2435_, v_as_2436_, v_sz_2437_, v_i_2438_, v_b_2439_, v___y_2440_, v___y_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___boxed(lean_object* v_p_2443_, lean_object* v___x_2444_, lean_object* v_as_2445_, lean_object* v_sz_2446_, lean_object* v_i_2447_, lean_object* v_b_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
size_t v_sz_boxed_2451_; size_t v_i_boxed_2452_; lean_object* v_res_2453_; 
v_sz_boxed_2451_ = lean_unbox_usize(v_sz_2446_);
lean_dec(v_sz_2446_);
v_i_boxed_2452_ = lean_unbox_usize(v_i_2447_);
lean_dec(v_i_2447_);
v_res_2453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(v_p_2443_, v___x_2444_, v_as_2445_, v_sz_boxed_2451_, v_i_boxed_2452_, v_b_2448_, v___y_2449_, v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec_ref(v_as_2445_);
lean_dec(v___x_2444_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2(lean_object* v_s_2454_, lean_object* v_pattern_2455_, lean_object* v_replacement_2456_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___redArg(v_s_2454_, v_replacement_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2___boxed(lean_object* v_s_2458_, lean_object* v_pattern_2459_, lean_object* v_replacement_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2(v_s_2458_, v_pattern_2459_, v_replacement_2460_);
lean_dec_ref(v_replacement_2460_);
lean_dec_ref(v_pattern_2459_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6(lean_object* v_s_2462_, lean_object* v_replacement_2463_, lean_object* v_inst_2464_, lean_object* v_R_2465_, lean_object* v_a_2466_, lean_object* v_b_2467_, lean_object* v_c_2468_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___redArg(v_s_2462_, v_replacement_2463_, v_a_2466_, v_b_2467_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6___boxed(lean_object* v_s_2470_, lean_object* v_replacement_2471_, lean_object* v_inst_2472_, lean_object* v_R_2473_, lean_object* v_a_2474_, lean_object* v_b_2475_, lean_object* v_c_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1_spec__2_spec__6(v_s_2470_, v_replacement_2471_, v_inst_2472_, v_R_2473_, v_a_2474_, v_b_2475_, v_c_2476_);
lean_dec_ref(v_replacement_2471_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_2478_, lean_object* v_declName_2479_, uint8_t v_includeBuiltin_2480_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_findInternalDocString_x3f(v_env_2478_, v_declName_2479_, v_includeBuiltin_2480_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2511_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2511_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2511_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
if (lean_obj_tag(v_a_2483_) == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2487_ = lean_box(0);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2487_);
v___x_2489_ = v___x_2485_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
else
{
lean_object* v_val_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2510_; 
v_val_2491_ = lean_ctor_get(v_a_2483_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_a_2483_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2493_ = v_a_2483_;
v_isShared_2494_ = v_isSharedCheck_2510_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_val_2491_);
lean_dec(v_a_2483_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2510_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
if (lean_obj_tag(v_val_2491_) == 0)
{
lean_object* v_val_2495_; lean_object* v___x_2497_; 
v_val_2495_ = lean_ctor_get(v_val_2491_, 0);
lean_inc(v_val_2495_);
lean_dec_ref(v_val_2491_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v_val_2495_);
v___x_2497_ = v___x_2493_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_val_2495_);
v___x_2497_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2499_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2497_);
v___x_2499_ = v___x_2485_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
else
{
lean_object* v_val_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v_val_2502_ = lean_ctor_get(v_val_2491_, 0);
lean_inc(v_val_2502_);
lean_dec_ref(v_val_2491_);
v___x_2503_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(v_val_2502_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2503_);
v___x_2505_ = v___x_2493_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2507_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2505_);
v___x_2507_ = v___x_2485_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
v_a_2512_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2482_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2482_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_2520_, lean_object* v_declName_2521_, lean_object* v_includeBuiltin_2522_, lean_object* v_a_2523_){
_start:
{
uint8_t v_includeBuiltin_boxed_2524_; lean_object* v_res_2525_; 
v_includeBuiltin_boxed_2524_ = lean_unbox(v_includeBuiltin_2522_);
v_res_2525_ = l_Lean_findSimpleDocString_x3f(v_env_2520_, v_declName_2521_, v_includeBuiltin_boxed_2524_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_es_2526_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_array_mk(v_es_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_x_2530_, lean_object* v_x_2531_, lean_object* v_es_2532_){
_start:
{
lean_object* v_ents_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v_ents_2533_ = lean_array_mk(v_es_2532_);
v___x_2534_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
lean_inc_ref(v_ents_2533_);
v___x_2535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
lean_ctor_set(v___x_2535_, 1, v_ents_2533_);
lean_ctor_set(v___x_2535_, 2, v_ents_2533_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_x_2536_, lean_object* v_x_2537_, lean_object* v_es_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v_x_2536_, v_x_2537_, v_es_2538_);
lean_dec_ref(v_x_2537_);
lean_dec_ref(v_x_2536_);
return v_res_2539_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = lean_unsigned_to_nat(32u);
v___x_2541_ = lean_mk_empty_array_with_capacity(v___x_2540_);
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v___x_2543_, lean_object* v_x_2544_){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; size_t v___x_2548_; lean_object* v___x_2549_; 
v___x_2545_ = lean_unsigned_to_nat(32u);
v___x_2546_ = lean_mk_empty_array_with_capacity(v___x_2545_);
v___x_2547_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_);
v___x_2548_ = ((size_t)5ULL);
lean_inc(v___x_2543_);
v___x_2549_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set(v___x_2549_, 1, v___x_2546_);
lean_ctor_set(v___x_2549_, 2, v___x_2543_);
lean_ctor_set(v___x_2549_, 3, v___x_2543_);
lean_ctor_set_usize(v___x_2549_, 4, v___x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v___x_2550_, lean_object* v_x_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v___x_2550_, v_x_2551_);
lean_dec_ref(v_x_2551_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
v___x_2574_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_a_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object* v_env_2577_, lean_object* v_doc_2578_){
_start:
{
lean_object* v___x_2579_; lean_object* v_toEnvExtension_2580_; lean_object* v_asyncMode_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2579_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2580_ = lean_ctor_get(v___x_2579_, 0);
v_asyncMode_2581_ = lean_ctor_get(v_toEnvExtension_2580_, 2);
v___x_2582_ = lean_box(0);
v___x_2583_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2579_, v_env_2577_, v_doc_2578_, v_asyncMode_2581_, v___x_2582_);
return v___x_2583_;
}
}
static lean_object* _init_l_Lean_getMainModuleDoc___closed__0(void){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object* v_env_2585_){
_start:
{
lean_object* v___x_2586_; lean_object* v_toEnvExtension_2587_; lean_object* v_asyncMode_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2586_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2587_ = lean_ctor_get(v___x_2586_, 0);
v_asyncMode_2588_ = lean_ctor_get(v_toEnvExtension_2587_, 2);
v___x_2589_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2590_ = lean_box(0);
v___x_2591_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2589_, v___x_2586_, v_env_2585_, v_asyncMode_2588_, v___x_2590_);
return v___x_2591_;
}
}
static lean_object* _init_l_Lean_getModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v___x_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object* v_env_2595_, lean_object* v_moduleName_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_Environment_getModuleIdx_x3f(v_env_2595_, v_moduleName_2596_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v___x_2598_; 
v___x_2598_ = lean_box(0);
return v___x_2598_;
}
else
{
lean_object* v_val_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2610_; 
v_val_2599_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2601_ = v___x_2597_;
v_isShared_2602_ = v_isSharedCheck_2610_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_val_2599_);
lean_dec(v___x_2597_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2610_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2608_; 
v___x_2603_ = lean_obj_once(&l_Lean_getModuleDoc_x3f___closed__0, &l_Lean_getModuleDoc_x3f___closed__0_once, _init_l_Lean_getModuleDoc_x3f___closed__0);
v___x_2604_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v___x_2605_ = 1;
v___x_2606_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2603_, v___x_2604_, v_env_2595_, v_val_2599_, v___x_2605_);
lean_dec(v_val_2599_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v___x_2606_);
v___x_2608_ = v___x_2601_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
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
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object* v_env_2611_, lean_object* v_moduleName_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_getModuleDoc_x3f(v_env_2611_, v_moduleName_2612_);
lean_dec(v_moduleName_2612_);
lean_dec_ref(v_env_2611_);
return v_res_2613_;
}
}
static lean_object* _init_l_Lean_getDocStringText___redArg___closed__1(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__0));
v___x_2616_ = l_Lean_stringToMessageData(v___x_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_stx_2622_){
_start:
{
lean_object* v_toApplicative_2629_; lean_object* v_toPure_2630_; lean_object* v_val_2632_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_toApplicative_2629_ = lean_ctor_get(v_inst_2620_, 0);
v_toPure_2630_ = lean_ctor_get(v_toApplicative_2629_, 1);
v___x_2639_ = lean_unsigned_to_nat(1u);
v___x_2640_ = l_Lean_Syntax_getArg(v_stx_2622_, v___x_2639_);
switch(lean_obj_tag(v___x_2640_))
{
case 2:
{
lean_object* v_val_2641_; 
lean_inc(v_toPure_2630_);
lean_dec(v_stx_2622_);
lean_dec_ref(v_inst_2621_);
lean_dec_ref(v_inst_2620_);
v_val_2641_ = lean_ctor_get(v___x_2640_, 1);
lean_inc_ref(v_val_2641_);
lean_dec_ref(v___x_2640_);
v_val_2632_ = v_val_2641_;
goto v___jp_2631_;
}
case 1:
{
lean_object* v_kind_2642_; 
v_kind_2642_ = lean_ctor_get(v___x_2640_, 1);
lean_inc(v_kind_2642_);
if (lean_obj_tag(v_kind_2642_) == 1)
{
lean_object* v_pre_2643_; 
v_pre_2643_ = lean_ctor_get(v_kind_2642_, 0);
lean_inc(v_pre_2643_);
if (lean_obj_tag(v_pre_2643_) == 1)
{
lean_object* v_pre_2644_; 
v_pre_2644_ = lean_ctor_get(v_pre_2643_, 0);
lean_inc(v_pre_2644_);
if (lean_obj_tag(v_pre_2644_) == 1)
{
lean_object* v_pre_2645_; 
v_pre_2645_ = lean_ctor_get(v_pre_2644_, 0);
lean_inc(v_pre_2645_);
if (lean_obj_tag(v_pre_2645_) == 1)
{
lean_object* v_pre_2646_; 
v_pre_2646_ = lean_ctor_get(v_pre_2645_, 0);
if (lean_obj_tag(v_pre_2646_) == 0)
{
lean_object* v_str_2647_; lean_object* v_str_2648_; lean_object* v_str_2649_; lean_object* v_str_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v_str_2647_ = lean_ctor_get(v_kind_2642_, 1);
lean_inc_ref(v_str_2647_);
lean_dec_ref(v_kind_2642_);
v_str_2648_ = lean_ctor_get(v_pre_2643_, 1);
lean_inc_ref(v_str_2648_);
lean_dec_ref(v_pre_2643_);
v_str_2649_ = lean_ctor_get(v_pre_2644_, 1);
lean_inc_ref(v_str_2649_);
lean_dec_ref(v_pre_2644_);
v_str_2650_ = lean_ctor_get(v_pre_2645_, 1);
lean_inc_ref(v_str_2650_);
lean_dec_ref(v_pre_2645_);
v___x_2651_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_2652_ = lean_string_dec_eq(v_str_2650_, v___x_2651_);
lean_dec_ref(v_str_2650_);
if (v___x_2652_ == 0)
{
lean_dec_ref(v_str_2649_);
lean_dec_ref(v_str_2648_);
lean_dec_ref(v_str_2647_);
lean_dec_ref(v___x_2640_);
goto v___jp_2623_;
}
else
{
lean_object* v___x_2653_; uint8_t v___x_2654_; 
v___x_2653_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__2));
v___x_2654_ = lean_string_dec_eq(v_str_2649_, v___x_2653_);
lean_dec_ref(v_str_2649_);
if (v___x_2654_ == 0)
{
lean_dec_ref(v_str_2648_);
lean_dec_ref(v_str_2647_);
lean_dec_ref(v___x_2640_);
goto v___jp_2623_;
}
else
{
lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2655_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__3));
v___x_2656_ = lean_string_dec_eq(v_str_2648_, v___x_2655_);
lean_dec_ref(v_str_2648_);
if (v___x_2656_ == 0)
{
lean_dec_ref(v_str_2647_);
lean_dec_ref(v___x_2640_);
goto v___jp_2623_;
}
else
{
lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__4));
v___x_2658_ = lean_string_dec_eq(v_str_2647_, v___x_2657_);
lean_dec_ref(v_str_2647_);
if (v___x_2658_ == 0)
{
lean_dec_ref(v___x_2640_);
goto v___jp_2623_;
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = lean_unsigned_to_nat(0u);
v___x_2660_ = l_Lean_Syntax_getArg(v___x_2640_, v___x_2659_);
lean_dec_ref(v___x_2640_);
if (lean_obj_tag(v___x_2660_) == 2)
{
lean_object* v_val_2661_; 
lean_inc(v_toPure_2630_);
lean_dec(v_stx_2622_);
lean_dec_ref(v_inst_2621_);
lean_dec_ref(v_inst_2620_);
v_val_2661_ = lean_ctor_get(v___x_2660_, 1);
lean_inc_ref(v_val_2661_);
lean_dec_ref(v___x_2660_);
v_val_2632_ = v_val_2661_;
goto v___jp_2631_;
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_dec(v___x_2660_);
v___x_2662_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2622_);
v___x_2663_ = l_Lean_MessageData_ofSyntax(v_stx_2622_);
v___x_2664_ = l_Lean_indentD(v___x_2663_);
v___x_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2662_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = l_Lean_throwErrorAt___redArg(v_inst_2620_, v_inst_2621_, v_stx_2622_, v___x_2665_);
return v___x_2666_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2645_);
lean_dec_ref(v_pre_2644_);
lean_dec_ref(v_pre_2643_);
lean_dec_ref(v_kind_2642_);
lean_dec_ref(v___x_2640_);
goto v___jp_2623_;
}
}
else
{
lean_dec_ref(v_pre_2644_);
lean_dec(v_pre_2645_);
lean_dec_ref(v_pre_2643_);
lean_dec_ref(v_kind_2642_);
lean_dec_ref(v___x_2640_);
goto v___jp_2623_;
}
}
else
{
lean_dec_ref(v_pre_2643_);
lean_dec(v_pre_2644_);
lean_dec_ref(v_kind_2642_);
lean_dec_ref(v___x_2640_);
goto v___jp_2623_;
}
}
else
{
lean_dec(v_pre_2643_);
lean_dec_ref(v_kind_2642_);
lean_dec_ref(v___x_2640_);
goto v___jp_2623_;
}
}
else
{
lean_dec(v_kind_2642_);
lean_dec_ref(v___x_2640_);
goto v___jp_2623_;
}
}
default: 
{
lean_dec(v___x_2640_);
goto v___jp_2623_;
}
}
v___jp_2623_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2624_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2622_);
v___x_2625_ = l_Lean_MessageData_ofSyntax(v_stx_2622_);
v___x_2626_ = l_Lean_indentD(v___x_2625_);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2624_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = l_Lean_throwErrorAt___redArg(v_inst_2620_, v_inst_2621_, v_stx_2622_, v___x_2627_);
return v___x_2628_;
}
v___jp_2631_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2633_ = lean_unsigned_to_nat(0u);
v___x_2634_ = lean_string_utf8_byte_size(v_val_2632_);
v___x_2635_ = lean_unsigned_to_nat(2u);
v___x_2636_ = lean_nat_sub(v___x_2634_, v___x_2635_);
v___x_2637_ = lean_string_utf8_extract(v_val_2632_, v___x_2633_, v___x_2636_);
lean_dec(v___x_2636_);
lean_dec_ref(v_val_2632_);
v___x_2638_ = lean_apply_2(v_toPure_2630_, lean_box(0), v___x_2637_);
return v___x_2638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object* v_m_2667_, lean_object* v_inst_2668_, lean_object* v_inst_2669_, lean_object* v_stx_2670_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_getDocStringText___redArg(v_inst_2668_, v_inst_2669_, v_stx_2670_);
return v___x_2671_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_2675_ = ((lean_object*)(l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0));
v___x_2676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
lean_ctor_set(v___x_2676_, 2, v___x_2674_);
return v___x_2676_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default(void){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_obj_once(&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1, &l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1_once, _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1);
return v___x_2677_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet(void){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object* v_a_2679_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = lean_nat_to_int(v_a_2679_);
return v___x_2680_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = lean_unsigned_to_nat(2u);
v___x_2688_ = lean_nat_to_int(v___x_2687_);
return v___x_2688_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = lean_unsigned_to_nat(1u);
v___x_2690_ = lean_nat_to_int(v___x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object* v_x_2703_, lean_object* v_x_2704_, lean_object* v_x_2705_){
_start:
{
if (lean_obj_tag(v_x_2705_) == 0)
{
lean_dec(v_x_2703_);
return v_x_2704_;
}
else
{
lean_object* v_head_2706_; lean_object* v_tail_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2718_; 
v_head_2706_ = lean_ctor_get(v_x_2705_, 0);
v_tail_2707_ = lean_ctor_get(v_x_2705_, 1);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_x_2705_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2709_ = v_x_2705_;
v_isShared_2710_ = v_isSharedCheck_2718_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_tail_2707_);
lean_inc(v_head_2706_);
lean_dec(v_x_2705_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2718_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
lean_inc(v_x_2703_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set_tag(v___x_2709_, 5);
lean_ctor_set(v___x_2709_, 1, v_x_2703_);
lean_ctor_set(v___x_2709_, 0, v_x_2704_);
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_x_2704_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_x_2703_);
v___x_2712_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2706_, v___x_2713_);
v___x_2715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2712_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v_x_2704_ = v___x_2715_;
v_x_2705_ = v_tail_2707_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object* v_x_2719_, lean_object* v_x_2720_, lean_object* v_x_2721_){
_start:
{
if (lean_obj_tag(v_x_2721_) == 0)
{
lean_dec(v_x_2719_);
return v_x_2720_;
}
else
{
lean_object* v_head_2722_; lean_object* v_tail_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2734_; 
v_head_2722_ = lean_ctor_get(v_x_2721_, 0);
v_tail_2723_ = lean_ctor_get(v_x_2721_, 1);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_x_2721_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2725_ = v_x_2721_;
v_isShared_2726_ = v_isSharedCheck_2734_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_tail_2723_);
lean_inc(v_head_2722_);
lean_dec(v_x_2721_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2734_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
lean_inc(v_x_2719_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set_tag(v___x_2725_, 5);
lean_ctor_set(v___x_2725_, 1, v_x_2719_);
lean_ctor_set(v___x_2725_, 0, v_x_2720_);
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_x_2720_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_x_2719_);
v___x_2728_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2729_ = lean_unsigned_to_nat(0u);
v___x_2730_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2722_, v___x_2729_);
v___x_2731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2728_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(v_x_2719_, v___x_2731_, v_tail_2723_);
return v___x_2732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2735_, lean_object* v_x_2736_){
_start:
{
if (lean_obj_tag(v_x_2735_) == 0)
{
lean_object* v___x_2737_; 
lean_dec(v_x_2736_);
v___x_2737_ = lean_box(0);
return v___x_2737_;
}
else
{
lean_object* v_tail_2738_; 
v_tail_2738_ = lean_ctor_get(v_x_2735_, 1);
if (lean_obj_tag(v_tail_2738_) == 0)
{
lean_object* v_head_2739_; lean_object* v___x_2740_; 
lean_dec(v_x_2736_);
v_head_2739_ = lean_ctor_get(v_x_2735_, 0);
lean_inc(v_head_2739_);
lean_dec_ref(v_x_2735_);
v___x_2740_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2739_);
return v___x_2740_;
}
else
{
lean_object* v_head_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_inc(v_tail_2738_);
v_head_2741_ = lean_ctor_get(v_x_2735_, 0);
lean_inc(v_head_2741_);
lean_dec_ref(v_x_2735_);
v___x_2742_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2741_);
v___x_2743_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(v_x_2736_, v___x_2742_, v_tail_2738_);
return v___x_2743_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0));
v___x_2746_ = lean_string_length(v___x_2745_);
return v___x_2746_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2747_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4);
v___x_2748_ = lean_nat_to_int(v___x_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_xs_2756_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___x_2757_ = lean_array_get_size(v_xs_2756_);
v___x_2758_ = lean_unsigned_to_nat(0u);
v___x_2759_ = lean_nat_dec_eq(v___x_2757_, v___x_2758_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2760_ = lean_array_to_list(v_xs_2756_);
v___x_2761_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2762_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_2760_, v___x_2761_);
v___x_2763_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_2764_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_2765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2764_);
lean_ctor_set(v___x_2765_, 1, v___x_2762_);
v___x_2766_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2763_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = l_Std_Format_fill(v___x_2768_);
return v___x_2769_;
}
else
{
lean_object* v___x_2770_; 
lean_dec_ref(v_xs_2756_);
v___x_2770_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_2770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_2825_, lean_object* v_prec_2826_){
_start:
{
switch(lean_obj_tag(v_x_2825_))
{
case 0:
{
lean_object* v_string_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2847_; 
v_string_2827_ = lean_ctor_get(v_x_2825_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_x_2825_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2829_ = v_x_2825_;
v_isShared_2830_ = v_isSharedCheck_2847_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_string_2827_);
lean_dec(v_x_2825_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2847_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___y_2832_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2843_ = lean_unsigned_to_nat(1024u);
v___x_2844_ = lean_nat_dec_le(v___x_2843_, v_prec_2826_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2832_ = v___x_2845_;
goto v___jp_2831_;
}
else
{
lean_object* v___x_2846_; 
v___x_2846_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2832_ = v___x_2846_;
goto v___jp_2831_;
}
v___jp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2833_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_2834_ = l_String_quote(v_string_2827_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set_tag(v___x_2829_, 3);
lean_ctor_set(v___x_2829_, 0, v___x_2834_);
v___x_2836_ = v___x_2829_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2833_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
lean_inc(v___y_2832_);
v___x_2838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___y_2832_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = 0;
v___x_2840_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*1, v___x_2839_);
v___x_2841_ = l_Repr_addAppParen(v___x_2840_, v_prec_2826_);
return v___x_2841_;
}
}
}
}
case 1:
{
lean_object* v_content_2848_; lean_object* v___y_2850_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_content_2848_ = lean_ctor_get(v_x_2825_, 0);
lean_inc_ref(v_content_2848_);
lean_dec_ref(v_x_2825_);
v___x_2858_ = lean_unsigned_to_nat(1024u);
v___x_2859_ = lean_nat_dec_le(v___x_2858_, v_prec_2826_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2850_ = v___x_2860_;
goto v___jp_2849_;
}
else
{
lean_object* v___x_2861_; 
v___x_2861_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2850_ = v___x_2861_;
goto v___jp_2849_;
}
v___jp_2849_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2851_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7));
v___x_2852_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2848_);
v___x_2853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2851_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
lean_inc(v___y_2850_);
v___x_2854_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___y_2850_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = 0;
v___x_2856_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*1, v___x_2855_);
v___x_2857_ = l_Repr_addAppParen(v___x_2856_, v_prec_2826_);
return v___x_2857_;
}
}
case 2:
{
lean_object* v_content_2862_; lean_object* v___y_2864_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v_content_2862_ = lean_ctor_get(v_x_2825_, 0);
lean_inc_ref(v_content_2862_);
lean_dec_ref(v_x_2825_);
v___x_2872_ = lean_unsigned_to_nat(1024u);
v___x_2873_ = lean_nat_dec_le(v___x_2872_, v_prec_2826_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; 
v___x_2874_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2864_ = v___x_2874_;
goto v___jp_2863_;
}
else
{
lean_object* v___x_2875_; 
v___x_2875_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2864_ = v___x_2875_;
goto v___jp_2863_;
}
v___jp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2865_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10));
v___x_2866_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2862_);
v___x_2867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2865_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
lean_inc(v___y_2864_);
v___x_2868_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___y_2864_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = 0;
v___x_2870_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2870_, 0, v___x_2868_);
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*1, v___x_2869_);
v___x_2871_ = l_Repr_addAppParen(v___x_2870_, v_prec_2826_);
return v___x_2871_;
}
}
case 3:
{
lean_object* v_string_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2896_; 
v_string_2876_ = lean_ctor_get(v_x_2825_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_x_2825_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2878_ = v_x_2825_;
v_isShared_2879_ = v_isSharedCheck_2896_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_string_2876_);
lean_dec(v_x_2825_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2896_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___y_2881_; lean_object* v___x_2892_; uint8_t v___x_2893_; 
v___x_2892_ = lean_unsigned_to_nat(1024u);
v___x_2893_ = lean_nat_dec_le(v___x_2892_, v_prec_2826_);
if (v___x_2893_ == 0)
{
lean_object* v___x_2894_; 
v___x_2894_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2881_ = v___x_2894_;
goto v___jp_2880_;
}
else
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2881_ = v___x_2895_;
goto v___jp_2880_;
}
v___jp_2880_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2882_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13));
v___x_2883_ = l_String_quote(v_string_2876_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2883_);
v___x_2885_ = v___x_2878_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2882_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
lean_inc(v___y_2881_);
v___x_2887_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___y_2881_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___x_2888_ = 0;
v___x_2889_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*1, v___x_2888_);
v___x_2890_ = l_Repr_addAppParen(v___x_2889_, v_prec_2826_);
return v___x_2890_;
}
}
}
}
case 4:
{
uint8_t v_mode_2897_; lean_object* v_string_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2923_; 
v_mode_2897_ = lean_ctor_get_uint8(v_x_2825_, sizeof(void*)*1);
v_string_2898_ = lean_ctor_get(v_x_2825_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_x_2825_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2900_ = v_x_2825_;
v_isShared_2901_ = v_isSharedCheck_2923_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_string_2898_);
lean_dec(v_x_2825_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2923_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___y_2903_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = lean_unsigned_to_nat(1024u);
v___x_2920_ = lean_nat_dec_le(v___x_2919_, v_prec_2826_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2903_ = v___x_2921_;
goto v___jp_2902_;
}
else
{
lean_object* v___x_2922_; 
v___x_2922_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2903_ = v___x_2922_;
goto v___jp_2902_;
}
v___jp_2902_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; uint8_t v___x_2914_; lean_object* v___x_2916_; 
v___x_2904_ = lean_box(1);
v___x_2905_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16));
v___x_2906_ = lean_unsigned_to_nat(1024u);
v___x_2907_ = l_Lean_Doc_instReprMathMode_repr(v_mode_2897_, v___x_2906_);
v___x_2908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2905_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v___x_2904_);
v___x_2910_ = l_String_quote(v_string_2898_);
v___x_2911_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2909_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
lean_inc(v___y_2903_);
v___x_2913_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___y_2903_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = 0;
if (v_isShared_2901_ == 0)
{
lean_ctor_set_tag(v___x_2900_, 6);
lean_ctor_set(v___x_2900_, 0, v___x_2913_);
v___x_2916_ = v___x_2900_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2913_);
v___x_2916_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; 
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*1, v___x_2914_);
v___x_2917_ = l_Repr_addAppParen(v___x_2916_, v_prec_2826_);
return v___x_2917_;
}
}
}
}
case 5:
{
lean_object* v_string_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2944_; 
v_string_2924_ = lean_ctor_get(v_x_2825_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_x_2825_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2926_ = v_x_2825_;
v_isShared_2927_ = v_isSharedCheck_2944_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_string_2924_);
lean_dec(v_x_2825_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2944_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___y_2929_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = lean_unsigned_to_nat(1024u);
v___x_2941_ = lean_nat_dec_le(v___x_2940_, v_prec_2826_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2929_ = v___x_2942_;
goto v___jp_2928_;
}
else
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2929_ = v___x_2943_;
goto v___jp_2928_;
}
v___jp_2928_:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2930_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19));
v___x_2931_ = l_String_quote(v_string_2924_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set_tag(v___x_2926_, 3);
lean_ctor_set(v___x_2926_, 0, v___x_2931_);
v___x_2933_ = v___x_2926_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2930_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
lean_inc(v___y_2929_);
v___x_2935_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___y_2929_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
v___x_2936_ = 0;
v___x_2937_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2937_, 0, v___x_2935_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*1, v___x_2936_);
v___x_2938_ = l_Repr_addAppParen(v___x_2937_, v_prec_2826_);
return v___x_2938_;
}
}
}
}
case 6:
{
lean_object* v_content_2945_; lean_object* v_url_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2970_; 
v_content_2945_ = lean_ctor_get(v_x_2825_, 0);
v_url_2946_ = lean_ctor_get(v_x_2825_, 1);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_x_2825_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2948_ = v_x_2825_;
v_isShared_2949_ = v_isSharedCheck_2970_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_url_2946_);
lean_inc(v_content_2945_);
lean_dec(v_x_2825_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2970_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___y_2951_; lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = lean_unsigned_to_nat(1024u);
v___x_2967_ = lean_nat_dec_le(v___x_2966_, v_prec_2826_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; 
v___x_2968_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2951_ = v___x_2968_;
goto v___jp_2950_;
}
else
{
lean_object* v___x_2969_; 
v___x_2969_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2951_ = v___x_2969_;
goto v___jp_2950_;
}
v___jp_2950_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
v___x_2952_ = lean_box(1);
v___x_2953_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22));
v___x_2954_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2945_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set_tag(v___x_2948_, 5);
lean_ctor_set(v___x_2948_, 1, v___x_2954_);
lean_ctor_set(v___x_2948_, 0, v___x_2953_);
v___x_2956_ = v___x_2948_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2953_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
lean_ctor_set(v___x_2957_, 1, v___x_2952_);
v___x_2958_ = l_String_quote(v_url_2946_);
v___x_2959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2957_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
lean_inc(v___y_2951_);
v___x_2961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___y_2951_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = 0;
v___x_2963_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*1, v___x_2962_);
v___x_2964_ = l_Repr_addAppParen(v___x_2963_, v_prec_2826_);
return v___x_2964_;
}
}
}
}
case 7:
{
lean_object* v_name_2971_; lean_object* v_content_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2996_; 
v_name_2971_ = lean_ctor_get(v_x_2825_, 0);
v_content_2972_ = lean_ctor_get(v_x_2825_, 1);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_x_2825_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2974_ = v_x_2825_;
v_isShared_2975_ = v_isSharedCheck_2996_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_content_2972_);
lean_inc(v_name_2971_);
lean_dec(v_x_2825_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2996_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___y_2977_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v___x_2992_ = lean_unsigned_to_nat(1024u);
v___x_2993_ = lean_nat_dec_le(v___x_2992_, v_prec_2826_);
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
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
v___x_2978_ = lean_box(1);
v___x_2979_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25));
v___x_2980_ = l_String_quote(v_name_2971_);
v___x_2981_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set_tag(v___x_2974_, 5);
lean_ctor_set(v___x_2974_, 1, v___x_2981_);
lean_ctor_set(v___x_2974_, 0, v___x_2979_);
v___x_2983_ = v___x_2974_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
lean_ctor_set(v___x_2984_, 1, v___x_2978_);
v___x_2985_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2972_);
v___x_2986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
lean_inc(v___y_2977_);
v___x_2987_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___y_2977_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = 0;
v___x_2989_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2989_, 0, v___x_2987_);
lean_ctor_set_uint8(v___x_2989_, sizeof(void*)*1, v___x_2988_);
v___x_2990_ = l_Repr_addAppParen(v___x_2989_, v_prec_2826_);
return v___x_2990_;
}
}
}
}
case 8:
{
lean_object* v_alt_2997_; lean_object* v_url_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3023_; 
v_alt_2997_ = lean_ctor_get(v_x_2825_, 0);
v_url_2998_ = lean_ctor_get(v_x_2825_, 1);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_x_2825_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3000_ = v_x_2825_;
v_isShared_3001_ = v_isSharedCheck_3023_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_url_2998_);
lean_inc(v_alt_2997_);
lean_dec(v_x_2825_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3023_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___y_3003_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3019_ = lean_unsigned_to_nat(1024u);
v___x_3020_ = lean_nat_dec_le(v___x_3019_, v_prec_2826_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3003_ = v___x_3021_;
goto v___jp_3002_;
}
else
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3003_ = v___x_3022_;
goto v___jp_3002_;
}
v___jp_3002_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3004_ = lean_box(1);
v___x_3005_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28));
v___x_3006_ = l_String_quote(v_alt_2997_);
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
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v___x_3004_);
v___x_3011_ = l_String_quote(v_url_2998_);
v___x_3012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
v___x_3013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3010_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
lean_inc(v___y_3003_);
v___x_3014_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___y_3003_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v___x_3015_ = 0;
v___x_3016_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3016_, 0, v___x_3014_);
lean_ctor_set_uint8(v___x_3016_, sizeof(void*)*1, v___x_3015_);
v___x_3017_ = l_Repr_addAppParen(v___x_3016_, v_prec_2826_);
return v___x_3017_;
}
}
}
}
case 9:
{
lean_object* v_content_3024_; lean_object* v___y_3026_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v_content_3024_ = lean_ctor_get(v_x_2825_, 0);
lean_inc_ref(v_content_3024_);
lean_dec_ref(v_x_2825_);
v___x_3034_ = lean_unsigned_to_nat(1024u);
v___x_3035_ = lean_nat_dec_le(v___x_3034_, v_prec_2826_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3026_ = v___x_3036_;
goto v___jp_3025_;
}
else
{
lean_object* v___x_3037_; 
v___x_3037_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3026_ = v___x_3037_;
goto v___jp_3025_;
}
v___jp_3025_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3027_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31));
v___x_3028_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3024_);
v___x_3029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
lean_inc(v___y_3026_);
v___x_3030_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___y_3026_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v___x_3031_ = 0;
v___x_3032_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set_uint8(v___x_3032_, sizeof(void*)*1, v___x_3031_);
v___x_3033_ = l_Repr_addAppParen(v___x_3032_, v_prec_2826_);
return v___x_3033_;
}
}
default: 
{
lean_object* v_container_3038_; lean_object* v_content_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3087_; 
v_container_3038_ = lean_ctor_get(v_x_2825_, 0);
v_content_3039_ = lean_ctor_get(v_x_2825_, 1);
v_isSharedCheck_3087_ = !lean_is_exclusive(v_x_2825_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3041_ = v_x_2825_;
v_isShared_3042_ = v_isSharedCheck_3087_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_content_3039_);
lean_inc(v_container_3038_);
lean_dec(v_x_2825_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3087_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___y_3044_; lean_object* v___x_3083_; uint8_t v___x_3084_; 
v___x_3083_ = lean_unsigned_to_nat(1024u);
v___x_3084_ = lean_nat_dec_le(v___x_3083_, v_prec_2826_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3044_ = v___x_3085_;
goto v___jp_3043_;
}
else
{
lean_object* v___x_3086_; 
v___x_3086_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3044_ = v___x_3086_;
goto v___jp_3043_;
}
v___jp_3043_:
{
lean_object* v_name_3045_; lean_object* v_val_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3082_; 
v_name_3045_ = lean_ctor_get(v_container_3038_, 0);
v_val_3046_ = lean_ctor_get(v_container_3038_, 1);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_container_3038_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3048_ = v_container_3038_;
v_isShared_3049_ = v_isSharedCheck_3082_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_val_3046_);
lean_inc(v_name_3045_);
lean_dec(v_container_3038_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3082_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3050_ = lean_box(1);
v___x_3051_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34));
v___x_3052_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3053_ = lean_unsigned_to_nat(0u);
v___x_3054_ = l_Lean_Name_reprPrec(v_name_3045_, v___x_3053_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set_tag(v___x_3048_, 5);
lean_ctor_set(v___x_3048_, 1, v___x_3054_);
lean_ctor_set(v___x_3048_, 0, v___x_3052_);
v___x_3056_ = v___x_3048_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3052_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3057_; uint8_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
v___x_3057_ = l_Std_Format_nestD(v___x_3056_);
v___x_3058_ = 0;
v___x_3059_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3059_, 0, v___x_3057_);
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*1, v___x_3058_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set_tag(v___x_3041_, 5);
lean_ctor_set(v___x_3041_, 1, v___x_3050_);
lean_ctor_set(v___x_3041_, 0, v___x_3059_);
v___x_3061_ = v___x_3041_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3059_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v___x_3050_);
v___x_3061_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3062_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3063_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3046_);
lean_dec(v_val_3046_);
v___x_3064_ = l_Lean_Name_reprPrec(v___x_3063_, v___x_3053_);
v___x_3065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3062_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3065_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = l_Std_Format_nestD(v___x_3067_);
v___x_3069_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*1, v___x_3058_);
v___x_3070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3061_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = l_Std_Format_nestD(v___x_3070_);
v___x_3072_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set_uint8(v___x_3072_, sizeof(void*)*1, v___x_3058_);
v___x_3073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3051_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v___x_3050_);
v___x_3075_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3039_);
v___x_3076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
lean_inc(v___y_3044_);
v___x_3077_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___y_3044_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set_uint8(v___x_3078_, sizeof(void*)*1, v___x_3058_);
v___x_3079_ = l_Repr_addAppParen(v___x_3078_, v_prec_2826_);
return v___x_3079_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_3088_){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = lean_unsigned_to_nat(0u);
v___x_3090_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v___y_3088_, v___x_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_3091_, lean_object* v_prec_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_x_3091_, v_prec_3092_);
lean_dec(v_prec_3092_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object* v_xs_3094_){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3095_ = lean_array_get_size(v_xs_3094_);
v___x_3096_ = lean_unsigned_to_nat(0u);
v___x_3097_ = lean_nat_dec_eq(v___x_3095_, v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3098_ = lean_array_to_list(v_xs_3094_);
v___x_3099_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3100_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_3098_, v___x_3099_);
v___x_3101_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3102_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
lean_ctor_set(v___x_3103_, 1, v___x_3100_);
v___x_3104_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3103_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3101_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = l_Std_Format_fill(v___x_3106_);
return v___x_3107_;
}
else
{
lean_object* v___x_3108_; 
lean_dec_ref(v_xs_3094_);
v___x_3108_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3108_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = lean_unsigned_to_nat(12u);
v___x_3140_ = lean_nat_to_int(v___x_3139_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object* v_x_3141_, lean_object* v_x_3142_, lean_object* v_x_3143_){
_start:
{
if (lean_obj_tag(v_x_3143_) == 0)
{
lean_dec(v_x_3141_);
return v_x_3142_;
}
else
{
lean_object* v_head_3144_; lean_object* v_tail_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3156_; 
v_head_3144_ = lean_ctor_get(v_x_3143_, 0);
v_tail_3145_ = lean_ctor_get(v_x_3143_, 1);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_x_3143_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3147_ = v_x_3143_;
v_isShared_3148_ = v_isSharedCheck_3156_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_tail_3145_);
lean_inc(v_head_3144_);
lean_dec(v_x_3143_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3156_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
lean_inc(v_x_3141_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 5);
lean_ctor_set(v___x_3147_, 1, v_x_3141_);
lean_ctor_set(v___x_3147_, 0, v_x_3142_);
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_x_3142_);
lean_ctor_set(v_reuseFailAlloc_3155_, 1, v_x_3141_);
v___x_3150_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3151_ = lean_unsigned_to_nat(0u);
v___x_3152_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_3144_, v___x_3151_);
v___x_3153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3150_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v_x_3142_ = v___x_3153_;
v_x_3143_ = v_tail_3145_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object* v_x_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_){
_start:
{
if (lean_obj_tag(v_x_3159_) == 0)
{
lean_dec(v_x_3157_);
return v_x_3158_;
}
else
{
lean_object* v_head_3160_; lean_object* v_tail_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3172_; 
v_head_3160_ = lean_ctor_get(v_x_3159_, 0);
v_tail_3161_ = lean_ctor_get(v_x_3159_, 1);
v_isSharedCheck_3172_ = !lean_is_exclusive(v_x_3159_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3163_ = v_x_3159_;
v_isShared_3164_ = v_isSharedCheck_3172_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_tail_3161_);
lean_inc(v_head_3160_);
lean_dec(v_x_3159_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3172_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
lean_inc(v_x_3157_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 5);
lean_ctor_set(v___x_3163_, 1, v_x_3157_);
lean_ctor_set(v___x_3163_, 0, v_x_3158_);
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_x_3158_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_x_3157_);
v___x_3166_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3167_ = lean_unsigned_to_nat(0u);
v___x_3168_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_3160_, v___x_3167_);
v___x_3169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3166_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(v_x_3157_, v___x_3169_, v_tail_3161_);
return v___x_3170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object* v_x_3173_, lean_object* v_x_3174_){
_start:
{
if (lean_obj_tag(v_x_3173_) == 0)
{
lean_object* v___x_3175_; 
lean_dec(v_x_3174_);
v___x_3175_ = lean_box(0);
return v___x_3175_;
}
else
{
lean_object* v_tail_3176_; 
v_tail_3176_ = lean_ctor_get(v_x_3173_, 1);
if (lean_obj_tag(v_tail_3176_) == 0)
{
lean_object* v_head_3177_; lean_object* v___x_3178_; 
lean_dec(v_x_3174_);
v_head_3177_ = lean_ctor_get(v_x_3173_, 0);
lean_inc(v_head_3177_);
lean_dec_ref(v_x_3173_);
v___x_3178_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3177_);
return v___x_3178_;
}
else
{
lean_object* v_head_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
lean_inc(v_tail_3176_);
v_head_3179_ = lean_ctor_get(v_x_3173_, 0);
lean_inc(v_head_3179_);
lean_dec_ref(v_x_3173_);
v___x_3180_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3179_);
v___x_3181_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(v_x_3174_, v___x_3180_, v_tail_3176_);
return v___x_3181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object* v_xs_3182_){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; uint8_t v___x_3185_; 
v___x_3183_ = lean_array_get_size(v_xs_3182_);
v___x_3184_ = lean_unsigned_to_nat(0u);
v___x_3185_ = lean_nat_dec_eq(v___x_3183_, v___x_3184_);
if (v___x_3185_ == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3186_ = lean_array_to_list(v_xs_3182_);
v___x_3187_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3188_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3186_, v___x_3187_);
v___x_3189_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3190_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set(v___x_3191_, 1, v___x_3188_);
v___x_3192_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3191_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___x_3194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3189_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = l_Std_Format_fill(v___x_3194_);
return v___x_3195_;
}
else
{
lean_object* v___x_3196_; 
lean_dec_ref(v_xs_3182_);
v___x_3196_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3196_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_3199_ = lean_string_length(v___x_3198_);
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9);
v___x_3201_ = lean_nat_to_int(v___x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_x_3207_){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; uint8_t v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3208_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6));
v___x_3209_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3210_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_x_3207_);
v___x_3211_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3209_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = 0;
v___x_3213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3213_, 0, v___x_3211_);
lean_ctor_set_uint8(v___x_3213_, sizeof(void*)*1, v___x_3212_);
v___x_3214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3208_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3216_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
lean_ctor_set(v___x_3217_, 1, v___x_3214_);
v___x_3218_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3217_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3215_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_ctor_set_uint8(v___x_3221_, sizeof(void*)*1, v___x_3212_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object* v_x_3222_, lean_object* v_x_3223_, lean_object* v_x_3224_){
_start:
{
if (lean_obj_tag(v_x_3224_) == 0)
{
lean_dec(v_x_3222_);
return v_x_3223_;
}
else
{
lean_object* v_head_3225_; lean_object* v_tail_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3236_; 
v_head_3225_ = lean_ctor_get(v_x_3224_, 0);
v_tail_3226_ = lean_ctor_get(v_x_3224_, 1);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_x_3224_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3228_ = v_x_3224_;
v_isShared_3229_ = v_isSharedCheck_3236_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_tail_3226_);
lean_inc(v_head_3225_);
lean_dec(v_x_3224_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3236_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
lean_inc(v_x_3222_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set_tag(v___x_3228_, 5);
lean_ctor_set(v___x_3228_, 1, v_x_3222_);
lean_ctor_set(v___x_3228_, 0, v_x_3223_);
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_x_3223_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_x_3222_);
v___x_3231_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3225_);
v___x_3233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3231_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v_x_3223_ = v___x_3233_;
v_x_3224_ = v_tail_3226_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object* v_x_3237_, lean_object* v_x_3238_, lean_object* v_x_3239_){
_start:
{
if (lean_obj_tag(v_x_3239_) == 0)
{
lean_dec(v_x_3237_);
return v_x_3238_;
}
else
{
lean_object* v_head_3240_; lean_object* v_tail_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3251_; 
v_head_3240_ = lean_ctor_get(v_x_3239_, 0);
v_tail_3241_ = lean_ctor_get(v_x_3239_, 1);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_x_3239_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3243_ = v_x_3239_;
v_isShared_3244_ = v_isSharedCheck_3251_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_tail_3241_);
lean_inc(v_head_3240_);
lean_dec(v_x_3239_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3251_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
lean_inc(v_x_3237_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set_tag(v___x_3243_, 5);
lean_ctor_set(v___x_3243_, 1, v_x_3237_);
lean_ctor_set(v___x_3243_, 0, v_x_3238_);
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_x_3238_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v_x_3237_);
v___x_3246_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3247_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3240_);
v___x_3248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(v_x_3237_, v___x_3248_, v_tail_3241_);
return v___x_3249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object* v_x_3252_, lean_object* v_x_3253_){
_start:
{
if (lean_obj_tag(v_x_3252_) == 0)
{
lean_object* v___x_3254_; 
lean_dec(v_x_3253_);
v___x_3254_ = lean_box(0);
return v___x_3254_;
}
else
{
lean_object* v_tail_3255_; 
v_tail_3255_ = lean_ctor_get(v_x_3252_, 1);
if (lean_obj_tag(v_tail_3255_) == 0)
{
lean_object* v_head_3256_; lean_object* v___x_3257_; 
lean_dec(v_x_3253_);
v_head_3256_ = lean_ctor_get(v_x_3252_, 0);
lean_inc(v_head_3256_);
lean_dec_ref(v_x_3252_);
v___x_3257_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3256_);
return v___x_3257_;
}
else
{
lean_object* v_head_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
lean_inc(v_tail_3255_);
v_head_3258_ = lean_ctor_get(v_x_3252_, 0);
lean_inc(v_head_3258_);
lean_dec_ref(v_x_3252_);
v___x_3259_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3258_);
v___x_3260_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(v_x_3253_, v___x_3259_, v_tail_3255_);
return v___x_3260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object* v_xs_3261_){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3262_ = lean_array_get_size(v_xs_3261_);
v___x_3263_ = lean_unsigned_to_nat(0u);
v___x_3264_ = lean_nat_dec_eq(v___x_3262_, v___x_3263_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3265_ = lean_array_to_list(v_xs_3261_);
v___x_3266_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3267_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(v___x_3265_, v___x_3266_);
v___x_3268_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3269_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
lean_ctor_set(v___x_3270_, 1, v___x_3267_);
v___x_3271_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3270_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
v___x_3273_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3268_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = l_Std_Format_fill(v___x_3273_);
return v___x_3274_;
}
else
{
lean_object* v___x_3275_; 
lean_dec_ref(v_xs_3261_);
v___x_3275_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3275_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = lean_unsigned_to_nat(0u);
v___x_3283_ = lean_nat_to_int(v___x_3282_);
return v___x_3283_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = lean_unsigned_to_nat(8u);
v___x_3300_ = lean_nat_to_int(v___x_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_x_3304_){
_start:
{
lean_object* v_term_3305_; lean_object* v_desc_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3338_; 
v_term_3305_ = lean_ctor_get(v_x_3304_, 0);
v_desc_3306_ = lean_ctor_get(v_x_3304_, 1);
v_isSharedCheck_3338_ = !lean_is_exclusive(v_x_3304_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3308_ = v_x_3304_;
v_isShared_3309_ = v_isSharedCheck_3338_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_desc_3306_);
lean_inc(v_term_3305_);
lean_dec(v_x_3304_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3338_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3310_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3311_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3));
v___x_3312_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3313_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_term_3305_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set_tag(v___x_3308_, 4);
lean_ctor_set(v___x_3308_, 1, v___x_3313_);
lean_ctor_set(v___x_3308_, 0, v___x_3312_);
v___x_3315_ = v___x_3308_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3312_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
uint8_t v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3316_ = 0;
v___x_3317_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3317_, 0, v___x_3315_);
lean_ctor_set_uint8(v___x_3317_, sizeof(void*)*1, v___x_3316_);
v___x_3318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3311_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3318_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = lean_box(1);
v___x_3322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6));
v___x_3324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v___x_3310_);
v___x_3326_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_desc_3306_);
v___x_3327_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3312_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
lean_ctor_set_uint8(v___x_3328_, sizeof(void*)*1, v___x_3316_);
v___x_3329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3325_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3331_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
lean_ctor_set(v___x_3332_, 1, v___x_3329_);
v___x_3333_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3330_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
lean_ctor_set_uint8(v___x_3336_, sizeof(void*)*1, v___x_3316_);
return v___x_3336_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object* v_x_3339_, lean_object* v_x_3340_, lean_object* v_x_3341_){
_start:
{
if (lean_obj_tag(v_x_3341_) == 0)
{
lean_dec(v_x_3339_);
return v_x_3340_;
}
else
{
lean_object* v_head_3342_; lean_object* v_tail_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3353_; 
v_head_3342_ = lean_ctor_get(v_x_3341_, 0);
v_tail_3343_ = lean_ctor_get(v_x_3341_, 1);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_x_3341_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3345_ = v_x_3341_;
v_isShared_3346_ = v_isSharedCheck_3353_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_tail_3343_);
lean_inc(v_head_3342_);
lean_dec(v_x_3341_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3353_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
lean_inc(v_x_3339_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set_tag(v___x_3345_, 5);
lean_ctor_set(v___x_3345_, 1, v_x_3339_);
lean_ctor_set(v___x_3345_, 0, v_x_3340_);
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_x_3340_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_x_3339_);
v___x_3348_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3342_);
v___x_3350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v_x_3340_ = v___x_3350_;
v_x_3341_ = v_tail_3343_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object* v_x_3354_, lean_object* v_x_3355_, lean_object* v_x_3356_){
_start:
{
if (lean_obj_tag(v_x_3356_) == 0)
{
lean_dec(v_x_3354_);
return v_x_3355_;
}
else
{
lean_object* v_head_3357_; lean_object* v_tail_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3368_; 
v_head_3357_ = lean_ctor_get(v_x_3356_, 0);
v_tail_3358_ = lean_ctor_get(v_x_3356_, 1);
v_isSharedCheck_3368_ = !lean_is_exclusive(v_x_3356_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3360_ = v_x_3356_;
v_isShared_3361_ = v_isSharedCheck_3368_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_tail_3358_);
lean_inc(v_head_3357_);
lean_dec(v_x_3356_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3368_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
lean_inc(v_x_3354_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 5);
lean_ctor_set(v___x_3360_, 1, v_x_3354_);
lean_ctor_set(v___x_3360_, 0, v_x_3355_);
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_x_3355_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_x_3354_);
v___x_3363_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3364_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3357_);
v___x_3365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3363_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(v_x_3354_, v___x_3365_, v_tail_3358_);
return v___x_3366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object* v_x_3369_, lean_object* v_x_3370_){
_start:
{
if (lean_obj_tag(v_x_3369_) == 0)
{
lean_object* v___x_3371_; 
lean_dec(v_x_3370_);
v___x_3371_ = lean_box(0);
return v___x_3371_;
}
else
{
lean_object* v_tail_3372_; 
v_tail_3372_ = lean_ctor_get(v_x_3369_, 1);
if (lean_obj_tag(v_tail_3372_) == 0)
{
lean_object* v_head_3373_; lean_object* v___x_3374_; 
lean_dec(v_x_3370_);
v_head_3373_ = lean_ctor_get(v_x_3369_, 0);
lean_inc(v_head_3373_);
lean_dec_ref(v_x_3369_);
v___x_3374_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3373_);
return v___x_3374_;
}
else
{
lean_object* v_head_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_inc(v_tail_3372_);
v_head_3375_ = lean_ctor_get(v_x_3369_, 0);
lean_inc(v_head_3375_);
lean_dec_ref(v_x_3369_);
v___x_3376_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3375_);
v___x_3377_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(v_x_3370_, v___x_3376_, v_tail_3372_);
return v___x_3377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object* v_xs_3378_){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3379_ = lean_array_get_size(v_xs_3378_);
v___x_3380_ = lean_unsigned_to_nat(0u);
v___x_3381_ = lean_nat_dec_eq(v___x_3379_, v___x_3380_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3382_ = lean_array_to_list(v_xs_3378_);
v___x_3383_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3384_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(v___x_3382_, v___x_3383_);
v___x_3385_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3386_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
lean_ctor_set(v___x_3387_, 1, v___x_3384_);
v___x_3388_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3385_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = l_Std_Format_fill(v___x_3390_);
return v___x_3391_;
}
else
{
lean_object* v___x_3392_; 
lean_dec_ref(v_xs_3378_);
v___x_3392_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object* v_x_3411_, lean_object* v_prec_3412_){
_start:
{
switch(lean_obj_tag(v_x_3411_))
{
case 0:
{
lean_object* v_contents_3413_; lean_object* v___y_3415_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v_contents_3413_ = lean_ctor_get(v_x_3411_, 0);
lean_inc_ref(v_contents_3413_);
lean_dec_ref(v_x_3411_);
v___x_3423_ = lean_unsigned_to_nat(1024u);
v___x_3424_ = lean_nat_dec_le(v___x_3423_, v_prec_3412_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3415_ = v___x_3425_;
goto v___jp_3414_;
}
else
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3415_ = v___x_3426_;
goto v___jp_3414_;
}
v___jp_3414_:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3416_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2));
v___x_3417_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_contents_3413_);
v___x_3418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
lean_inc(v___y_3415_);
v___x_3419_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___y_3415_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = 0;
v___x_3421_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3421_, 0, v___x_3419_);
lean_ctor_set_uint8(v___x_3421_, sizeof(void*)*1, v___x_3420_);
v___x_3422_ = l_Repr_addAppParen(v___x_3421_, v_prec_3412_);
return v___x_3422_;
}
}
case 1:
{
lean_object* v_content_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3447_; 
v_content_3427_ = lean_ctor_get(v_x_3411_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_x_3411_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3429_ = v_x_3411_;
v_isShared_3430_ = v_isSharedCheck_3447_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_content_3427_);
lean_dec(v_x_3411_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3447_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___y_3432_; lean_object* v___x_3443_; uint8_t v___x_3444_; 
v___x_3443_ = lean_unsigned_to_nat(1024u);
v___x_3444_ = lean_nat_dec_le(v___x_3443_, v_prec_3412_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3432_ = v___x_3445_;
goto v___jp_3431_;
}
else
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3432_ = v___x_3446_;
goto v___jp_3431_;
}
v___jp_3431_:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3433_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5));
v___x_3434_ = l_String_quote(v_content_3427_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set_tag(v___x_3429_, 3);
lean_ctor_set(v___x_3429_, 0, v___x_3434_);
v___x_3436_ = v___x_3429_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3433_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
lean_inc(v___y_3432_);
v___x_3438_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___y_3432_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = 0;
v___x_3440_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3440_, 0, v___x_3438_);
lean_ctor_set_uint8(v___x_3440_, sizeof(void*)*1, v___x_3439_);
v___x_3441_ = l_Repr_addAppParen(v___x_3440_, v_prec_3412_);
return v___x_3441_;
}
}
}
}
case 2:
{
lean_object* v_items_3448_; lean_object* v___y_3450_; lean_object* v___x_3458_; uint8_t v___x_3459_; 
v_items_3448_ = lean_ctor_get(v_x_3411_, 0);
lean_inc_ref(v_items_3448_);
lean_dec_ref(v_x_3411_);
v___x_3458_ = lean_unsigned_to_nat(1024u);
v___x_3459_ = lean_nat_dec_le(v___x_3458_, v_prec_3412_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3450_ = v___x_3460_;
goto v___jp_3449_;
}
else
{
lean_object* v___x_3461_; 
v___x_3461_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3450_ = v___x_3461_;
goto v___jp_3449_;
}
v___jp_3449_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3451_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8));
v___x_3452_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3448_);
v___x_3453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3451_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
lean_inc(v___y_3450_);
v___x_3454_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___y_3450_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = 0;
v___x_3456_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set_uint8(v___x_3456_, sizeof(void*)*1, v___x_3455_);
v___x_3457_ = l_Repr_addAppParen(v___x_3456_, v_prec_3412_);
return v___x_3457_;
}
}
case 3:
{
lean_object* v_start_3462_; lean_object* v_items_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3498_; 
v_start_3462_ = lean_ctor_get(v_x_3411_, 0);
v_items_3463_ = lean_ctor_get(v_x_3411_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_x_3411_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3465_ = v_x_3411_;
v_isShared_3466_ = v_isSharedCheck_3498_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_items_3463_);
lean_inc(v_start_3462_);
lean_dec(v_x_3411_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3498_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3483_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3494_ = lean_unsigned_to_nat(1024u);
v___x_3495_ = lean_nat_dec_le(v___x_3494_, v_prec_3412_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; 
v___x_3496_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3483_ = v___x_3496_;
goto v___jp_3482_;
}
else
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3483_ = v___x_3497_;
goto v___jp_3482_;
}
v___jp_3467_:
{
lean_object* v___x_3473_; 
lean_inc(v___y_3468_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set_tag(v___x_3465_, 5);
lean_ctor_set(v___x_3465_, 1, v___y_3471_);
lean_ctor_set(v___x_3465_, 0, v___y_3468_);
v___x_3473_ = v___x_3465_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___y_3468_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v___y_3471_);
v___x_3473_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; uint8_t v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
lean_inc(v___y_3469_);
v___x_3474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___y_3469_);
v___x_3475_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3463_);
v___x_3476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3474_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
lean_inc(v___y_3470_);
v___x_3477_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___y_3470_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v___x_3478_ = 0;
v___x_3479_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3479_, 0, v___x_3477_);
lean_ctor_set_uint8(v___x_3479_, sizeof(void*)*1, v___x_3478_);
v___x_3480_ = l_Repr_addAppParen(v___x_3479_, v_prec_3412_);
return v___x_3480_;
}
}
v___jp_3482_:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3484_ = lean_box(1);
v___x_3485_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11));
v___x_3486_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12, &l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12);
v___x_3487_ = lean_int_dec_lt(v_start_3462_, v___x_3486_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = l_Int_repr(v_start_3462_);
lean_dec(v_start_3462_);
v___x_3489_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
v___y_3468_ = v___x_3485_;
v___y_3469_ = v___x_3484_;
v___y_3470_ = v___y_3483_;
v___y_3471_ = v___x_3489_;
goto v___jp_3467_;
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3490_ = lean_unsigned_to_nat(1024u);
v___x_3491_ = l_Int_repr(v_start_3462_);
lean_dec(v_start_3462_);
v___x_3492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
v___x_3493_ = l_Repr_addAppParen(v___x_3492_, v___x_3490_);
v___y_3468_ = v___x_3485_;
v___y_3469_ = v___x_3484_;
v___y_3470_ = v___y_3483_;
v___y_3471_ = v___x_3493_;
goto v___jp_3467_;
}
}
}
}
case 4:
{
lean_object* v_items_3499_; lean_object* v___y_3501_; lean_object* v___x_3509_; uint8_t v___x_3510_; 
v_items_3499_ = lean_ctor_get(v_x_3411_, 0);
lean_inc_ref(v_items_3499_);
lean_dec_ref(v_x_3411_);
v___x_3509_ = lean_unsigned_to_nat(1024u);
v___x_3510_ = lean_nat_dec_le(v___x_3509_, v_prec_3412_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; 
v___x_3511_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3501_ = v___x_3511_;
goto v___jp_3500_;
}
else
{
lean_object* v___x_3512_; 
v___x_3512_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3501_ = v___x_3512_;
goto v___jp_3500_;
}
v___jp_3500_:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3502_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15));
v___x_3503_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(v_items_3499_);
v___x_3504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3502_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
lean_inc(v___y_3501_);
v___x_3505_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___y_3501_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
v___x_3506_ = 0;
v___x_3507_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3507_, 0, v___x_3505_);
lean_ctor_set_uint8(v___x_3507_, sizeof(void*)*1, v___x_3506_);
v___x_3508_ = l_Repr_addAppParen(v___x_3507_, v_prec_3412_);
return v___x_3508_;
}
}
case 5:
{
lean_object* v_items_3513_; lean_object* v___y_3515_; lean_object* v___x_3523_; uint8_t v___x_3524_; 
v_items_3513_ = lean_ctor_get(v_x_3411_, 0);
lean_inc_ref(v_items_3513_);
lean_dec_ref(v_x_3411_);
v___x_3523_ = lean_unsigned_to_nat(1024u);
v___x_3524_ = lean_nat_dec_le(v___x_3523_, v_prec_3412_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; 
v___x_3525_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3515_ = v___x_3525_;
goto v___jp_3514_;
}
else
{
lean_object* v___x_3526_; 
v___x_3526_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3515_ = v___x_3526_;
goto v___jp_3514_;
}
v___jp_3514_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3516_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18));
v___x_3517_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_items_3513_);
v___x_3518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3516_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
lean_inc(v___y_3515_);
v___x_3519_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___y_3515_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
v___x_3520_ = 0;
v___x_3521_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3521_, 0, v___x_3519_);
lean_ctor_set_uint8(v___x_3521_, sizeof(void*)*1, v___x_3520_);
v___x_3522_ = l_Repr_addAppParen(v___x_3521_, v_prec_3412_);
return v___x_3522_;
}
}
case 6:
{
lean_object* v_content_3527_; lean_object* v___y_3529_; lean_object* v___x_3537_; uint8_t v___x_3538_; 
v_content_3527_ = lean_ctor_get(v_x_3411_, 0);
lean_inc_ref(v_content_3527_);
lean_dec_ref(v_x_3411_);
v___x_3537_ = lean_unsigned_to_nat(1024u);
v___x_3538_ = lean_nat_dec_le(v___x_3537_, v_prec_3412_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; 
v___x_3539_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3529_ = v___x_3539_;
goto v___jp_3528_;
}
else
{
lean_object* v___x_3540_; 
v___x_3540_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3529_ = v___x_3540_;
goto v___jp_3528_;
}
v___jp_3528_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3530_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21));
v___x_3531_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3527_);
v___x_3532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3530_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
lean_inc(v___y_3529_);
v___x_3533_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___y_3529_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = 0;
v___x_3535_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set_uint8(v___x_3535_, sizeof(void*)*1, v___x_3534_);
v___x_3536_ = l_Repr_addAppParen(v___x_3535_, v_prec_3412_);
return v___x_3536_;
}
}
default: 
{
lean_object* v_container_3541_; lean_object* v_content_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3590_; 
v_container_3541_ = lean_ctor_get(v_x_3411_, 0);
v_content_3542_ = lean_ctor_get(v_x_3411_, 1);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_x_3411_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3544_ = v_x_3411_;
v_isShared_3545_ = v_isSharedCheck_3590_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_content_3542_);
lean_inc(v_container_3541_);
lean_dec(v_x_3411_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3590_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___y_3547_; lean_object* v___x_3586_; uint8_t v___x_3587_; 
v___x_3586_ = lean_unsigned_to_nat(1024u);
v___x_3587_ = lean_nat_dec_le(v___x_3586_, v_prec_3412_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; 
v___x_3588_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3547_ = v___x_3588_;
goto v___jp_3546_;
}
else
{
lean_object* v___x_3589_; 
v___x_3589_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3547_ = v___x_3589_;
goto v___jp_3546_;
}
v___jp_3546_:
{
lean_object* v_name_3548_; lean_object* v_val_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3585_; 
v_name_3548_ = lean_ctor_get(v_container_3541_, 0);
v_val_3549_ = lean_ctor_get(v_container_3541_, 1);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_container_3541_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3551_ = v_container_3541_;
v_isShared_3552_ = v_isSharedCheck_3585_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_val_3549_);
lean_inc(v_name_3548_);
lean_dec(v_container_3541_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3585_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3553_ = lean_box(1);
v___x_3554_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24));
v___x_3555_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3556_ = lean_unsigned_to_nat(0u);
v___x_3557_ = l_Lean_Name_reprPrec(v_name_3548_, v___x_3556_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set_tag(v___x_3551_, 5);
lean_ctor_set(v___x_3551_, 1, v___x_3557_);
lean_ctor_set(v___x_3551_, 0, v___x_3555_);
v___x_3559_ = v___x_3551_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3560_; uint8_t v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3564_; 
v___x_3560_ = l_Std_Format_nestD(v___x_3559_);
v___x_3561_ = 0;
v___x_3562_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set_uint8(v___x_3562_, sizeof(void*)*1, v___x_3561_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set_tag(v___x_3544_, 5);
lean_ctor_set(v___x_3544_, 1, v___x_3553_);
lean_ctor_set(v___x_3544_, 0, v___x_3562_);
v___x_3564_ = v___x_3544_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3562_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v___x_3553_);
v___x_3564_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3565_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3566_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3549_);
lean_dec(v_val_3549_);
v___x_3567_ = l_Lean_Name_reprPrec(v___x_3566_, v___x_3556_);
v___x_3568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3565_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = l_Std_Format_nestD(v___x_3570_);
v___x_3572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*1, v___x_3561_);
v___x_3573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3564_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = l_Std_Format_nestD(v___x_3573_);
v___x_3575_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
lean_ctor_set_uint8(v___x_3575_, sizeof(void*)*1, v___x_3561_);
v___x_3576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3554_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
lean_ctor_set(v___x_3577_, 1, v___x_3553_);
v___x_3578_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3542_);
v___x_3579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3577_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
lean_inc(v___y_3547_);
v___x_3580_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___y_3547_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v___x_3581_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
lean_ctor_set_uint8(v___x_3581_, sizeof(void*)*1, v___x_3561_);
v___x_3582_ = l_Repr_addAppParen(v___x_3581_, v_prec_3412_);
return v___x_3582_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object* v___y_3591_){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = lean_unsigned_to_nat(0u);
v___x_3593_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v___y_3591_, v___x_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object* v_x_3594_, lean_object* v_prec_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_x_3594_, v_prec_3595_);
lean_dec(v_prec_3595_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object* v_xs_3597_){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; 
v___x_3598_ = lean_array_get_size(v_xs_3597_);
v___x_3599_ = lean_unsigned_to_nat(0u);
v___x_3600_ = lean_nat_dec_eq(v___x_3598_, v___x_3599_);
if (v___x_3600_ == 0)
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3601_ = lean_array_to_list(v_xs_3597_);
v___x_3602_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3603_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3601_, v___x_3602_);
v___x_3604_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3605_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
lean_ctor_set(v___x_3606_, 1, v___x_3603_);
v___x_3607_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3606_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3604_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = l_Std_Format_fill(v___x_3609_);
return v___x_3610_;
}
else
{
lean_object* v___x_3611_; 
lean_dec_ref(v_xs_3597_);
v___x_3611_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3611_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object* v_x_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = ((lean_object*)(l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1));
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object* v_x_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3617_);
lean_dec(v_x_3617_);
return v_res_3618_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = lean_unsigned_to_nat(9u);
v___x_3629_ = lean_nat_to_int(v___x_3628_);
return v___x_3629_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = lean_unsigned_to_nat(15u);
v___x_3634_ = lean_nat_to_int(v___x_3633_);
return v___x_3634_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = lean_unsigned_to_nat(11u);
v___x_3642_ = lean_nat_to_int(v___x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object* v_x_3646_, lean_object* v_x_3647_, lean_object* v_x_3648_){
_start:
{
if (lean_obj_tag(v_x_3648_) == 0)
{
lean_dec(v_x_3646_);
return v_x_3647_;
}
else
{
lean_object* v_head_3649_; lean_object* v_tail_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3660_; 
v_head_3649_ = lean_ctor_get(v_x_3648_, 0);
v_tail_3650_ = lean_ctor_get(v_x_3648_, 1);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_x_3648_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3652_ = v_x_3648_;
v_isShared_3653_ = v_isSharedCheck_3660_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_tail_3650_);
lean_inc(v_head_3649_);
lean_dec(v_x_3648_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3660_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
lean_inc(v_x_3646_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set_tag(v___x_3652_, 5);
lean_ctor_set(v___x_3652_, 1, v_x_3646_);
lean_ctor_set(v___x_3652_, 0, v_x_3647_);
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_x_3647_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_x_3646_);
v___x_3655_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3656_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3649_);
v___x_3657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(v_x_3646_, v___x_3657_, v_tail_3650_);
return v___x_3658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object* v_x_3661_, lean_object* v_x_3662_){
_start:
{
if (lean_obj_tag(v_x_3661_) == 0)
{
lean_object* v___x_3663_; 
lean_dec(v_x_3662_);
v___x_3663_ = lean_box(0);
return v___x_3663_;
}
else
{
lean_object* v_tail_3664_; 
v_tail_3664_ = lean_ctor_get(v_x_3661_, 1);
if (lean_obj_tag(v_tail_3664_) == 0)
{
lean_object* v_head_3665_; lean_object* v___x_3666_; 
lean_dec(v_x_3662_);
v_head_3665_ = lean_ctor_get(v_x_3661_, 0);
lean_inc(v_head_3665_);
lean_dec_ref(v_x_3661_);
v___x_3666_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3665_);
return v___x_3666_;
}
else
{
lean_object* v_head_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
lean_inc(v_tail_3664_);
v_head_3667_ = lean_ctor_get(v_x_3661_, 0);
lean_inc(v_head_3667_);
lean_dec_ref(v_x_3661_);
v___x_3668_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3667_);
v___x_3669_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(v_x_3662_, v___x_3668_, v_tail_3664_);
return v___x_3669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object* v_xs_3670_){
_start:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v___x_3671_ = lean_array_get_size(v_xs_3670_);
v___x_3672_ = lean_unsigned_to_nat(0u);
v___x_3673_ = lean_nat_dec_eq(v___x_3671_, v___x_3672_);
if (v___x_3673_ == 0)
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3674_ = lean_array_to_list(v_xs_3670_);
v___x_3675_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3676_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(v___x_3674_, v___x_3675_);
v___x_3677_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3678_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
lean_ctor_set(v___x_3679_, 1, v___x_3676_);
v___x_3680_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3679_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3677_);
lean_ctor_set(v___x_3682_, 1, v___x_3681_);
v___x_3683_ = l_Std_Format_fill(v___x_3682_);
return v___x_3683_;
}
else
{
lean_object* v___x_3684_; 
lean_dec_ref(v_xs_3670_);
v___x_3684_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object* v_x_3685_){
_start:
{
lean_object* v_title_3686_; lean_object* v_titleString_3687_; lean_object* v_metadata_3688_; lean_object* v_content_3689_; lean_object* v_subParts_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v_title_3686_ = lean_ctor_get(v_x_3685_, 0);
lean_inc_ref(v_title_3686_);
v_titleString_3687_ = lean_ctor_get(v_x_3685_, 1);
lean_inc_ref(v_titleString_3687_);
v_metadata_3688_ = lean_ctor_get(v_x_3685_, 2);
lean_inc(v_metadata_3688_);
v_content_3689_ = lean_ctor_get(v_x_3685_, 3);
lean_inc_ref(v_content_3689_);
v_subParts_3690_ = lean_ctor_get(v_x_3685_, 4);
lean_inc_ref(v_subParts_3690_);
lean_dec_ref(v_x_3685_);
v___x_3691_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3692_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3));
v___x_3693_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4);
v___x_3694_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_title_3686_);
v___x_3695_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = 0;
v___x_3697_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3697_, 0, v___x_3695_);
lean_ctor_set_uint8(v___x_3697_, sizeof(void*)*1, v___x_3696_);
v___x_3698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3692_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3698_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
v___x_3701_ = lean_box(1);
v___x_3702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3700_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
v___x_3703_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6));
v___x_3704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
lean_ctor_set(v___x_3705_, 1, v___x_3691_);
v___x_3706_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7);
v___x_3707_ = l_String_quote(v_titleString_3687_);
v___x_3708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
v___x_3709_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3706_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set_uint8(v___x_3710_, sizeof(void*)*1, v___x_3696_);
v___x_3711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3705_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
lean_ctor_set(v___x_3712_, 1, v___x_3699_);
v___x_3713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set(v___x_3713_, 1, v___x_3701_);
v___x_3714_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9));
v___x_3715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3713_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
lean_ctor_set(v___x_3716_, 1, v___x_3691_);
v___x_3717_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3718_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_metadata_3688_);
lean_dec(v_metadata_3688_);
v___x_3719_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3717_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
lean_ctor_set_uint8(v___x_3720_, sizeof(void*)*1, v___x_3696_);
v___x_3721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3716_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
lean_ctor_set(v___x_3722_, 1, v___x_3699_);
v___x_3723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
lean_ctor_set(v___x_3723_, 1, v___x_3701_);
v___x_3724_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11));
v___x_3725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
lean_ctor_set(v___x_3726_, 1, v___x_3691_);
v___x_3727_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12);
v___x_3728_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_content_3689_);
v___x_3729_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
lean_ctor_set_uint8(v___x_3730_, sizeof(void*)*1, v___x_3696_);
v___x_3731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3726_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
lean_ctor_set(v___x_3732_, 1, v___x_3699_);
v___x_3733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
lean_ctor_set(v___x_3733_, 1, v___x_3701_);
v___x_3734_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14));
v___x_3735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set(v___x_3736_, 1, v___x_3691_);
v___x_3737_ = l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(v_subParts_3690_);
v___x_3738_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3717_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
lean_ctor_set_uint8(v___x_3739_, sizeof(void*)*1, v___x_3696_);
v___x_3740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3736_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3742_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
lean_ctor_set(v___x_3743_, 1, v___x_3740_);
v___x_3744_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3743_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3741_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*1, v___x_3696_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object* v_x_3748_, lean_object* v_x_3749_, lean_object* v_x_3750_){
_start:
{
if (lean_obj_tag(v_x_3750_) == 0)
{
lean_dec(v_x_3748_);
return v_x_3749_;
}
else
{
lean_object* v_head_3751_; lean_object* v_tail_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3762_; 
v_head_3751_ = lean_ctor_get(v_x_3750_, 0);
v_tail_3752_ = lean_ctor_get(v_x_3750_, 1);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_x_3750_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3754_ = v_x_3750_;
v_isShared_3755_ = v_isSharedCheck_3762_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_tail_3752_);
lean_inc(v_head_3751_);
lean_dec(v_x_3750_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3762_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
lean_inc(v_x_3748_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set_tag(v___x_3754_, 5);
lean_ctor_set(v___x_3754_, 1, v_x_3748_);
lean_ctor_set(v___x_3754_, 0, v_x_3749_);
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_x_3749_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_x_3748_);
v___x_3757_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3758_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3751_);
v___x_3759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v_x_3749_ = v___x_3759_;
v_x_3750_ = v_tail_3752_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object* v_x_3763_, lean_object* v_x_3764_){
_start:
{
lean_object* v_fst_3765_; lean_object* v_snd_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3776_; 
v_fst_3765_ = lean_ctor_get(v_x_3763_, 0);
v_snd_3766_ = lean_ctor_get(v_x_3763_, 1);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_x_3763_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3768_ = v_x_3763_;
v_isShared_3769_ = v_isSharedCheck_3776_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_snd_3766_);
lean_inc(v_fst_3765_);
lean_dec(v_x_3763_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3776_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3770_; lean_object* v___x_3772_; 
v___x_3770_ = l_Lean_instReprDeclarationRange_repr___redArg(v_fst_3765_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set_tag(v___x_3768_, 1);
lean_ctor_set(v___x_3768_, 1, v_x_3764_);
lean_ctor_set(v___x_3768_, 0, v___x_3770_);
v___x_3772_ = v___x_3768_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_x_3764_);
v___x_3772_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_snd_3766_);
v___x_3774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
lean_ctor_set(v___x_3774_, 1, v___x_3772_);
return v___x_3774_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object* v_x_3777_, lean_object* v_x_3778_, lean_object* v_x_3779_){
_start:
{
if (lean_obj_tag(v_x_3779_) == 0)
{
lean_dec(v_x_3777_);
return v_x_3778_;
}
else
{
lean_object* v_head_3780_; lean_object* v_tail_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3790_; 
v_head_3780_ = lean_ctor_get(v_x_3779_, 0);
v_tail_3781_ = lean_ctor_get(v_x_3779_, 1);
v_isSharedCheck_3790_ = !lean_is_exclusive(v_x_3779_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3783_ = v_x_3779_;
v_isShared_3784_ = v_isSharedCheck_3790_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_tail_3781_);
lean_inc(v_head_3780_);
lean_dec(v_x_3779_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3790_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
lean_inc(v_x_3777_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set_tag(v___x_3783_, 5);
lean_ctor_set(v___x_3783_, 1, v_x_3777_);
lean_ctor_set(v___x_3783_, 0, v_x_3778_);
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_x_3778_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_x_3777_);
v___x_3786_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3787_; 
v___x_3787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3786_);
lean_ctor_set(v___x_3787_, 1, v_head_3780_);
v_x_3778_ = v___x_3787_;
v_x_3779_ = v_tail_3781_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object* v_x_3791_, lean_object* v_x_3792_){
_start:
{
if (lean_obj_tag(v_x_3791_) == 0)
{
lean_object* v___x_3793_; 
lean_dec(v_x_3792_);
v___x_3793_ = lean_box(0);
return v___x_3793_;
}
else
{
lean_object* v_tail_3794_; 
v_tail_3794_ = lean_ctor_get(v_x_3791_, 1);
if (lean_obj_tag(v_tail_3794_) == 0)
{
lean_object* v_head_3795_; 
lean_dec(v_x_3792_);
v_head_3795_ = lean_ctor_get(v_x_3791_, 0);
lean_inc(v_head_3795_);
lean_dec_ref(v_x_3791_);
return v_head_3795_;
}
else
{
lean_object* v_head_3796_; lean_object* v___x_3797_; 
lean_inc(v_tail_3794_);
v_head_3796_ = lean_ctor_get(v_x_3791_, 0);
lean_inc(v_head_3796_);
lean_dec_ref(v_x_3791_);
v___x_3797_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(v_x_3792_, v_head_3796_, v_tail_3794_);
return v___x_3797_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0));
v___x_3800_ = lean_string_length(v___x_3799_);
return v___x_3800_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1);
v___x_3802_ = lean_nat_to_int(v___x_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object* v_x_3807_){
_start:
{
lean_object* v_fst_3808_; lean_object* v_snd_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3831_; 
v_fst_3808_ = lean_ctor_get(v_x_3807_, 0);
v_snd_3809_ = lean_ctor_get(v_x_3807_, 1);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_x_3807_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3811_ = v_x_3807_;
v_isShared_3812_ = v_isSharedCheck_3831_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_snd_3809_);
lean_inc(v_fst_3808_);
lean_dec(v_x_3807_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3831_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3817_; 
v___x_3813_ = l_Nat_reprFast(v_fst_3808_);
v___x_3814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
v___x_3815_ = lean_box(0);
if (v_isShared_3812_ == 0)
{
lean_ctor_set_tag(v___x_3811_, 1);
lean_ctor_set(v___x_3811_, 1, v___x_3815_);
lean_ctor_set(v___x_3811_, 0, v___x_3814_);
v___x_3817_ = v___x_3811_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; lean_object* v___x_3829_; 
v___x_3818_ = l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(v_snd_3809_, v___x_3817_);
v___x_3819_ = l_List_reverse___redArg(v___x_3818_);
v___x_3820_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3821_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(v___x_3819_, v___x_3820_);
v___x_3822_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2);
v___x_3823_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3));
v___x_3824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
lean_ctor_set(v___x_3824_, 1, v___x_3821_);
v___x_3825_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4));
v___x_3826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3822_);
lean_ctor_set(v___x_3827_, 1, v___x_3826_);
v___x_3828_ = 0;
v___x_3829_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3829_, 0, v___x_3827_);
lean_ctor_set_uint8(v___x_3829_, sizeof(void*)*1, v___x_3828_);
return v___x_3829_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object* v_x_3832_, lean_object* v_x_3833_, lean_object* v_x_3834_){
_start:
{
if (lean_obj_tag(v_x_3834_) == 0)
{
lean_dec(v_x_3832_);
return v_x_3833_;
}
else
{
lean_object* v_head_3835_; lean_object* v_tail_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3846_; 
v_head_3835_ = lean_ctor_get(v_x_3834_, 0);
v_tail_3836_ = lean_ctor_get(v_x_3834_, 1);
v_isSharedCheck_3846_ = !lean_is_exclusive(v_x_3834_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3838_ = v_x_3834_;
v_isShared_3839_ = v_isSharedCheck_3846_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_tail_3836_);
lean_inc(v_head_3835_);
lean_dec(v_x_3834_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3846_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
lean_inc(v_x_3832_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set_tag(v___x_3838_, 5);
lean_ctor_set(v___x_3838_, 1, v_x_3832_);
lean_ctor_set(v___x_3838_, 0, v_x_3833_);
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_x_3833_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v_x_3832_);
v___x_3841_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3835_);
v___x_3843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3841_);
lean_ctor_set(v___x_3843_, 1, v___x_3842_);
v_x_3833_ = v___x_3843_;
v_x_3834_ = v_tail_3836_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object* v_x_3847_, lean_object* v_x_3848_, lean_object* v_x_3849_){
_start:
{
if (lean_obj_tag(v_x_3849_) == 0)
{
lean_dec(v_x_3847_);
return v_x_3848_;
}
else
{
lean_object* v_head_3850_; lean_object* v_tail_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3861_; 
v_head_3850_ = lean_ctor_get(v_x_3849_, 0);
v_tail_3851_ = lean_ctor_get(v_x_3849_, 1);
v_isSharedCheck_3861_ = !lean_is_exclusive(v_x_3849_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3853_ = v_x_3849_;
v_isShared_3854_ = v_isSharedCheck_3861_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_tail_3851_);
lean_inc(v_head_3850_);
lean_dec(v_x_3849_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3861_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
lean_inc(v_x_3847_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set_tag(v___x_3853_, 5);
lean_ctor_set(v___x_3853_, 1, v_x_3847_);
lean_ctor_set(v___x_3853_, 0, v_x_3848_);
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_x_3848_);
lean_ctor_set(v_reuseFailAlloc_3860_, 1, v_x_3847_);
v___x_3856_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3857_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3850_);
v___x_3858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(v_x_3847_, v___x_3858_, v_tail_3851_);
return v___x_3859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object* v_x_3862_, lean_object* v_x_3863_){
_start:
{
if (lean_obj_tag(v_x_3862_) == 0)
{
lean_object* v___x_3864_; 
lean_dec(v_x_3863_);
v___x_3864_ = lean_box(0);
return v___x_3864_;
}
else
{
lean_object* v_tail_3865_; 
v_tail_3865_ = lean_ctor_get(v_x_3862_, 1);
if (lean_obj_tag(v_tail_3865_) == 0)
{
lean_object* v_head_3866_; lean_object* v___x_3867_; 
lean_dec(v_x_3863_);
v_head_3866_ = lean_ctor_get(v_x_3862_, 0);
lean_inc(v_head_3866_);
lean_dec_ref(v_x_3862_);
v___x_3867_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3866_);
return v___x_3867_;
}
else
{
lean_object* v_head_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
lean_inc(v_tail_3865_);
v_head_3868_ = lean_ctor_get(v_x_3862_, 0);
lean_inc(v_head_3868_);
lean_dec_ref(v_x_3862_);
v___x_3869_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3868_);
v___x_3870_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(v_x_3863_, v___x_3869_, v_tail_3865_);
return v___x_3870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object* v_xs_3871_){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; 
v___x_3872_ = lean_array_get_size(v_xs_3871_);
v___x_3873_ = lean_unsigned_to_nat(0u);
v___x_3874_ = lean_nat_dec_eq(v___x_3872_, v___x_3873_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3875_ = lean_array_to_list(v_xs_3871_);
v___x_3876_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3877_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(v___x_3875_, v___x_3876_);
v___x_3878_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3879_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
lean_ctor_set(v___x_3880_, 1, v___x_3877_);
v___x_3881_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3880_);
lean_ctor_set(v___x_3882_, 1, v___x_3881_);
v___x_3883_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3878_);
lean_ctor_set(v___x_3883_, 1, v___x_3882_);
v___x_3884_ = l_Std_Format_fill(v___x_3883_);
return v___x_3884_;
}
else
{
lean_object* v___x_3885_; 
lean_dec_ref(v_xs_3871_);
v___x_3885_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3885_;
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = lean_unsigned_to_nat(20u);
v___x_3902_ = lean_nat_to_int(v___x_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object* v_x_3903_){
_start:
{
lean_object* v_text_3904_; lean_object* v_sections_3905_; lean_object* v_declarationRange_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; uint8_t v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v_text_3904_ = lean_ctor_get(v_x_3903_, 0);
lean_inc_ref(v_text_3904_);
v_sections_3905_ = lean_ctor_get(v_x_3903_, 1);
lean_inc_ref(v_sections_3905_);
v_declarationRange_3906_ = lean_ctor_get(v_x_3903_, 2);
lean_inc_ref(v_declarationRange_3906_);
lean_dec_ref(v_x_3903_);
v___x_3907_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3908_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3));
v___x_3909_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3910_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_text_3904_);
v___x_3911_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3909_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = 0;
v___x_3913_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3913_, 0, v___x_3911_);
lean_ctor_set_uint8(v___x_3913_, sizeof(void*)*1, v___x_3912_);
v___x_3914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3908_);
lean_ctor_set(v___x_3914_, 1, v___x_3913_);
v___x_3915_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3914_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
v___x_3917_ = lean_box(1);
v___x_3918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3916_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
v___x_3919_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5));
v___x_3920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3918_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
lean_ctor_set(v___x_3921_, 1, v___x_3907_);
v___x_3922_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3923_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(v_sections_3905_);
v___x_3924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3922_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
lean_ctor_set_uint8(v___x_3925_, sizeof(void*)*1, v___x_3912_);
v___x_3926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3921_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
lean_ctor_set(v___x_3927_, 1, v___x_3915_);
v___x_3928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
lean_ctor_set(v___x_3928_, 1, v___x_3917_);
v___x_3929_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7));
v___x_3930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3928_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
lean_ctor_set(v___x_3931_, 1, v___x_3907_);
v___x_3932_ = lean_obj_once(&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8, &l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once, _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8);
v___x_3933_ = l_Lean_instReprDeclarationRange_repr___redArg(v_declarationRange_3906_);
v___x_3934_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3932_);
lean_ctor_set(v___x_3934_, 1, v___x_3933_);
v___x_3935_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
lean_ctor_set_uint8(v___x_3935_, sizeof(void*)*1, v___x_3912_);
v___x_3936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3931_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3938_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
lean_ctor_set(v___x_3939_, 1, v___x_3936_);
v___x_3940_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3939_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
v___x_3942_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3937_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
v___x_3943_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
lean_ctor_set_uint8(v___x_3943_, sizeof(void*)*1, v___x_3912_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object* v_x_3944_, lean_object* v_prec_3945_){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(v_x_3944_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object* v_x_3947_, lean_object* v_prec_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l_Lean_VersoModuleDocs_instReprSnippet_repr(v_x_3947_, v_prec_3948_);
lean_dec(v_prec_3948_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object* v_x_3950_, lean_object* v_x_3951_){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_x_3950_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object* v_x_3953_, lean_object* v_x_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(v_x_3953_, v_x_3954_);
lean_dec(v_x_3954_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_3956_, lean_object* v_prec_3957_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_x_3956_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_x_3959_, lean_object* v_prec_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(v_x_3959_, v_prec_3960_);
lean_dec(v_prec_3960_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object* v_x_3962_, lean_object* v_prec_3963_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_x_3962_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_x_3965_, lean_object* v_prec_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(v_x_3965_, v_prec_3966_);
lean_dec(v_prec_3966_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object* v_x_3968_, lean_object* v_x_3969_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3968_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object* v_x_3971_, lean_object* v_x_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(v_x_3971_, v_x_3972_);
lean_dec(v_x_3972_);
lean_dec(v_x_3971_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object* v_x_3974_, lean_object* v_prec_3975_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_x_3974_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object* v_x_3977_, lean_object* v_prec_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(v_x_3977_, v_prec_3978_);
lean_dec(v_prec_3978_);
return v_res_3979_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object* v_level_3982_, lean_object* v_snippet_3983_){
_start:
{
lean_object* v_sections_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; uint8_t v___x_3987_; 
v_sections_3984_ = lean_ctor_get(v_snippet_3983_, 1);
v___x_3985_ = lean_unsigned_to_nat(0u);
v___x_3986_ = lean_array_get_size(v_sections_3984_);
v___x_3987_ = lean_nat_dec_lt(v___x_3985_, v___x_3986_);
if (v___x_3987_ == 0)
{
uint8_t v___x_3988_; 
v___x_3988_ = 1;
return v___x_3988_;
}
else
{
lean_object* v___x_3989_; lean_object* v_fst_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; uint8_t v___x_3993_; 
v___x_3989_ = lean_array_fget_borrowed(v_sections_3984_, v___x_3985_);
v_fst_3990_ = lean_ctor_get(v___x_3989_, 0);
v___x_3991_ = lean_unsigned_to_nat(1u);
v___x_3992_ = lean_nat_add(v_level_3982_, v___x_3991_);
v___x_3993_ = lean_nat_dec_le(v_fst_3990_, v___x_3992_);
lean_dec(v___x_3992_);
return v___x_3993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object* v_level_3994_, lean_object* v_snippet_3995_){
_start:
{
uint8_t v_res_3996_; lean_object* v_r_3997_; 
v_res_3996_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_level_3994_, v_snippet_3995_);
lean_dec_ref(v_snippet_3995_);
lean_dec(v_level_3994_);
v_r_3997_ = lean_box(v_res_3996_);
return v_r_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object* v_snippet_3998_){
_start:
{
lean_object* v_sections_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; uint8_t v___x_4003_; 
v_sections_3999_ = lean_ctor_get(v_snippet_3998_, 1);
v___x_4000_ = lean_array_get_size(v_sections_3999_);
v___x_4001_ = lean_unsigned_to_nat(1u);
v___x_4002_ = lean_nat_sub(v___x_4000_, v___x_4001_);
v___x_4003_ = lean_nat_dec_lt(v___x_4002_, v___x_4000_);
if (v___x_4003_ == 0)
{
lean_object* v___x_4004_; 
lean_dec(v___x_4002_);
v___x_4004_ = lean_box(0);
return v___x_4004_;
}
else
{
lean_object* v___x_4005_; lean_object* v_fst_4006_; lean_object* v___x_4007_; 
v___x_4005_ = lean_array_fget_borrowed(v_sections_3999_, v___x_4002_);
lean_dec(v___x_4002_);
v_fst_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_fst_4006_);
v___x_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4007_, 0, v_fst_4006_);
return v___x_4007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object* v_snippet_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4008_);
lean_dec_ref(v_snippet_4008_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object* v_snippet_4010_, lean_object* v_block_4011_){
_start:
{
lean_object* v_text_4012_; lean_object* v_sections_4013_; lean_object* v_declarationRange_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; uint8_t v___x_4017_; 
v_text_4012_ = lean_ctor_get(v_snippet_4010_, 0);
v_sections_4013_ = lean_ctor_get(v_snippet_4010_, 1);
v_declarationRange_4014_ = lean_ctor_get(v_snippet_4010_, 2);
v___x_4015_ = lean_array_get_size(v_sections_4013_);
v___x_4016_ = lean_unsigned_to_nat(0u);
v___x_4017_ = lean_nat_dec_eq(v___x_4015_, v___x_4016_);
if (v___x_4017_ == 0)
{
lean_object* v___x_4018_; lean_object* v___x_4019_; uint8_t v___x_4020_; 
v___x_4018_ = lean_unsigned_to_nat(1u);
v___x_4019_ = lean_nat_sub(v___x_4015_, v___x_4018_);
v___x_4020_ = lean_nat_dec_lt(v___x_4019_, v___x_4015_);
if (v___x_4020_ == 0)
{
lean_dec(v___x_4019_);
lean_dec_ref(v_block_4011_);
return v_snippet_4010_;
}
else
{
lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4064_; 
lean_inc_ref(v_declarationRange_4014_);
lean_inc_ref(v_sections_4013_);
lean_inc_ref(v_text_4012_);
v_isSharedCheck_4064_ = !lean_is_exclusive(v_snippet_4010_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; lean_object* v_unused_4066_; lean_object* v_unused_4067_; 
v_unused_4065_ = lean_ctor_get(v_snippet_4010_, 2);
lean_dec(v_unused_4065_);
v_unused_4066_ = lean_ctor_get(v_snippet_4010_, 1);
lean_dec(v_unused_4066_);
v_unused_4067_ = lean_ctor_get(v_snippet_4010_, 0);
lean_dec(v_unused_4067_);
v___x_4022_ = v_snippet_4010_;
v_isShared_4023_ = v_isSharedCheck_4064_;
goto v_resetjp_4021_;
}
else
{
lean_dec(v_snippet_4010_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4064_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v_v_4024_; lean_object* v_snd_4025_; lean_object* v_snd_4026_; lean_object* v_fst_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4062_; 
v_v_4024_ = lean_array_fget(v_sections_4013_, v___x_4019_);
v_snd_4025_ = lean_ctor_get(v_v_4024_, 1);
lean_inc(v_snd_4025_);
v_snd_4026_ = lean_ctor_get(v_snd_4025_, 1);
lean_inc(v_snd_4026_);
v_fst_4027_ = lean_ctor_get(v_v_4024_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v_v_4024_);
if (v_isSharedCheck_4062_ == 0)
{
lean_object* v_unused_4063_; 
v_unused_4063_ = lean_ctor_get(v_v_4024_, 1);
lean_dec(v_unused_4063_);
v___x_4029_ = v_v_4024_;
v_isShared_4030_ = v_isSharedCheck_4062_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_fst_4027_);
lean_dec(v_v_4024_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4062_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v_fst_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4060_; 
v_fst_4031_ = lean_ctor_get(v_snd_4025_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_snd_4025_);
if (v_isSharedCheck_4060_ == 0)
{
lean_object* v_unused_4061_; 
v_unused_4061_ = lean_ctor_get(v_snd_4025_, 1);
lean_dec(v_unused_4061_);
v___x_4033_ = v_snd_4025_;
v_isShared_4034_ = v_isSharedCheck_4060_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_fst_4031_);
lean_dec(v_snd_4025_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4060_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v_title_4035_; lean_object* v_titleString_4036_; lean_object* v_metadata_4037_; lean_object* v_content_4038_; lean_object* v_subParts_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4059_; 
v_title_4035_ = lean_ctor_get(v_snd_4026_, 0);
v_titleString_4036_ = lean_ctor_get(v_snd_4026_, 1);
v_metadata_4037_ = lean_ctor_get(v_snd_4026_, 2);
v_content_4038_ = lean_ctor_get(v_snd_4026_, 3);
v_subParts_4039_ = lean_ctor_get(v_snd_4026_, 4);
v_isSharedCheck_4059_ = !lean_is_exclusive(v_snd_4026_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4041_ = v_snd_4026_;
v_isShared_4042_ = v_isSharedCheck_4059_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_subParts_4039_);
lean_inc(v_content_4038_);
lean_inc(v_metadata_4037_);
lean_inc(v_titleString_4036_);
lean_inc(v_title_4035_);
lean_dec(v_snd_4026_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4059_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4043_; lean_object* v_xs_x27_4044_; lean_object* v___x_4045_; lean_object* v___x_4047_; 
v___x_4043_ = lean_box(0);
v_xs_x27_4044_ = lean_array_fset(v_sections_4013_, v___x_4019_, v___x_4043_);
v___x_4045_ = lean_array_push(v_content_4038_, v_block_4011_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 3, v___x_4045_);
v___x_4047_ = v___x_4041_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_title_4035_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v_titleString_4036_);
lean_ctor_set(v_reuseFailAlloc_4058_, 2, v_metadata_4037_);
lean_ctor_set(v_reuseFailAlloc_4058_, 3, v___x_4045_);
lean_ctor_set(v_reuseFailAlloc_4058_, 4, v_subParts_4039_);
v___x_4047_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
lean_object* v___x_4049_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 1, v___x_4047_);
v___x_4049_ = v___x_4033_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_fst_4031_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v___x_4047_);
v___x_4049_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
lean_object* v___x_4051_; 
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 1, v___x_4049_);
v___x_4051_ = v___x_4029_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_fst_4027_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
lean_object* v___x_4052_; lean_object* v___x_4054_; 
v___x_4052_ = lean_array_fset(v_xs_x27_4044_, v___x_4019_, v___x_4051_);
lean_dec(v___x_4019_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 1, v___x_4052_);
v___x_4054_ = v___x_4022_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_text_4012_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v___x_4052_);
lean_ctor_set(v_reuseFailAlloc_4055_, 2, v_declarationRange_4014_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
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
lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4075_; 
lean_inc_ref(v_declarationRange_4014_);
lean_inc_ref(v_sections_4013_);
lean_inc_ref(v_text_4012_);
v_isSharedCheck_4075_ = !lean_is_exclusive(v_snippet_4010_);
if (v_isSharedCheck_4075_ == 0)
{
lean_object* v_unused_4076_; lean_object* v_unused_4077_; lean_object* v_unused_4078_; 
v_unused_4076_ = lean_ctor_get(v_snippet_4010_, 2);
lean_dec(v_unused_4076_);
v_unused_4077_ = lean_ctor_get(v_snippet_4010_, 1);
lean_dec(v_unused_4077_);
v_unused_4078_ = lean_ctor_get(v_snippet_4010_, 0);
lean_dec(v_unused_4078_);
v___x_4069_ = v_snippet_4010_;
v_isShared_4070_ = v_isSharedCheck_4075_;
goto v_resetjp_4068_;
}
else
{
lean_dec(v_snippet_4010_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4075_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4071_; lean_object* v___x_4073_; 
v___x_4071_ = lean_array_push(v_text_4012_, v_block_4011_);
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 0, v___x_4071_);
v___x_4073_ = v___x_4069_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___x_4071_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_sections_4013_);
lean_ctor_set(v_reuseFailAlloc_4074_, 2, v_declarationRange_4014_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object* v_snippet_4079_, lean_object* v_level_4080_, lean_object* v_range_4081_, lean_object* v_part_4082_){
_start:
{
lean_object* v_text_4083_; lean_object* v_sections_4084_; lean_object* v_declarationRange_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4095_; 
v_text_4083_ = lean_ctor_get(v_snippet_4079_, 0);
v_sections_4084_ = lean_ctor_get(v_snippet_4079_, 1);
v_declarationRange_4085_ = lean_ctor_get(v_snippet_4079_, 2);
v_isSharedCheck_4095_ = !lean_is_exclusive(v_snippet_4079_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4087_ = v_snippet_4079_;
v_isShared_4088_ = v_isSharedCheck_4095_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_declarationRange_4085_);
lean_inc(v_sections_4084_);
lean_inc(v_text_4083_);
lean_dec(v_snippet_4079_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4095_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4093_; 
v___x_4089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4089_, 0, v_range_4081_);
lean_ctor_set(v___x_4089_, 1, v_part_4082_);
v___x_4090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4090_, 0, v_level_4080_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = lean_array_push(v_sections_4084_, v___x_4090_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 1, v___x_4091_);
v___x_4093_ = v___x_4087_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_text_4083_);
lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4091_);
lean_ctor_set(v_reuseFailAlloc_4094_, 2, v_declarationRange_4085_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
return v___x_4093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0(lean_object* v___x_4096_, lean_object* v___x_4097_, lean_object* v_x_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v___x_4096_, v___x_4097_, v___y_4099_, v___y_4100_, v___y_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0___boxed(lean_object* v___x_4103_, lean_object* v___x_4104_, lean_object* v_x_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_instToMarkdownSnippet___lam__0(v___x_4103_, v___x_4104_, v_x_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec_ref(v___y_4107_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1(lean_object* v___x_4110_, lean_object* v___x_4111_, lean_object* v___x_4112_, lean_object* v_a_4113_, lean_object* v_x_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4118_; lean_object* v_snd_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4127_; 
v___x_4118_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v___x_4110_, v___x_4111_, v_a_4113_, v___y_4116_, v___y_4117_);
v_snd_4119_ = lean_ctor_get(v___x_4118_, 1);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4127_ == 0)
{
lean_object* v_unused_4128_; 
v_unused_4128_ = lean_ctor_get(v___x_4118_, 0);
lean_dec(v_unused_4128_);
v___x_4121_ = v___x_4118_;
v_isShared_4122_ = v_isSharedCheck_4127_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_snd_4119_);
lean_dec(v___x_4118_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4127_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4123_; lean_object* v___x_4125_; 
v___x_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4112_);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v___x_4123_);
v___x_4125_ = v___x_4121_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v_snd_4119_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1___boxed(lean_object* v___x_4129_, lean_object* v___x_4130_, lean_object* v___x_4131_, lean_object* v_a_4132_, lean_object* v_x_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_instToMarkdownSnippet___lam__1(v___x_4129_, v___x_4130_, v___x_4131_, v_a_4132_, v_x_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
lean_dec_ref(v___y_4135_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2(lean_object* v___x_4138_, lean_object* v___x_4139_, lean_object* v_a_4140_, lean_object* v_x_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4145_; lean_object* v_snd_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4154_; 
v___x_4145_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_box(0), v___x_4138_, v_a_4140_, v___y_4143_, v___y_4144_);
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
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2___boxed(lean_object* v___x_4156_, lean_object* v___x_4157_, lean_object* v_a_4158_, lean_object* v_x_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Lean_instToMarkdownSnippet___lam__2(v___x_4156_, v___x_4157_, v_a_4158_, v_x_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec_ref(v___y_4161_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3(uint32_t v___x_4164_, lean_object* v_s_4165_){
_start:
{
lean_object* v___x_4166_; 
v___x_4166_ = lean_string_push(v_s_4165_, v___x_4164_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3___boxed(lean_object* v___x_4167_, lean_object* v_s_4168_){
_start:
{
uint32_t v___x_5743__boxed_4169_; lean_object* v_res_4170_; 
v___x_5743__boxed_4169_ = lean_unbox_uint32(v___x_4167_);
lean_dec(v___x_4167_);
v_res_4170_ = l_Lean_instToMarkdownSnippet___lam__3(v___x_5743__boxed_4169_, v_s_4168_);
return v_res_4170_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_4171_; lean_object* v___x_4172_; 
v___x_4171_ = 35;
v___x_4172_ = lean_box_uint32(v___x_4171_);
return v___x_4172_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0(void){
_start:
{
lean_object* v___x_4173_; lean_object* v___f_4174_; 
v___x_4173_ = l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1;
v___f_4174_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__3___boxed), 2, 1);
lean_closure_set(v___f_4174_, 0, v___x_4173_);
return v___f_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4(lean_object* v___x_4175_, lean_object* v___f_4176_, lean_object* v___x_4177_, lean_object* v___f_4178_, lean_object* v_a_4179_, lean_object* v_x_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
lean_object* v_snd_4184_; lean_object* v_fst_4185_; lean_object* v_snd_4186_; lean_object* v___x_4187_; lean_object* v___f_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v_snd_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v_snd_4196_; lean_object* v_title_4197_; lean_object* v_content_4198_; size_t v_sz_4199_; size_t v___x_4200_; lean_object* v___x_5585__overap_4201_; lean_object* v___x_4202_; lean_object* v_snd_4203_; lean_object* v___x_4204_; lean_object* v_snd_4205_; size_t v_sz_4206_; lean_object* v___x_5591__overap_4207_; lean_object* v___x_4208_; lean_object* v_snd_4209_; lean_object* v___x_4210_; lean_object* v_snd_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4219_; 
v_snd_4184_ = lean_ctor_get(v_a_4179_, 1);
lean_inc(v_snd_4184_);
v_fst_4185_ = lean_ctor_get(v_a_4179_, 0);
lean_inc(v_fst_4185_);
lean_dec_ref(v_a_4179_);
v_snd_4186_ = lean_ctor_get(v_snd_4184_, 1);
lean_inc(v_snd_4186_);
lean_dec(v_snd_4184_);
v___x_4187_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___f_4188_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___lam__4___closed__0, &l_Lean_instToMarkdownSnippet___lam__4___closed__0_once, _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0);
v___x_4189_ = lean_unsigned_to_nat(1u);
v___x_4190_ = lean_nat_add(v_fst_4185_, v___x_4189_);
lean_dec(v_fst_4185_);
v___x_4191_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_4188_, v___x_4190_, v___x_4187_);
v___x_4192_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_4191_, v___y_4183_);
lean_dec(v___x_4191_);
v_snd_4193_ = lean_ctor_get(v___x_4192_, 1);
lean_inc(v_snd_4193_);
lean_dec_ref(v___x_4192_);
v___x_4194_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0));
v___x_4195_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_4194_, v_snd_4193_);
v_snd_4196_ = lean_ctor_get(v___x_4195_, 1);
lean_inc(v_snd_4196_);
lean_dec_ref(v___x_4195_);
v_title_4197_ = lean_ctor_get(v_snd_4186_, 0);
lean_inc_ref(v_title_4197_);
v_content_4198_ = lean_ctor_get(v_snd_4186_, 3);
lean_inc_ref(v_content_4198_);
lean_dec(v_snd_4186_);
v_sz_4199_ = lean_array_size(v_title_4197_);
v___x_4200_ = ((size_t)0ULL);
lean_inc_ref(v___x_4175_);
v___x_5585__overap_4201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4175_, v_title_4197_, v___f_4176_, v_sz_4199_, v___x_4200_, v___x_4177_);
lean_inc_ref_n(v___y_4182_, 2);
v___x_4202_ = lean_apply_2(v___x_5585__overap_4201_, v___y_4182_, v_snd_4196_);
v_snd_4203_ = lean_ctor_get(v___x_4202_, 1);
lean_inc(v_snd_4203_);
lean_dec_ref(v___x_4202_);
v___x_4204_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4203_);
v_snd_4205_ = lean_ctor_get(v___x_4204_, 1);
lean_inc(v_snd_4205_);
lean_dec_ref(v___x_4204_);
v_sz_4206_ = lean_array_size(v_content_4198_);
v___x_5591__overap_4207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4175_, v_content_4198_, v___f_4178_, v_sz_4206_, v___x_4200_, v___x_4177_);
v___x_4208_ = lean_apply_2(v___x_5591__overap_4207_, v___y_4182_, v_snd_4205_);
v_snd_4209_ = lean_ctor_get(v___x_4208_, 1);
lean_inc(v_snd_4209_);
lean_dec_ref(v___x_4208_);
v___x_4210_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4209_);
v_snd_4211_ = lean_ctor_get(v___x_4210_, 1);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4219_ == 0)
{
lean_object* v_unused_4220_; 
v_unused_4220_ = lean_ctor_get(v___x_4210_, 0);
lean_dec(v_unused_4220_);
v___x_4213_ = v___x_4210_;
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_snd_4211_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4215_; lean_object* v___x_4217_; 
v___x_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4177_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4215_);
v___x_4217_ = v___x_4213_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_snd_4211_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4___boxed(lean_object* v___x_4221_, lean_object* v___f_4222_, lean_object* v___x_4223_, lean_object* v___f_4224_, lean_object* v_a_4225_, lean_object* v_x_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l_Lean_instToMarkdownSnippet___lam__4(v___x_4221_, v___f_4222_, v___x_4223_, v___f_4224_, v_a_4225_, v_x_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
lean_dec_ref(v___y_4228_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5(lean_object* v___x_4231_, lean_object* v___x_4232_, lean_object* v___x_4233_, lean_object* v___f_4234_, lean_object* v_x_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v_text_4238_; lean_object* v_sections_4239_; lean_object* v_snd_4241_; lean_object* v___y_4262_; lean_object* v___x_4264_; lean_object* v___x_4265_; uint8_t v___x_4266_; 
v_text_4238_ = lean_ctor_get(v_x_4235_, 0);
lean_inc_ref(v_text_4238_);
v_sections_4239_ = lean_ctor_get(v_x_4235_, 1);
lean_inc_ref(v_sections_4239_);
lean_dec_ref(v_x_4235_);
v___x_4264_ = lean_unsigned_to_nat(0u);
v___x_4265_ = lean_array_get_size(v_text_4238_);
v___x_4266_ = lean_nat_dec_lt(v___x_4264_, v___x_4265_);
if (v___x_4266_ == 0)
{
lean_dec_ref(v_text_4238_);
lean_dec_ref(v___f_4234_);
v_snd_4241_ = v___y_4237_;
goto v___jp_4240_;
}
else
{
lean_object* v___x_4267_; uint8_t v___x_4268_; 
v___x_4267_ = lean_box(0);
v___x_4268_ = lean_nat_dec_le(v___x_4265_, v___x_4265_);
if (v___x_4268_ == 0)
{
if (v___x_4266_ == 0)
{
lean_dec_ref(v_text_4238_);
lean_dec_ref(v___f_4234_);
v_snd_4241_ = v___y_4237_;
goto v___jp_4240_;
}
else
{
size_t v___x_4269_; size_t v___x_4270_; lean_object* v___x_5634__overap_4271_; lean_object* v___x_4272_; 
v___x_4269_ = ((size_t)0ULL);
v___x_4270_ = lean_usize_of_nat(v___x_4265_);
lean_inc_ref(v___x_4233_);
v___x_5634__overap_4271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4233_, v___f_4234_, v_text_4238_, v___x_4269_, v___x_4270_, v___x_4267_);
lean_inc_ref(v___y_4236_);
v___x_4272_ = lean_apply_2(v___x_5634__overap_4271_, v___y_4236_, v___y_4237_);
v___y_4262_ = v___x_4272_;
goto v___jp_4261_;
}
}
else
{
size_t v___x_4273_; size_t v___x_4274_; lean_object* v___x_5637__overap_4275_; lean_object* v___x_4276_; 
v___x_4273_ = ((size_t)0ULL);
v___x_4274_ = lean_usize_of_nat(v___x_4265_);
lean_inc_ref(v___x_4233_);
v___x_5637__overap_4275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4233_, v___f_4234_, v_text_4238_, v___x_4273_, v___x_4274_, v___x_4267_);
lean_inc_ref(v___y_4236_);
v___x_4276_ = lean_apply_2(v___x_5637__overap_4275_, v___y_4236_, v___y_4237_);
v___y_4262_ = v___x_4276_;
goto v___jp_4261_;
}
}
v___jp_4240_:
{
lean_object* v___x_4242_; lean_object* v_snd_4243_; lean_object* v___x_4244_; lean_object* v___f_4245_; lean_object* v___f_4246_; lean_object* v___f_4247_; size_t v_sz_4248_; size_t v___x_4249_; lean_object* v___x_5619__overap_4250_; lean_object* v___x_4251_; lean_object* v_snd_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
v___x_4242_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4241_);
v_snd_4243_ = lean_ctor_get(v___x_4242_, 1);
lean_inc(v_snd_4243_);
lean_dec_ref(v___x_4242_);
v___x_4244_ = lean_box(0);
lean_inc_ref(v___x_4231_);
v___f_4245_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__1___boxed), 8, 3);
lean_closure_set(v___f_4245_, 0, v___x_4231_);
lean_closure_set(v___f_4245_, 1, v___x_4232_);
lean_closure_set(v___f_4245_, 2, v___x_4244_);
v___f_4246_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__2___boxed), 7, 2);
lean_closure_set(v___f_4246_, 0, v___x_4231_);
lean_closure_set(v___f_4246_, 1, v___x_4244_);
lean_inc_ref(v___x_4233_);
v___f_4247_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__4___boxed), 9, 4);
lean_closure_set(v___f_4247_, 0, v___x_4233_);
lean_closure_set(v___f_4247_, 1, v___f_4246_);
lean_closure_set(v___f_4247_, 2, v___x_4244_);
lean_closure_set(v___f_4247_, 3, v___f_4245_);
v_sz_4248_ = lean_array_size(v_sections_4239_);
v___x_4249_ = ((size_t)0ULL);
v___x_5619__overap_4250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4233_, v_sections_4239_, v___f_4247_, v_sz_4248_, v___x_4249_, v___x_4244_);
lean_inc_ref(v___y_4236_);
v___x_4251_ = lean_apply_2(v___x_5619__overap_4250_, v___y_4236_, v_snd_4243_);
v_snd_4252_ = lean_ctor_get(v___x_4251_, 1);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4259_ == 0)
{
lean_object* v_unused_4260_; 
v_unused_4260_ = lean_ctor_get(v___x_4251_, 0);
lean_dec(v_unused_4260_);
v___x_4254_ = v___x_4251_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_snd_4252_);
lean_dec(v___x_4251_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
lean_ctor_set(v___x_4254_, 0, v___x_4244_);
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4244_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_snd_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
v___jp_4261_:
{
lean_object* v_snd_4263_; 
v_snd_4263_ = lean_ctor_get(v___y_4262_, 1);
lean_inc(v_snd_4263_);
lean_dec_ref(v___y_4262_);
v_snd_4241_ = v_snd_4263_;
goto v___jp_4240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5___boxed(lean_object* v___x_4277_, lean_object* v___x_4278_, lean_object* v___x_4279_, lean_object* v___f_4280_, lean_object* v_x_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l_Lean_instToMarkdownSnippet___lam__5(v___x_4277_, v___x_4278_, v___x_4279_, v___f_4280_, v_x_4281_, v___y_4282_, v___y_4283_);
lean_dec_ref(v___y_4282_);
return v_res_4284_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___f_4287_; 
v___x_4285_ = l_Lean_instMarkdownBlockElabInlineElabBlock;
v___x_4286_ = l_Lean_instMarkdownInlineElabInline;
v___f_4287_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__0___boxed), 6, 2);
lean_closure_set(v___f_4287_, 0, v___x_4286_);
lean_closure_set(v___f_4287_, 1, v___x_4285_);
return v___f_4287_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___closed__1(void){
_start:
{
lean_object* v___f_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___f_4292_; 
v___f_4288_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___closed__0, &l_Lean_instToMarkdownSnippet___closed__0_once, _init_l_Lean_instToMarkdownSnippet___closed__0);
v___x_4289_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__20, &l_Lean_instMarkdownInlineElabInline___closed__20_once, _init_l_Lean_instMarkdownInlineElabInline___closed__20);
v___x_4290_ = l_Lean_instMarkdownBlockElabInlineElabBlock;
v___x_4291_ = l_Lean_instMarkdownInlineElabInline;
v___f_4292_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__5___boxed), 7, 4);
lean_closure_set(v___f_4292_, 0, v___x_4291_);
lean_closure_set(v___f_4292_, 1, v___x_4290_);
lean_closure_set(v___f_4292_, 2, v___x_4289_);
lean_closure_set(v___f_4292_, 3, v___f_4288_);
return v___f_4292_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet(void){
_start:
{
lean_object* v___f_4293_; 
v___f_4293_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___closed__1, &l_Lean_instToMarkdownSnippet___closed__1_once, _init_l_Lean_instToMarkdownSnippet___closed__1);
return v___f_4293_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0(void){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = lean_unsigned_to_nat(32u);
v___x_4295_ = lean_mk_empty_array_with_capacity(v___x_4294_);
v___x_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
return v___x_4296_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1(void){
_start:
{
size_t v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4297_ = ((size_t)5ULL);
v___x_4298_ = lean_unsigned_to_nat(0u);
v___x_4299_ = lean_unsigned_to_nat(32u);
v___x_4300_ = lean_mk_empty_array_with_capacity(v___x_4299_);
v___x_4301_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_4302_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
lean_ctor_set(v___x_4302_, 1, v___x_4300_);
lean_ctor_set(v___x_4302_, 2, v___x_4298_);
lean_ctor_set(v___x_4302_, 3, v___x_4298_);
lean_ctor_set_usize(v___x_4302_, 4, v___x_4297_);
return v___x_4302_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default(void){
_start:
{
lean_object* v___x_4303_; 
v___x_4303_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__1, &l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1);
return v___x_4303_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs(void){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = l_Lean_instInhabitedVersoModuleDocs_default;
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(lean_object* v_as_4305_, lean_object* v_i_4306_){
_start:
{
lean_object* v_zero_4307_; uint8_t v_isZero_4308_; 
v_zero_4307_ = lean_unsigned_to_nat(0u);
v_isZero_4308_ = lean_nat_dec_eq(v_i_4306_, v_zero_4307_);
if (v_isZero_4308_ == 1)
{
lean_object* v___x_4309_; 
lean_dec(v_i_4306_);
v___x_4309_ = lean_box(0);
return v___x_4309_;
}
else
{
lean_object* v_one_4310_; lean_object* v_n_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v_one_4310_ = lean_unsigned_to_nat(1u);
v_n_4311_ = lean_nat_sub(v_i_4306_, v_one_4310_);
lean_dec(v_i_4306_);
v___x_4312_ = lean_array_fget_borrowed(v_as_4305_, v_n_4311_);
v___x_4313_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v___x_4312_);
if (lean_obj_tag(v___x_4313_) == 0)
{
v_i_4306_ = v_n_4311_;
goto _start;
}
else
{
lean_dec(v_n_4311_);
return v___x_4313_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg___boxed(lean_object* v_as_4315_, lean_object* v_i_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_as_4315_, v_i_4316_);
lean_dec_ref(v_as_4315_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(lean_object* v_as_4318_, lean_object* v_i_4319_){
_start:
{
lean_object* v_zero_4320_; uint8_t v_isZero_4321_; 
v_zero_4320_ = lean_unsigned_to_nat(0u);
v_isZero_4321_ = lean_nat_dec_eq(v_i_4319_, v_zero_4320_);
if (v_isZero_4321_ == 1)
{
lean_object* v___x_4322_; 
lean_dec(v_i_4319_);
v___x_4322_ = lean_box(0);
return v___x_4322_;
}
else
{
lean_object* v_one_4323_; lean_object* v_n_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v_one_4323_ = lean_unsigned_to_nat(1u);
v_n_4324_ = lean_nat_sub(v_i_4319_, v_one_4323_);
lean_dec(v_i_4319_);
v___x_4325_ = lean_array_fget_borrowed(v_as_4318_, v_n_4324_);
v___x_4326_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v___x_4325_);
if (lean_obj_tag(v___x_4326_) == 0)
{
v_i_4319_ = v_n_4324_;
goto _start;
}
else
{
lean_dec(v_n_4324_);
return v___x_4326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(lean_object* v_x_4328_){
_start:
{
if (lean_obj_tag(v_x_4328_) == 0)
{
lean_object* v_cs_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v_cs_4329_ = lean_ctor_get(v_x_4328_, 0);
v___x_4330_ = lean_array_get_size(v_cs_4329_);
v___x_4331_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_cs_4329_, v___x_4330_);
return v___x_4331_;
}
else
{
lean_object* v_vs_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v_vs_4332_ = lean_ctor_get(v_x_4328_, 0);
v___x_4333_ = lean_array_get_size(v_vs_4332_);
v___x_4334_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_vs_4332_, v___x_4333_);
return v___x_4334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1___boxed(lean_object* v_x_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v_x_4335_);
lean_dec_ref(v_x_4335_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_4337_, lean_object* v_i_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_as_4337_, v_i_4338_);
lean_dec_ref(v_as_4337_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(lean_object* v_t_4340_){
_start:
{
lean_object* v_root_4341_; lean_object* v_tail_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v_root_4341_ = lean_ctor_get(v_t_4340_, 0);
v_tail_4342_ = lean_ctor_get(v_t_4340_, 1);
v___x_4343_ = lean_array_get_size(v_tail_4342_);
v___x_4344_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_tail_4342_, v___x_4343_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v___x_4345_; 
v___x_4345_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v_root_4341_);
return v___x_4345_;
}
else
{
return v___x_4344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0___boxed(lean_object* v_t_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_t_4346_);
lean_dec_ref(v_t_4346_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object* v_x_4348_){
_start:
{
lean_object* v___x_4349_; 
v___x_4349_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_x_4348_);
return v___x_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting___boxed(lean_object* v_x_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l_Lean_VersoModuleDocs_terminalNesting(v_x_4350_);
lean_dec_ref(v_x_4350_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(lean_object* v_as_4352_, lean_object* v_i_4353_, lean_object* v_a_4354_){
_start:
{
lean_object* v___x_4355_; 
v___x_4355_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_as_4352_, v_i_4353_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___boxed(lean_object* v_as_4356_, lean_object* v_i_4357_, lean_object* v_a_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(v_as_4356_, v_i_4357_, v_a_4358_);
lean_dec_ref(v_as_4356_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(lean_object* v_as_4360_, lean_object* v_i_4361_, lean_object* v_a_4362_){
_start:
{
lean_object* v___x_4363_; 
v___x_4363_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_as_4360_, v_i_4361_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___boxed(lean_object* v_as_4364_, lean_object* v_i_4365_, lean_object* v_a_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(v_as_4364_, v_i_4365_, v_a_4366_);
lean_dec_ref(v_as_4364_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object* v___x_4374_, lean_object* v_v_4375_, lean_object* v_x_4376_){
_start:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; uint8_t v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4377_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___x_4378_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_4379_ = lean_box(1);
v___x_4380_ = ((lean_object*)(l_Lean_instReprVersoModuleDocs___lam__0___closed__2));
v___x_4381_ = l_Lean_PersistentArray_toArray___redArg(v_v_4375_);
v___x_4382_ = l_Array_repr___redArg(v___x_4374_, v___x_4381_);
v___x_4383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4380_);
lean_ctor_set(v___x_4383_, 1, v___x_4382_);
v___x_4384_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4377_);
lean_ctor_set(v___x_4384_, 1, v___x_4383_);
v___x_4385_ = 0;
v___x_4386_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4386_, 0, v___x_4384_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*1, v___x_4385_);
lean_inc_ref(v___x_4386_);
v___x_4387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4378_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
lean_ctor_set(v___x_4388_, 1, v___x_4379_);
v___x_4389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4388_);
lean_ctor_set(v___x_4389_, 1, v___x_4386_);
v___x_4390_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_4391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4389_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4377_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4393_, 0, v___x_4392_);
lean_ctor_set_uint8(v___x_4393_, sizeof(void*)*1, v___x_4385_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object* v___x_4394_, lean_object* v_v_4395_, lean_object* v_x_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Lean_instReprVersoModuleDocs___lam__0(v___x_4394_, v_v_4395_, v_x_4396_);
lean_dec(v_x_4396_);
lean_dec_ref(v_v_4395_);
return v_res_4397_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object* v_docs_4401_){
_start:
{
uint8_t v___x_4402_; 
v___x_4402_ = l_Lean_PersistentArray_isEmpty___redArg(v_docs_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object* v_docs_4403_){
_start:
{
uint8_t v_res_4404_; lean_object* v_r_4405_; 
v_res_4404_ = l_Lean_VersoModuleDocs_isEmpty(v_docs_4403_);
lean_dec_ref(v_docs_4403_);
v_r_4405_ = lean_box(v_res_4404_);
return v_r_4405_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object* v_docs_4406_, lean_object* v_snippet_4407_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_4406_);
if (lean_obj_tag(v___x_4408_) == 1)
{
lean_object* v_val_4409_; uint8_t v___x_4410_; 
v_val_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_val_4409_);
lean_dec_ref(v___x_4408_);
v___x_4410_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4409_, v_snippet_4407_);
lean_dec(v_val_4409_);
return v___x_4410_;
}
else
{
uint8_t v___x_4411_; 
lean_dec(v___x_4408_);
v___x_4411_ = 1;
return v___x_4411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object* v_docs_4412_, lean_object* v_snippet_4413_){
_start:
{
uint8_t v_res_4414_; lean_object* v_r_4415_; 
v_res_4414_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4412_, v_snippet_4413_);
lean_dec_ref(v_snippet_4413_);
lean_dec_ref(v_docs_4412_);
v_r_4415_ = lean_box(v_res_4414_);
return v_r_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object* v_docs_4419_, lean_object* v_snippet_4420_){
_start:
{
uint8_t v___x_4421_; 
v___x_4421_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4419_, v_snippet_4420_);
if (v___x_4421_ == 0)
{
lean_object* v___x_4422_; 
lean_dec_ref(v_snippet_4420_);
lean_dec_ref(v_docs_4419_);
v___x_4422_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__1));
return v___x_4422_;
}
else
{
lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4423_ = l_Lean_PersistentArray_push___redArg(v_docs_4419_, v_snippet_4420_);
v___x_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4423_);
return v___x_4424_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object* v_msg_4425_){
_start:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4426_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_4427_ = lean_panic_fn_borrowed(v___x_4426_, v_msg_4425_);
return v___x_4427_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_add_x21___closed__2(void){
_start:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4430_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__0));
v___x_4431_ = lean_unsigned_to_nat(4u);
v___x_4432_ = lean_unsigned_to_nat(327u);
v___x_4433_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__1));
v___x_4434_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__0));
v___x_4435_ = l_mkPanicMessageWithDecl(v___x_4434_, v___x_4433_, v___x_4432_, v___x_4431_, v___x_4430_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object* v_docs_4436_, lean_object* v_snippet_4437_){
_start:
{
lean_object* v___x_4438_; 
v___x_4438_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_4436_);
if (lean_obj_tag(v___x_4438_) == 1)
{
lean_object* v_val_4439_; uint8_t v___x_4440_; 
v_val_4439_ = lean_ctor_get(v___x_4438_, 0);
lean_inc(v_val_4439_);
lean_dec_ref(v___x_4438_);
v___x_4440_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4439_, v_snippet_4437_);
lean_dec(v_val_4439_);
if (v___x_4440_ == 0)
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
lean_dec_ref(v_snippet_4437_);
lean_dec_ref(v_docs_4436_);
v___x_4441_ = lean_obj_once(&l_Lean_VersoModuleDocs_add_x21___closed__2, &l_Lean_VersoModuleDocs_add_x21___closed__2_once, _init_l_Lean_VersoModuleDocs_add_x21___closed__2);
v___x_4442_ = l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(v___x_4441_);
return v___x_4442_;
}
else
{
lean_object* v___x_4443_; 
v___x_4443_ = l_Lean_PersistentArray_push___redArg(v_docs_4436_, v_snippet_4437_);
return v___x_4443_;
}
}
else
{
lean_object* v___x_4444_; 
lean_dec(v___x_4438_);
v___x_4444_ = l_Lean_PersistentArray_push___redArg(v_docs_4436_, v_snippet_4437_);
return v___x_4444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object* v_ctx_4445_){
_start:
{
lean_object* v_context_4446_; lean_object* v___x_4447_; 
v_context_4446_ = lean_ctor_get(v_ctx_4445_, 2);
v___x_4447_ = lean_array_get_size(v_context_4446_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object* v_ctx_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4448_);
lean_dec_ref(v_ctx_4448_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object* v_ctx_4453_){
_start:
{
lean_object* v_content_4454_; lean_object* v_priorParts_4455_; lean_object* v_context_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4479_; 
v_content_4454_ = lean_ctor_get(v_ctx_4453_, 0);
v_priorParts_4455_ = lean_ctor_get(v_ctx_4453_, 1);
v_context_4456_ = lean_ctor_get(v_ctx_4453_, 2);
v_isSharedCheck_4479_ = !lean_is_exclusive(v_ctx_4453_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4458_ = v_ctx_4453_;
v_isShared_4459_ = v_isSharedCheck_4479_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_context_4456_);
lean_inc(v_priorParts_4455_);
lean_inc(v_content_4454_);
lean_dec(v_ctx_4453_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4479_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; uint8_t v___x_4462_; 
v___x_4460_ = lean_array_get_size(v_context_4456_);
v___x_4461_ = lean_unsigned_to_nat(0u);
v___x_4462_ = lean_nat_dec_eq(v___x_4460_, v___x_4461_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v_last_4465_; lean_object* v_content_4466_; lean_object* v_priorParts_4467_; lean_object* v_titleString_4468_; lean_object* v_title_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4475_; 
v___x_4463_ = lean_unsigned_to_nat(1u);
v___x_4464_ = lean_nat_sub(v___x_4460_, v___x_4463_);
v_last_4465_ = lean_array_fget_borrowed(v_context_4456_, v___x_4464_);
lean_dec(v___x_4464_);
v_content_4466_ = lean_ctor_get(v_last_4465_, 0);
lean_inc_ref(v_content_4466_);
v_priorParts_4467_ = lean_ctor_get(v_last_4465_, 1);
v_titleString_4468_ = lean_ctor_get(v_last_4465_, 2);
v_title_4469_ = lean_ctor_get(v_last_4465_, 3);
v___x_4470_ = lean_box(0);
lean_inc_ref(v_titleString_4468_);
lean_inc_ref(v_title_4469_);
v___x_4471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4471_, 0, v_title_4469_);
lean_ctor_set(v___x_4471_, 1, v_titleString_4468_);
lean_ctor_set(v___x_4471_, 2, v___x_4470_);
lean_ctor_set(v___x_4471_, 3, v_content_4454_);
lean_ctor_set(v___x_4471_, 4, v_priorParts_4455_);
lean_inc_ref(v_priorParts_4467_);
v___x_4472_ = lean_array_push(v_priorParts_4467_, v___x_4471_);
v___x_4473_ = lean_array_pop(v_context_4456_);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 2, v___x_4473_);
lean_ctor_set(v___x_4458_, 1, v___x_4472_);
lean_ctor_set(v___x_4458_, 0, v_content_4466_);
v___x_4475_ = v___x_4458_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_content_4466_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v___x_4472_);
lean_ctor_set(v_reuseFailAlloc_4477_, 2, v___x_4473_);
v___x_4475_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4476_; 
v___x_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4475_);
return v___x_4476_;
}
}
else
{
lean_object* v___x_4478_; 
lean_del_object(v___x_4458_);
lean_dec_ref(v_context_4456_);
lean_dec_ref(v_priorParts_4455_);
lean_dec_ref(v_content_4454_);
v___x_4478_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1));
return v___x_4478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object* v_ctx_4480_){
_start:
{
lean_object* v_context_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; uint8_t v___x_4484_; 
v_context_4481_ = lean_ctor_get(v_ctx_4480_, 2);
v___x_4482_ = lean_array_get_size(v_context_4481_);
v___x_4483_ = lean_unsigned_to_nat(0u);
v___x_4484_ = lean_nat_dec_eq(v___x_4482_, v___x_4483_);
if (v___x_4484_ == 0)
{
lean_object* v___x_4485_; 
v___x_4485_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4480_);
if (lean_obj_tag(v___x_4485_) == 0)
{
return v___x_4485_;
}
else
{
lean_object* v_a_4486_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref(v___x_4485_);
v_ctx_4480_ = v_a_4486_;
goto _start;
}
}
else
{
lean_object* v___x_4488_; 
v___x_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4488_, 0, v_ctx_4480_);
return v___x_4488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object* v_ctx_4491_, lean_object* v_partLevel_4492_, lean_object* v_part_4493_){
_start:
{
lean_object* v___x_4494_; uint8_t v___x_4495_; 
v___x_4494_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4491_);
v___x_4495_ = lean_nat_dec_lt(v___x_4494_, v_partLevel_4492_);
if (v___x_4495_ == 0)
{
uint8_t v___x_4496_; 
v___x_4496_ = lean_nat_dec_eq(v_partLevel_4492_, v___x_4494_);
lean_dec(v___x_4494_);
if (v___x_4496_ == 0)
{
lean_object* v___x_4497_; 
v___x_4497_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4491_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_dec_ref(v_part_4493_);
lean_dec(v_partLevel_4492_);
return v___x_4497_;
}
else
{
lean_object* v_a_4498_; 
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4498_);
lean_dec_ref(v___x_4497_);
v_ctx_4491_ = v_a_4498_;
goto _start;
}
}
else
{
lean_object* v_content_4500_; lean_object* v_priorParts_4501_; lean_object* v_context_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4511_; 
lean_dec(v_partLevel_4492_);
v_content_4500_ = lean_ctor_get(v_ctx_4491_, 0);
v_priorParts_4501_ = lean_ctor_get(v_ctx_4491_, 1);
v_context_4502_ = lean_ctor_get(v_ctx_4491_, 2);
v_isSharedCheck_4511_ = !lean_is_exclusive(v_ctx_4491_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4504_ = v_ctx_4491_;
v_isShared_4505_ = v_isSharedCheck_4511_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_context_4502_);
lean_inc(v_priorParts_4501_);
lean_inc(v_content_4500_);
lean_dec(v_ctx_4491_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4511_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4506_ = lean_array_push(v_priorParts_4501_, v_part_4493_);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 1, v___x_4506_);
v___x_4508_ = v___x_4504_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_content_4500_);
lean_ctor_set(v_reuseFailAlloc_4510_, 1, v___x_4506_);
lean_ctor_set(v_reuseFailAlloc_4510_, 2, v_context_4502_);
v___x_4508_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4509_; 
v___x_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4508_);
return v___x_4509_;
}
}
}
}
else
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
lean_dec_ref(v_part_4493_);
lean_dec_ref(v_ctx_4491_);
v___x_4512_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0));
v___x_4513_ = l_Nat_reprFast(v___x_4494_);
v___x_4514_ = lean_string_append(v___x_4512_, v___x_4513_);
lean_dec_ref(v___x_4513_);
v___x_4515_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1));
v___x_4516_ = lean_string_append(v___x_4514_, v___x_4515_);
v___x_4517_ = l_Nat_reprFast(v_partLevel_4492_);
v___x_4518_ = lean_string_append(v___x_4516_, v___x_4517_);
lean_dec_ref(v___x_4517_);
v___x_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
return v___x_4519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object* v_ctx_4523_, lean_object* v_blocks_4524_){
_start:
{
lean_object* v_content_4525_; lean_object* v_priorParts_4526_; lean_object* v_context_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4540_; 
v_content_4525_ = lean_ctor_get(v_ctx_4523_, 0);
v_priorParts_4526_ = lean_ctor_get(v_ctx_4523_, 1);
v_context_4527_ = lean_ctor_get(v_ctx_4523_, 2);
v_isSharedCheck_4540_ = !lean_is_exclusive(v_ctx_4523_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4529_ = v_ctx_4523_;
v_isShared_4530_ = v_isSharedCheck_4540_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_context_4527_);
lean_inc(v_priorParts_4526_);
lean_inc(v_content_4525_);
lean_dec(v_ctx_4523_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4540_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; uint8_t v___x_4533_; 
v___x_4531_ = lean_array_get_size(v_priorParts_4526_);
v___x_4532_ = lean_unsigned_to_nat(0u);
v___x_4533_ = lean_nat_dec_eq(v___x_4531_, v___x_4532_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4534_; 
lean_del_object(v___x_4529_);
lean_dec_ref(v_context_4527_);
lean_dec_ref(v_priorParts_4526_);
lean_dec_ref(v_content_4525_);
v___x_4534_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1));
return v___x_4534_;
}
else
{
lean_object* v___x_4535_; lean_object* v___x_4537_; 
v___x_4535_ = l_Array_append___redArg(v_content_4525_, v_blocks_4524_);
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 0, v___x_4535_);
v___x_4537_ = v___x_4529_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4535_);
lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_priorParts_4526_);
lean_ctor_set(v_reuseFailAlloc_4539_, 2, v_context_4527_);
v___x_4537_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
lean_object* v___x_4538_; 
v___x_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4537_);
return v___x_4538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object* v_ctx_4541_, lean_object* v_blocks_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4541_, v_blocks_4542_);
lean_dec_ref(v_blocks_4542_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object* v_as_4544_, size_t v_sz_4545_, size_t v_i_4546_, lean_object* v_b_4547_){
_start:
{
uint8_t v___x_4548_; 
v___x_4548_ = lean_usize_dec_lt(v_i_4546_, v_sz_4545_);
if (v___x_4548_ == 0)
{
lean_object* v___x_4549_; 
v___x_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4549_, 0, v_b_4547_);
return v___x_4549_;
}
else
{
lean_object* v_a_4550_; lean_object* v_snd_4551_; lean_object* v_fst_4552_; lean_object* v_snd_4553_; lean_object* v___x_4554_; 
v_a_4550_ = lean_array_uget_borrowed(v_as_4544_, v_i_4546_);
v_snd_4551_ = lean_ctor_get(v_a_4550_, 1);
v_fst_4552_ = lean_ctor_get(v_a_4550_, 0);
v_snd_4553_ = lean_ctor_get(v_snd_4551_, 1);
lean_inc(v_snd_4553_);
lean_inc(v_fst_4552_);
v___x_4554_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(v_b_4547_, v_fst_4552_, v_snd_4553_);
if (lean_obj_tag(v___x_4554_) == 0)
{
return v___x_4554_;
}
else
{
lean_object* v_a_4555_; size_t v___x_4556_; size_t v___x_4557_; 
v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc(v_a_4555_);
lean_dec_ref(v___x_4554_);
v___x_4556_ = ((size_t)1ULL);
v___x_4557_ = lean_usize_add(v_i_4546_, v___x_4556_);
v_i_4546_ = v___x_4557_;
v_b_4547_ = v_a_4555_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object* v_as_4559_, lean_object* v_sz_4560_, lean_object* v_i_4561_, lean_object* v_b_4562_){
_start:
{
size_t v_sz_boxed_4563_; size_t v_i_boxed_4564_; lean_object* v_res_4565_; 
v_sz_boxed_4563_ = lean_unbox_usize(v_sz_4560_);
lean_dec(v_sz_4560_);
v_i_boxed_4564_ = lean_unbox_usize(v_i_4561_);
lean_dec(v_i_4561_);
v_res_4565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_as_4559_, v_sz_boxed_4563_, v_i_boxed_4564_, v_b_4562_);
lean_dec_ref(v_as_4559_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object* v_ctx_4566_, lean_object* v_snippet_4567_){
_start:
{
lean_object* v_text_4568_; lean_object* v_sections_4569_; lean_object* v___x_4570_; 
v_text_4568_ = lean_ctor_get(v_snippet_4567_, 0);
v_sections_4569_ = lean_ctor_get(v_snippet_4567_, 1);
v___x_4570_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4566_, v_text_4568_);
if (lean_obj_tag(v___x_4570_) == 0)
{
return v___x_4570_;
}
else
{
lean_object* v_a_4571_; size_t v_sz_4572_; size_t v___x_4573_; lean_object* v___x_4574_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_a_4571_);
lean_dec_ref(v___x_4570_);
v_sz_4572_ = lean_array_size(v_sections_4569_);
v___x_4573_ = ((size_t)0ULL);
v___x_4574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_sections_4569_, v_sz_4572_, v___x_4573_, v_a_4571_);
return v___x_4574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object* v_ctx_4575_, lean_object* v_snippet_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_ctx_4575_, v_snippet_4576_);
lean_dec_ref(v_snippet_4576_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object* v_as_4578_, size_t v_sz_4579_, size_t v_i_4580_, lean_object* v_b_4581_){
_start:
{
uint8_t v___x_4582_; 
v___x_4582_ = lean_usize_dec_lt(v_i_4580_, v_sz_4579_);
if (v___x_4582_ == 0)
{
lean_object* v___x_4583_; 
v___x_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4583_, 0, v_b_4581_);
return v___x_4583_;
}
else
{
lean_object* v_snd_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4606_; 
v_snd_4584_ = lean_ctor_get(v_b_4581_, 1);
v_isSharedCheck_4606_ = !lean_is_exclusive(v_b_4581_);
if (v_isSharedCheck_4606_ == 0)
{
lean_object* v_unused_4607_; 
v_unused_4607_ = lean_ctor_get(v_b_4581_, 0);
lean_dec(v_unused_4607_);
v___x_4586_ = v_b_4581_;
v_isShared_4587_ = v_isSharedCheck_4606_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_snd_4584_);
lean_dec(v_b_4581_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4606_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v_a_4588_; lean_object* v___x_4589_; 
v_a_4588_ = lean_array_uget_borrowed(v_as_4578_, v_i_4580_);
v___x_4589_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4584_, v_a_4588_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4597_; 
lean_del_object(v___x_4586_);
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4592_ = v___x_4589_;
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4589_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4595_; 
if (v_isShared_4593_ == 0)
{
v___x_4595_ = v___x_4592_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_a_4590_);
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
lean_object* v_a_4598_; lean_object* v___x_4599_; lean_object* v___x_4601_; 
v_a_4598_ = lean_ctor_get(v___x_4589_, 0);
lean_inc(v_a_4598_);
lean_dec_ref(v___x_4589_);
v___x_4599_ = lean_box(0);
if (v_isShared_4587_ == 0)
{
lean_ctor_set(v___x_4586_, 1, v_a_4598_);
lean_ctor_set(v___x_4586_, 0, v___x_4599_);
v___x_4601_ = v___x_4586_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4599_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_a_4598_);
v___x_4601_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
size_t v___x_4602_; size_t v___x_4603_; 
v___x_4602_ = ((size_t)1ULL);
v___x_4603_ = lean_usize_add(v_i_4580_, v___x_4602_);
v_i_4580_ = v___x_4603_;
v_b_4581_ = v___x_4601_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4608_, lean_object* v_sz_4609_, lean_object* v_i_4610_, lean_object* v_b_4611_){
_start:
{
size_t v_sz_boxed_4612_; size_t v_i_boxed_4613_; lean_object* v_res_4614_; 
v_sz_boxed_4612_ = lean_unbox_usize(v_sz_4609_);
lean_dec(v_sz_4609_);
v_i_boxed_4613_ = lean_unbox_usize(v_i_4610_);
lean_dec(v_i_4610_);
v_res_4614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4608_, v_sz_boxed_4612_, v_i_boxed_4613_, v_b_4611_);
lean_dec_ref(v_as_4608_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object* v_as_4615_, size_t v_sz_4616_, size_t v_i_4617_, lean_object* v_b_4618_){
_start:
{
uint8_t v___x_4619_; 
v___x_4619_ = lean_usize_dec_lt(v_i_4617_, v_sz_4616_);
if (v___x_4619_ == 0)
{
lean_object* v___x_4620_; 
v___x_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4620_, 0, v_b_4618_);
return v___x_4620_;
}
else
{
lean_object* v_snd_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4643_; 
v_snd_4621_ = lean_ctor_get(v_b_4618_, 1);
v_isSharedCheck_4643_ = !lean_is_exclusive(v_b_4618_);
if (v_isSharedCheck_4643_ == 0)
{
lean_object* v_unused_4644_; 
v_unused_4644_ = lean_ctor_get(v_b_4618_, 0);
lean_dec(v_unused_4644_);
v___x_4623_ = v_b_4618_;
v_isShared_4624_ = v_isSharedCheck_4643_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_snd_4621_);
lean_dec(v_b_4618_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4643_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v_a_4625_; lean_object* v___x_4626_; 
v_a_4625_ = lean_array_uget_borrowed(v_as_4615_, v_i_4617_);
v___x_4626_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4621_, v_a_4625_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
lean_del_object(v___x_4623_);
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4626_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4626_);
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
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4635_; lean_object* v___x_4636_; lean_object* v___x_4638_; 
v_a_4635_ = lean_ctor_get(v___x_4626_, 0);
lean_inc(v_a_4635_);
lean_dec_ref(v___x_4626_);
v___x_4636_ = lean_box(0);
if (v_isShared_4624_ == 0)
{
lean_ctor_set(v___x_4623_, 1, v_a_4635_);
lean_ctor_set(v___x_4623_, 0, v___x_4636_);
v___x_4638_ = v___x_4623_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4636_);
lean_ctor_set(v_reuseFailAlloc_4642_, 1, v_a_4635_);
v___x_4638_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
size_t v___x_4639_; size_t v___x_4640_; lean_object* v___x_4641_; 
v___x_4639_ = ((size_t)1ULL);
v___x_4640_ = lean_usize_add(v_i_4617_, v___x_4639_);
v___x_4641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4615_, v_sz_4616_, v___x_4640_, v___x_4638_);
return v___x_4641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object* v_as_4645_, lean_object* v_sz_4646_, lean_object* v_i_4647_, lean_object* v_b_4648_){
_start:
{
size_t v_sz_boxed_4649_; size_t v_i_boxed_4650_; lean_object* v_res_4651_; 
v_sz_boxed_4649_ = lean_unbox_usize(v_sz_4646_);
lean_dec(v_sz_4646_);
v_i_boxed_4650_ = lean_unbox_usize(v_i_4647_);
lean_dec(v_i_4647_);
v_res_4651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_as_4645_, v_sz_boxed_4649_, v_i_boxed_4650_, v_b_4648_);
lean_dec_ref(v_as_4645_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_4652_, size_t v_sz_4653_, size_t v_i_4654_, lean_object* v_b_4655_){
_start:
{
uint8_t v___x_4656_; 
v___x_4656_ = lean_usize_dec_lt(v_i_4654_, v_sz_4653_);
if (v___x_4656_ == 0)
{
lean_object* v___x_4657_; 
v___x_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4657_, 0, v_b_4655_);
return v___x_4657_;
}
else
{
lean_object* v_snd_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4680_; 
v_snd_4658_ = lean_ctor_get(v_b_4655_, 1);
v_isSharedCheck_4680_ = !lean_is_exclusive(v_b_4655_);
if (v_isSharedCheck_4680_ == 0)
{
lean_object* v_unused_4681_; 
v_unused_4681_ = lean_ctor_get(v_b_4655_, 0);
lean_dec(v_unused_4681_);
v___x_4660_ = v_b_4655_;
v_isShared_4661_ = v_isSharedCheck_4680_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_snd_4658_);
lean_dec(v_b_4655_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4680_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v_a_4662_; lean_object* v___x_4663_; 
v_a_4662_ = lean_array_uget_borrowed(v_as_4652_, v_i_4654_);
v___x_4663_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4658_, v_a_4662_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
lean_del_object(v___x_4660_);
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___x_4663_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4663_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4673_; lean_object* v___x_4675_; 
v_a_4672_ = lean_ctor_get(v___x_4663_, 0);
lean_inc(v_a_4672_);
lean_dec_ref(v___x_4663_);
v___x_4673_ = lean_box(0);
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 1, v_a_4672_);
lean_ctor_set(v___x_4660_, 0, v___x_4673_);
v___x_4675_ = v___x_4660_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4673_);
lean_ctor_set(v_reuseFailAlloc_4679_, 1, v_a_4672_);
v___x_4675_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
size_t v___x_4676_; size_t v___x_4677_; 
v___x_4676_ = ((size_t)1ULL);
v___x_4677_ = lean_usize_add(v_i_4654_, v___x_4676_);
v_i_4654_ = v___x_4677_;
v_b_4655_ = v___x_4675_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_4682_, lean_object* v_sz_4683_, lean_object* v_i_4684_, lean_object* v_b_4685_){
_start:
{
size_t v_sz_boxed_4686_; size_t v_i_boxed_4687_; lean_object* v_res_4688_; 
v_sz_boxed_4686_ = lean_unbox_usize(v_sz_4683_);
lean_dec(v_sz_4683_);
v_i_boxed_4687_ = lean_unbox_usize(v_i_4684_);
lean_dec(v_i_4684_);
v_res_4688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4682_, v_sz_boxed_4686_, v_i_boxed_4687_, v_b_4685_);
lean_dec_ref(v_as_4682_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object* v_as_4689_, size_t v_sz_4690_, size_t v_i_4691_, lean_object* v_b_4692_){
_start:
{
uint8_t v___x_4693_; 
v___x_4693_ = lean_usize_dec_lt(v_i_4691_, v_sz_4690_);
if (v___x_4693_ == 0)
{
lean_object* v___x_4694_; 
v___x_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4694_, 0, v_b_4692_);
return v___x_4694_;
}
else
{
lean_object* v_snd_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4717_; 
v_snd_4695_ = lean_ctor_get(v_b_4692_, 1);
v_isSharedCheck_4717_ = !lean_is_exclusive(v_b_4692_);
if (v_isSharedCheck_4717_ == 0)
{
lean_object* v_unused_4718_; 
v_unused_4718_ = lean_ctor_get(v_b_4692_, 0);
lean_dec(v_unused_4718_);
v___x_4697_ = v_b_4692_;
v_isShared_4698_ = v_isSharedCheck_4717_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_snd_4695_);
lean_dec(v_b_4692_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4717_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v_a_4699_; lean_object* v___x_4700_; 
v_a_4699_ = lean_array_uget_borrowed(v_as_4689_, v_i_4691_);
v___x_4700_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4695_, v_a_4699_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
lean_del_object(v___x_4697_);
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4703_ = v___x_4700_;
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v___x_4700_);
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
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4709_; lean_object* v___x_4710_; lean_object* v___x_4712_; 
v_a_4709_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4709_);
lean_dec_ref(v___x_4700_);
v___x_4710_ = lean_box(0);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 1, v_a_4709_);
lean_ctor_set(v___x_4697_, 0, v___x_4710_);
v___x_4712_ = v___x_4697_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v___x_4710_);
lean_ctor_set(v_reuseFailAlloc_4716_, 1, v_a_4709_);
v___x_4712_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
size_t v___x_4713_; size_t v___x_4714_; lean_object* v___x_4715_; 
v___x_4713_ = ((size_t)1ULL);
v___x_4714_ = lean_usize_add(v_i_4691_, v___x_4713_);
v___x_4715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4689_, v_sz_4690_, v___x_4714_, v___x_4712_);
return v___x_4715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4719_, lean_object* v_sz_4720_, lean_object* v_i_4721_, lean_object* v_b_4722_){
_start:
{
size_t v_sz_boxed_4723_; size_t v_i_boxed_4724_; lean_object* v_res_4725_; 
v_sz_boxed_4723_ = lean_unbox_usize(v_sz_4720_);
lean_dec(v_sz_4720_);
v_i_boxed_4724_ = lean_unbox_usize(v_i_4721_);
lean_dec(v_i_4721_);
v_res_4725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_as_4719_, v_sz_boxed_4723_, v_i_boxed_4724_, v_b_4722_);
lean_dec_ref(v_as_4719_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object* v_init_4726_, lean_object* v_n_4727_, lean_object* v_b_4728_){
_start:
{
if (lean_obj_tag(v_n_4727_) == 0)
{
lean_object* v_cs_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; size_t v_sz_4732_; size_t v___x_4733_; lean_object* v___x_4734_; 
v_cs_4729_ = lean_ctor_get(v_n_4727_, 0);
v___x_4730_ = lean_box(0);
v___x_4731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4730_);
lean_ctor_set(v___x_4731_, 1, v_b_4728_);
v_sz_4732_ = lean_array_size(v_cs_4729_);
v___x_4733_ = ((size_t)0ULL);
v___x_4734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_4726_, v_cs_4729_, v_sz_4732_, v___x_4733_, v___x_4731_);
if (lean_obj_tag(v___x_4734_) == 0)
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
v_a_4735_ = lean_ctor_get(v___x_4734_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4734_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4737_ = v___x_4734_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4734_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4757_; 
v_a_4743_ = lean_ctor_get(v___x_4734_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4734_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4745_ = v___x_4734_;
v_isShared_4746_ = v_isSharedCheck_4757_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4734_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4757_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v_fst_4747_; 
v_fst_4747_ = lean_ctor_get(v_a_4743_, 0);
if (lean_obj_tag(v_fst_4747_) == 0)
{
lean_object* v_snd_4748_; lean_object* v___x_4749_; lean_object* v___x_4751_; 
v_snd_4748_ = lean_ctor_get(v_a_4743_, 1);
lean_inc(v_snd_4748_);
lean_dec(v_a_4743_);
v___x_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4749_, 0, v_snd_4748_);
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 0, v___x_4749_);
v___x_4751_ = v___x_4745_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4749_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
else
{
lean_object* v_val_4753_; lean_object* v___x_4755_; 
lean_inc_ref(v_fst_4747_);
lean_dec(v_a_4743_);
v_val_4753_ = lean_ctor_get(v_fst_4747_, 0);
lean_inc(v_val_4753_);
lean_dec_ref(v_fst_4747_);
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 0, v_val_4753_);
v___x_4755_ = v___x_4745_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_val_4753_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
}
else
{
lean_object* v_vs_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; size_t v_sz_4761_; size_t v___x_4762_; lean_object* v___x_4763_; 
v_vs_4758_ = lean_ctor_get(v_n_4727_, 0);
v___x_4759_ = lean_box(0);
v___x_4760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4759_);
lean_ctor_set(v___x_4760_, 1, v_b_4728_);
v_sz_4761_ = lean_array_size(v_vs_4758_);
v___x_4762_ = ((size_t)0ULL);
v___x_4763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_vs_4758_, v_sz_4761_, v___x_4762_, v___x_4760_);
if (lean_obj_tag(v___x_4763_) == 0)
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
v_a_4764_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4763_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4763_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
else
{
lean_object* v_a_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4786_; 
v_a_4772_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4774_ = v___x_4763_;
v_isShared_4775_ = v_isSharedCheck_4786_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_a_4772_);
lean_dec(v___x_4763_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4786_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v_fst_4776_; 
v_fst_4776_ = lean_ctor_get(v_a_4772_, 0);
if (lean_obj_tag(v_fst_4776_) == 0)
{
lean_object* v_snd_4777_; lean_object* v___x_4778_; lean_object* v___x_4780_; 
v_snd_4777_ = lean_ctor_get(v_a_4772_, 1);
lean_inc(v_snd_4777_);
lean_dec(v_a_4772_);
v___x_4778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4778_, 0, v_snd_4777_);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 0, v___x_4778_);
v___x_4780_ = v___x_4774_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4778_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
else
{
lean_object* v_val_4782_; lean_object* v___x_4784_; 
lean_inc_ref(v_fst_4776_);
lean_dec(v_a_4772_);
v_val_4782_ = lean_ctor_get(v_fst_4776_, 0);
lean_inc(v_val_4782_);
lean_dec_ref(v_fst_4776_);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 0, v_val_4782_);
v___x_4784_ = v___x_4774_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_val_4782_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object* v_init_4787_, lean_object* v_as_4788_, size_t v_sz_4789_, size_t v_i_4790_, lean_object* v_b_4791_){
_start:
{
uint8_t v___x_4792_; 
v___x_4792_ = lean_usize_dec_lt(v_i_4790_, v_sz_4789_);
if (v___x_4792_ == 0)
{
lean_object* v___x_4793_; 
v___x_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4793_, 0, v_b_4791_);
return v___x_4793_;
}
else
{
lean_object* v_snd_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4828_; 
v_snd_4794_ = lean_ctor_get(v_b_4791_, 1);
v_isSharedCheck_4828_ = !lean_is_exclusive(v_b_4791_);
if (v_isSharedCheck_4828_ == 0)
{
lean_object* v_unused_4829_; 
v_unused_4829_ = lean_ctor_get(v_b_4791_, 0);
lean_dec(v_unused_4829_);
v___x_4796_ = v_b_4791_;
v_isShared_4797_ = v_isSharedCheck_4828_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_snd_4794_);
lean_dec(v_b_4791_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4828_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v_a_4798_; lean_object* v___x_4799_; 
v_a_4798_ = lean_array_uget_borrowed(v_as_4788_, v_i_4790_);
lean_inc(v_snd_4794_);
v___x_4799_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4787_, v_a_4798_, v_snd_4794_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
lean_del_object(v___x_4796_);
lean_dec(v_snd_4794_);
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4802_ = v___x_4799_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4827_; 
v_a_4808_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4810_ = v___x_4799_;
v_isShared_4811_ = v_isSharedCheck_4827_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4799_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4827_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
if (lean_obj_tag(v_a_4808_) == 0)
{
lean_object* v___x_4812_; lean_object* v___x_4814_; 
v___x_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4812_, 0, v_a_4808_);
if (v_isShared_4797_ == 0)
{
lean_ctor_set(v___x_4796_, 0, v___x_4812_);
v___x_4814_ = v___x_4796_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v___x_4812_);
lean_ctor_set(v_reuseFailAlloc_4818_, 1, v_snd_4794_);
v___x_4814_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
lean_object* v___x_4816_; 
if (v_isShared_4811_ == 0)
{
lean_ctor_set(v___x_4810_, 0, v___x_4814_);
v___x_4816_ = v___x_4810_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4814_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
else
{
lean_object* v_a_4819_; lean_object* v___x_4820_; lean_object* v___x_4822_; 
lean_del_object(v___x_4810_);
lean_dec(v_snd_4794_);
v_a_4819_ = lean_ctor_get(v_a_4808_, 0);
lean_inc(v_a_4819_);
lean_dec_ref(v_a_4808_);
v___x_4820_ = lean_box(0);
if (v_isShared_4797_ == 0)
{
lean_ctor_set(v___x_4796_, 1, v_a_4819_);
lean_ctor_set(v___x_4796_, 0, v___x_4820_);
v___x_4822_ = v___x_4796_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4820_);
lean_ctor_set(v_reuseFailAlloc_4826_, 1, v_a_4819_);
v___x_4822_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
size_t v___x_4823_; size_t v___x_4824_; 
v___x_4823_ = ((size_t)1ULL);
v___x_4824_ = lean_usize_add(v_i_4790_, v___x_4823_);
v_i_4790_ = v___x_4824_;
v_b_4791_ = v___x_4822_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4830_, lean_object* v_as_4831_, lean_object* v_sz_4832_, lean_object* v_i_4833_, lean_object* v_b_4834_){
_start:
{
size_t v_sz_boxed_4835_; size_t v_i_boxed_4836_; lean_object* v_res_4837_; 
v_sz_boxed_4835_ = lean_unbox_usize(v_sz_4832_);
lean_dec(v_sz_4832_);
v_i_boxed_4836_ = lean_unbox_usize(v_i_4833_);
lean_dec(v_i_4833_);
v_res_4837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_4830_, v_as_4831_, v_sz_boxed_4835_, v_i_boxed_4836_, v_b_4834_);
lean_dec_ref(v_as_4831_);
lean_dec_ref(v_init_4830_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object* v_init_4838_, lean_object* v_n_4839_, lean_object* v_b_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4838_, v_n_4839_, v_b_4840_);
lean_dec_ref(v_n_4839_);
lean_dec_ref(v_init_4838_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object* v_t_4842_, lean_object* v_init_4843_){
_start:
{
lean_object* v_root_4844_; lean_object* v_tail_4845_; lean_object* v___x_4846_; 
v_root_4844_ = lean_ctor_get(v_t_4842_, 0);
v_tail_4845_ = lean_ctor_get(v_t_4842_, 1);
lean_inc_ref(v_init_4843_);
v___x_4846_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4843_, v_root_4844_, v_init_4843_);
lean_dec_ref(v_init_4843_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4846_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4846_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
else
{
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4891_; 
v_a_4855_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4857_ = v___x_4846_;
v_isShared_4858_ = v_isSharedCheck_4891_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_a_4855_);
lean_dec(v___x_4846_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4891_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
if (lean_obj_tag(v_a_4855_) == 0)
{
lean_object* v_a_4859_; lean_object* v___x_4861_; 
v_a_4859_ = lean_ctor_get(v_a_4855_, 0);
lean_inc(v_a_4859_);
lean_dec_ref(v_a_4855_);
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 0, v_a_4859_);
v___x_4861_ = v___x_4857_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4859_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
else
{
lean_object* v_a_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; size_t v_sz_4866_; size_t v___x_4867_; lean_object* v___x_4868_; 
lean_del_object(v___x_4857_);
v_a_4863_ = lean_ctor_get(v_a_4855_, 0);
lean_inc(v_a_4863_);
lean_dec_ref(v_a_4855_);
v___x_4864_ = lean_box(0);
v___x_4865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4864_);
lean_ctor_set(v___x_4865_, 1, v_a_4863_);
v_sz_4866_ = lean_array_size(v_tail_4845_);
v___x_4867_ = ((size_t)0ULL);
v___x_4868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_tail_4845_, v_sz_4866_, v___x_4867_, v___x_4865_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4876_; 
v_a_4869_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4871_ = v___x_4868_;
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4868_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4874_; 
if (v_isShared_4872_ == 0)
{
v___x_4874_ = v___x_4871_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4869_);
v___x_4874_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
return v___x_4874_;
}
}
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4890_; 
v_a_4877_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4879_ = v___x_4868_;
v_isShared_4880_ = v_isSharedCheck_4890_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4868_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4890_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v_fst_4881_; 
v_fst_4881_ = lean_ctor_get(v_a_4877_, 0);
if (lean_obj_tag(v_fst_4881_) == 0)
{
lean_object* v_snd_4882_; lean_object* v___x_4884_; 
v_snd_4882_ = lean_ctor_get(v_a_4877_, 1);
lean_inc(v_snd_4882_);
lean_dec(v_a_4877_);
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 0, v_snd_4882_);
v___x_4884_ = v___x_4879_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_snd_4882_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
else
{
lean_object* v_val_4886_; lean_object* v___x_4888_; 
lean_inc_ref(v_fst_4881_);
lean_dec(v_a_4877_);
v_val_4886_ = lean_ctor_get(v_fst_4881_, 0);
lean_inc(v_val_4886_);
lean_dec_ref(v_fst_4881_);
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 0, v_val_4886_);
v___x_4888_ = v___x_4879_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_val_4886_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0___boxed(lean_object* v_t_4892_, lean_object* v_init_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_t_4892_, v_init_4893_);
lean_dec_ref(v_t_4892_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object* v_docs_4897_){
_start:
{
lean_object* v_ctx_4898_; lean_object* v___x_4899_; 
v_ctx_4898_ = ((lean_object*)(l_Lean_VersoModuleDocs_assemble___closed__0));
v___x_4899_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_docs_4897_, v_ctx_4898_);
if (lean_obj_tag(v___x_4899_) == 0)
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4907_; 
v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4902_ = v___x_4899_;
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4899_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4905_; 
if (v_isShared_4903_ == 0)
{
v___x_4905_ = v___x_4902_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4900_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
else
{
lean_object* v_a_4908_; lean_object* v___x_4909_; 
v_a_4908_ = lean_ctor_get(v___x_4899_, 0);
lean_inc(v_a_4908_);
lean_dec_ref(v___x_4899_);
v___x_4909_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(v_a_4908_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4917_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4912_ = v___x_4909_;
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4913_ == 0)
{
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
else
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4928_; 
v_a_4918_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4920_ = v___x_4909_;
v_isShared_4921_ = v_isSharedCheck_4928_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4909_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4928_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v_content_4922_; lean_object* v_priorParts_4923_; lean_object* v___x_4924_; lean_object* v___x_4926_; 
v_content_4922_ = lean_ctor_get(v_a_4918_, 0);
lean_inc_ref(v_content_4922_);
v_priorParts_4923_ = lean_ctor_get(v_a_4918_, 1);
lean_inc_ref(v_priorParts_4923_);
lean_dec(v_a_4918_);
v___x_4924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4924_, 0, v_content_4922_);
lean_ctor_set(v___x_4924_, 1, v_priorParts_4923_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 0, v___x_4924_);
v___x_4926_ = v___x_4920_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v___x_4924_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble___boxed(lean_object* v_docs_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l_Lean_VersoModuleDocs_assemble(v_docs_4929_);
lean_dec_ref(v_docs_4929_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_es_4931_){
_start:
{
lean_object* v___x_4932_; 
v___x_4932_ = lean_array_mk(v_es_4931_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_x_4935_, lean_object* v_x_4936_, lean_object* v_es_4937_){
_start:
{
lean_object* v_ents_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
v_ents_4938_ = lean_array_mk(v_es_4937_);
v___x_4939_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
lean_inc_ref(v_ents_4938_);
v___x_4940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4939_);
lean_ctor_set(v___x_4940_, 1, v_ents_4938_);
lean_ctor_set(v___x_4940_, 2, v_ents_4938_);
return v___x_4940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_x_4941_, lean_object* v_x_4942_, lean_object* v_es_4943_){
_start:
{
lean_object* v_res_4944_; 
v_res_4944_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v_x_4941_, v_x_4942_, v_es_4943_);
lean_dec_ref(v_x_4942_);
lean_dec_ref(v_x_4941_);
return v_res_4944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v___x_4945_, lean_object* v_x_4946_){
_start:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; size_t v___x_4950_; lean_object* v___x_4951_; 
v___x_4947_ = lean_unsigned_to_nat(32u);
v___x_4948_ = lean_mk_empty_array_with_capacity(v___x_4947_);
v___x_4949_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_4950_ = ((size_t)5ULL);
lean_inc(v___x_4945_);
v___x_4951_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4951_, 0, v___x_4949_);
lean_ctor_set(v___x_4951_, 1, v___x_4948_);
lean_ctor_set(v___x_4951_, 2, v___x_4945_);
lean_ctor_set(v___x_4951_, 3, v___x_4945_);
lean_ctor_set_usize(v___x_4951_, 4, v___x_4950_);
return v___x_4951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v___x_4952_, lean_object* v_x_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v___x_4952_, v_x_4953_);
lean_dec_ref(v_x_4953_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4975_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
v___x_4976_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_4975_);
return v___x_4976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_a_4977_){
_start:
{
lean_object* v_res_4978_; 
v_res_4978_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object* v_env_4979_){
_start:
{
lean_object* v___x_4980_; lean_object* v_toEnvExtension_4981_; lean_object* v_asyncMode_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4980_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_4981_ = lean_ctor_get(v___x_4980_, 0);
v_asyncMode_4982_ = lean_ctor_get(v_toEnvExtension_4981_, 2);
v___x_4983_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_4984_ = lean_box(0);
v___x_4985_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4983_, v___x_4980_, v_env_4979_, v_asyncMode_4982_, v___x_4984_);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object* v_env_4986_){
_start:
{
lean_object* v___x_4987_; 
v___x_4987_ = l_Lean_getMainVersoModuleDocs(v_env_4986_);
return v___x_4987_;
}
}
static lean_object* _init_l_Lean_getVersoModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4988_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_4989_ = lean_box(0);
v___x_4990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
lean_ctor_set(v___x_4990_, 1, v___x_4988_);
return v___x_4990_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object* v_env_4991_, lean_object* v_moduleName_4992_){
_start:
{
lean_object* v___x_4993_; 
v___x_4993_ = l_Lean_Environment_getModuleIdx_x3f(v_env_4991_, v_moduleName_4992_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v___x_4994_; 
v___x_4994_ = lean_box(0);
return v___x_4994_;
}
else
{
lean_object* v_val_4995_; lean_object* v___x_4997_; uint8_t v_isShared_4998_; uint8_t v_isSharedCheck_5006_; 
v_val_4995_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_4997_ = v___x_4993_;
v_isShared_4998_ = v_isSharedCheck_5006_;
goto v_resetjp_4996_;
}
else
{
lean_inc(v_val_4995_);
lean_dec(v___x_4993_);
v___x_4997_ = lean_box(0);
v_isShared_4998_ = v_isSharedCheck_5006_;
goto v_resetjp_4996_;
}
v_resetjp_4996_:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; uint8_t v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5004_; 
v___x_4999_ = lean_obj_once(&l_Lean_getVersoModuleDoc_x3f___closed__0, &l_Lean_getVersoModuleDoc_x3f___closed__0_once, _init_l_Lean_getVersoModuleDoc_x3f___closed__0);
v___x_5000_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v___x_5001_ = 1;
v___x_5002_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_4999_, v___x_5000_, v_env_4991_, v_val_4995_, v___x_5001_);
lean_dec(v_val_4995_);
if (v_isShared_4998_ == 0)
{
lean_ctor_set(v___x_4997_, 0, v___x_5002_);
v___x_5004_ = v___x_4997_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v___x_5002_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object* v_env_5007_, lean_object* v_moduleName_5008_){
_start:
{
lean_object* v_res_5009_; 
v_res_5009_ = l_Lean_getVersoModuleDoc_x3f(v_env_5007_, v_moduleName_5008_);
lean_dec(v_moduleName_5008_);
lean_dec_ref(v_env_5007_);
return v_res_5009_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object* v_env_5012_, lean_object* v_snippet_5013_){
_start:
{
lean_object* v_docs_5014_; uint8_t v___x_5015_; 
lean_inc_ref(v_env_5012_);
v_docs_5014_ = l_Lean_getMainVersoModuleDocs(v_env_5012_);
v___x_5015_ = l_Lean_VersoModuleDocs_canAdd(v_docs_5014_, v_snippet_5013_);
if (v___x_5015_ == 0)
{
lean_object* v___x_5016_; lean_object* v___y_5018_; lean_object* v___x_5023_; 
lean_dec_ref(v_snippet_5013_);
lean_dec_ref(v_env_5012_);
v___x_5016_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__0));
v___x_5023_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_5014_);
lean_dec_ref(v_docs_5014_);
if (lean_obj_tag(v___x_5023_) == 0)
{
lean_object* v___x_5024_; 
v___x_5024_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___y_5018_ = v___x_5024_;
goto v___jp_5017_;
}
else
{
lean_object* v_val_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v_val_5025_ = lean_ctor_get(v___x_5023_, 0);
lean_inc(v_val_5025_);
lean_dec_ref(v___x_5023_);
v___x_5026_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__1));
v___x_5027_ = l_Nat_reprFast(v_val_5025_);
v___x_5028_ = lean_string_append(v___x_5026_, v___x_5027_);
lean_dec_ref(v___x_5027_);
v___x_5029_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_5030_ = lean_string_append(v___x_5028_, v___x_5029_);
v___y_5018_ = v___x_5030_;
goto v___jp_5017_;
}
v___jp_5017_:
{
lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5019_ = lean_string_append(v___x_5016_, v___y_5018_);
lean_dec_ref(v___y_5018_);
v___x_5020_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___closed__8));
v___x_5021_ = lean_string_append(v___x_5019_, v___x_5020_);
v___x_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5021_);
return v___x_5022_;
}
}
else
{
lean_object* v___x_5031_; lean_object* v_toEnvExtension_5032_; lean_object* v_asyncMode_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; 
lean_dec_ref(v_docs_5014_);
v___x_5031_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_5032_ = lean_ctor_get(v___x_5031_, 0);
v_asyncMode_5033_ = lean_ctor_get(v_toEnvExtension_5032_, 2);
v___x_5034_ = lean_box(0);
v___x_5035_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5031_, v_env_5012_, v_snippet_5013_, v_asyncMode_5033_, v___x_5034_);
v___x_5036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5035_);
return v___x_5036_;
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
