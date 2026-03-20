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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object*);
lean_object* l_Lean_Doc_MarkdownM_push___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object*);
lean_object* l_Lean_Doc_MarkdownM_endsWith___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* lean_string_push(lean_object*, uint32_t);
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
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__1;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__3;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__4;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__5;
static const lean_ctor_object l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__6 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "**"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__2 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "​"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__3 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__3_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__4 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__5 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__6 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]("};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__7 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__8 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 3, .m_data = "[ˆ^"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__9 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__10 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__10_value;
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_findInternalDocString_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__11 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__11_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__12 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__12_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__13;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__14 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__10_value)}};
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
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__8_value)}};
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
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_instToMarkdownSnippet___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToMarkdownSnippet___lam__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_62_ = lean_apply_3(v_go_57_, v___y_59_, v___y_60_, v___y_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__1(lean_object* v___x_63_, lean_object* v_go_64_, lean_object* v___i_65_, lean_object* v_content_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_array_get_size(v_content_66_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_nat_dec_lt(v___x_69_, v___x_70_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
lean_dec_ref(v___y_67_);
lean_dec_ref(v_content_66_);
lean_dec_ref(v_go_64_);
lean_dec_ref(v___x_63_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___y_68_);
return v___x_73_;
}
else
{
lean_object* v___f_74_; uint8_t v___x_75_; 
v___f_74_ = lean_alloc_closure((void*)(l_Lean_instMarkdownInlineElabInline___lam__0), 5, 1);
lean_closure_set(v___f_74_, 0, v_go_64_);
v___x_75_ = lean_nat_dec_le(v___x_70_, v___x_70_);
if (v___x_75_ == 0)
{
if (v___x_72_ == 0)
{
lean_object* v___x_76_; 
lean_dec_ref(v___f_74_);
lean_dec_ref(v___y_67_);
lean_dec_ref(v_content_66_);
lean_dec_ref(v___x_63_);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_71_);
lean_ctor_set(v___x_76_, 1, v___y_68_);
return v___x_76_;
}
else
{
size_t v___x_77_; size_t v___x_78_; lean_object* v___x_499__overap_79_; lean_object* v___x_80_; 
v___x_77_ = ((size_t)0ULL);
v___x_78_ = lean_usize_of_nat(v___x_70_);
v___x_499__overap_79_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_63_, v___f_74_, v_content_66_, v___x_77_, v___x_78_, v___x_71_);
v___x_80_ = lean_apply_2(v___x_499__overap_79_, v___y_67_, v___y_68_);
return v___x_80_;
}
}
else
{
size_t v___x_81_; size_t v___x_82_; lean_object* v___x_502__overap_83_; lean_object* v___x_84_; 
v___x_81_ = ((size_t)0ULL);
v___x_82_ = lean_usize_of_nat(v___x_70_);
v___x_502__overap_83_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_63_, v___f_74_, v_content_66_, v___x_81_, v___x_82_, v___x_71_);
v___x_84_ = lean_apply_2(v___x_502__overap_83_, v___y_67_, v___y_68_);
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__1___boxed(lean_object* v___x_85_, lean_object* v_go_86_, lean_object* v___i_87_, lean_object* v_content_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_instMarkdownInlineElabInline___lam__1(v___x_85_, v_go_86_, v___i_87_, v_content_88_, v___y_89_, v___y_90_);
lean_dec_ref(v___i_87_);
return v_res_91_;
}
}
static lean_object* _init_l_Lean_instMarkdownInlineElabInline___closed__20(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_instMarkdownInlineElabInline___closed__19));
v___x_138_ = l_ReaderT_instMonad___redArg(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_instMarkdownInlineElabInline___closed__21(void){
_start:
{
lean_object* v___x_139_; lean_object* v___f_140_; 
v___x_139_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__20, &l_Lean_instMarkdownInlineElabInline___closed__20_once, _init_l_Lean_instMarkdownInlineElabInline___closed__20);
v___f_140_ = lean_alloc_closure((void*)(l_Lean_instMarkdownInlineElabInline___lam__1___boxed), 6, 1);
lean_closure_set(v___f_140_, 0, v___x_139_);
return v___f_140_;
}
}
static lean_object* _init_l_Lean_instMarkdownInlineElabInline(void){
_start:
{
lean_object* v___f_141_; 
v___f_141_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__21, &l_Lean_instMarkdownInlineElabInline___closed__21_once, _init_l_Lean_instMarkdownInlineElabInline___closed__21);
return v___f_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0(lean_object* v_v_142_, lean_object* v_x_143_){
_start:
{
lean_object* v_name_144_; lean_object* v_val_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_171_; 
v_name_144_ = lean_ctor_get(v_v_142_, 0);
v_val_145_ = lean_ctor_get(v_v_142_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_v_142_);
if (v_isSharedCheck_171_ == 0)
{
v___x_147_ = v_v_142_;
v_isShared_148_ = v_isSharedCheck_171_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_val_145_);
lean_inc(v_name_144_);
lean_dec(v_v_142_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_171_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_149_ = lean_box(1);
v___x_150_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = l_Lean_Name_reprPrec(v_name_144_, v___x_151_);
if (v_isShared_148_ == 0)
{
lean_ctor_set_tag(v___x_147_, 5);
lean_ctor_set(v___x_147_, 1, v___x_152_);
lean_ctor_set(v___x_147_, 0, v___x_150_);
v___x_154_ = v___x_147_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_170_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_155_ = l_Std_Format_nestD(v___x_154_);
v___x_156_ = 0;
v___x_157_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*1, v___x_156_);
v___x_158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_149_);
v___x_159_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_160_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_145_);
lean_dec(v_val_145_);
v___x_161_ = l_Lean_Name_reprPrec(v___x_160_, v___x_151_);
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_159_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = l_Std_Format_nestD(v___x_164_);
v___x_166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_156_);
v___x_167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_158_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = l_Std_Format_nestD(v___x_167_);
v___x_169_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*1, v___x_156_);
return v___x_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0___boxed(lean_object* v_v_172_, lean_object* v_x_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_instReprElabBlock___lam__0(v_v_172_, v_x_173_);
lean_dec(v_x_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v_goB_177_, lean_object* v_x_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_apply_3(v_goB_177_, v___y_179_, v___y_180_, v___y_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1(lean_object* v___x_183_, lean_object* v___goI_184_, lean_object* v_goB_185_, lean_object* v___b_186_, lean_object* v_content_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = lean_array_get_size(v_content_187_);
v___x_192_ = lean_box(0);
v___x_193_ = lean_nat_dec_lt(v___x_190_, v___x_191_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
lean_dec_ref(v___y_188_);
lean_dec_ref(v_content_187_);
lean_dec_ref(v_goB_185_);
lean_dec_ref(v___x_183_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_192_);
lean_ctor_set(v___x_194_, 1, v___y_189_);
return v___x_194_;
}
else
{
lean_object* v___f_195_; uint8_t v___x_196_; 
v___f_195_ = lean_alloc_closure((void*)(l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0), 5, 1);
lean_closure_set(v___f_195_, 0, v_goB_185_);
v___x_196_ = lean_nat_dec_le(v___x_191_, v___x_191_);
if (v___x_196_ == 0)
{
if (v___x_193_ == 0)
{
lean_object* v___x_197_; 
lean_dec_ref(v___f_195_);
lean_dec_ref(v___y_188_);
lean_dec_ref(v_content_187_);
lean_dec_ref(v___x_183_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_192_);
lean_ctor_set(v___x_197_, 1, v___y_189_);
return v___x_197_;
}
else
{
size_t v___x_198_; size_t v___x_199_; lean_object* v___x_499__overap_200_; lean_object* v___x_201_; 
v___x_198_ = ((size_t)0ULL);
v___x_199_ = lean_usize_of_nat(v___x_191_);
v___x_499__overap_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_183_, v___f_195_, v_content_187_, v___x_198_, v___x_199_, v___x_192_);
v___x_201_ = lean_apply_2(v___x_499__overap_200_, v___y_188_, v___y_189_);
return v___x_201_;
}
}
else
{
size_t v___x_202_; size_t v___x_203_; lean_object* v___x_502__overap_204_; lean_object* v___x_205_; 
v___x_202_ = ((size_t)0ULL);
v___x_203_ = lean_usize_of_nat(v___x_191_);
v___x_502__overap_204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_183_, v___f_195_, v_content_187_, v___x_202_, v___x_203_, v___x_192_);
v___x_205_ = lean_apply_2(v___x_502__overap_204_, v___y_188_, v___y_189_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1___boxed(lean_object* v___x_206_, lean_object* v___goI_207_, lean_object* v_goB_208_, lean_object* v___b_209_, lean_object* v_content_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1(v___x_206_, v___goI_207_, v_goB_208_, v___b_209_, v_content_210_, v___y_211_, v___y_212_);
lean_dec_ref(v___b_209_);
lean_dec_ref(v___goI_207_);
return v_res_213_;
}
}
static lean_object* _init_l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0(void){
_start:
{
lean_object* v___x_214_; lean_object* v___f_215_; 
v___x_214_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__20, &l_Lean_instMarkdownInlineElabInline___closed__20_once, _init_l_Lean_instMarkdownInlineElabInline___closed__20);
v___f_215_ = lean_alloc_closure((void*)(l_Lean_instMarkdownBlockElabInlineElabBlock___lam__1___boxed), 7, 1);
lean_closure_set(v___f_215_, 0, v___x_214_);
return v___f_215_;
}
}
static lean_object* _init_l_Lean_instMarkdownBlockElabInlineElabBlock(void){
_start:
{
lean_object* v___f_216_; 
v___f_216_ = lean_obj_once(&l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0, &l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0_once, _init_l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0);
return v___f_216_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoDocString_default___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default___closed__0));
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoDocString_default(void){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Lean_instInhabitedVersoDocString_default___closed__1, &l_Lean_instInhabitedVersoDocString_default___closed__1_once, _init_l_Lean_instInhabitedVersoDocString_default___closed__1);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoDocString(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_instInhabitedVersoDocString_default;
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(lean_object* v_name_223_, lean_object* v_decl_224_, lean_object* v_ref_225_){
_start:
{
lean_object* v_defValue_227_; lean_object* v_descr_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_255_; 
v_defValue_227_ = lean_ctor_get(v_decl_224_, 0);
v_descr_228_ = lean_ctor_get(v_decl_224_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_decl_224_);
if (v_isSharedCheck_255_ == 0)
{
v___x_230_ = v_decl_224_;
v_isShared_231_ = v_isSharedCheck_255_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_descr_228_);
lean_inc(v_defValue_227_);
lean_dec(v_decl_224_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_255_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_232_ = lean_alloc_ctor(1, 0, 1);
v___x_233_ = lean_unbox(v_defValue_227_);
lean_ctor_set_uint8(v___x_232_, 0, v___x_233_);
lean_inc(v_name_223_);
v___x_234_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_234_, 0, v_name_223_);
lean_ctor_set(v___x_234_, 1, v_ref_225_);
lean_ctor_set(v___x_234_, 2, v___x_232_);
lean_ctor_set(v___x_234_, 3, v_descr_228_);
lean_inc(v_name_223_);
v___x_235_ = lean_register_option(v_name_223_, v___x_234_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_245_; 
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v___x_235_, 0);
lean_dec(v_unused_246_);
v___x_237_ = v___x_235_;
v_isShared_238_ = v_isSharedCheck_245_;
goto v_resetjp_236_;
}
else
{
lean_dec(v___x_235_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_245_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v_defValue_227_);
lean_ctor_set(v___x_230_, 0, v_name_223_);
v___x_240_ = v___x_230_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_name_223_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_defValue_227_);
v___x_240_ = v_reuseFailAlloc_244_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_242_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_240_);
v___x_242_ = v___x_237_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_del_object(v___x_230_);
lean_dec(v_defValue_227_);
lean_dec(v_name_223_);
v_a_247_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_235_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_235_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_256_, lean_object* v_decl_257_, lean_object* v_ref_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v_name_256_, v_decl_257_, v_ref_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_278_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_279_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_280_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_277_, v___x_278_, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4____boxed(lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_300_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_301_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_302_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_299_, v___x_300_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4____boxed(lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_box(1);
v___x_307_ = lean_st_mk_ref(v___x_306_);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2____boxed(lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_311_, lean_object* v_x_312_){
_start:
{
if (lean_obj_tag(v_x_312_) == 0)
{
lean_object* v_k_313_; lean_object* v_v_314_; lean_object* v_l_315_; lean_object* v_r_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_k_313_ = lean_ctor_get(v_x_312_, 1);
v_v_314_ = lean_ctor_get(v_x_312_, 2);
v_l_315_ = lean_ctor_get(v_x_312_, 3);
v_r_316_ = lean_ctor_get(v_x_312_, 4);
v___x_317_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(v_init_311_, v_l_315_);
lean_inc(v_v_314_);
lean_inc(v_k_313_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v_k_313_);
lean_ctor_set(v___x_318_, 1, v_v_314_);
v___x_319_ = lean_array_push(v___x_317_, v___x_318_);
v_init_311_ = v___x_319_;
v_x_312_ = v_r_316_;
goto _start;
}
else
{
return v_init_311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_321_, lean_object* v_x_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(v_init_321_, v_x_322_);
lean_dec(v_x_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_(lean_object* v_x_326_, lean_object* v_s_327_, uint8_t v_level_328_){
_start:
{
uint8_t v___x_329_; uint8_t v___x_330_; 
v___x_329_ = 1;
v___x_330_ = l_Lean_instOrdOLeanLevel_ord(v_level_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
v___x_331_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_333_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(v___x_332_, v_s_327_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2____boxed(lean_object* v_x_334_, lean_object* v_s_335_, lean_object* v_level_336_){
_start:
{
uint8_t v_level_boxed_337_; lean_object* v_res_338_; 
v_level_boxed_337_ = lean_unbox(v_level_336_);
v_res_338_ = l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_(v_x_334_, v_s_335_, v_level_boxed_337_);
lean_dec(v_s_335_);
lean_dec_ref(v_x_334_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___f_347_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_348_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_349_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_350_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_348_, v___x_349_, v___f_347_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2____boxed(lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_();
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0(lean_object* v_init_353_, lean_object* v_t_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0_spec__0(v_init_353_, v_t_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_356_, lean_object* v_t_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2__spec__0(v_init_356_, v_t_357_);
lean_dec(v_t_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
lean_object* v_k_361_; lean_object* v_v_362_; lean_object* v_l_363_; lean_object* v_r_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_k_361_ = lean_ctor_get(v_x_360_, 1);
v_v_362_ = lean_ctor_get(v_x_360_, 2);
v_l_363_ = lean_ctor_get(v_x_360_, 3);
v_r_364_ = lean_ctor_get(v_x_360_, 4);
v___x_365_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(v_init_359_, v_l_363_);
lean_inc(v_v_362_);
lean_inc(v_k_361_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_k_361_);
lean_ctor_set(v___x_366_, 1, v_v_362_);
v___x_367_ = lean_array_push(v___x_365_, v___x_366_);
v_init_359_ = v___x_367_;
v_x_360_ = v_r_364_;
goto _start;
}
else
{
return v_init_359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_369_, lean_object* v_x_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(v_init_369_, v_x_370_);
lean_dec(v_x_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_(lean_object* v_x_374_, lean_object* v_s_375_, uint8_t v_level_376_){
_start:
{
uint8_t v___x_377_; uint8_t v___x_378_; 
v___x_377_ = 1;
v___x_378_ = l_Lean_instOrdOLeanLevel_ord(v_level_376_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
v___x_379_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
return v___x_379_;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
v___x_381_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(v___x_380_, v_s_375_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2____boxed(lean_object* v_x_382_, lean_object* v_s_383_, lean_object* v_level_384_){
_start:
{
uint8_t v_level_boxed_385_; lean_object* v_res_386_; 
v_level_boxed_385_ = lean_unbox(v_level_384_);
v_res_386_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_(v_x_382_, v_s_383_, v_level_boxed_385_);
lean_dec(v_s_383_);
lean_dec_ref(v_x_382_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___f_416_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
v___x_417_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
v___x_418_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_));
v___x_419_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_417_, v___x_418_, v___f_416_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2____boxed(lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2_();
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0(lean_object* v_init_422_, lean_object* v_t_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0_spec__0(v_init_422_, v_t_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_425_, lean_object* v_t_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_177922276____hygCtx___hyg_2__spec__0(v_init_425_, v_t_426_);
lean_dec(v_t_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_box(1);
v___x_430_ = lean_st_mk_ref(v___x_429_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_434_, lean_object* v_x_435_){
_start:
{
if (lean_obj_tag(v_x_435_) == 0)
{
lean_object* v_k_436_; lean_object* v_v_437_; lean_object* v_l_438_; lean_object* v_r_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_k_436_ = lean_ctor_get(v_x_435_, 1);
v_v_437_ = lean_ctor_get(v_x_435_, 2);
v_l_438_ = lean_ctor_get(v_x_435_, 3);
v_r_439_ = lean_ctor_get(v_x_435_, 4);
v___x_440_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(v_init_434_, v_l_438_);
lean_inc(v_v_437_);
lean_inc(v_k_436_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_k_436_);
lean_ctor_set(v___x_441_, 1, v_v_437_);
v___x_442_ = lean_array_push(v___x_440_, v___x_441_);
v_init_434_ = v___x_442_;
v_x_435_ = v_r_439_;
goto _start;
}
else
{
return v_init_434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_444_, lean_object* v_x_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(v_init_444_, v_x_445_);
lean_dec(v_x_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_(lean_object* v_x_449_, lean_object* v_s_450_, uint8_t v_level_451_){
_start:
{
uint8_t v___x_452_; uint8_t v___x_453_; 
v___x_452_ = 1;
v___x_453_ = l_Lean_instOrdOLeanLevel_ord(v_level_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
v___x_454_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_));
return v___x_454_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_));
v___x_456_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(v___x_455_, v_s_450_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2____boxed(lean_object* v_x_457_, lean_object* v_s_458_, lean_object* v_level_459_){
_start:
{
uint8_t v_level_boxed_460_; lean_object* v_res_461_; 
v_level_boxed_460_ = lean_unbox(v_level_459_);
v_res_461_ = l_Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_(v_x_457_, v_s_458_, v_level_boxed_460_);
lean_dec(v_s_458_);
lean_dec_ref(v_x_457_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___f_468_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_));
v___x_469_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_));
v___x_470_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1505119820____hygCtx___hyg_2_));
v___x_471_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_469_, v___x_470_, v___f_468_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2____boxed(lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2_();
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0(lean_object* v_init_474_, lean_object* v_t_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0_spec__0(v_init_474_, v_t_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_477_, lean_object* v_t_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_DocString_Extension_152104186____hygCtx___hyg_2__spec__0(v_init_477_, v_t_478_);
lean_dec(v_t_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString(lean_object* v_declName_480_, lean_object* v_docString_481_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_483_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_484_ = lean_st_ref_take(v___x_483_);
v___x_485_ = l_String_removeLeadingSpaces(v_docString_481_);
v___x_486_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_480_, v___x_485_, v___x_484_);
v___x_487_ = lean_st_ref_set(v___x_483_, v___x_486_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString___boxed(lean_object* v_declName_489_, lean_object* v_docString_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_addBuiltinDocString(v_declName_489_, v_docString_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object* v_k_493_, lean_object* v_t_494_){
_start:
{
if (lean_obj_tag(v_t_494_) == 0)
{
lean_object* v_k_495_; lean_object* v_v_496_; lean_object* v_l_497_; lean_object* v_r_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_1152_; 
v_k_495_ = lean_ctor_get(v_t_494_, 1);
v_v_496_ = lean_ctor_get(v_t_494_, 2);
v_l_497_ = lean_ctor_get(v_t_494_, 3);
v_r_498_ = lean_ctor_get(v_t_494_, 4);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_t_494_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; 
v_unused_1153_ = lean_ctor_get(v_t_494_, 0);
lean_dec(v_unused_1153_);
v___x_500_ = v_t_494_;
v_isShared_501_ = v_isSharedCheck_1152_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_r_498_);
lean_inc(v_l_497_);
lean_inc(v_v_496_);
lean_inc(v_k_495_);
lean_dec(v_t_494_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_1152_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
uint8_t v___x_502_; 
v___x_502_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_493_, v_k_495_);
switch(v___x_502_)
{
case 0:
{
lean_object* v_impl_503_; lean_object* v___x_504_; 
v_impl_503_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_493_, v_l_497_);
v___x_504_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_503_) == 0)
{
if (lean_obj_tag(v_r_498_) == 0)
{
lean_object* v_size_505_; lean_object* v_size_506_; lean_object* v_k_507_; lean_object* v_v_508_; lean_object* v_l_509_; lean_object* v_r_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_size_505_ = lean_ctor_get(v_impl_503_, 0);
lean_inc(v_size_505_);
v_size_506_ = lean_ctor_get(v_r_498_, 0);
v_k_507_ = lean_ctor_get(v_r_498_, 1);
v_v_508_ = lean_ctor_get(v_r_498_, 2);
v_l_509_ = lean_ctor_get(v_r_498_, 3);
lean_inc(v_l_509_);
v_r_510_ = lean_ctor_get(v_r_498_, 4);
v___x_511_ = lean_unsigned_to_nat(3u);
v___x_512_ = lean_nat_mul(v___x_511_, v_size_505_);
v___x_513_ = lean_nat_dec_lt(v___x_512_, v_size_506_);
lean_dec(v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
lean_dec(v_l_509_);
v___x_514_ = lean_nat_add(v___x_504_, v_size_505_);
lean_dec(v_size_505_);
v___x_515_ = lean_nat_add(v___x_514_, v_size_506_);
lean_dec(v___x_514_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 3, v_impl_503_);
lean_ctor_set(v___x_500_, 0, v___x_515_);
v___x_517_ = v___x_500_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_impl_503_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v_r_498_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
else
{
lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_582_; 
lean_inc(v_r_510_);
lean_inc(v_v_508_);
lean_inc(v_k_507_);
lean_inc(v_size_506_);
v_isSharedCheck_582_ = !lean_is_exclusive(v_r_498_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; lean_object* v_unused_584_; lean_object* v_unused_585_; lean_object* v_unused_586_; lean_object* v_unused_587_; 
v_unused_583_ = lean_ctor_get(v_r_498_, 4);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_r_498_, 3);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_r_498_, 2);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_r_498_, 1);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_r_498_, 0);
lean_dec(v_unused_587_);
v___x_520_ = v_r_498_;
v_isShared_521_ = v_isSharedCheck_582_;
goto v_resetjp_519_;
}
else
{
lean_dec(v_r_498_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_582_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_size_522_; lean_object* v_k_523_; lean_object* v_v_524_; lean_object* v_l_525_; lean_object* v_r_526_; lean_object* v_size_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v_size_522_ = lean_ctor_get(v_l_509_, 0);
v_k_523_ = lean_ctor_get(v_l_509_, 1);
v_v_524_ = lean_ctor_get(v_l_509_, 2);
v_l_525_ = lean_ctor_get(v_l_509_, 3);
v_r_526_ = lean_ctor_get(v_l_509_, 4);
v_size_527_ = lean_ctor_get(v_r_510_, 0);
v___x_528_ = lean_unsigned_to_nat(2u);
v___x_529_ = lean_nat_mul(v___x_528_, v_size_527_);
v___x_530_ = lean_nat_dec_lt(v_size_522_, v___x_529_);
lean_dec(v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_558_; 
lean_inc(v_r_526_);
lean_inc(v_l_525_);
lean_inc(v_v_524_);
lean_inc(v_k_523_);
v_isSharedCheck_558_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; lean_object* v_unused_560_; lean_object* v_unused_561_; lean_object* v_unused_562_; lean_object* v_unused_563_; 
v_unused_559_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_560_);
v_unused_561_ = lean_ctor_get(v_l_509_, 2);
lean_dec(v_unused_561_);
v_unused_562_ = lean_ctor_get(v_l_509_, 1);
lean_dec(v_unused_562_);
v_unused_563_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_563_);
v___x_532_ = v_l_509_;
v_isShared_533_ = v_isSharedCheck_558_;
goto v_resetjp_531_;
}
else
{
lean_dec(v_l_509_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_558_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_548_; 
v___x_534_ = lean_nat_add(v___x_504_, v_size_505_);
lean_dec(v_size_505_);
v___x_535_ = lean_nat_add(v___x_534_, v_size_506_);
lean_dec(v_size_506_);
if (lean_obj_tag(v_l_525_) == 0)
{
lean_object* v_size_556_; 
v_size_556_ = lean_ctor_get(v_l_525_, 0);
lean_inc(v_size_556_);
v___y_548_ = v_size_556_;
goto v___jp_547_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = lean_unsigned_to_nat(0u);
v___y_548_ = v___x_557_;
goto v___jp_547_;
}
v___jp_536_:
{
lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_540_ = lean_nat_add(v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec(v___y_538_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 4, v_r_510_);
lean_ctor_set(v___x_532_, 3, v_r_526_);
lean_ctor_set(v___x_532_, 2, v_v_508_);
lean_ctor_set(v___x_532_, 1, v_k_507_);
lean_ctor_set(v___x_532_, 0, v___x_540_);
v___x_542_ = v___x_532_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_r_526_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_r_510_);
v___x_542_ = v_reuseFailAlloc_546_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_544_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 4, v___x_542_);
lean_ctor_set(v___x_520_, 3, v___y_537_);
lean_ctor_set(v___x_520_, 2, v_v_524_);
lean_ctor_set(v___x_520_, 1, v_k_523_);
lean_ctor_set(v___x_520_, 0, v___x_535_);
v___x_544_ = v___x_520_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_k_523_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_v_524_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v___y_537_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
v___jp_547_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_nat_add(v___x_534_, v___y_548_);
lean_dec(v___y_548_);
lean_dec(v___x_534_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_l_525_);
lean_ctor_set(v___x_500_, 3, v_impl_503_);
lean_ctor_set(v___x_500_, 0, v___x_549_);
v___x_551_ = v___x_500_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_impl_503_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_l_525_);
v___x_551_ = v_reuseFailAlloc_555_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; 
v___x_552_ = lean_nat_add(v___x_504_, v_size_527_);
if (lean_obj_tag(v_r_526_) == 0)
{
lean_object* v_size_553_; 
v_size_553_ = lean_ctor_get(v_r_526_, 0);
lean_inc(v_size_553_);
v___y_537_ = v___x_551_;
v___y_538_ = v___x_552_;
v___y_539_ = v_size_553_;
goto v___jp_536_;
}
else
{
lean_object* v___x_554_; 
v___x_554_ = lean_unsigned_to_nat(0u);
v___y_537_ = v___x_551_;
v___y_538_ = v___x_552_;
v___y_539_ = v___x_554_;
goto v___jp_536_;
}
}
}
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
lean_del_object(v___x_500_);
v___x_564_ = lean_nat_add(v___x_504_, v_size_505_);
lean_dec(v_size_505_);
v___x_565_ = lean_nat_add(v___x_564_, v_size_506_);
lean_dec(v_size_506_);
v___x_566_ = lean_nat_add(v___x_564_, v_size_522_);
lean_dec(v___x_564_);
lean_inc_ref(v_impl_503_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 4, v_l_509_);
lean_ctor_set(v___x_520_, 3, v_impl_503_);
lean_ctor_set(v___x_520_, 2, v_v_496_);
lean_ctor_set(v___x_520_, 1, v_k_495_);
lean_ctor_set(v___x_520_, 0, v___x_566_);
v___x_568_ = v___x_520_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v_impl_503_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_l_509_);
v___x_568_ = v_reuseFailAlloc_581_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_isSharedCheck_575_ = !lean_is_exclusive(v_impl_503_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; lean_object* v_unused_577_; lean_object* v_unused_578_; lean_object* v_unused_579_; lean_object* v_unused_580_; 
v_unused_576_ = lean_ctor_get(v_impl_503_, 4);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_impl_503_, 3);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_impl_503_, 2);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_impl_503_, 1);
lean_dec(v_unused_579_);
v_unused_580_ = lean_ctor_get(v_impl_503_, 0);
lean_dec(v_unused_580_);
v___x_570_ = v_impl_503_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_dec(v_impl_503_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 4, v_r_510_);
lean_ctor_set(v___x_570_, 3, v___x_568_);
lean_ctor_set(v___x_570_, 2, v_v_508_);
lean_ctor_set(v___x_570_, 1, v_k_507_);
lean_ctor_set(v___x_570_, 0, v___x_565_);
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_574_, 3, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_574_, 4, v_r_510_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v_size_588_ = lean_ctor_get(v_impl_503_, 0);
lean_inc(v_size_588_);
v___x_589_ = lean_nat_add(v___x_504_, v_size_588_);
lean_dec(v_size_588_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 3, v_impl_503_);
lean_ctor_set(v___x_500_, 0, v___x_589_);
v___x_591_ = v___x_500_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_592_, 3, v_impl_503_);
lean_ctor_set(v_reuseFailAlloc_592_, 4, v_r_498_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
if (lean_obj_tag(v_r_498_) == 0)
{
lean_object* v_l_593_; 
v_l_593_ = lean_ctor_get(v_r_498_, 3);
lean_inc(v_l_593_);
if (lean_obj_tag(v_l_593_) == 0)
{
lean_object* v_r_594_; 
v_r_594_ = lean_ctor_get(v_r_498_, 4);
lean_inc(v_r_594_);
if (lean_obj_tag(v_r_594_) == 0)
{
lean_object* v_size_595_; lean_object* v_k_596_; lean_object* v_v_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_610_; 
v_size_595_ = lean_ctor_get(v_r_498_, 0);
v_k_596_ = lean_ctor_get(v_r_498_, 1);
v_v_597_ = lean_ctor_get(v_r_498_, 2);
v_isSharedCheck_610_ = !lean_is_exclusive(v_r_498_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; lean_object* v_unused_612_; 
v_unused_611_ = lean_ctor_get(v_r_498_, 4);
lean_dec(v_unused_611_);
v_unused_612_ = lean_ctor_get(v_r_498_, 3);
lean_dec(v_unused_612_);
v___x_599_ = v_r_498_;
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_v_597_);
lean_inc(v_k_596_);
lean_inc(v_size_595_);
lean_dec(v_r_498_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_size_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v_size_601_ = lean_ctor_get(v_l_593_, 0);
v___x_602_ = lean_nat_add(v___x_504_, v_size_595_);
lean_dec(v_size_595_);
v___x_603_ = lean_nat_add(v___x_504_, v_size_601_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 4, v_l_593_);
lean_ctor_set(v___x_599_, 3, v_impl_503_);
lean_ctor_set(v___x_599_, 2, v_v_496_);
lean_ctor_set(v___x_599_, 1, v_k_495_);
lean_ctor_set(v___x_599_, 0, v___x_603_);
v___x_605_ = v___x_599_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_impl_503_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_l_593_);
v___x_605_ = v_reuseFailAlloc_609_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_r_594_);
lean_ctor_set(v___x_500_, 3, v___x_605_);
lean_ctor_set(v___x_500_, 2, v_v_597_);
lean_ctor_set(v___x_500_, 1, v_k_596_);
lean_ctor_set(v___x_500_, 0, v___x_602_);
v___x_607_ = v___x_500_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_r_594_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_k_613_; lean_object* v_v_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_637_; 
v_k_613_ = lean_ctor_get(v_r_498_, 1);
v_v_614_ = lean_ctor_get(v_r_498_, 2);
v_isSharedCheck_637_ = !lean_is_exclusive(v_r_498_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; lean_object* v_unused_639_; lean_object* v_unused_640_; 
v_unused_638_ = lean_ctor_get(v_r_498_, 4);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_r_498_, 3);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_r_498_, 0);
lean_dec(v_unused_640_);
v___x_616_ = v_r_498_;
v_isShared_617_ = v_isSharedCheck_637_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_v_614_);
lean_inc(v_k_613_);
lean_dec(v_r_498_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_637_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v_k_618_; lean_object* v_v_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_633_; 
v_k_618_ = lean_ctor_get(v_l_593_, 1);
v_v_619_ = lean_ctor_get(v_l_593_, 2);
v_isSharedCheck_633_ = !lean_is_exclusive(v_l_593_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; lean_object* v_unused_635_; lean_object* v_unused_636_; 
v_unused_634_ = lean_ctor_get(v_l_593_, 4);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_l_593_, 3);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_l_593_, 0);
lean_dec(v_unused_636_);
v___x_621_ = v_l_593_;
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_v_619_);
lean_inc(v_k_618_);
lean_dec(v_l_593_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = lean_unsigned_to_nat(3u);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v_r_594_);
lean_ctor_set(v___x_621_, 3, v_r_594_);
lean_ctor_set(v___x_621_, 2, v_v_496_);
lean_ctor_set(v___x_621_, 1, v_k_495_);
lean_ctor_set(v___x_621_, 0, v___x_504_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_r_594_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_r_594_);
v___x_625_ = v_reuseFailAlloc_632_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 3, v_r_594_);
lean_ctor_set(v___x_616_, 0, v___x_504_);
v___x_627_ = v___x_616_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v_r_594_);
lean_ctor_set(v_reuseFailAlloc_631_, 4, v_r_594_);
v___x_627_ = v_reuseFailAlloc_631_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v___x_627_);
lean_ctor_set(v___x_500_, 3, v___x_625_);
lean_ctor_set(v___x_500_, 2, v_v_619_);
lean_ctor_set(v___x_500_, 1, v_k_618_);
lean_ctor_set(v___x_500_, 0, v___x_623_);
v___x_629_ = v___x_500_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_k_618_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_v_619_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_630_, 4, v___x_627_);
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
}
}
else
{
lean_object* v_r_641_; 
v_r_641_ = lean_ctor_get(v_r_498_, 4);
lean_inc(v_r_641_);
if (lean_obj_tag(v_r_641_) == 0)
{
lean_object* v_k_642_; lean_object* v_v_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_654_; 
v_k_642_ = lean_ctor_get(v_r_498_, 1);
v_v_643_ = lean_ctor_get(v_r_498_, 2);
v_isSharedCheck_654_ = !lean_is_exclusive(v_r_498_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; lean_object* v_unused_656_; lean_object* v_unused_657_; 
v_unused_655_ = lean_ctor_get(v_r_498_, 4);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_r_498_, 3);
lean_dec(v_unused_656_);
v_unused_657_ = lean_ctor_get(v_r_498_, 0);
lean_dec(v_unused_657_);
v___x_645_ = v_r_498_;
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_v_643_);
lean_inc(v_k_642_);
lean_dec(v_r_498_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = lean_unsigned_to_nat(3u);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 4, v_l_593_);
lean_ctor_set(v___x_645_, 2, v_v_496_);
lean_ctor_set(v___x_645_, 1, v_k_495_);
lean_ctor_set(v___x_645_, 0, v___x_504_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_l_593_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v_l_593_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_r_641_);
lean_ctor_set(v___x_500_, 3, v___x_649_);
lean_ctor_set(v___x_500_, 2, v_v_643_);
lean_ctor_set(v___x_500_, 1, v_k_642_);
lean_ctor_set(v___x_500_, 0, v___x_647_);
v___x_651_ = v___x_500_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_652_, 4, v_r_641_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v_size_658_; lean_object* v_k_659_; lean_object* v_v_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_671_; 
v_size_658_ = lean_ctor_get(v_r_498_, 0);
v_k_659_ = lean_ctor_get(v_r_498_, 1);
v_v_660_ = lean_ctor_get(v_r_498_, 2);
v_isSharedCheck_671_ = !lean_is_exclusive(v_r_498_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; lean_object* v_unused_673_; 
v_unused_672_ = lean_ctor_get(v_r_498_, 4);
lean_dec(v_unused_672_);
v_unused_673_ = lean_ctor_get(v_r_498_, 3);
lean_dec(v_unused_673_);
v___x_662_ = v_r_498_;
v_isShared_663_ = v_isSharedCheck_671_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_v_660_);
lean_inc(v_k_659_);
lean_inc(v_size_658_);
lean_dec(v_r_498_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_671_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 3, v_r_641_);
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_size_658_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v_r_641_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v_r_641_);
v___x_665_ = v_reuseFailAlloc_670_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = lean_unsigned_to_nat(2u);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v___x_665_);
lean_ctor_set(v___x_500_, 3, v_r_641_);
lean_ctor_set(v___x_500_, 0, v___x_666_);
v___x_668_ = v___x_500_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v_r_641_);
lean_ctor_set(v_reuseFailAlloc_669_, 4, v___x_665_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
}
else
{
lean_object* v___x_675_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 3, v_r_498_);
lean_ctor_set(v___x_500_, 0, v___x_504_);
v___x_675_ = v___x_500_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_r_498_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v_r_498_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
case 1:
{
lean_del_object(v___x_500_);
lean_dec(v_v_496_);
lean_dec(v_k_495_);
if (lean_obj_tag(v_l_497_) == 0)
{
if (lean_obj_tag(v_r_498_) == 0)
{
lean_object* v_size_677_; lean_object* v_k_678_; lean_object* v_v_679_; lean_object* v_l_680_; lean_object* v_r_681_; lean_object* v_size_682_; lean_object* v_k_683_; lean_object* v_v_684_; lean_object* v_l_685_; lean_object* v_r_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_size_677_ = lean_ctor_get(v_l_497_, 0);
v_k_678_ = lean_ctor_get(v_l_497_, 1);
v_v_679_ = lean_ctor_get(v_l_497_, 2);
v_l_680_ = lean_ctor_get(v_l_497_, 3);
v_r_681_ = lean_ctor_get(v_l_497_, 4);
lean_inc(v_r_681_);
v_size_682_ = lean_ctor_get(v_r_498_, 0);
v_k_683_ = lean_ctor_get(v_r_498_, 1);
v_v_684_ = lean_ctor_get(v_r_498_, 2);
v_l_685_ = lean_ctor_get(v_r_498_, 3);
lean_inc(v_l_685_);
v_r_686_ = lean_ctor_get(v_r_498_, 4);
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_dec_lt(v_size_677_, v_size_682_);
if (v___x_688_ == 0)
{
lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_824_; 
lean_inc(v_l_680_);
lean_inc(v_v_679_);
lean_inc(v_k_678_);
v_isSharedCheck_824_ = !lean_is_exclusive(v_l_497_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; lean_object* v_unused_826_; lean_object* v_unused_827_; lean_object* v_unused_828_; lean_object* v_unused_829_; 
v_unused_825_ = lean_ctor_get(v_l_497_, 4);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_l_497_, 3);
lean_dec(v_unused_826_);
v_unused_827_ = lean_ctor_get(v_l_497_, 2);
lean_dec(v_unused_827_);
v_unused_828_ = lean_ctor_get(v_l_497_, 1);
lean_dec(v_unused_828_);
v_unused_829_ = lean_ctor_get(v_l_497_, 0);
lean_dec(v_unused_829_);
v___x_690_ = v_l_497_;
v_isShared_691_ = v_isSharedCheck_824_;
goto v_resetjp_689_;
}
else
{
lean_dec(v_l_497_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_824_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v_tree_693_; 
v___x_692_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_678_, v_v_679_, v_l_680_, v_r_681_);
v_tree_693_ = lean_ctor_get(v___x_692_, 2);
lean_inc(v_tree_693_);
if (lean_obj_tag(v_tree_693_) == 0)
{
lean_object* v_k_694_; lean_object* v_v_695_; lean_object* v_size_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_k_694_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_k_694_);
v_v_695_ = lean_ctor_get(v___x_692_, 1);
lean_inc(v_v_695_);
lean_dec_ref(v___x_692_);
v_size_696_ = lean_ctor_get(v_tree_693_, 0);
v___x_697_ = lean_unsigned_to_nat(3u);
v___x_698_ = lean_nat_mul(v___x_697_, v_size_696_);
v___x_699_ = lean_nat_dec_lt(v___x_698_, v_size_682_);
lean_dec(v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
lean_dec(v_l_685_);
v___x_700_ = lean_nat_add(v___x_687_, v_size_696_);
v___x_701_ = lean_nat_add(v___x_700_, v_size_682_);
lean_dec(v___x_700_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 4, v_r_498_);
lean_ctor_set(v___x_690_, 3, v_tree_693_);
lean_ctor_set(v___x_690_, 2, v_v_695_);
lean_ctor_set(v___x_690_, 1, v_k_694_);
lean_ctor_set(v___x_690_, 0, v___x_701_);
v___x_703_ = v___x_690_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_k_694_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_v_695_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_tree_693_);
lean_ctor_set(v_reuseFailAlloc_704_, 4, v_r_498_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
else
{
lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_759_; 
lean_inc(v_r_686_);
lean_inc(v_v_684_);
lean_inc(v_k_683_);
lean_inc(v_size_682_);
v_isSharedCheck_759_ = !lean_is_exclusive(v_r_498_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; lean_object* v_unused_761_; lean_object* v_unused_762_; lean_object* v_unused_763_; lean_object* v_unused_764_; 
v_unused_760_ = lean_ctor_get(v_r_498_, 4);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_r_498_, 3);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_r_498_, 2);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_r_498_, 1);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_r_498_, 0);
lean_dec(v_unused_764_);
v___x_706_ = v_r_498_;
v_isShared_707_ = v_isSharedCheck_759_;
goto v_resetjp_705_;
}
else
{
lean_dec(v_r_498_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_759_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_size_708_; lean_object* v_k_709_; lean_object* v_v_710_; lean_object* v_l_711_; lean_object* v_r_712_; lean_object* v_size_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v_size_708_ = lean_ctor_get(v_l_685_, 0);
v_k_709_ = lean_ctor_get(v_l_685_, 1);
v_v_710_ = lean_ctor_get(v_l_685_, 2);
v_l_711_ = lean_ctor_get(v_l_685_, 3);
v_r_712_ = lean_ctor_get(v_l_685_, 4);
v_size_713_ = lean_ctor_get(v_r_686_, 0);
v___x_714_ = lean_unsigned_to_nat(2u);
v___x_715_ = lean_nat_mul(v___x_714_, v_size_713_);
v___x_716_ = lean_nat_dec_lt(v_size_708_, v___x_715_);
lean_dec(v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_744_; 
lean_inc(v_r_712_);
lean_inc(v_l_711_);
lean_inc(v_v_710_);
lean_inc(v_k_709_);
v_isSharedCheck_744_ = !lean_is_exclusive(v_l_685_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; lean_object* v_unused_746_; lean_object* v_unused_747_; lean_object* v_unused_748_; lean_object* v_unused_749_; 
v_unused_745_ = lean_ctor_get(v_l_685_, 4);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v_l_685_, 3);
lean_dec(v_unused_746_);
v_unused_747_ = lean_ctor_get(v_l_685_, 2);
lean_dec(v_unused_747_);
v_unused_748_ = lean_ctor_get(v_l_685_, 1);
lean_dec(v_unused_748_);
v_unused_749_ = lean_ctor_get(v_l_685_, 0);
lean_dec(v_unused_749_);
v___x_718_ = v_l_685_;
v_isShared_719_ = v_isSharedCheck_744_;
goto v_resetjp_717_;
}
else
{
lean_dec(v_l_685_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_744_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_734_; 
v___x_720_ = lean_nat_add(v___x_687_, v_size_696_);
v___x_721_ = lean_nat_add(v___x_720_, v_size_682_);
lean_dec(v_size_682_);
if (lean_obj_tag(v_l_711_) == 0)
{
lean_object* v_size_742_; 
v_size_742_ = lean_ctor_get(v_l_711_, 0);
lean_inc(v_size_742_);
v___y_734_ = v_size_742_;
goto v___jp_733_;
}
else
{
lean_object* v___x_743_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___y_734_ = v___x_743_;
goto v___jp_733_;
}
v___jp_722_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = lean_nat_add(v___y_723_, v___y_725_);
lean_dec(v___y_725_);
lean_dec(v___y_723_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 4, v_r_686_);
lean_ctor_set(v___x_718_, 3, v_r_712_);
lean_ctor_set(v___x_718_, 2, v_v_684_);
lean_ctor_set(v___x_718_, 1, v_k_683_);
lean_ctor_set(v___x_718_, 0, v___x_726_);
v___x_728_ = v___x_718_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_k_683_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_v_684_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v_r_712_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v_r_686_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 4, v___x_728_);
lean_ctor_set(v___x_706_, 3, v___y_724_);
lean_ctor_set(v___x_706_, 2, v_v_710_);
lean_ctor_set(v___x_706_, 1, v_k_709_);
lean_ctor_set(v___x_706_, 0, v___x_721_);
v___x_730_ = v___x_706_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_k_709_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_v_710_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v___y_724_);
lean_ctor_set(v_reuseFailAlloc_731_, 4, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
v___jp_733_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = lean_nat_add(v___x_720_, v___y_734_);
lean_dec(v___y_734_);
lean_dec(v___x_720_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 4, v_l_711_);
lean_ctor_set(v___x_690_, 3, v_tree_693_);
lean_ctor_set(v___x_690_, 2, v_v_695_);
lean_ctor_set(v___x_690_, 1, v_k_694_);
lean_ctor_set(v___x_690_, 0, v___x_735_);
v___x_737_ = v___x_690_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_k_694_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v_v_695_);
lean_ctor_set(v_reuseFailAlloc_741_, 3, v_tree_693_);
lean_ctor_set(v_reuseFailAlloc_741_, 4, v_l_711_);
v___x_737_ = v_reuseFailAlloc_741_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; 
v___x_738_ = lean_nat_add(v___x_687_, v_size_713_);
if (lean_obj_tag(v_r_712_) == 0)
{
lean_object* v_size_739_; 
v_size_739_ = lean_ctor_get(v_r_712_, 0);
lean_inc(v_size_739_);
v___y_723_ = v___x_738_;
v___y_724_ = v___x_737_;
v___y_725_ = v_size_739_;
goto v___jp_722_;
}
else
{
lean_object* v___x_740_; 
v___x_740_ = lean_unsigned_to_nat(0u);
v___y_723_ = v___x_738_;
v___y_724_ = v___x_737_;
v___y_725_ = v___x_740_;
goto v___jp_722_;
}
}
}
}
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_750_ = lean_nat_add(v___x_687_, v_size_696_);
v___x_751_ = lean_nat_add(v___x_750_, v_size_682_);
lean_dec(v_size_682_);
v___x_752_ = lean_nat_add(v___x_750_, v_size_708_);
lean_dec(v___x_750_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 4, v_l_685_);
lean_ctor_set(v___x_706_, 3, v_tree_693_);
lean_ctor_set(v___x_706_, 2, v_v_695_);
lean_ctor_set(v___x_706_, 1, v_k_694_);
lean_ctor_set(v___x_706_, 0, v___x_752_);
v___x_754_ = v___x_706_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_k_694_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_v_695_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_tree_693_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_l_685_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 4, v_r_686_);
lean_ctor_set(v___x_690_, 3, v___x_754_);
lean_ctor_set(v___x_690_, 2, v_v_684_);
lean_ctor_set(v___x_690_, 1, v_k_683_);
lean_ctor_set(v___x_690_, 0, v___x_751_);
v___x_756_ = v___x_690_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_k_683_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_v_684_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v_r_686_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
else
{
lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_818_; 
lean_inc(v_r_686_);
lean_inc(v_v_684_);
lean_inc(v_k_683_);
lean_inc(v_size_682_);
v_isSharedCheck_818_ = !lean_is_exclusive(v_r_498_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; lean_object* v_unused_820_; lean_object* v_unused_821_; lean_object* v_unused_822_; lean_object* v_unused_823_; 
v_unused_819_ = lean_ctor_get(v_r_498_, 4);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_r_498_, 3);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_r_498_, 2);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_r_498_, 1);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_r_498_, 0);
lean_dec(v_unused_823_);
v___x_766_ = v_r_498_;
v_isShared_767_ = v_isSharedCheck_818_;
goto v_resetjp_765_;
}
else
{
lean_dec(v_r_498_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_818_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
if (lean_obj_tag(v_l_685_) == 0)
{
if (lean_obj_tag(v_r_686_) == 0)
{
lean_object* v_k_768_; lean_object* v_v_769_; lean_object* v_size_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v_k_768_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_k_768_);
v_v_769_ = lean_ctor_get(v___x_692_, 1);
lean_inc(v_v_769_);
lean_dec_ref(v___x_692_);
v_size_770_ = lean_ctor_get(v_l_685_, 0);
v___x_771_ = lean_nat_add(v___x_687_, v_size_682_);
lean_dec(v_size_682_);
v___x_772_ = lean_nat_add(v___x_687_, v_size_770_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 4, v_l_685_);
lean_ctor_set(v___x_766_, 3, v_tree_693_);
lean_ctor_set(v___x_766_, 2, v_v_769_);
lean_ctor_set(v___x_766_, 1, v_k_768_);
lean_ctor_set(v___x_766_, 0, v___x_772_);
v___x_774_ = v___x_766_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_k_768_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_v_769_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v_tree_693_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v_l_685_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 4, v_r_686_);
lean_ctor_set(v___x_690_, 3, v___x_774_);
lean_ctor_set(v___x_690_, 2, v_v_684_);
lean_ctor_set(v___x_690_, 1, v_k_683_);
lean_ctor_set(v___x_690_, 0, v___x_771_);
v___x_776_ = v___x_690_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_k_683_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_v_684_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_r_686_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
else
{
lean_object* v_k_779_; lean_object* v_v_780_; lean_object* v_k_781_; lean_object* v_v_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_size_682_);
v_k_779_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_k_779_);
v_v_780_ = lean_ctor_get(v___x_692_, 1);
lean_inc(v_v_780_);
lean_dec_ref(v___x_692_);
v_k_781_ = lean_ctor_get(v_l_685_, 1);
v_v_782_ = lean_ctor_get(v_l_685_, 2);
v_isSharedCheck_796_ = !lean_is_exclusive(v_l_685_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; lean_object* v_unused_798_; lean_object* v_unused_799_; 
v_unused_797_ = lean_ctor_get(v_l_685_, 4);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_l_685_, 3);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_l_685_, 0);
lean_dec(v_unused_799_);
v___x_784_ = v_l_685_;
v_isShared_785_ = v_isSharedCheck_796_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_v_782_);
lean_inc(v_k_781_);
lean_dec(v_l_685_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_796_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_786_ = lean_unsigned_to_nat(3u);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 4, v_r_686_);
lean_ctor_set(v___x_784_, 3, v_r_686_);
lean_ctor_set(v___x_784_, 2, v_v_780_);
lean_ctor_set(v___x_784_, 1, v_k_779_);
lean_ctor_set(v___x_784_, 0, v___x_687_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_k_779_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_v_780_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_r_686_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_r_686_);
v___x_788_ = v_reuseFailAlloc_795_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 3, v_r_686_);
lean_ctor_set(v___x_766_, 0, v___x_687_);
v___x_790_ = v___x_766_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_k_683_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_v_684_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_r_686_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_r_686_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 4, v___x_790_);
lean_ctor_set(v___x_690_, 3, v___x_788_);
lean_ctor_set(v___x_690_, 2, v_v_782_);
lean_ctor_set(v___x_690_, 1, v_k_781_);
lean_ctor_set(v___x_690_, 0, v___x_786_);
v___x_792_ = v___x_690_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_k_781_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_v_782_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_686_) == 0)
{
lean_object* v_k_800_; lean_object* v_v_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec(v_size_682_);
v_k_800_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_k_800_);
v_v_801_ = lean_ctor_get(v___x_692_, 1);
lean_inc(v_v_801_);
lean_dec_ref(v___x_692_);
v___x_802_ = lean_unsigned_to_nat(3u);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 4, v_l_685_);
lean_ctor_set(v___x_766_, 2, v_v_801_);
lean_ctor_set(v___x_766_, 1, v_k_800_);
lean_ctor_set(v___x_766_, 0, v___x_687_);
v___x_804_ = v___x_766_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_k_800_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_v_801_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v_l_685_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v_l_685_);
v___x_804_ = v_reuseFailAlloc_808_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_806_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 4, v_r_686_);
lean_ctor_set(v___x_690_, 3, v___x_804_);
lean_ctor_set(v___x_690_, 2, v_v_684_);
lean_ctor_set(v___x_690_, 1, v_k_683_);
lean_ctor_set(v___x_690_, 0, v___x_802_);
v___x_806_ = v___x_690_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_k_683_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_v_684_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v_r_686_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
else
{
lean_object* v_k_809_; lean_object* v_v_810_; lean_object* v___x_812_; 
v_k_809_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_k_809_);
v_v_810_ = lean_ctor_get(v___x_692_, 1);
lean_inc(v_v_810_);
lean_dec_ref(v___x_692_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 3, v_r_686_);
v___x_812_ = v___x_766_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_size_682_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_k_683_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_v_684_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v_r_686_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v_r_686_);
v___x_812_ = v_reuseFailAlloc_817_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_unsigned_to_nat(2u);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 4, v___x_812_);
lean_ctor_set(v___x_690_, 3, v_r_686_);
lean_ctor_set(v___x_690_, 2, v_v_810_);
lean_ctor_set(v___x_690_, 1, v_k_809_);
lean_ctor_set(v___x_690_, 0, v___x_813_);
v___x_815_ = v___x_690_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_k_809_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_v_810_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_r_686_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v___x_812_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
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
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_982_; 
lean_inc(v_r_686_);
lean_inc(v_v_684_);
lean_inc(v_k_683_);
v_isSharedCheck_982_ = !lean_is_exclusive(v_r_498_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; lean_object* v_unused_984_; lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; 
v_unused_983_ = lean_ctor_get(v_r_498_, 4);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_r_498_, 3);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_r_498_, 2);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_r_498_, 1);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_r_498_, 0);
lean_dec(v_unused_987_);
v___x_831_ = v_r_498_;
v_isShared_832_ = v_isSharedCheck_982_;
goto v_resetjp_830_;
}
else
{
lean_dec(v_r_498_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_982_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v_tree_834_; 
v___x_833_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_683_, v_v_684_, v_l_685_, v_r_686_);
v_tree_834_ = lean_ctor_get(v___x_833_, 2);
lean_inc(v_tree_834_);
if (lean_obj_tag(v_tree_834_) == 0)
{
lean_object* v_k_835_; lean_object* v_v_836_; lean_object* v_size_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_k_835_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_k_835_);
v_v_836_ = lean_ctor_get(v___x_833_, 1);
lean_inc(v_v_836_);
lean_dec_ref(v___x_833_);
v_size_837_ = lean_ctor_get(v_tree_834_, 0);
v___x_838_ = lean_unsigned_to_nat(3u);
v___x_839_ = lean_nat_mul(v___x_838_, v_size_837_);
v___x_840_ = lean_nat_dec_lt(v___x_839_, v_size_677_);
lean_dec(v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
lean_dec(v_r_681_);
v___x_841_ = lean_nat_add(v___x_687_, v_size_677_);
v___x_842_ = lean_nat_add(v___x_841_, v_size_837_);
lean_dec(v___x_841_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 4, v_tree_834_);
lean_ctor_set(v___x_831_, 3, v_l_497_);
lean_ctor_set(v___x_831_, 2, v_v_836_);
lean_ctor_set(v___x_831_, 1, v_k_835_);
lean_ctor_set(v___x_831_, 0, v___x_842_);
v___x_844_ = v___x_831_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_k_835_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_v_836_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_l_497_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v_tree_834_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
else
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_911_; 
lean_inc(v_l_680_);
lean_inc(v_v_679_);
lean_inc(v_k_678_);
lean_inc(v_size_677_);
v_isSharedCheck_911_ = !lean_is_exclusive(v_l_497_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; lean_object* v_unused_913_; lean_object* v_unused_914_; lean_object* v_unused_915_; lean_object* v_unused_916_; 
v_unused_912_ = lean_ctor_get(v_l_497_, 4);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_l_497_, 3);
lean_dec(v_unused_913_);
v_unused_914_ = lean_ctor_get(v_l_497_, 2);
lean_dec(v_unused_914_);
v_unused_915_ = lean_ctor_get(v_l_497_, 1);
lean_dec(v_unused_915_);
v_unused_916_ = lean_ctor_get(v_l_497_, 0);
lean_dec(v_unused_916_);
v___x_847_ = v_l_497_;
v_isShared_848_ = v_isSharedCheck_911_;
goto v_resetjp_846_;
}
else
{
lean_dec(v_l_497_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_911_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_size_849_; lean_object* v_size_850_; lean_object* v_k_851_; lean_object* v_v_852_; lean_object* v_l_853_; lean_object* v_r_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_size_849_ = lean_ctor_get(v_l_680_, 0);
v_size_850_ = lean_ctor_get(v_r_681_, 0);
v_k_851_ = lean_ctor_get(v_r_681_, 1);
v_v_852_ = lean_ctor_get(v_r_681_, 2);
v_l_853_ = lean_ctor_get(v_r_681_, 3);
v_r_854_ = lean_ctor_get(v_r_681_, 4);
v___x_855_ = lean_unsigned_to_nat(2u);
v___x_856_ = lean_nat_mul(v___x_855_, v_size_849_);
v___x_857_ = lean_nat_dec_lt(v_size_850_, v___x_856_);
lean_dec(v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_895_; 
lean_inc(v_r_854_);
lean_inc(v_l_853_);
lean_inc(v_v_852_);
lean_inc(v_k_851_);
lean_del_object(v___x_847_);
v_isSharedCheck_895_ = !lean_is_exclusive(v_r_681_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; lean_object* v_unused_897_; lean_object* v_unused_898_; lean_object* v_unused_899_; lean_object* v_unused_900_; 
v_unused_896_ = lean_ctor_get(v_r_681_, 4);
lean_dec(v_unused_896_);
v_unused_897_ = lean_ctor_get(v_r_681_, 3);
lean_dec(v_unused_897_);
v_unused_898_ = lean_ctor_get(v_r_681_, 2);
lean_dec(v_unused_898_);
v_unused_899_ = lean_ctor_get(v_r_681_, 1);
lean_dec(v_unused_899_);
v_unused_900_ = lean_ctor_get(v_r_681_, 0);
lean_dec(v_unused_900_);
v___x_859_ = v_r_681_;
v_isShared_860_ = v_isSharedCheck_895_;
goto v_resetjp_858_;
}
else
{
lean_dec(v_r_681_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_895_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___x_883_; lean_object* v___y_885_; 
v___x_861_ = lean_nat_add(v___x_687_, v_size_677_);
lean_dec(v_size_677_);
v___x_862_ = lean_nat_add(v___x_861_, v_size_837_);
lean_dec(v___x_861_);
v___x_883_ = lean_nat_add(v___x_687_, v_size_849_);
if (lean_obj_tag(v_l_853_) == 0)
{
lean_object* v_size_893_; 
v_size_893_ = lean_ctor_get(v_l_853_, 0);
lean_inc(v_size_893_);
v___y_885_ = v_size_893_;
goto v___jp_884_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v___y_885_ = v___x_894_;
goto v___jp_884_;
}
v___jp_863_:
{
lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_867_ = lean_nat_add(v___y_864_, v___y_866_);
lean_dec(v___y_866_);
lean_dec(v___y_864_);
lean_inc_ref(v_tree_834_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 4, v_tree_834_);
lean_ctor_set(v___x_859_, 3, v_r_854_);
lean_ctor_set(v___x_859_, 2, v_v_836_);
lean_ctor_set(v___x_859_, 1, v_k_835_);
lean_ctor_set(v___x_859_, 0, v___x_867_);
v___x_869_ = v___x_859_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_k_835_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_v_836_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v_r_854_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v_tree_834_);
v___x_869_ = v_reuseFailAlloc_882_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_isSharedCheck_876_ = !lean_is_exclusive(v_tree_834_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; lean_object* v_unused_878_; lean_object* v_unused_879_; lean_object* v_unused_880_; lean_object* v_unused_881_; 
v_unused_877_ = lean_ctor_get(v_tree_834_, 4);
lean_dec(v_unused_877_);
v_unused_878_ = lean_ctor_get(v_tree_834_, 3);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v_tree_834_, 2);
lean_dec(v_unused_879_);
v_unused_880_ = lean_ctor_get(v_tree_834_, 1);
lean_dec(v_unused_880_);
v_unused_881_ = lean_ctor_get(v_tree_834_, 0);
lean_dec(v_unused_881_);
v___x_871_ = v_tree_834_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_dec(v_tree_834_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 4, v___x_869_);
lean_ctor_set(v___x_871_, 3, v___y_865_);
lean_ctor_set(v___x_871_, 2, v_v_852_);
lean_ctor_set(v___x_871_, 1, v_k_851_);
lean_ctor_set(v___x_871_, 0, v___x_862_);
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_k_851_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_v_852_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v___y_865_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v___x_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
v___jp_884_:
{
lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_886_ = lean_nat_add(v___x_883_, v___y_885_);
lean_dec(v___y_885_);
lean_dec(v___x_883_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 4, v_l_853_);
lean_ctor_set(v___x_831_, 3, v_l_680_);
lean_ctor_set(v___x_831_, 2, v_v_679_);
lean_ctor_set(v___x_831_, 1, v_k_678_);
lean_ctor_set(v___x_831_, 0, v___x_886_);
v___x_888_ = v___x_831_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_k_678_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_v_679_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v_l_853_);
v___x_888_ = v_reuseFailAlloc_892_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; 
v___x_889_ = lean_nat_add(v___x_687_, v_size_837_);
if (lean_obj_tag(v_r_854_) == 0)
{
lean_object* v_size_890_; 
v_size_890_ = lean_ctor_get(v_r_854_, 0);
lean_inc(v_size_890_);
v___y_864_ = v___x_889_;
v___y_865_ = v___x_888_;
v___y_866_ = v_size_890_;
goto v___jp_863_;
}
else
{
lean_object* v___x_891_; 
v___x_891_ = lean_unsigned_to_nat(0u);
v___y_864_ = v___x_889_;
v___y_865_ = v___x_888_;
v___y_866_ = v___x_891_;
goto v___jp_863_;
}
}
}
}
}
else
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_901_ = lean_nat_add(v___x_687_, v_size_677_);
lean_dec(v_size_677_);
v___x_902_ = lean_nat_add(v___x_901_, v_size_837_);
lean_dec(v___x_901_);
v___x_903_ = lean_nat_add(v___x_687_, v_size_837_);
v___x_904_ = lean_nat_add(v___x_903_, v_size_850_);
lean_dec(v___x_903_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 4, v_tree_834_);
lean_ctor_set(v___x_831_, 3, v_r_681_);
lean_ctor_set(v___x_831_, 2, v_v_836_);
lean_ctor_set(v___x_831_, 1, v_k_835_);
lean_ctor_set(v___x_831_, 0, v___x_904_);
v___x_906_ = v___x_831_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_k_835_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_v_836_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_r_681_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_tree_834_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 4, v___x_906_);
lean_ctor_set(v___x_847_, 0, v___x_902_);
v___x_908_ = v___x_847_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_k_678_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_v_679_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_909_, 4, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_680_) == 0)
{
lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_940_; 
lean_inc_ref(v_l_680_);
lean_inc(v_v_679_);
lean_inc(v_k_678_);
lean_inc(v_size_677_);
v_isSharedCheck_940_ = !lean_is_exclusive(v_l_497_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; lean_object* v_unused_942_; lean_object* v_unused_943_; lean_object* v_unused_944_; lean_object* v_unused_945_; 
v_unused_941_ = lean_ctor_get(v_l_497_, 4);
lean_dec(v_unused_941_);
v_unused_942_ = lean_ctor_get(v_l_497_, 3);
lean_dec(v_unused_942_);
v_unused_943_ = lean_ctor_get(v_l_497_, 2);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_l_497_, 1);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_l_497_, 0);
lean_dec(v_unused_945_);
v___x_918_ = v_l_497_;
v_isShared_919_ = v_isSharedCheck_940_;
goto v_resetjp_917_;
}
else
{
lean_dec(v_l_497_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_940_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
if (lean_obj_tag(v_r_681_) == 0)
{
lean_object* v_k_920_; lean_object* v_v_921_; lean_object* v_size_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v_k_920_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_k_920_);
v_v_921_ = lean_ctor_get(v___x_833_, 1);
lean_inc(v_v_921_);
lean_dec_ref(v___x_833_);
v_size_922_ = lean_ctor_get(v_r_681_, 0);
v___x_923_ = lean_nat_add(v___x_687_, v_size_677_);
lean_dec(v_size_677_);
v___x_924_ = lean_nat_add(v___x_687_, v_size_922_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 4, v_tree_834_);
lean_ctor_set(v___x_831_, 3, v_r_681_);
lean_ctor_set(v___x_831_, 2, v_v_921_);
lean_ctor_set(v___x_831_, 1, v_k_920_);
lean_ctor_set(v___x_831_, 0, v___x_924_);
v___x_926_ = v___x_831_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_k_920_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_v_921_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v_r_681_);
lean_ctor_set(v_reuseFailAlloc_930_, 4, v_tree_834_);
v___x_926_ = v_reuseFailAlloc_930_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_928_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 4, v___x_926_);
lean_ctor_set(v___x_918_, 0, v___x_923_);
v___x_928_ = v___x_918_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_k_678_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_v_679_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
else
{
lean_object* v_k_931_; lean_object* v_v_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
lean_dec(v_size_677_);
v_k_931_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_k_931_);
v_v_932_ = lean_ctor_get(v___x_833_, 1);
lean_inc(v_v_932_);
lean_dec_ref(v___x_833_);
v___x_933_ = lean_unsigned_to_nat(3u);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 4, v_r_681_);
lean_ctor_set(v___x_831_, 3, v_r_681_);
lean_ctor_set(v___x_831_, 2, v_v_932_);
lean_ctor_set(v___x_831_, 1, v_k_931_);
lean_ctor_set(v___x_831_, 0, v___x_687_);
v___x_935_ = v___x_831_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_k_931_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_v_932_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v_r_681_);
lean_ctor_set(v_reuseFailAlloc_939_, 4, v_r_681_);
v___x_935_ = v_reuseFailAlloc_939_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_937_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 4, v___x_935_);
lean_ctor_set(v___x_918_, 0, v___x_933_);
v___x_937_ = v___x_918_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_k_678_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_v_679_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_938_, 4, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_681_) == 0)
{
lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_970_; 
lean_inc(v_l_680_);
lean_inc(v_v_679_);
lean_inc(v_k_678_);
v_isSharedCheck_970_ = !lean_is_exclusive(v_l_497_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; lean_object* v_unused_972_; lean_object* v_unused_973_; lean_object* v_unused_974_; lean_object* v_unused_975_; 
v_unused_971_ = lean_ctor_get(v_l_497_, 4);
lean_dec(v_unused_971_);
v_unused_972_ = lean_ctor_get(v_l_497_, 3);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_l_497_, 2);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_l_497_, 1);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_l_497_, 0);
lean_dec(v_unused_975_);
v___x_947_ = v_l_497_;
v_isShared_948_ = v_isSharedCheck_970_;
goto v_resetjp_946_;
}
else
{
lean_dec(v_l_497_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_970_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_k_949_; lean_object* v_v_950_; lean_object* v_k_951_; lean_object* v_v_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_966_; 
v_k_949_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_k_949_);
v_v_950_ = lean_ctor_get(v___x_833_, 1);
lean_inc(v_v_950_);
lean_dec_ref(v___x_833_);
v_k_951_ = lean_ctor_get(v_r_681_, 1);
v_v_952_ = lean_ctor_get(v_r_681_, 2);
v_isSharedCheck_966_ = !lean_is_exclusive(v_r_681_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; lean_object* v_unused_968_; lean_object* v_unused_969_; 
v_unused_967_ = lean_ctor_get(v_r_681_, 4);
lean_dec(v_unused_967_);
v_unused_968_ = lean_ctor_get(v_r_681_, 3);
lean_dec(v_unused_968_);
v_unused_969_ = lean_ctor_get(v_r_681_, 0);
lean_dec(v_unused_969_);
v___x_954_ = v_r_681_;
v_isShared_955_ = v_isSharedCheck_966_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_v_952_);
lean_inc(v_k_951_);
lean_dec(v_r_681_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_966_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = lean_unsigned_to_nat(3u);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 4, v_l_680_);
lean_ctor_set(v___x_954_, 3, v_l_680_);
lean_ctor_set(v___x_954_, 2, v_v_679_);
lean_ctor_set(v___x_954_, 1, v_k_678_);
lean_ctor_set(v___x_954_, 0, v___x_687_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_k_678_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_v_679_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_l_680_);
v___x_958_ = v_reuseFailAlloc_965_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_960_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 4, v_l_680_);
lean_ctor_set(v___x_831_, 3, v_l_680_);
lean_ctor_set(v___x_831_, 2, v_v_950_);
lean_ctor_set(v___x_831_, 1, v_k_949_);
lean_ctor_set(v___x_831_, 0, v___x_687_);
v___x_960_ = v___x_831_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_k_949_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_v_950_);
lean_ctor_set(v_reuseFailAlloc_964_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_964_, 4, v_l_680_);
v___x_960_ = v_reuseFailAlloc_964_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 4, v___x_960_);
lean_ctor_set(v___x_947_, 3, v___x_958_);
lean_ctor_set(v___x_947_, 2, v_v_952_);
lean_ctor_set(v___x_947_, 1, v_k_951_);
lean_ctor_set(v___x_947_, 0, v___x_956_);
v___x_962_ = v___x_947_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_k_951_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_v_952_);
lean_ctor_set(v_reuseFailAlloc_963_, 3, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_963_, 4, v___x_960_);
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
}
}
else
{
lean_object* v_k_976_; lean_object* v_v_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
v_k_976_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_k_976_);
v_v_977_ = lean_ctor_get(v___x_833_, 1);
lean_inc(v_v_977_);
lean_dec_ref(v___x_833_);
v___x_978_ = lean_unsigned_to_nat(2u);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 4, v_r_681_);
lean_ctor_set(v___x_831_, 3, v_l_497_);
lean_ctor_set(v___x_831_, 2, v_v_977_);
lean_ctor_set(v___x_831_, 1, v_k_976_);
lean_ctor_set(v___x_831_, 0, v___x_978_);
v___x_980_ = v___x_831_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_k_976_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_v_977_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_l_497_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_r_681_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
}
}
else
{
return v_l_497_;
}
}
else
{
return v_r_498_;
}
}
default: 
{
lean_object* v_impl_988_; lean_object* v___x_989_; 
v_impl_988_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_493_, v_r_498_);
v___x_989_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_988_) == 0)
{
if (lean_obj_tag(v_l_497_) == 0)
{
lean_object* v_size_990_; lean_object* v_size_991_; lean_object* v_k_992_; lean_object* v_v_993_; lean_object* v_l_994_; lean_object* v_r_995_; lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v_size_990_ = lean_ctor_get(v_impl_988_, 0);
lean_inc(v_size_990_);
v_size_991_ = lean_ctor_get(v_l_497_, 0);
v_k_992_ = lean_ctor_get(v_l_497_, 1);
v_v_993_ = lean_ctor_get(v_l_497_, 2);
v_l_994_ = lean_ctor_get(v_l_497_, 3);
v_r_995_ = lean_ctor_get(v_l_497_, 4);
lean_inc(v_r_995_);
v___x_996_ = lean_unsigned_to_nat(3u);
v___x_997_ = lean_nat_mul(v___x_996_, v_size_990_);
v___x_998_ = lean_nat_dec_lt(v___x_997_, v_size_991_);
lean_dec(v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
lean_dec(v_r_995_);
v___x_999_ = lean_nat_add(v___x_989_, v_size_991_);
v___x_1000_ = lean_nat_add(v___x_999_, v_size_990_);
lean_dec(v_size_990_);
lean_dec(v___x_999_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_impl_988_);
lean_ctor_set(v___x_500_, 0, v___x_1000_);
v___x_1002_ = v___x_500_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_1003_, 3, v_l_497_);
lean_ctor_set(v_reuseFailAlloc_1003_, 4, v_impl_988_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1069_; 
lean_inc(v_l_994_);
lean_inc(v_v_993_);
lean_inc(v_k_992_);
lean_inc(v_size_991_);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_l_497_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; lean_object* v_unused_1071_; lean_object* v_unused_1072_; lean_object* v_unused_1073_; lean_object* v_unused_1074_; 
v_unused_1070_ = lean_ctor_get(v_l_497_, 4);
lean_dec(v_unused_1070_);
v_unused_1071_ = lean_ctor_get(v_l_497_, 3);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_l_497_, 2);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_l_497_, 1);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v_l_497_, 0);
lean_dec(v_unused_1074_);
v___x_1005_ = v_l_497_;
v_isShared_1006_ = v_isSharedCheck_1069_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v_l_497_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1069_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_size_1007_; lean_object* v_size_1008_; lean_object* v_k_1009_; lean_object* v_v_1010_; lean_object* v_l_1011_; lean_object* v_r_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v_size_1007_ = lean_ctor_get(v_l_994_, 0);
v_size_1008_ = lean_ctor_get(v_r_995_, 0);
v_k_1009_ = lean_ctor_get(v_r_995_, 1);
v_v_1010_ = lean_ctor_get(v_r_995_, 2);
v_l_1011_ = lean_ctor_get(v_r_995_, 3);
v_r_1012_ = lean_ctor_get(v_r_995_, 4);
v___x_1013_ = lean_unsigned_to_nat(2u);
v___x_1014_ = lean_nat_mul(v___x_1013_, v_size_1007_);
v___x_1015_ = lean_nat_dec_lt(v_size_1008_, v___x_1014_);
lean_dec(v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1044_; 
lean_inc(v_r_1012_);
lean_inc(v_l_1011_);
lean_inc(v_v_1010_);
lean_inc(v_k_1009_);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_r_995_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; lean_object* v_unused_1046_; lean_object* v_unused_1047_; lean_object* v_unused_1048_; lean_object* v_unused_1049_; 
v_unused_1045_ = lean_ctor_get(v_r_995_, 4);
lean_dec(v_unused_1045_);
v_unused_1046_ = lean_ctor_get(v_r_995_, 3);
lean_dec(v_unused_1046_);
v_unused_1047_ = lean_ctor_get(v_r_995_, 2);
lean_dec(v_unused_1047_);
v_unused_1048_ = lean_ctor_get(v_r_995_, 1);
lean_dec(v_unused_1048_);
v_unused_1049_ = lean_ctor_get(v_r_995_, 0);
lean_dec(v_unused_1049_);
v___x_1017_ = v_r_995_;
v_isShared_1018_ = v_isSharedCheck_1044_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v_r_995_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1044_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___x_1032_; lean_object* v___y_1034_; 
v___x_1019_ = lean_nat_add(v___x_989_, v_size_991_);
lean_dec(v_size_991_);
v___x_1020_ = lean_nat_add(v___x_1019_, v_size_990_);
lean_dec(v___x_1019_);
v___x_1032_ = lean_nat_add(v___x_989_, v_size_1007_);
if (lean_obj_tag(v_l_1011_) == 0)
{
lean_object* v_size_1042_; 
v_size_1042_ = lean_ctor_get(v_l_1011_, 0);
lean_inc(v_size_1042_);
v___y_1034_ = v_size_1042_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_unsigned_to_nat(0u);
v___y_1034_ = v___x_1043_;
goto v___jp_1033_;
}
v___jp_1021_:
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1025_ = lean_nat_add(v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec(v___y_1023_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 4, v_impl_988_);
lean_ctor_set(v___x_1017_, 3, v_r_1012_);
lean_ctor_set(v___x_1017_, 2, v_v_496_);
lean_ctor_set(v___x_1017_, 1, v_k_495_);
lean_ctor_set(v___x_1017_, 0, v___x_1025_);
v___x_1027_ = v___x_1017_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v_r_1012_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v_impl_988_);
v___x_1027_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1029_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 4, v___x_1027_);
lean_ctor_set(v___x_1005_, 3, v___y_1022_);
lean_ctor_set(v___x_1005_, 2, v_v_1010_);
lean_ctor_set(v___x_1005_, 1, v_k_1009_);
lean_ctor_set(v___x_1005_, 0, v___x_1020_);
v___x_1029_ = v___x_1005_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_k_1009_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_v_1010_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v___y_1022_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
v___jp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_nat_add(v___x_1032_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec(v___x_1032_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_l_1011_);
lean_ctor_set(v___x_500_, 3, v_l_994_);
lean_ctor_set(v___x_500_, 2, v_v_993_);
lean_ctor_set(v___x_500_, 1, v_k_992_);
lean_ctor_set(v___x_500_, 0, v___x_1035_);
v___x_1037_ = v___x_500_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_k_992_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_v_993_);
lean_ctor_set(v_reuseFailAlloc_1041_, 3, v_l_994_);
lean_ctor_set(v_reuseFailAlloc_1041_, 4, v_l_1011_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_nat_add(v___x_989_, v_size_990_);
lean_dec(v_size_990_);
if (lean_obj_tag(v_r_1012_) == 0)
{
lean_object* v_size_1039_; 
v_size_1039_ = lean_ctor_get(v_r_1012_, 0);
lean_inc(v_size_1039_);
v___y_1022_ = v___x_1037_;
v___y_1023_ = v___x_1038_;
v___y_1024_ = v_size_1039_;
goto v___jp_1021_;
}
else
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_unsigned_to_nat(0u);
v___y_1022_ = v___x_1037_;
v___y_1023_ = v___x_1038_;
v___y_1024_ = v___x_1040_;
goto v___jp_1021_;
}
}
}
}
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_del_object(v___x_500_);
v___x_1050_ = lean_nat_add(v___x_989_, v_size_991_);
lean_dec(v_size_991_);
v___x_1051_ = lean_nat_add(v___x_1050_, v_size_990_);
lean_dec(v___x_1050_);
v___x_1052_ = lean_nat_add(v___x_989_, v_size_990_);
lean_dec(v_size_990_);
v___x_1053_ = lean_nat_add(v___x_1052_, v_size_1008_);
lean_dec(v___x_1052_);
lean_inc_ref(v_impl_988_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 4, v_impl_988_);
lean_ctor_set(v___x_1005_, 3, v_r_995_);
lean_ctor_set(v___x_1005_, 2, v_v_496_);
lean_ctor_set(v___x_1005_, 1, v_k_495_);
lean_ctor_set(v___x_1005_, 0, v___x_1053_);
v___x_1055_ = v___x_1005_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v_r_995_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_impl_988_);
v___x_1055_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_isSharedCheck_1062_ = !lean_is_exclusive(v_impl_988_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; lean_object* v_unused_1064_; lean_object* v_unused_1065_; lean_object* v_unused_1066_; lean_object* v_unused_1067_; 
v_unused_1063_ = lean_ctor_get(v_impl_988_, 4);
lean_dec(v_unused_1063_);
v_unused_1064_ = lean_ctor_get(v_impl_988_, 3);
lean_dec(v_unused_1064_);
v_unused_1065_ = lean_ctor_get(v_impl_988_, 2);
lean_dec(v_unused_1065_);
v_unused_1066_ = lean_ctor_get(v_impl_988_, 1);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_impl_988_, 0);
lean_dec(v_unused_1067_);
v___x_1057_ = v_impl_988_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_dec(v_impl_988_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 4, v___x_1055_);
lean_ctor_set(v___x_1057_, 3, v_l_994_);
lean_ctor_set(v___x_1057_, 2, v_v_993_);
lean_ctor_set(v___x_1057_, 1, v_k_992_);
lean_ctor_set(v___x_1057_, 0, v___x_1051_);
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_k_992_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v_v_993_);
lean_ctor_set(v_reuseFailAlloc_1061_, 3, v_l_994_);
lean_ctor_set(v_reuseFailAlloc_1061_, 4, v___x_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v_size_1075_ = lean_ctor_get(v_impl_988_, 0);
lean_inc(v_size_1075_);
v___x_1076_ = lean_nat_add(v___x_989_, v_size_1075_);
lean_dec(v_size_1075_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_impl_988_);
lean_ctor_set(v___x_500_, 0, v___x_1076_);
v___x_1078_ = v___x_500_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_l_497_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_impl_988_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
else
{
if (lean_obj_tag(v_l_497_) == 0)
{
lean_object* v_l_1080_; 
v_l_1080_ = lean_ctor_get(v_l_497_, 3);
if (lean_obj_tag(v_l_1080_) == 0)
{
lean_object* v_r_1081_; 
lean_inc_ref(v_l_1080_);
v_r_1081_ = lean_ctor_get(v_l_497_, 4);
lean_inc(v_r_1081_);
if (lean_obj_tag(v_r_1081_) == 0)
{
lean_object* v_size_1082_; lean_object* v_k_1083_; lean_object* v_v_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1097_; 
v_size_1082_ = lean_ctor_get(v_l_497_, 0);
v_k_1083_ = lean_ctor_get(v_l_497_, 1);
v_v_1084_ = lean_ctor_get(v_l_497_, 2);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_l_497_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; lean_object* v_unused_1099_; 
v_unused_1098_ = lean_ctor_get(v_l_497_, 4);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_l_497_, 3);
lean_dec(v_unused_1099_);
v___x_1086_ = v_l_497_;
v_isShared_1087_ = v_isSharedCheck_1097_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_v_1084_);
lean_inc(v_k_1083_);
lean_inc(v_size_1082_);
lean_dec(v_l_497_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1097_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v_size_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v_size_1088_ = lean_ctor_get(v_r_1081_, 0);
v___x_1089_ = lean_nat_add(v___x_989_, v_size_1082_);
lean_dec(v_size_1082_);
v___x_1090_ = lean_nat_add(v___x_989_, v_size_1088_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 4, v_impl_988_);
lean_ctor_set(v___x_1086_, 3, v_r_1081_);
lean_ctor_set(v___x_1086_, 2, v_v_496_);
lean_ctor_set(v___x_1086_, 1, v_k_495_);
lean_ctor_set(v___x_1086_, 0, v___x_1090_);
v___x_1092_ = v___x_1086_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_1096_, 3, v_r_1081_);
lean_ctor_set(v_reuseFailAlloc_1096_, 4, v_impl_988_);
v___x_1092_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1094_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v___x_1092_);
lean_ctor_set(v___x_500_, 3, v_l_1080_);
lean_ctor_set(v___x_500_, 2, v_v_1084_);
lean_ctor_set(v___x_500_, 1, v_k_1083_);
lean_ctor_set(v___x_500_, 0, v___x_1089_);
v___x_1094_ = v___x_500_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_k_1083_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_v_1084_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_l_1080_);
lean_ctor_set(v_reuseFailAlloc_1095_, 4, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v_k_1100_; lean_object* v_v_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1112_; 
v_k_1100_ = lean_ctor_get(v_l_497_, 1);
v_v_1101_ = lean_ctor_get(v_l_497_, 2);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_l_497_);
if (v_isSharedCheck_1112_ == 0)
{
lean_object* v_unused_1113_; lean_object* v_unused_1114_; lean_object* v_unused_1115_; 
v_unused_1113_ = lean_ctor_get(v_l_497_, 4);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v_l_497_, 3);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v_l_497_, 0);
lean_dec(v_unused_1115_);
v___x_1103_ = v_l_497_;
v_isShared_1104_ = v_isSharedCheck_1112_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_v_1101_);
lean_inc(v_k_1100_);
lean_dec(v_l_497_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1112_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1105_ = lean_unsigned_to_nat(3u);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 3, v_r_1081_);
lean_ctor_set(v___x_1103_, 2, v_v_496_);
lean_ctor_set(v___x_1103_, 1, v_k_495_);
lean_ctor_set(v___x_1103_, 0, v___x_989_);
v___x_1107_ = v___x_1103_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_1111_, 3, v_r_1081_);
lean_ctor_set(v_reuseFailAlloc_1111_, 4, v_r_1081_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v___x_1107_);
lean_ctor_set(v___x_500_, 3, v_l_1080_);
lean_ctor_set(v___x_500_, 2, v_v_1101_);
lean_ctor_set(v___x_500_, 1, v_k_1100_);
lean_ctor_set(v___x_500_, 0, v___x_1105_);
v___x_1109_ = v___x_500_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_k_1100_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_v_1101_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v_l_1080_);
lean_ctor_set(v_reuseFailAlloc_1110_, 4, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
else
{
lean_object* v_r_1116_; 
v_r_1116_ = lean_ctor_get(v_l_497_, 4);
lean_inc(v_r_1116_);
if (lean_obj_tag(v_r_1116_) == 0)
{
lean_object* v_k_1117_; lean_object* v_v_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1141_; 
lean_inc(v_l_1080_);
v_k_1117_ = lean_ctor_get(v_l_497_, 1);
v_v_1118_ = lean_ctor_get(v_l_497_, 2);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_l_497_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; lean_object* v_unused_1143_; lean_object* v_unused_1144_; 
v_unused_1142_ = lean_ctor_get(v_l_497_, 4);
lean_dec(v_unused_1142_);
v_unused_1143_ = lean_ctor_get(v_l_497_, 3);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_l_497_, 0);
lean_dec(v_unused_1144_);
v___x_1120_ = v_l_497_;
v_isShared_1121_ = v_isSharedCheck_1141_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_v_1118_);
lean_inc(v_k_1117_);
lean_dec(v_l_497_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1141_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v_k_1122_; lean_object* v_v_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1137_; 
v_k_1122_ = lean_ctor_get(v_r_1116_, 1);
v_v_1123_ = lean_ctor_get(v_r_1116_, 2);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_r_1116_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; 
v_unused_1138_ = lean_ctor_get(v_r_1116_, 4);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_r_1116_, 3);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_r_1116_, 0);
lean_dec(v_unused_1140_);
v___x_1125_ = v_r_1116_;
v_isShared_1126_ = v_isSharedCheck_1137_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_v_1123_);
lean_inc(v_k_1122_);
lean_dec(v_r_1116_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1137_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_unsigned_to_nat(3u);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 4, v_l_1080_);
lean_ctor_set(v___x_1125_, 3, v_l_1080_);
lean_ctor_set(v___x_1125_, 2, v_v_1118_);
lean_ctor_set(v___x_1125_, 1, v_k_1117_);
lean_ctor_set(v___x_1125_, 0, v___x_989_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_k_1117_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_v_1118_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v_l_1080_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_l_1080_);
v___x_1129_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v_l_1080_);
lean_ctor_set(v___x_1120_, 2, v_v_496_);
lean_ctor_set(v___x_1120_, 1, v_k_495_);
lean_ctor_set(v___x_1120_, 0, v___x_989_);
v___x_1131_ = v___x_1120_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_l_1080_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_l_1080_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v___x_1131_);
lean_ctor_set(v___x_500_, 3, v___x_1129_);
lean_ctor_set(v___x_500_, 2, v_v_1123_);
lean_ctor_set(v___x_500_, 1, v_k_1122_);
lean_ctor_set(v___x_500_, 0, v___x_1127_);
v___x_1133_ = v___x_500_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_k_1122_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_v_1123_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = lean_unsigned_to_nat(2u);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_r_1116_);
lean_ctor_set(v___x_500_, 0, v___x_1145_);
v___x_1147_ = v___x_500_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_l_497_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_r_1116_);
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
else
{
lean_object* v___x_1150_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_l_497_);
lean_ctor_set(v___x_500_, 0, v___x_989_);
v___x_1150_ = v___x_500_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_l_497_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_l_497_);
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
}
}
}
else
{
return v_t_494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg___boxed(lean_object* v_k_1154_, lean_object* v_t_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1154_, v_t_1155_);
lean_dec(v_k_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString(lean_object* v_declName_1157_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1159_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1160_ = lean_st_ref_take(v___x_1159_);
v___x_1161_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_declName_1157_, v___x_1160_);
v___x_1162_ = lean_st_ref_set(v___x_1159_, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString___boxed(lean_object* v_declName_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_removeBuiltinDocString(v_declName_1164_);
lean_dec(v_declName_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(lean_object* v_00_u03b2_1167_, lean_object* v_k_1168_, lean_object* v_t_1169_, lean_object* v_h_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1168_, v_t_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___boxed(lean_object* v_00_u03b2_1172_, lean_object* v_k_1173_, lean_object* v_t_1174_, lean_object* v_h_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(v_00_u03b2_1172_, v_k_1173_, v_t_1174_, v_h_1175_);
lean_dec(v_k_1173_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings(){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1179_ = lean_st_ref_get(v___x_1178_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings___boxed(lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_getBuiltinVersoDocStrings();
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object* v_docString_1183_, lean_object* v_declName_1184_, lean_object* v_env_1185_){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1186_ = l_Lean_docStringExt;
v___x_1187_ = l_String_removeLeadingSpaces(v_docString_1183_);
v___x_1188_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1186_, v_env_1185_, v_declName_1184_, v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_1189_, lean_object* v___f_1190_, lean_object* v_____r_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_apply_1(v_modifyEnv_1189_, v___f_1190_);
return v___x_1192_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__0));
v___x_1195_ = l_Lean_stringToMessageData(v___x_1194_);
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__2));
v___x_1198_ = l_Lean_stringToMessageData(v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2(lean_object* v_declName_1199_, lean_object* v_modifyEnv_1200_, lean_object* v___f_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_toBind_1204_, lean_object* v___f_1205_, lean_object* v_____do__lift_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1206_, v_declName_1199_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v___x_1208_; 
lean_dec(v___f_1205_);
lean_dec(v_toBind_1204_);
lean_dec_ref(v_inst_1203_);
lean_dec_ref(v_inst_1202_);
lean_dec(v_declName_1199_);
v___x_1208_ = lean_apply_1(v_modifyEnv_1200_, v___f_1201_);
return v___x_1208_;
}
else
{
uint8_t v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___f_1201_);
lean_dec(v_modifyEnv_1200_);
v___x_1209_ = 0;
v___x_1210_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1211_ = l_Lean_MessageData_ofConstName(v_declName_1199_, v___x_1209_);
v___x_1212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = l_Lean_throwError___redArg(v_inst_1202_, v_inst_1203_, v___x_1214_);
v___x_1216_ = lean_apply_4(v_toBind_1204_, lean_box(0), lean_box(0), v___x_1215_, v___f_1205_);
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1217_, lean_object* v_modifyEnv_1218_, lean_object* v___f_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_toBind_1222_, lean_object* v___f_1223_, lean_object* v_____do__lift_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_addDocStringCore___redArg___lam__2(v_declName_1217_, v_modifyEnv_1218_, v___f_1219_, v_inst_1220_, v_inst_1221_, v_toBind_1222_, v___f_1223_, v_____do__lift_1224_);
lean_dec_ref(v_____do__lift_1224_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg(lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_inst_1228_, lean_object* v_declName_1229_, lean_object* v_docString_1230_){
_start:
{
lean_object* v_toBind_1231_; lean_object* v_getEnv_1232_; lean_object* v_modifyEnv_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___x_1237_; 
v_toBind_1231_ = lean_ctor_get(v_inst_1226_, 1);
lean_inc(v_toBind_1231_);
v_getEnv_1232_ = lean_ctor_get(v_inst_1228_, 0);
lean_inc(v_getEnv_1232_);
v_modifyEnv_1233_ = lean_ctor_get(v_inst_1228_, 1);
lean_inc(v_modifyEnv_1233_);
lean_dec_ref(v_inst_1228_);
lean_inc(v_declName_1229_);
v___f_1234_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1234_, 0, v_docString_1230_);
lean_closure_set(v___f_1234_, 1, v_declName_1229_);
lean_inc_ref(v___f_1234_);
lean_inc(v_modifyEnv_1233_);
v___f_1235_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1235_, 0, v_modifyEnv_1233_);
lean_closure_set(v___f_1235_, 1, v___f_1234_);
lean_inc(v_toBind_1231_);
v___f_1236_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1236_, 0, v_declName_1229_);
lean_closure_set(v___f_1236_, 1, v_modifyEnv_1233_);
lean_closure_set(v___f_1236_, 2, v___f_1234_);
lean_closure_set(v___f_1236_, 3, v_inst_1226_);
lean_closure_set(v___f_1236_, 4, v_inst_1227_);
lean_closure_set(v___f_1236_, 5, v_toBind_1231_);
lean_closure_set(v___f_1236_, 6, v___f_1235_);
v___x_1237_ = lean_apply_4(v_toBind_1231_, lean_box(0), lean_box(0), v_getEnv_1232_, v___f_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore(lean_object* v_m_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_declName_1243_, lean_object* v_docString_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_addDocStringCore___redArg(v_inst_1239_, v_inst_1240_, v_inst_1241_, v_declName_1243_, v_docString_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___boxed(lean_object* v_m_1246_, lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_declName_1251_, lean_object* v_docString_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_addDocStringCore(v_m_1246_, v_inst_1247_, v_inst_1248_, v_inst_1249_, v_inst_1250_, v_declName_1251_, v_docString_1252_);
lean_dec(v_inst_1250_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__0(lean_object* v_declName_1255_, lean_object* v_x_1256_){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__0___closed__0));
v___x_1258_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_1257_, v_declName_1255_, v_x_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__1(lean_object* v___f_1259_, lean_object* v_env_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1261_ = l_Lean_docStringExt;
v___x_1262_ = lean_box(2);
v___x_1263_ = lean_box(0);
v___x_1264_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_1261_, v_env_1260_, v___f_1259_, v___x_1262_, v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__3___closed__0));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3(lean_object* v_declName_1268_, lean_object* v_modifyEnv_1269_, lean_object* v___f_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_toBind_1273_, lean_object* v___f_1274_, lean_object* v_____do__lift_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1275_, v_declName_1268_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; 
lean_dec(v___f_1274_);
lean_dec(v_toBind_1273_);
lean_dec_ref(v_inst_1272_);
lean_dec_ref(v_inst_1271_);
lean_dec(v_declName_1268_);
v___x_1277_ = lean_apply_1(v_modifyEnv_1269_, v___f_1270_);
return v___x_1277_;
}
else
{
uint8_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec_ref(v___x_1276_);
lean_dec_ref(v___f_1270_);
lean_dec(v_modifyEnv_1269_);
v___x_1278_ = 0;
v___x_1279_ = lean_obj_once(&l_Lean_removeDocStringCore___redArg___lam__3___closed__1, &l_Lean_removeDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1);
v___x_1280_ = l_Lean_MessageData_ofConstName(v_declName_1268_, v___x_1278_);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_throwError___redArg(v_inst_1271_, v_inst_1272_, v___x_1283_);
v___x_1285_ = lean_apply_4(v_toBind_1273_, lean_box(0), lean_box(0), v___x_1284_, v___f_1274_);
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_1286_, lean_object* v_modifyEnv_1287_, lean_object* v___f_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_toBind_1291_, lean_object* v___f_1292_, lean_object* v_____do__lift_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_removeDocStringCore___redArg___lam__3(v_declName_1286_, v_modifyEnv_1287_, v___f_1288_, v_inst_1289_, v_inst_1290_, v_toBind_1291_, v___f_1292_, v_____do__lift_1293_);
lean_dec_ref(v_____do__lift_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg(lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_declName_1298_){
_start:
{
lean_object* v_toBind_1299_; lean_object* v_getEnv_1300_; lean_object* v_modifyEnv_1301_; lean_object* v___f_1302_; lean_object* v___f_1303_; lean_object* v___f_1304_; lean_object* v___f_1305_; lean_object* v___x_1306_; 
v_toBind_1299_ = lean_ctor_get(v_inst_1295_, 1);
lean_inc(v_toBind_1299_);
v_getEnv_1300_ = lean_ctor_get(v_inst_1297_, 0);
lean_inc(v_getEnv_1300_);
v_modifyEnv_1301_ = lean_ctor_get(v_inst_1297_, 1);
lean_inc(v_modifyEnv_1301_);
lean_dec_ref(v_inst_1297_);
lean_inc(v_declName_1298_);
v___f_1302_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1302_, 0, v_declName_1298_);
v___f_1303_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1303_, 0, v___f_1302_);
lean_inc_ref(v___f_1303_);
lean_inc(v_modifyEnv_1301_);
v___f_1304_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1304_, 0, v_modifyEnv_1301_);
lean_closure_set(v___f_1304_, 1, v___f_1303_);
lean_inc(v_toBind_1299_);
v___f_1305_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1305_, 0, v_declName_1298_);
lean_closure_set(v___f_1305_, 1, v_modifyEnv_1301_);
lean_closure_set(v___f_1305_, 2, v___f_1303_);
lean_closure_set(v___f_1305_, 3, v_inst_1295_);
lean_closure_set(v___f_1305_, 4, v_inst_1296_);
lean_closure_set(v___f_1305_, 5, v_toBind_1299_);
lean_closure_set(v___f_1305_, 6, v___f_1304_);
v___x_1306_ = lean_apply_4(v_toBind_1299_, lean_box(0), lean_box(0), v_getEnv_1300_, v___f_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore(lean_object* v_m_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_declName_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_removeDocStringCore___redArg(v_inst_1308_, v_inst_1309_, v_inst_1310_, v_declName_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___boxed(lean_object* v_m_1314_, lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_declName_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_removeDocStringCore(v_m_1314_, v_inst_1315_, v_inst_1316_, v_inst_1317_, v_inst_1318_, v_declName_1319_);
lean_dec(v_inst_1318_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___redArg(lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_declName_1324_, lean_object* v_docString_x3f_1325_){
_start:
{
if (lean_obj_tag(v_docString_x3f_1325_) == 0)
{
lean_object* v_toApplicative_1326_; lean_object* v_toPure_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_toApplicative_1326_ = lean_ctor_get(v_inst_1321_, 0);
lean_inc_ref(v_toApplicative_1326_);
lean_dec(v_declName_1324_);
lean_dec_ref(v_inst_1323_);
lean_dec_ref(v_inst_1322_);
lean_dec_ref(v_inst_1321_);
v_toPure_1327_ = lean_ctor_get(v_toApplicative_1326_, 1);
lean_inc(v_toPure_1327_);
lean_dec_ref(v_toApplicative_1326_);
v___x_1328_ = lean_box(0);
v___x_1329_ = lean_apply_2(v_toPure_1327_, lean_box(0), v___x_1328_);
return v___x_1329_;
}
else
{
lean_object* v_val_1330_; lean_object* v___x_1331_; 
v_val_1330_ = lean_ctor_get(v_docString_x3f_1325_, 0);
lean_inc(v_val_1330_);
lean_dec_ref(v_docString_x3f_1325_);
v___x_1331_ = l_Lean_addDocStringCore___redArg(v_inst_1321_, v_inst_1322_, v_inst_1323_, v_declName_1324_, v_val_1330_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27(lean_object* v_m_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_declName_1337_, lean_object* v_docString_x3f_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_addDocStringCore_x27___redArg(v_inst_1333_, v_inst_1334_, v_inst_1335_, v_declName_1337_, v_docString_x3f_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___boxed(lean_object* v_m_1340_, lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_declName_1345_, lean_object* v_docString_x3f_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_addDocStringCore_x27(v_m_1340_, v_inst_1341_, v_inst_1342_, v_inst_1343_, v_inst_1344_, v_declName_1345_, v_docString_x3f_1346_);
lean_dec(v_inst_1344_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object* v_declName_1348_, lean_object* v_target_1349_, lean_object* v_env_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1352_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1351_, v_env_1350_, v_declName_1348_, v_target_1349_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__2___closed__0));
v___x_1355_ = l_Lean_stringToMessageData(v___x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object* v___x_1356_, lean_object* v_target_1357_, lean_object* v_declName_1358_, lean_object* v___x_1359_, lean_object* v_modifyEnv_1360_, lean_object* v___f_1361_, lean_object* v_inst_1362_, lean_object* v_inst_1363_, lean_object* v_toBind_1364_, lean_object* v___f_1365_, lean_object* v_____do__lift_1366_){
_start:
{
lean_object* v___x_1367_; lean_object* v_toEnvExtension_1368_; lean_object* v_asyncMode_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1367_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc_ref(v_toEnvExtension_1368_);
v_asyncMode_1369_ = lean_ctor_get(v_toEnvExtension_1368_, 2);
lean_inc(v_asyncMode_1369_);
lean_dec_ref(v_toEnvExtension_1368_);
v___x_1370_ = 1;
v___x_1371_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1356_, v___x_1367_, v_____do__lift_1366_, v_target_1357_, v_asyncMode_1369_, v___x_1370_);
lean_dec(v_asyncMode_1369_);
v___x_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_declName_1358_);
v___x_1373_ = l_Option_instBEq_beq___redArg(v___x_1359_, v___x_1371_, v___x_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
lean_dec(v___f_1365_);
lean_dec(v_toBind_1364_);
lean_dec_ref(v_inst_1363_);
lean_dec_ref(v_inst_1362_);
v___x_1374_ = lean_apply_1(v_modifyEnv_1360_, v___f_1361_);
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref(v___f_1361_);
lean_dec(v_modifyEnv_1360_);
v___x_1375_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__2___closed__1, &l_Lean_addInheritedDocString___redArg___lam__2___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1);
v___x_1376_ = l_Lean_throwError___redArg(v_inst_1362_, v_inst_1363_, v___x_1375_);
v___x_1377_ = lean_apply_4(v_toBind_1364_, lean_box(0), lean_box(0), v___x_1376_, v___f_1365_);
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object* v_toBind_1378_, lean_object* v_getEnv_1379_, lean_object* v___f_1380_, lean_object* v_____r_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_apply_4(v_toBind_1378_, lean_box(0), lean_box(0), v_getEnv_1379_, v___f_1380_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__0));
v___x_1385_ = l_Lean_stringToMessageData(v___x_1384_);
return v___x_1385_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__2));
v___x_1388_ = l_Lean_stringToMessageData(v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object* v___x_1389_, lean_object* v_declName_1390_, lean_object* v_toBind_1391_, lean_object* v_getEnv_1392_, lean_object* v___f_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_, lean_object* v___f_1396_, lean_object* v_____do__lift_1397_){
_start:
{
lean_object* v___x_1398_; lean_object* v_toEnvExtension_1399_; lean_object* v_asyncMode_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; 
v___x_1398_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc_ref(v_toEnvExtension_1399_);
v_asyncMode_1400_ = lean_ctor_get(v_toEnvExtension_1399_, 2);
lean_inc(v_asyncMode_1400_);
lean_dec_ref(v_toEnvExtension_1399_);
v___x_1401_ = 1;
lean_inc(v_declName_1390_);
v___x_1402_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1389_, v___x_1398_, v_____do__lift_1397_, v_declName_1390_, v_asyncMode_1400_, v___x_1401_);
lean_dec(v_asyncMode_1400_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v___x_1403_; 
lean_dec(v___f_1396_);
lean_dec_ref(v_inst_1395_);
lean_dec_ref(v_inst_1394_);
lean_dec(v_declName_1390_);
v___x_1403_ = lean_apply_4(v_toBind_1391_, lean_box(0), lean_box(0), v_getEnv_1392_, v___f_1393_);
return v___x_1403_;
}
else
{
lean_object* v___x_1404_; uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_dec_ref(v___x_1402_);
lean_dec(v___f_1393_);
lean_dec(v_getEnv_1392_);
v___x_1404_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1405_ = 0;
v___x_1406_ = l_Lean_MessageData_ofConstName(v_declName_1390_, v___x_1405_);
v___x_1407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1404_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__3, &l_Lean_addInheritedDocString___redArg___lam__3___closed__3_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3);
v___x_1409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1407_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = l_Lean_throwError___redArg(v_inst_1394_, v_inst_1395_, v___x_1409_);
v___x_1411_ = lean_apply_4(v_toBind_1391_, lean_box(0), lean_box(0), v___x_1410_, v___f_1396_);
return v___x_1411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object* v_declName_1412_, lean_object* v_toBind_1413_, lean_object* v_getEnv_1414_, lean_object* v___f_1415_, lean_object* v_inst_1416_, lean_object* v_inst_1417_, lean_object* v___f_1418_, lean_object* v_____do__lift_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1419_, v_declName_1412_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1421_; 
lean_dec(v___f_1418_);
lean_dec_ref(v_inst_1417_);
lean_dec_ref(v_inst_1416_);
lean_dec(v_declName_1412_);
v___x_1421_ = lean_apply_4(v_toBind_1413_, lean_box(0), lean_box(0), v_getEnv_1414_, v___f_1415_);
return v___x_1421_;
}
else
{
uint8_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec_ref(v___x_1420_);
lean_dec(v___f_1415_);
lean_dec(v_getEnv_1414_);
v___x_1422_ = 0;
v___x_1423_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1424_ = l_Lean_MessageData_ofConstName(v_declName_1412_, v___x_1422_);
v___x_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v___x_1426_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = l_Lean_throwError___redArg(v_inst_1416_, v_inst_1417_, v___x_1427_);
v___x_1429_ = lean_apply_4(v_toBind_1413_, lean_box(0), lean_box(0), v___x_1428_, v___f_1418_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object* v_declName_1430_, lean_object* v_toBind_1431_, lean_object* v_getEnv_1432_, lean_object* v___f_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v___f_1436_, lean_object* v_____do__lift_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_addInheritedDocString___redArg___lam__5(v_declName_1430_, v_toBind_1431_, v_getEnv_1432_, v___f_1433_, v_inst_1434_, v_inst_1435_, v___f_1436_, v_____do__lift_1437_);
lean_dec_ref(v_____do__lift_1437_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object* v_inst_1440_, lean_object* v_inst_1441_, lean_object* v_inst_1442_, lean_object* v_declName_1443_, lean_object* v_target_1444_){
_start:
{
lean_object* v_toBind_1445_; lean_object* v_getEnv_1446_; lean_object* v_modifyEnv_1447_; lean_object* v___f_1448_; lean_object* v___f_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___f_1452_; lean_object* v___f_1453_; lean_object* v___f_1454_; lean_object* v___f_1455_; lean_object* v___f_1456_; lean_object* v___x_1457_; 
v_toBind_1445_ = lean_ctor_get(v_inst_1440_, 1);
lean_inc(v_toBind_1445_);
v_getEnv_1446_ = lean_ctor_get(v_inst_1442_, 0);
lean_inc(v_getEnv_1446_);
v_modifyEnv_1447_ = lean_ctor_get(v_inst_1442_, 1);
lean_inc(v_modifyEnv_1447_);
lean_dec_ref(v_inst_1442_);
lean_inc(v_target_1444_);
lean_inc(v_declName_1443_);
v___f_1448_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1448_, 0, v_declName_1443_);
lean_closure_set(v___f_1448_, 1, v_target_1444_);
lean_inc_ref(v___f_1448_);
lean_inc(v_modifyEnv_1447_);
v___f_1449_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1449_, 0, v_modifyEnv_1447_);
lean_closure_set(v___f_1449_, 1, v___f_1448_);
v___x_1450_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___closed__0));
v___x_1451_ = lean_box(0);
lean_inc(v_toBind_1445_);
lean_inc_ref(v_inst_1441_);
lean_inc_ref(v_inst_1440_);
lean_inc(v_declName_1443_);
v___f_1452_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__2), 11, 10);
lean_closure_set(v___f_1452_, 0, v___x_1451_);
lean_closure_set(v___f_1452_, 1, v_target_1444_);
lean_closure_set(v___f_1452_, 2, v_declName_1443_);
lean_closure_set(v___f_1452_, 3, v___x_1450_);
lean_closure_set(v___f_1452_, 4, v_modifyEnv_1447_);
lean_closure_set(v___f_1452_, 5, v___f_1448_);
lean_closure_set(v___f_1452_, 6, v_inst_1440_);
lean_closure_set(v___f_1452_, 7, v_inst_1441_);
lean_closure_set(v___f_1452_, 8, v_toBind_1445_);
lean_closure_set(v___f_1452_, 9, v___f_1449_);
lean_inc_ref(v___f_1452_);
lean_inc(v_getEnv_1446_);
lean_inc(v_toBind_1445_);
v___f_1453_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1453_, 0, v_toBind_1445_);
lean_closure_set(v___f_1453_, 1, v_getEnv_1446_);
lean_closure_set(v___f_1453_, 2, v___f_1452_);
lean_inc_ref(v_inst_1441_);
lean_inc_ref(v_inst_1440_);
lean_inc(v_getEnv_1446_);
lean_inc(v_toBind_1445_);
lean_inc(v_declName_1443_);
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__3), 9, 8);
lean_closure_set(v___f_1454_, 0, v___x_1451_);
lean_closure_set(v___f_1454_, 1, v_declName_1443_);
lean_closure_set(v___f_1454_, 2, v_toBind_1445_);
lean_closure_set(v___f_1454_, 3, v_getEnv_1446_);
lean_closure_set(v___f_1454_, 4, v___f_1452_);
lean_closure_set(v___f_1454_, 5, v_inst_1440_);
lean_closure_set(v___f_1454_, 6, v_inst_1441_);
lean_closure_set(v___f_1454_, 7, v___f_1453_);
lean_inc_ref(v___f_1454_);
lean_inc(v_getEnv_1446_);
lean_inc(v_toBind_1445_);
v___f_1455_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1455_, 0, v_toBind_1445_);
lean_closure_set(v___f_1455_, 1, v_getEnv_1446_);
lean_closure_set(v___f_1455_, 2, v___f_1454_);
lean_inc(v_getEnv_1446_);
lean_inc(v_toBind_1445_);
v___f_1456_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1456_, 0, v_declName_1443_);
lean_closure_set(v___f_1456_, 1, v_toBind_1445_);
lean_closure_set(v___f_1456_, 2, v_getEnv_1446_);
lean_closure_set(v___f_1456_, 3, v___f_1454_);
lean_closure_set(v___f_1456_, 4, v_inst_1440_);
lean_closure_set(v___f_1456_, 5, v_inst_1441_);
lean_closure_set(v___f_1456_, 6, v___f_1455_);
v___x_1457_ = lean_apply_4(v_toBind_1445_, lean_box(0), lean_box(0), v_getEnv_1446_, v___f_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object* v_m_1458_, lean_object* v_inst_1459_, lean_object* v_inst_1460_, lean_object* v_inst_1461_, lean_object* v_declName_1462_, lean_object* v_target_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_addInheritedDocString___redArg(v_inst_1459_, v_inst_1460_, v_inst_1461_, v_declName_1462_, v_target_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f(lean_object* v_env_1466_, lean_object* v_declName_1467_, uint8_t v_includeBuiltin_1468_){
_start:
{
lean_object* v___x_1473_; lean_object* v_toEnvExtension_1474_; lean_object* v_asyncMode_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; 
v___x_1473_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc_ref(v_toEnvExtension_1474_);
v_asyncMode_1475_ = lean_ctor_get(v_toEnvExtension_1474_, 2);
lean_inc(v_asyncMode_1475_);
lean_dec_ref(v_toEnvExtension_1474_);
v___x_1476_ = lean_box(0);
v___x_1477_ = 1;
lean_inc(v_declName_1467_);
lean_inc_ref(v_env_1466_);
v___x_1478_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1476_, v___x_1473_, v_env_1466_, v_declName_1467_, v_asyncMode_1475_, v___x_1477_);
lean_dec(v_asyncMode_1475_);
if (lean_obj_tag(v___x_1478_) == 1)
{
lean_object* v_val_1479_; 
lean_dec(v_declName_1467_);
v_val_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_val_1479_);
lean_dec_ref(v___x_1478_);
v_declName_1467_ = v_val_1479_;
goto _start;
}
else
{
lean_object* v___x_1481_; lean_object* v_toEnvExtension_1482_; lean_object* v_asyncMode_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec(v___x_1478_);
v___x_1481_ = l_Lean_docStringExt;
v_toEnvExtension_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc_ref(v_toEnvExtension_1482_);
v_asyncMode_1483_ = lean_ctor_get(v_toEnvExtension_1482_, 2);
lean_inc(v_asyncMode_1483_);
lean_dec_ref(v_toEnvExtension_1482_);
v___x_1484_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
lean_inc(v_declName_1467_);
lean_inc_ref(v_env_1466_);
v___x_1485_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1484_, v___x_1481_, v_env_1466_, v_declName_1467_, v_asyncMode_1483_, v___x_1477_);
lean_dec(v_asyncMode_1483_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v___x_1486_; lean_object* v_toEnvExtension_1487_; lean_object* v_asyncMode_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1486_ = l_Lean_versoDocStringExt;
v_toEnvExtension_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc_ref(v_toEnvExtension_1487_);
v_asyncMode_1488_ = lean_ctor_get(v_toEnvExtension_1487_, 2);
lean_inc(v_asyncMode_1488_);
lean_dec_ref(v_toEnvExtension_1487_);
v___x_1489_ = l_Lean_instInhabitedVersoDocString_default;
lean_inc(v_declName_1467_);
v___x_1490_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1489_, v___x_1486_, v_env_1466_, v_declName_1467_, v_asyncMode_1488_, v___x_1477_);
lean_dec(v_asyncMode_1488_);
if (lean_obj_tag(v___x_1490_) == 0)
{
if (v_includeBuiltin_1468_ == 0)
{
lean_dec(v_declName_1467_);
goto v___jp_1470_;
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1492_ = lean_st_ref_get(v___x_1491_);
v___x_1493_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1492_, v_declName_1467_);
lean_dec(v___x_1492_);
if (lean_obj_tag(v___x_1493_) == 1)
{
lean_object* v_val_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_declName_1467_);
v_val_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1503_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_val_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1503_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_val_1494_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1498_);
v___x_1500_ = v___x_1496_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec(v___x_1493_);
v___x_1504_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1505_ = lean_st_ref_get(v___x_1504_);
v___x_1506_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1505_, v_declName_1467_);
lean_dec(v_declName_1467_);
lean_dec(v___x_1505_);
if (lean_obj_tag(v___x_1506_) == 1)
{
lean_object* v_val_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1516_; 
v_val_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1516_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_val_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1516_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_val_1507_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1511_);
v___x_1513_ = v___x_1509_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
}
}
else
{
lean_dec(v___x_1506_);
goto v___jp_1470_;
}
}
}
}
else
{
lean_object* v_val_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1526_; 
lean_dec(v_declName_1467_);
v_val_1517_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1519_ = v___x_1490_;
v_isShared_1520_ = v_isSharedCheck_1526_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_val_1517_);
lean_dec(v___x_1490_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1526_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1521_, 0, v_val_1517_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1521_);
v___x_1523_ = v___x_1519_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_val_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v_declName_1467_);
lean_dec_ref(v_env_1466_);
v_val_1527_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1529_ = v___x_1485_;
v_isShared_1530_ = v_isSharedCheck_1536_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_val_1527_);
lean_dec(v___x_1485_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1536_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v_val_1527_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1531_);
v___x_1533_ = v___x_1529_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
}
}
}
v___jp_1470_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object* v_env_1537_, lean_object* v_declName_1538_, lean_object* v_includeBuiltin_1539_, lean_object* v_a_1540_){
_start:
{
uint8_t v_includeBuiltin_boxed_1541_; lean_object* v_res_1542_; 
v_includeBuiltin_boxed_1541_ = lean_unbox(v_includeBuiltin_1539_);
v_res_1542_ = l_Lean_findInternalDocString_x3f(v_env_1537_, v_declName_1538_, v_includeBuiltin_boxed_1541_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__1(lean_object* v_x_1543_, lean_object* v_x_1544_){
_start:
{
lean_object* v_zero_1545_; uint8_t v_isZero_1546_; 
v_zero_1545_ = lean_unsigned_to_nat(0u);
v_isZero_1546_ = lean_nat_dec_eq(v_x_1543_, v_zero_1545_);
if (v_isZero_1546_ == 1)
{
lean_dec(v_x_1543_);
return v_x_1544_;
}
else
{
uint32_t v___x_1547_; lean_object* v_one_1548_; lean_object* v_n_1549_; lean_object* v___x_1550_; 
v___x_1547_ = 35;
v_one_1548_ = lean_unsigned_to_nat(1u);
v_n_1549_ = lean_nat_sub(v_x_1543_, v_one_1548_);
lean_dec(v_x_1543_);
v___x_1550_ = lean_string_push(v_x_1544_, v___x_1547_);
v_x_1543_ = v_n_1549_;
v_x_1544_ = v___x_1550_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_s_1552_, lean_object* v_replacement_1553_, lean_object* v_a_1554_, lean_object* v_b_1555_){
_start:
{
lean_object* v_it_1557_; lean_object* v_startPos_1558_; lean_object* v_endPos_1559_; lean_object* v_it_1568_; 
switch(lean_obj_tag(v_a_1554_))
{
case 0:
{
lean_object* v_pos_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1586_; 
v_pos_1574_ = lean_ctor_get(v_a_1554_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_a_1554_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1576_ = v_a_1554_;
v_isShared_1577_ = v_isSharedCheck_1586_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_pos_1574_);
lean_dec(v_a_1554_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1586_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_startInclusive_1578_; lean_object* v_endExclusive_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v_startInclusive_1578_ = lean_ctor_get(v_s_1552_, 1);
v_endExclusive_1579_ = lean_ctor_get(v_s_1552_, 2);
v___x_1580_ = lean_nat_sub(v_endExclusive_1579_, v_startInclusive_1578_);
v___x_1581_ = lean_nat_dec_eq(v_pos_1574_, v___x_1580_);
lean_dec(v___x_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1583_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 1);
v___x_1583_ = v___x_1576_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_pos_1574_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
v_it_1568_ = v___x_1583_;
goto v___jp_1567_;
}
}
else
{
lean_object* v___x_1585_; 
lean_del_object(v___x_1576_);
lean_dec(v_pos_1574_);
v___x_1585_ = lean_box(3);
v_it_1568_ = v___x_1585_;
goto v___jp_1567_;
}
}
}
case 1:
{
lean_object* v_pos_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1599_; 
v_pos_1587_ = lean_ctor_get(v_a_1554_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_a_1554_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1589_ = v_a_1554_;
v_isShared_1590_ = v_isSharedCheck_1599_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_pos_1587_);
lean_dec(v_a_1554_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1599_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v_str_1591_; lean_object* v_startInclusive_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v_str_1591_ = lean_ctor_get(v_s_1552_, 0);
v_startInclusive_1592_ = lean_ctor_get(v_s_1552_, 1);
v___x_1593_ = lean_nat_add(v_startInclusive_1592_, v_pos_1587_);
v___x_1594_ = lean_string_utf8_next_fast(v_str_1591_, v___x_1593_);
lean_dec(v___x_1593_);
v___x_1595_ = lean_nat_sub(v___x_1594_, v_startInclusive_1592_);
lean_inc(v___x_1595_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1595_);
v___x_1597_ = v___x_1589_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
v_it_1557_ = v___x_1597_;
v_startPos_1558_ = v_pos_1587_;
v_endPos_1559_ = v___x_1595_;
goto v___jp_1556_;
}
}
}
case 2:
{
lean_object* v_needle_1600_; lean_object* v_table_1601_; lean_object* v_stackPos_1602_; lean_object* v_needlePos_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1662_; 
v_needle_1600_ = lean_ctor_get(v_a_1554_, 0);
v_table_1601_ = lean_ctor_get(v_a_1554_, 1);
v_stackPos_1602_ = lean_ctor_get(v_a_1554_, 2);
v_needlePos_1603_ = lean_ctor_get(v_a_1554_, 3);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_a_1554_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1605_ = v_a_1554_;
v_isShared_1606_ = v_isSharedCheck_1662_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_needlePos_1603_);
lean_inc(v_stackPos_1602_);
lean_inc(v_table_1601_);
lean_inc(v_needle_1600_);
lean_dec(v_a_1554_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1662_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v_str_1607_; lean_object* v_startInclusive_1608_; lean_object* v_endExclusive_1609_; lean_object* v_str_1610_; lean_object* v_startInclusive_1611_; lean_object* v_endExclusive_1612_; lean_object* v_basePos_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_str_1607_ = lean_ctor_get(v_needle_1600_, 0);
v_startInclusive_1608_ = lean_ctor_get(v_needle_1600_, 1);
v_endExclusive_1609_ = lean_ctor_get(v_needle_1600_, 2);
v_str_1610_ = lean_ctor_get(v_s_1552_, 0);
v_startInclusive_1611_ = lean_ctor_get(v_s_1552_, 1);
v_endExclusive_1612_ = lean_ctor_get(v_s_1552_, 2);
v_basePos_1613_ = lean_nat_sub(v_stackPos_1602_, v_needlePos_1603_);
v___x_1614_ = lean_nat_sub(v_endExclusive_1609_, v_startInclusive_1608_);
v___x_1615_ = lean_nat_add(v_basePos_1613_, v___x_1614_);
v___x_1616_ = lean_nat_sub(v_endExclusive_1612_, v_startInclusive_1611_);
v___x_1617_ = lean_nat_dec_le(v___x_1615_, v___x_1616_);
lean_dec(v___x_1615_);
if (v___x_1617_ == 0)
{
uint8_t v___x_1618_; 
lean_dec(v___x_1614_);
lean_del_object(v___x_1605_);
lean_dec(v_needlePos_1603_);
lean_dec(v_stackPos_1602_);
lean_dec_ref(v_table_1601_);
lean_dec_ref(v_needle_1600_);
v___x_1618_ = lean_nat_dec_lt(v_basePos_1613_, v___x_1616_);
if (v___x_1618_ == 0)
{
lean_dec(v___x_1616_);
lean_dec(v_basePos_1613_);
lean_dec_ref(v_s_1552_);
return v_b_1555_;
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = l_String_Slice_pos_x21(v_s_1552_, v_basePos_1613_);
lean_dec(v_basePos_1613_);
v___x_1620_ = lean_box(3);
v_it_1557_ = v___x_1620_;
v_startPos_1558_ = v___x_1619_;
v_endPos_1559_ = v___x_1616_;
goto v___jp_1556_;
}
}
else
{
lean_object* v___x_1621_; uint8_t v_stackByte_1622_; lean_object* v___x_1623_; uint8_t v_patByte_1624_; uint8_t v___x_1625_; 
lean_dec(v___x_1616_);
v___x_1621_ = lean_nat_add(v_startInclusive_1611_, v_stackPos_1602_);
v_stackByte_1622_ = lean_string_get_byte_fast(v_str_1610_, v___x_1621_);
v___x_1623_ = lean_nat_add(v_startInclusive_1608_, v_needlePos_1603_);
v_patByte_1624_ = lean_string_get_byte_fast(v_str_1607_, v___x_1623_);
v___x_1625_ = lean_uint8_dec_eq(v_stackByte_1622_, v_patByte_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
lean_dec(v___x_1614_);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = lean_nat_dec_eq(v_needlePos_1603_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v_newNeedlePos_1630_; uint8_t v___x_1631_; 
v___x_1628_ = lean_unsigned_to_nat(1u);
v___x_1629_ = lean_nat_sub(v_needlePos_1603_, v___x_1628_);
lean_dec(v_needlePos_1603_);
v_newNeedlePos_1630_ = lean_array_fget_borrowed(v_table_1601_, v___x_1629_);
lean_dec(v___x_1629_);
v___x_1631_ = lean_nat_dec_eq(v_newNeedlePos_1630_, v___x_1626_);
if (v___x_1631_ == 0)
{
lean_object* v_oldBasePos_1632_; lean_object* v___x_1633_; lean_object* v_newBasePos_1634_; lean_object* v___x_1636_; 
lean_inc(v_newNeedlePos_1630_);
v_oldBasePos_1632_ = l_String_Slice_pos_x21(v_s_1552_, v_basePos_1613_);
lean_dec(v_basePos_1613_);
v___x_1633_ = lean_nat_sub(v_stackPos_1602_, v_newNeedlePos_1630_);
v_newBasePos_1634_ = l_String_Slice_pos_x21(v_s_1552_, v___x_1633_);
lean_dec(v___x_1633_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 3, v_newNeedlePos_1630_);
v___x_1636_ = v___x_1605_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_needle_1600_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_table_1601_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_stackPos_1602_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v_newNeedlePos_1630_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
v_it_1557_ = v___x_1636_;
v_startPos_1558_ = v_oldBasePos_1632_;
v_endPos_1559_ = v_newBasePos_1634_;
goto v___jp_1556_;
}
}
else
{
lean_object* v_basePos_1638_; lean_object* v_nextStackPos_1639_; lean_object* v___x_1641_; 
v_basePos_1638_ = l_String_Slice_pos_x21(v_s_1552_, v_basePos_1613_);
lean_dec(v_basePos_1613_);
v_nextStackPos_1639_ = l_String_Slice_posGE___redArg(v_s_1552_, v_stackPos_1602_);
lean_inc(v_nextStackPos_1639_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 3, v___x_1626_);
lean_ctor_set(v___x_1605_, 2, v_nextStackPos_1639_);
v___x_1641_ = v___x_1605_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_needle_1600_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_table_1601_);
lean_ctor_set(v_reuseFailAlloc_1642_, 2, v_nextStackPos_1639_);
lean_ctor_set(v_reuseFailAlloc_1642_, 3, v___x_1626_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
v_it_1557_ = v___x_1641_;
v_startPos_1558_ = v_basePos_1638_;
v_endPos_1559_ = v_nextStackPos_1639_;
goto v___jp_1556_;
}
}
}
else
{
lean_object* v_basePos_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v_nextStackPos_1646_; lean_object* v___x_1648_; 
lean_dec(v_basePos_1613_);
lean_dec(v_needlePos_1603_);
v_basePos_1643_ = l_String_Slice_pos_x21(v_s_1552_, v_stackPos_1602_);
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_nat_add(v_stackPos_1602_, v___x_1644_);
lean_dec(v_stackPos_1602_);
v_nextStackPos_1646_ = l_String_Slice_posGE___redArg(v_s_1552_, v___x_1645_);
lean_inc(v_nextStackPos_1646_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 3, v___x_1626_);
lean_ctor_set(v___x_1605_, 2, v_nextStackPos_1646_);
v___x_1648_ = v___x_1605_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_needle_1600_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_table_1601_);
lean_ctor_set(v_reuseFailAlloc_1649_, 2, v_nextStackPos_1646_);
lean_ctor_set(v_reuseFailAlloc_1649_, 3, v___x_1626_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
v_it_1557_ = v___x_1648_;
v_startPos_1558_ = v_basePos_1643_;
v_endPos_1559_ = v_nextStackPos_1646_;
goto v___jp_1556_;
}
}
}
else
{
lean_object* v___x_1650_; lean_object* v_nextStackPos_1651_; lean_object* v_nextNeedlePos_1652_; uint8_t v___x_1653_; 
lean_dec(v_basePos_1613_);
v___x_1650_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1651_ = lean_nat_add(v_stackPos_1602_, v___x_1650_);
lean_dec(v_stackPos_1602_);
v_nextNeedlePos_1652_ = lean_nat_add(v_needlePos_1603_, v___x_1650_);
lean_dec(v_needlePos_1603_);
v___x_1653_ = lean_nat_dec_eq(v_nextNeedlePos_1652_, v___x_1614_);
lean_dec(v___x_1614_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1655_; 
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 3, v_nextNeedlePos_1652_);
lean_ctor_set(v___x_1605_, 2, v_nextStackPos_1651_);
v___x_1655_ = v___x_1605_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_needle_1600_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_table_1601_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_nextStackPos_1651_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_nextNeedlePos_1652_);
v___x_1655_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
v_a_1554_ = v___x_1655_;
goto _start;
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
lean_dec(v_nextNeedlePos_1652_);
v___x_1658_ = lean_unsigned_to_nat(0u);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 3, v___x_1658_);
lean_ctor_set(v___x_1605_, 2, v_nextStackPos_1651_);
v___x_1660_ = v___x_1605_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_needle_1600_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_table_1601_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_nextStackPos_1651_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
v_it_1568_ = v___x_1660_;
goto v___jp_1567_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_1552_);
return v_b_1555_;
}
}
v___jp_1556_:
{
lean_object* v___x_1560_; lean_object* v_str_1561_; lean_object* v_startInclusive_1562_; lean_object* v_endExclusive_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_inc_ref(v_s_1552_);
v___x_1560_ = l_String_Slice_slice_x21(v_s_1552_, v_startPos_1558_, v_endPos_1559_);
lean_dec(v_endPos_1559_);
lean_dec(v_startPos_1558_);
v_str_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc_ref(v_str_1561_);
v_startInclusive_1562_ = lean_ctor_get(v___x_1560_, 1);
lean_inc(v_startInclusive_1562_);
v_endExclusive_1563_ = lean_ctor_get(v___x_1560_, 2);
lean_inc(v_endExclusive_1563_);
lean_dec_ref(v___x_1560_);
v___x_1564_ = lean_string_utf8_extract(v_str_1561_, v_startInclusive_1562_, v_endExclusive_1563_);
lean_dec(v_endExclusive_1563_);
lean_dec(v_startInclusive_1562_);
lean_dec_ref(v_str_1561_);
v___x_1565_ = lean_string_append(v_b_1555_, v___x_1564_);
lean_dec_ref(v___x_1564_);
v_a_1554_ = v_it_1557_;
v_b_1555_ = v___x_1565_;
goto _start;
}
v___jp_1567_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_string_utf8_byte_size(v_replacement_1553_);
v___x_1571_ = lean_string_utf8_extract(v_replacement_1553_, v___x_1569_, v___x_1570_);
v___x_1572_ = lean_string_append(v_b_1555_, v___x_1571_);
lean_dec_ref(v___x_1571_);
v_a_1554_ = v_it_1568_;
v_b_1555_ = v___x_1572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_s_1663_, lean_object* v_replacement_1664_, lean_object* v_a_1665_, lean_object* v_b_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8___redArg(v_s_1663_, v_replacement_1664_, v_a_1665_, v_b_1666_);
lean_dec_ref(v_replacement_1664_);
return v_res_1667_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_1670_ = lean_string_utf8_byte_size(v___x_1669_);
return v___x_1670_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1671_ = lean_unsigned_to_nat(0u);
v___x_1672_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_1673_ = lean_nat_dec_eq(v___x_1672_, v___x_1671_);
return v___x_1673_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1674_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_1677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v___x_1675_);
lean_ctor_set(v___x_1677_, 2, v___x_1674_);
return v___x_1677_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_1679_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1678_);
return v___x_1679_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1680_ = lean_unsigned_to_nat(0u);
v___x_1681_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__4);
v___x_1682_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_1683_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v___x_1681_);
lean_ctor_set(v___x_1683_, 2, v___x_1680_);
lean_ctor_set(v___x_1683_, 3, v___x_1680_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg(lean_object* v_s_1686_, lean_object* v_replacement_1687_){
_start:
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_1689_ = lean_uint8_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__2);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__5, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__5_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__5);
v___x_1691_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8___redArg(v_s_1686_, v_replacement_1687_, v___x_1690_, v___x_1688_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__6));
v___x_1693_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8___redArg(v_s_1686_, v_replacement_1687_, v___x_1692_, v___x_1688_);
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_s_1694_, lean_object* v_replacement_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg(v_s_1694_, v_replacement_1695_);
lean_dec_ref(v_replacement_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__3(lean_object* v_as_1704_, size_t v_sz_1705_, size_t v_i_1706_, lean_object* v_b_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_usize_dec_lt(v_i_1706_, v_sz_1705_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec_ref(v___y_1708_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v_b_1707_);
lean_ctor_set(v___x_1711_, 1, v___y_1709_);
return v___x_1711_;
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1713_; lean_object* v_snd_1714_; lean_object* v___x_1715_; size_t v___x_1716_; size_t v___x_1717_; 
v_a_1712_ = lean_array_uget_borrowed(v_as_1704_, v_i_1706_);
lean_inc_ref(v___y_1708_);
lean_inc(v_a_1712_);
v___x_1713_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2(v_a_1712_, v___y_1708_, v___y_1709_);
v_snd_1714_ = lean_ctor_get(v___x_1713_, 1);
lean_inc(v_snd_1714_);
lean_dec_ref(v___x_1713_);
v___x_1715_ = lean_box(0);
v___x_1716_ = ((size_t)1ULL);
v___x_1717_ = lean_usize_add(v_i_1706_, v___x_1716_);
v_i_1706_ = v___x_1717_;
v_b_1707_ = v___x_1715_;
v___y_1709_ = v_snd_1714_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__12));
v___x_1729_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_1730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
lean_ctor_set(v___x_1730_, 2, v___x_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2(lean_object* v_x_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
switch(lean_obj_tag(v_x_1732_))
{
case 0:
{
lean_object* v_string_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec_ref(v_a_1733_);
v_string_1735_ = lean_ctor_get(v_x_1732_, 0);
lean_inc_ref(v_string_1735_);
lean_dec_ref(v_x_1732_);
v___x_1736_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1735_);
lean_dec_ref(v_string_1735_);
v___x_1737_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1736_, v_a_1734_);
lean_dec_ref(v___x_1736_);
return v___x_1737_;
}
case 1:
{
lean_object* v_content_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1779_; 
v_content_1738_ = lean_ctor_get(v_x_1732_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_x_1732_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1740_ = v_x_1732_;
v_isShared_1741_ = v_isSharedCheck_1779_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_content_1738_);
lean_dec(v_x_1732_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1779_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set_tag(v___x_1740_, 9);
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_content_1738_);
v___x_1743_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; lean_object* v_snd_1745_; lean_object* v_fst_1746_; lean_object* v_fst_1747_; lean_object* v_snd_1748_; uint8_t v_inEmph_1750_; uint8_t v_inBold_1751_; uint8_t v_inLink_1752_; lean_object* v_linePrefix_1753_; lean_object* v___y_1754_; lean_object* v___x_1765_; uint8_t v_inEmph_1766_; 
v___x_1744_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1743_);
v_snd_1745_ = lean_ctor_get(v___x_1744_, 1);
lean_inc(v_snd_1745_);
v_fst_1746_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_fst_1746_);
lean_dec_ref(v___x_1744_);
v_fst_1747_ = lean_ctor_get(v_snd_1745_, 0);
lean_inc(v_fst_1747_);
v_snd_1748_ = lean_ctor_get(v_snd_1745_, 1);
lean_inc(v_snd_1748_);
lean_dec(v_snd_1745_);
v___x_1765_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_1746_, v_a_1734_);
lean_dec(v_fst_1746_);
v_inEmph_1766_ = lean_ctor_get_uint8(v_a_1733_, sizeof(void*)*1);
if (v_inEmph_1766_ == 0)
{
lean_object* v_snd_1767_; uint8_t v_inBold_1768_; uint8_t v_inLink_1769_; lean_object* v_linePrefix_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v_snd_1773_; 
v_snd_1767_ = lean_ctor_get(v___x_1765_, 1);
lean_inc(v_snd_1767_);
lean_dec_ref(v___x_1765_);
v_inBold_1768_ = lean_ctor_get_uint8(v_a_1733_, sizeof(void*)*1 + 1);
v_inLink_1769_ = lean_ctor_get_uint8(v_a_1733_, sizeof(void*)*1 + 2);
v_linePrefix_1770_ = lean_ctor_get(v_a_1733_, 0);
lean_inc_ref(v_linePrefix_1770_);
lean_dec_ref(v_a_1733_);
v___x_1771_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__0));
v___x_1772_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1771_, v_snd_1767_);
v_snd_1773_ = lean_ctor_get(v___x_1772_, 1);
lean_inc(v_snd_1773_);
lean_dec_ref(v___x_1772_);
v_inEmph_1750_ = v_inEmph_1766_;
v_inBold_1751_ = v_inBold_1768_;
v_inLink_1752_ = v_inLink_1769_;
v_linePrefix_1753_ = v_linePrefix_1770_;
v___y_1754_ = v_snd_1773_;
goto v___jp_1749_;
}
else
{
lean_object* v_snd_1774_; uint8_t v_inBold_1775_; uint8_t v_inLink_1776_; lean_object* v_linePrefix_1777_; 
v_snd_1774_ = lean_ctor_get(v___x_1765_, 1);
lean_inc(v_snd_1774_);
lean_dec_ref(v___x_1765_);
v_inBold_1775_ = lean_ctor_get_uint8(v_a_1733_, sizeof(void*)*1 + 1);
v_inLink_1776_ = lean_ctor_get_uint8(v_a_1733_, sizeof(void*)*1 + 2);
v_linePrefix_1777_ = lean_ctor_get(v_a_1733_, 0);
lean_inc_ref(v_linePrefix_1777_);
lean_dec_ref(v_a_1733_);
v_inEmph_1750_ = v_inEmph_1766_;
v_inBold_1751_ = v_inBold_1775_;
v_inLink_1752_ = v_inLink_1776_;
v_linePrefix_1753_ = v_linePrefix_1777_;
v___y_1754_ = v_snd_1774_;
goto v___jp_1749_;
}
v___jp_1749_:
{
uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = 1;
v___x_1756_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1756_, 0, v_linePrefix_1753_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*1, v___x_1755_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*1 + 1, v_inBold_1751_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*1 + 2, v_inLink_1752_);
v___x_1757_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2(v_fst_1747_, v___x_1756_, v___y_1754_);
if (v_inEmph_1750_ == 0)
{
lean_object* v_snd_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_snd_1761_; lean_object* v___x_1762_; 
v_snd_1758_ = lean_ctor_get(v___x_1757_, 1);
lean_inc(v_snd_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__0));
v___x_1760_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1759_, v_snd_1758_);
v_snd_1761_ = lean_ctor_get(v___x_1760_, 1);
lean_inc(v_snd_1761_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1748_, v_snd_1761_);
lean_dec(v_snd_1748_);
return v___x_1762_;
}
else
{
lean_object* v_snd_1763_; lean_object* v___x_1764_; 
v_snd_1763_ = lean_ctor_get(v___x_1757_, 1);
lean_inc(v_snd_1763_);
lean_dec_ref(v___x_1757_);
v___x_1764_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1748_, v_snd_1763_);
lean_dec(v_snd_1748_);
return v___x_1764_;
}
}
}
}
}
case 2:
{
lean_object* v_content_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1818_; 
v_content_1780_ = lean_ctor_get(v_x_1732_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_x_1732_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1782_ = v_x_1732_;
v_isShared_1783_ = v_isSharedCheck_1818_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_content_1780_);
lean_dec(v_x_1732_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1818_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set_tag(v___x_1782_, 9);
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_content_1780_);
v___x_1785_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1786_; lean_object* v_snd_1787_; lean_object* v_fst_1788_; lean_object* v_fst_1789_; lean_object* v_snd_1790_; uint8_t v_inBold_1792_; uint8_t v_inLink_1793_; lean_object* v_linePrefix_1794_; lean_object* v___y_1795_; lean_object* v___x_1806_; uint8_t v_inBold_1807_; 
v___x_1786_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1785_);
v_snd_1787_ = lean_ctor_get(v___x_1786_, 1);
lean_inc(v_snd_1787_);
v_fst_1788_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_fst_1788_);
lean_dec_ref(v___x_1786_);
v_fst_1789_ = lean_ctor_get(v_snd_1787_, 0);
lean_inc(v_fst_1789_);
v_snd_1790_ = lean_ctor_get(v_snd_1787_, 1);
lean_inc(v_snd_1790_);
lean_dec(v_snd_1787_);
v___x_1806_ = l_Lean_Doc_MarkdownM_push___redArg(v_fst_1788_, v_a_1734_);
lean_dec(v_fst_1788_);
v_inBold_1807_ = lean_ctor_get_uint8(v_a_1733_, sizeof(void*)*1 + 1);
if (v_inBold_1807_ == 0)
{
lean_object* v_snd_1808_; uint8_t v_inLink_1809_; lean_object* v_linePrefix_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v_snd_1813_; 
v_snd_1808_ = lean_ctor_get(v___x_1806_, 1);
lean_inc(v_snd_1808_);
lean_dec_ref(v___x_1806_);
v_inLink_1809_ = lean_ctor_get_uint8(v_a_1733_, sizeof(void*)*1 + 2);
v_linePrefix_1810_ = lean_ctor_get(v_a_1733_, 0);
lean_inc_ref(v_linePrefix_1810_);
lean_dec_ref(v_a_1733_);
v___x_1811_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__1));
v___x_1812_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1811_, v_snd_1808_);
v_snd_1813_ = lean_ctor_get(v___x_1812_, 1);
lean_inc(v_snd_1813_);
lean_dec_ref(v___x_1812_);
v_inBold_1792_ = v_inBold_1807_;
v_inLink_1793_ = v_inLink_1809_;
v_linePrefix_1794_ = v_linePrefix_1810_;
v___y_1795_ = v_snd_1813_;
goto v___jp_1791_;
}
else
{
lean_object* v_snd_1814_; uint8_t v_inLink_1815_; lean_object* v_linePrefix_1816_; 
v_snd_1814_ = lean_ctor_get(v___x_1806_, 1);
lean_inc(v_snd_1814_);
lean_dec_ref(v___x_1806_);
v_inLink_1815_ = lean_ctor_get_uint8(v_a_1733_, sizeof(void*)*1 + 2);
v_linePrefix_1816_ = lean_ctor_get(v_a_1733_, 0);
lean_inc_ref(v_linePrefix_1816_);
lean_dec_ref(v_a_1733_);
v_inBold_1792_ = v_inBold_1807_;
v_inLink_1793_ = v_inLink_1815_;
v_linePrefix_1794_ = v_linePrefix_1816_;
v___y_1795_ = v_snd_1814_;
goto v___jp_1791_;
}
v___jp_1791_:
{
uint8_t v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = 1;
v___x_1797_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1797_, 0, v_linePrefix_1794_);
lean_ctor_set_uint8(v___x_1797_, sizeof(void*)*1, v___x_1796_);
lean_ctor_set_uint8(v___x_1797_, sizeof(void*)*1 + 1, v_inBold_1792_);
lean_ctor_set_uint8(v___x_1797_, sizeof(void*)*1 + 2, v_inLink_1793_);
v___x_1798_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2(v_fst_1789_, v___x_1797_, v___y_1795_);
if (v_inBold_1792_ == 0)
{
lean_object* v_snd_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v_snd_1802_; lean_object* v___x_1803_; 
v_snd_1799_ = lean_ctor_get(v___x_1798_, 1);
lean_inc(v_snd_1799_);
lean_dec_ref(v___x_1798_);
v___x_1800_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__1));
v___x_1801_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1800_, v_snd_1799_);
v_snd_1802_ = lean_ctor_get(v___x_1801_, 1);
lean_inc(v_snd_1802_);
lean_dec_ref(v___x_1801_);
v___x_1803_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1790_, v_snd_1802_);
lean_dec(v_snd_1790_);
return v___x_1803_;
}
else
{
lean_object* v_snd_1804_; lean_object* v___x_1805_; 
v_snd_1804_ = lean_ctor_get(v___x_1798_, 1);
lean_inc(v_snd_1804_);
lean_dec_ref(v___x_1798_);
v___x_1805_ = l_Lean_Doc_MarkdownM_push___redArg(v_snd_1790_, v_snd_1804_);
lean_dec(v_snd_1790_);
return v___x_1805_;
}
}
}
}
}
case 3:
{
lean_object* v_string_1819_; lean_object* v___y_1821_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v_fst_1826_; uint8_t v___x_1827_; 
lean_dec_ref(v_a_1733_);
v_string_1819_ = lean_ctor_get(v_x_1732_, 0);
lean_inc_ref(v_string_1819_);
lean_dec_ref(v_x_1732_);
v___x_1824_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__2));
v___x_1825_ = l_Lean_Doc_MarkdownM_endsWith___redArg(v___x_1824_, v_a_1734_);
v_fst_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_fst_1826_);
v___x_1827_ = lean_unbox(v_fst_1826_);
lean_dec(v_fst_1826_);
if (v___x_1827_ == 0)
{
lean_object* v_snd_1828_; 
v_snd_1828_ = lean_ctor_get(v___x_1825_, 1);
lean_inc(v_snd_1828_);
lean_dec_ref(v___x_1825_);
v___y_1821_ = v_snd_1828_;
goto v___jp_1820_;
}
else
{
lean_object* v_snd_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v_snd_1832_; 
v_snd_1829_ = lean_ctor_get(v___x_1825_, 1);
lean_inc(v_snd_1829_);
lean_dec_ref(v___x_1825_);
v___x_1830_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__3));
v___x_1831_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1830_, v_snd_1829_);
v_snd_1832_ = lean_ctor_get(v___x_1831_, 1);
lean_inc(v_snd_1832_);
lean_dec_ref(v___x_1831_);
v___y_1821_ = v_snd_1832_;
goto v___jp_1820_;
}
v___jp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1819_);
v___x_1823_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1822_, v___y_1821_);
lean_dec_ref(v___x_1822_);
return v___x_1823_;
}
}
case 4:
{
uint8_t v_mode_1833_; 
lean_dec_ref(v_a_1733_);
v_mode_1833_ = lean_ctor_get_uint8(v_x_1732_, sizeof(void*)*1);
if (v_mode_1833_ == 0)
{
lean_object* v_string_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v_string_1834_ = lean_ctor_get(v_x_1732_, 0);
lean_inc_ref(v_string_1834_);
lean_dec_ref(v_x_1732_);
v___x_1835_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__4));
v___x_1836_ = lean_string_append(v___x_1835_, v_string_1834_);
lean_dec_ref(v_string_1834_);
v___x_1837_ = lean_string_append(v___x_1836_, v___x_1835_);
v___x_1838_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1837_, v_a_1734_);
lean_dec_ref(v___x_1837_);
return v___x_1838_;
}
else
{
lean_object* v_string_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v_string_1839_ = lean_ctor_get(v_x_1732_, 0);
lean_inc_ref(v_string_1839_);
lean_dec_ref(v_x_1732_);
v___x_1840_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__5));
v___x_1841_ = lean_string_append(v___x_1840_, v_string_1839_);
lean_dec_ref(v_string_1839_);
v___x_1842_ = lean_string_append(v___x_1841_, v___x_1840_);
v___x_1843_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1842_, v_a_1734_);
lean_dec_ref(v___x_1842_);
return v___x_1843_;
}
}
case 5:
{
lean_object* v_string_1844_; lean_object* v_linePrefix_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_string_1844_ = lean_ctor_get(v_x_1732_, 0);
lean_inc_ref(v_string_1844_);
lean_dec_ref(v_x_1732_);
v_linePrefix_1845_ = lean_ctor_get(v_a_1733_, 0);
lean_inc_ref(v_linePrefix_1845_);
lean_dec_ref(v_a_1733_);
v___x_1846_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_1847_ = lean_string_append(v___x_1846_, v_linePrefix_1845_);
lean_dec_ref(v_linePrefix_1845_);
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = lean_string_utf8_byte_size(v_string_1844_);
v___x_1850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1850_, 0, v_string_1844_);
lean_ctor_set(v___x_1850_, 1, v___x_1848_);
lean_ctor_set(v___x_1850_, 2, v___x_1849_);
v___x_1851_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg(v___x_1850_, v___x_1847_);
lean_dec_ref(v___x_1847_);
v___x_1852_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1851_, v_a_1734_);
lean_dec_ref(v___x_1851_);
return v___x_1852_;
}
case 6:
{
uint8_t v_inLink_1853_; 
v_inLink_1853_ = lean_ctor_get_uint8(v_a_1733_, sizeof(void*)*1 + 2);
if (v_inLink_1853_ == 0)
{
lean_object* v_content_1854_; lean_object* v_url_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v_snd_1858_; lean_object* v___x_1859_; size_t v_sz_1860_; size_t v___x_1861_; lean_object* v___x_1862_; lean_object* v_snd_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v_snd_1866_; lean_object* v___x_1867_; lean_object* v_snd_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_content_1854_ = lean_ctor_get(v_x_1732_, 0);
lean_inc_ref(v_content_1854_);
v_url_1855_ = lean_ctor_get(v_x_1732_, 1);
lean_inc_ref(v_url_1855_);
lean_dec_ref(v_x_1732_);
v___x_1856_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__6));
v___x_1857_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1856_, v_a_1734_);
v_snd_1858_ = lean_ctor_get(v___x_1857_, 1);
lean_inc(v_snd_1858_);
lean_dec_ref(v___x_1857_);
v___x_1859_ = lean_box(0);
v_sz_1860_ = lean_array_size(v_content_1854_);
v___x_1861_ = ((size_t)0ULL);
v___x_1862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__3(v_content_1854_, v_sz_1860_, v___x_1861_, v___x_1859_, v_a_1733_, v_snd_1858_);
lean_dec_ref(v_content_1854_);
v_snd_1863_ = lean_ctor_get(v___x_1862_, 1);
lean_inc(v_snd_1863_);
lean_dec_ref(v___x_1862_);
v___x_1864_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__7));
v___x_1865_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1864_, v_snd_1863_);
v_snd_1866_ = lean_ctor_get(v___x_1865_, 1);
lean_inc(v_snd_1866_);
lean_dec_ref(v___x_1865_);
v___x_1867_ = l_Lean_Doc_MarkdownM_push___redArg(v_url_1855_, v_snd_1866_);
lean_dec_ref(v_url_1855_);
v_snd_1868_ = lean_ctor_get(v___x_1867_, 1);
lean_inc(v_snd_1868_);
lean_dec_ref(v___x_1867_);
v___x_1869_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__8));
v___x_1870_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1869_, v_snd_1868_);
return v___x_1870_;
}
else
{
lean_object* v_content_1871_; lean_object* v___x_1872_; size_t v_sz_1873_; size_t v___x_1874_; lean_object* v___x_1875_; lean_object* v_snd_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
v_content_1871_ = lean_ctor_get(v_x_1732_, 0);
lean_inc_ref(v_content_1871_);
lean_dec_ref(v_x_1732_);
v___x_1872_ = lean_box(0);
v_sz_1873_ = lean_array_size(v_content_1871_);
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__3(v_content_1871_, v_sz_1873_, v___x_1874_, v___x_1872_, v_a_1733_, v_a_1734_);
lean_dec_ref(v_content_1871_);
v_snd_1876_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1883_ == 0)
{
lean_object* v_unused_1884_; 
v_unused_1884_ = lean_ctor_get(v___x_1875_, 0);
lean_dec(v_unused_1884_);
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_snd_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1872_);
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_snd_1876_);
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
case 7:
{
lean_object* v_name_1885_; lean_object* v_content_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v_snd_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1931_; 
lean_dec_ref(v_a_1733_);
v_name_1885_ = lean_ctor_get(v_x_1732_, 0);
lean_inc_ref(v_name_1885_);
v_content_1886_ = lean_ctor_get(v_x_1732_, 1);
lean_inc_ref(v_content_1886_);
lean_dec_ref(v_x_1732_);
v___x_1887_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__9));
v___x_1888_ = lean_string_append(v___x_1887_, v_name_1885_);
v___x_1889_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__10));
v___x_1890_ = lean_string_append(v___x_1888_, v___x_1889_);
v___x_1891_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1890_, v_a_1734_);
lean_dec_ref(v___x_1890_);
v_snd_1892_ = lean_ctor_get(v___x_1891_, 1);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v___x_1891_, 0);
lean_dec(v_unused_1932_);
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_1931_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_snd_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1931_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v_snd_1897_; lean_object* v___y_1916_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1918_ = lean_unsigned_to_nat(0u);
v___x_1919_ = lean_array_get_size(v_content_1886_);
v___x_1920_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__11));
v___x_1921_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__13, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__13_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__13);
v___x_1922_ = lean_nat_dec_lt(v___x_1918_, v___x_1919_);
if (v___x_1922_ == 0)
{
lean_dec_ref(v_content_1886_);
v_snd_1897_ = v___x_1921_;
goto v___jp_1896_;
}
else
{
lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1923_ = lean_box(0);
v___x_1924_ = lean_nat_dec_le(v___x_1919_, v___x_1919_);
if (v___x_1924_ == 0)
{
if (v___x_1922_ == 0)
{
lean_dec_ref(v_content_1886_);
v_snd_1897_ = v___x_1921_;
goto v___jp_1896_;
}
else
{
size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = ((size_t)0ULL);
v___x_1926_ = lean_usize_of_nat(v___x_1919_);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__6(v_content_1886_, v___x_1925_, v___x_1926_, v___x_1923_, v___x_1920_, v___x_1921_);
lean_dec_ref(v_content_1886_);
v___y_1916_ = v___x_1927_;
goto v___jp_1915_;
}
}
else
{
size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = ((size_t)0ULL);
v___x_1929_ = lean_usize_of_nat(v___x_1919_);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__6(v_content_1886_, v___x_1928_, v___x_1929_, v___x_1923_, v___x_1920_, v___x_1921_);
lean_dec_ref(v_content_1886_);
v___y_1916_ = v___x_1930_;
goto v___jp_1915_;
}
}
v___jp_1896_:
{
lean_object* v_priorBlocks_1898_; lean_object* v_currentBlock_1899_; lean_object* v_footnotes_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1914_; 
v_priorBlocks_1898_ = lean_ctor_get(v_snd_1892_, 0);
v_currentBlock_1899_ = lean_ctor_get(v_snd_1892_, 1);
v_footnotes_1900_ = lean_ctor_get(v_snd_1892_, 2);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_snd_1892_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1902_ = v_snd_1892_;
v_isShared_1903_ = v_isSharedCheck_1914_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_footnotes_1900_);
lean_inc(v_currentBlock_1899_);
lean_inc(v_priorBlocks_1898_);
lean_dec(v_snd_1892_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1914_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1904_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_State_render(v_snd_1897_);
v___x_1905_ = lean_box(0);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v___x_1904_);
lean_ctor_set(v___x_1894_, 0, v_name_1885_);
v___x_1907_ = v___x_1894_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_name_1885_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1904_);
v___x_1907_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1908_ = lean_array_push(v_footnotes_1900_, v___x_1907_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 2, v___x_1908_);
v___x_1910_ = v___x_1902_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_priorBlocks_1898_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_currentBlock_1899_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1905_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
return v___x_1911_;
}
}
}
}
v___jp_1915_:
{
lean_object* v_snd_1917_; 
v_snd_1917_ = lean_ctor_get(v___y_1916_, 1);
lean_inc(v_snd_1917_);
lean_dec_ref(v___y_1916_);
v_snd_1897_ = v_snd_1917_;
goto v___jp_1896_;
}
}
}
case 8:
{
lean_object* v_alt_1933_; lean_object* v_url_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
lean_dec_ref(v_a_1733_);
v_alt_1933_ = lean_ctor_get(v_x_1732_, 0);
lean_inc_ref(v_alt_1933_);
v_url_1934_ = lean_ctor_get(v_x_1732_, 1);
lean_inc_ref(v_url_1934_);
lean_dec_ref(v_x_1732_);
v___x_1935_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__14));
v___x_1936_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1933_);
lean_dec_ref(v_alt_1933_);
v___x_1937_ = lean_string_append(v___x_1935_, v___x_1936_);
lean_dec_ref(v___x_1936_);
v___x_1938_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__7));
v___x_1939_ = lean_string_append(v___x_1937_, v___x_1938_);
v___x_1940_ = lean_string_append(v___x_1939_, v_url_1934_);
lean_dec_ref(v_url_1934_);
v___x_1941_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__8));
v___x_1942_ = lean_string_append(v___x_1940_, v___x_1941_);
v___x_1943_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_1942_, v_a_1734_);
lean_dec_ref(v___x_1942_);
return v___x_1943_;
}
case 9:
{
lean_object* v_content_1944_; lean_object* v___x_1945_; size_t v_sz_1946_; size_t v___x_1947_; lean_object* v___x_1948_; lean_object* v_snd_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
v_content_1944_ = lean_ctor_get(v_x_1732_, 0);
lean_inc_ref(v_content_1944_);
lean_dec_ref(v_x_1732_);
v___x_1945_ = lean_box(0);
v_sz_1946_ = lean_array_size(v_content_1944_);
v___x_1947_ = ((size_t)0ULL);
v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__3(v_content_1944_, v_sz_1946_, v___x_1947_, v___x_1945_, v_a_1733_, v_a_1734_);
lean_dec_ref(v_content_1944_);
v_snd_1949_ = lean_ctor_get(v___x_1948_, 1);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; 
v_unused_1957_ = lean_ctor_get(v___x_1948_, 0);
lean_dec(v_unused_1957_);
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_snd_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1945_);
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1945_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_snd_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
default: 
{
lean_object* v_content_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v_content_1958_ = lean_ctor_get(v_x_1732_, 1);
lean_inc_ref(v_content_1958_);
lean_dec_ref(v_x_1732_);
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = lean_array_get_size(v_content_1958_);
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_nat_dec_lt(v___x_1959_, v___x_1960_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
lean_dec_ref(v_content_1958_);
lean_dec_ref(v_a_1733_);
v___x_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v_a_1734_);
return v___x_1963_;
}
else
{
uint8_t v___x_1964_; 
v___x_1964_ = lean_nat_dec_le(v___x_1960_, v___x_1960_);
if (v___x_1964_ == 0)
{
if (v___x_1962_ == 0)
{
lean_object* v___x_1965_; 
lean_dec_ref(v_content_1958_);
lean_dec_ref(v_a_1733_);
v___x_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1961_);
lean_ctor_set(v___x_1965_, 1, v_a_1734_);
return v___x_1965_;
}
else
{
size_t v___x_1966_; size_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = ((size_t)0ULL);
v___x_1967_ = lean_usize_of_nat(v___x_1960_);
v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__6(v_content_1958_, v___x_1966_, v___x_1967_, v___x_1961_, v_a_1733_, v_a_1734_);
lean_dec_ref(v_content_1958_);
return v___x_1968_;
}
}
else
{
size_t v___x_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = ((size_t)0ULL);
v___x_1970_ = lean_usize_of_nat(v___x_1960_);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__6(v_content_1958_, v___x_1969_, v___x_1970_, v___x_1961_, v_a_1733_, v_a_1734_);
lean_dec_ref(v_content_1958_);
return v___x_1971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__6(lean_object* v_as_1972_, size_t v_i_1973_, size_t v_stop_1974_, lean_object* v_b_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_usize_dec_eq(v_i_1973_, v_stop_1974_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v_fst_1981_; lean_object* v_snd_1982_; size_t v___x_1983_; size_t v___x_1984_; 
v___x_1979_ = lean_array_uget_borrowed(v_as_1972_, v_i_1973_);
lean_inc_ref(v___y_1976_);
lean_inc(v___x_1979_);
v___x_1980_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2(v___x_1979_, v___y_1976_, v___y_1977_);
v_fst_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_fst_1981_);
v_snd_1982_ = lean_ctor_get(v___x_1980_, 1);
lean_inc(v_snd_1982_);
lean_dec_ref(v___x_1980_);
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1973_, v___x_1983_);
v_i_1973_ = v___x_1984_;
v_b_1975_ = v_fst_1981_;
v___y_1977_ = v_snd_1982_;
goto _start;
}
else
{
lean_object* v___x_1986_; 
lean_dec_ref(v___y_1976_);
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v_b_1975_);
lean_ctor_set(v___x_1986_, 1, v___y_1977_);
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__6___boxed(lean_object* v_as_1987_, lean_object* v_i_1988_, lean_object* v_stop_1989_, lean_object* v_b_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
size_t v_i_boxed_1993_; size_t v_stop_boxed_1994_; lean_object* v_res_1995_; 
v_i_boxed_1993_ = lean_unbox_usize(v_i_1988_);
lean_dec(v_i_1988_);
v_stop_boxed_1994_ = lean_unbox_usize(v_stop_1989_);
lean_dec(v_stop_1989_);
v_res_1995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__6(v_as_1987_, v_i_boxed_1993_, v_stop_boxed_1994_, v_b_1990_, v___y_1991_, v___y_1992_);
lean_dec_ref(v_as_1987_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__3___boxed(lean_object* v_as_1996_, lean_object* v_sz_1997_, lean_object* v_i_1998_, lean_object* v_b_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
size_t v_sz_boxed_2002_; size_t v_i_boxed_2003_; lean_object* v_res_2004_; 
v_sz_boxed_2002_ = lean_unbox_usize(v_sz_1997_);
lean_dec(v_sz_1997_);
v_i_boxed_2003_ = lean_unbox_usize(v_i_1998_);
lean_dec(v_i_1998_);
v_res_2004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__3(v_as_1996_, v_sz_boxed_2002_, v_i_boxed_2003_, v_b_1999_, v___y_2000_, v___y_2001_);
lean_dec_ref(v_as_1996_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(lean_object* v_as_2007_, size_t v_sz_2008_, size_t v_i_2009_, lean_object* v_b_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_usize_dec_lt(v_i_2009_, v_sz_2008_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
lean_dec_ref(v___y_2011_);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v_b_2010_);
lean_ctor_set(v___x_2014_, 1, v___y_2012_);
return v___x_2014_;
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2016_; lean_object* v_snd_2017_; lean_object* v___x_2018_; size_t v___x_2019_; size_t v___x_2020_; 
v_a_2015_ = lean_array_uget_borrowed(v_as_2007_, v_i_2009_);
lean_inc_ref(v___y_2011_);
lean_inc(v_a_2015_);
v___x_2016_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v_a_2015_, v___y_2011_, v___y_2012_);
v_snd_2017_ = lean_ctor_get(v___x_2016_, 1);
lean_inc(v_snd_2017_);
lean_dec_ref(v___x_2016_);
v___x_2018_ = lean_box(0);
v___x_2019_ = ((size_t)1ULL);
v___x_2020_ = lean_usize_add(v_i_2009_, v___x_2019_);
v_i_2009_ = v___x_2020_;
v_b_2010_ = v___x_2018_;
v___y_2012_ = v_snd_2017_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4(lean_object* v_as_2022_, size_t v_sz_2023_, size_t v_i_2024_, lean_object* v_b_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_usize_dec_lt(v_i_2024_, v_sz_2023_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
lean_dec_ref(v___y_2026_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_b_2025_);
lean_ctor_set(v___x_2029_, 1, v___y_2027_);
return v___x_2029_;
}
else
{
uint8_t v_inEmph_2030_; uint8_t v_inBold_2031_; uint8_t v_inLink_2032_; lean_object* v_linePrefix_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v_snd_2037_; lean_object* v___x_2038_; lean_object* v_a_2039_; size_t v_sz_2040_; size_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v_snd_2046_; size_t v___x_2047_; size_t v___x_2048_; 
v_inEmph_2030_ = lean_ctor_get_uint8(v___y_2026_, sizeof(void*)*1);
v_inBold_2031_ = lean_ctor_get_uint8(v___y_2026_, sizeof(void*)*1 + 1);
v_inLink_2032_ = lean_ctor_get_uint8(v___y_2026_, sizeof(void*)*1 + 2);
v_linePrefix_2033_ = lean_ctor_get(v___y_2026_, 0);
v___x_2034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___closed__0));
lean_inc_ref(v_linePrefix_2033_);
v___x_2035_ = lean_string_append(v_linePrefix_2033_, v___x_2034_);
v___x_2036_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2035_, v___y_2027_);
lean_dec_ref(v___x_2035_);
v_snd_2037_ = lean_ctor_get(v___x_2036_, 1);
lean_inc(v_snd_2037_);
lean_dec_ref(v___x_2036_);
v___x_2038_ = lean_box(0);
v_a_2039_ = lean_array_uget_borrowed(v_as_2022_, v_i_2024_);
v_sz_2040_ = lean_array_size(v_a_2039_);
v___x_2041_ = ((size_t)0ULL);
v___x_2042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___closed__1));
lean_inc_ref(v_linePrefix_2033_);
v___x_2043_ = lean_string_append(v_linePrefix_2033_, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*1, v_inEmph_2030_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*1 + 1, v_inBold_2031_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*1 + 2, v_inLink_2032_);
v___x_2045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_a_2039_, v_sz_2040_, v___x_2041_, v___x_2038_, v___x_2044_, v_snd_2037_);
v_snd_2046_ = lean_ctor_get(v___x_2045_, 1);
lean_inc(v_snd_2046_);
lean_dec_ref(v___x_2045_);
v___x_2047_ = ((size_t)1ULL);
v___x_2048_ = lean_usize_add(v_i_2024_, v___x_2047_);
v_i_2024_ = v___x_2048_;
v_b_2025_ = v___x_2038_;
v___y_2027_ = v_snd_2046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(lean_object* v_as_2051_, size_t v_sz_2052_, size_t v_i_2053_, lean_object* v_b_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
uint8_t v___x_2057_; 
v___x_2057_ = lean_usize_dec_lt(v_i_2053_, v_sz_2052_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; 
lean_dec_ref(v___y_2055_);
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v_b_2054_);
lean_ctor_set(v___x_2058_, 1, v___y_2056_);
return v___x_2058_;
}
else
{
uint8_t v_inEmph_2059_; uint8_t v_inBold_2060_; uint8_t v_inLink_2061_; lean_object* v_linePrefix_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v_snd_2068_; lean_object* v_a_2069_; lean_object* v___x_2070_; size_t v_sz_2071_; size_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v_snd_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; size_t v___x_2080_; size_t v___x_2081_; 
v_inEmph_2059_ = lean_ctor_get_uint8(v___y_2055_, sizeof(void*)*1);
v_inBold_2060_ = lean_ctor_get_uint8(v___y_2055_, sizeof(void*)*1 + 1);
v_inLink_2061_ = lean_ctor_get_uint8(v___y_2055_, sizeof(void*)*1 + 2);
v_linePrefix_2062_ = lean_ctor_get(v___y_2055_, 0);
lean_inc(v_b_2054_);
v___x_2063_ = l_Nat_reprFast(v_b_2054_);
v___x_2064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___closed__0));
v___x_2065_ = lean_string_append(v___x_2063_, v___x_2064_);
lean_inc_ref(v_linePrefix_2062_);
v___x_2066_ = lean_string_append(v_linePrefix_2062_, v___x_2065_);
lean_dec_ref(v___x_2065_);
v___x_2067_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2066_, v___y_2056_);
lean_dec_ref(v___x_2066_);
v_snd_2068_ = lean_ctor_get(v___x_2067_, 1);
lean_inc(v_snd_2068_);
lean_dec_ref(v___x_2067_);
v_a_2069_ = lean_array_uget_borrowed(v_as_2051_, v_i_2053_);
v___x_2070_ = lean_box(0);
v_sz_2071_ = lean_array_size(v_a_2069_);
v___x_2072_ = ((size_t)0ULL);
v___x_2073_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___closed__1));
lean_inc_ref(v_linePrefix_2062_);
v___x_2074_ = lean_string_append(v_linePrefix_2062_, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
lean_ctor_set_uint8(v___x_2075_, sizeof(void*)*1, v_inEmph_2059_);
lean_ctor_set_uint8(v___x_2075_, sizeof(void*)*1 + 1, v_inBold_2060_);
lean_ctor_set_uint8(v___x_2075_, sizeof(void*)*1 + 2, v_inLink_2061_);
v___x_2076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_a_2069_, v_sz_2071_, v___x_2072_, v___x_2070_, v___x_2075_, v_snd_2068_);
v_snd_2077_ = lean_ctor_get(v___x_2076_, 1);
lean_inc(v_snd_2077_);
lean_dec_ref(v___x_2076_);
v___x_2078_ = lean_unsigned_to_nat(1u);
v___x_2079_ = lean_nat_add(v_b_2054_, v___x_2078_);
lean_dec(v_b_2054_);
v___x_2080_ = ((size_t)1ULL);
v___x_2081_ = lean_usize_add(v_i_2053_, v___x_2080_);
v_i_2053_ = v___x_2081_;
v_b_2054_ = v___x_2079_;
v___y_2056_ = v_snd_2077_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(lean_object* v_as_2086_, size_t v_sz_2087_, size_t v_i_2088_, lean_object* v_b_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
uint8_t v___x_2092_; 
v___x_2092_ = lean_usize_dec_lt(v_i_2088_, v_sz_2087_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
lean_dec_ref(v___y_2090_);
v___x_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2093_, 0, v_b_2089_);
lean_ctor_set(v___x_2093_, 1, v___y_2091_);
return v___x_2093_;
}
else
{
uint8_t v_inEmph_2094_; uint8_t v_inBold_2095_; uint8_t v_inLink_2096_; lean_object* v_linePrefix_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v_snd_2101_; lean_object* v_a_2102_; lean_object* v_term_2103_; lean_object* v_desc_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v_snd_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_snd_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v_snd_2116_; lean_object* v___x_2117_; lean_object* v_snd_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v_snd_2121_; lean_object* v___x_2122_; size_t v___x_2123_; size_t v___x_2124_; 
v_inEmph_2094_ = lean_ctor_get_uint8(v___y_2090_, sizeof(void*)*1);
v_inBold_2095_ = lean_ctor_get_uint8(v___y_2090_, sizeof(void*)*1 + 1);
v_inLink_2096_ = lean_ctor_get_uint8(v___y_2090_, sizeof(void*)*1 + 2);
v_linePrefix_2097_ = lean_ctor_get(v___y_2090_, 0);
v___x_2098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___closed__0));
lean_inc_ref(v_linePrefix_2097_);
v___x_2099_ = lean_string_append(v_linePrefix_2097_, v___x_2098_);
v___x_2100_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2099_, v___y_2091_);
lean_dec_ref(v___x_2099_);
v_snd_2101_ = lean_ctor_get(v___x_2100_, 1);
lean_inc(v_snd_2101_);
lean_dec_ref(v___x_2100_);
v_a_2102_ = lean_array_uget_borrowed(v_as_2086_, v_i_2088_);
v_term_2103_ = lean_ctor_get(v_a_2102_, 0);
v_desc_2104_ = lean_ctor_get(v_a_2102_, 1);
lean_inc_ref(v_term_2103_);
v___x_2105_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2105_, 0, v_term_2103_);
v___x_2106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___closed__1));
lean_inc_ref(v_linePrefix_2097_);
v___x_2107_ = lean_string_append(v_linePrefix_2097_, v___x_2106_);
lean_inc_ref(v___x_2107_);
v___x_2108_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*1, v_inEmph_2094_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*1 + 1, v_inBold_2095_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*1 + 2, v_inLink_2096_);
lean_inc_ref(v___x_2108_);
v___x_2109_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2(v___x_2105_, v___x_2108_, v_snd_2101_);
v_snd_2110_ = lean_ctor_get(v___x_2109_, 1);
lean_inc(v_snd_2110_);
lean_dec_ref(v___x_2109_);
v___x_2111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__1));
lean_inc_ref(v___x_2108_);
v___x_2112_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2(v___x_2111_, v___x_2108_, v_snd_2110_);
v_snd_2113_ = lean_ctor_get(v___x_2112_, 1);
lean_inc(v_snd_2113_);
lean_dec_ref(v___x_2112_);
v___x_2114_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2115_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2114_, v_snd_2113_);
v_snd_2116_ = lean_ctor_get(v___x_2115_, 1);
lean_inc(v_snd_2116_);
lean_dec_ref(v___x_2115_);
v___x_2117_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2107_, v_snd_2116_);
lean_dec_ref(v___x_2107_);
v_snd_2118_ = lean_ctor_get(v___x_2117_, 1);
lean_inc(v_snd_2118_);
lean_dec_ref(v___x_2117_);
lean_inc_ref(v_desc_2104_);
v___x_2119_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2119_, 0, v_desc_2104_);
v___x_2120_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v___x_2119_, v___x_2108_, v_snd_2118_);
v_snd_2121_ = lean_ctor_get(v___x_2120_, 1);
lean_inc(v_snd_2121_);
lean_dec_ref(v___x_2120_);
v___x_2122_ = lean_box(0);
v___x_2123_ = ((size_t)1ULL);
v___x_2124_ = lean_usize_add(v_i_2088_, v___x_2123_);
v_i_2088_ = v___x_2124_;
v_b_2089_ = v___x_2122_;
v___y_2091_ = v_snd_2121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(lean_object* v_x_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
switch(lean_obj_tag(v_x_2127_))
{
case 0:
{
lean_object* v_contents_2130_; lean_object* v___x_2131_; size_t v_sz_2132_; size_t v___x_2133_; lean_object* v___x_2134_; lean_object* v_snd_2135_; lean_object* v___x_2136_; 
v_contents_2130_ = lean_ctor_get(v_x_2127_, 0);
lean_inc_ref(v_contents_2130_);
lean_dec_ref(v_x_2127_);
v___x_2131_ = lean_box(0);
v_sz_2132_ = lean_array_size(v_contents_2130_);
v___x_2133_ = ((size_t)0ULL);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__3(v_contents_2130_, v_sz_2132_, v___x_2133_, v___x_2131_, v_a_2128_, v_a_2129_);
lean_dec_ref(v_contents_2130_);
v_snd_2135_ = lean_ctor_get(v___x_2134_, 1);
lean_inc(v_snd_2135_);
lean_dec_ref(v___x_2134_);
v___x_2136_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2135_);
return v___x_2136_;
}
case 1:
{
lean_object* v_content_2137_; lean_object* v___y_2139_; lean_object* v___y_2140_; uint8_t v___y_2148_; lean_object* v_currentBlock_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
v_content_2137_ = lean_ctor_get(v_x_2127_, 0);
lean_inc_ref(v_content_2137_);
lean_dec_ref(v_x_2127_);
v_currentBlock_2152_ = lean_ctor_get(v_a_2129_, 1);
v___x_2153_ = lean_string_utf8_byte_size(v_currentBlock_2152_);
v___x_2154_ = lean_unsigned_to_nat(0u);
v___x_2155_ = lean_nat_dec_eq(v___x_2153_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2156_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2157_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2158_ = lean_nat_dec_le(v___x_2157_, v___x_2153_);
if (v___x_2158_ == 0)
{
v___y_2148_ = v___x_2155_;
goto v___jp_2147_;
}
else
{
lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2159_ = lean_nat_sub(v___x_2153_, v___x_2157_);
v___x_2160_ = lean_string_memcmp(v_currentBlock_2152_, v___x_2156_, v___x_2159_, v___x_2154_, v___x_2157_);
lean_dec(v___x_2159_);
v___y_2148_ = v___x_2160_;
goto v___jp_2147_;
}
}
else
{
v___y_2148_ = v___x_2155_;
goto v___jp_2147_;
}
v___jp_2138_:
{
lean_object* v_linePrefix_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v_snd_2145_; lean_object* v___x_2146_; 
v_linePrefix_2141_ = lean_ctor_get(v___y_2139_, 0);
lean_inc_ref(v_linePrefix_2141_);
lean_dec_ref(v___y_2139_);
v___x_2142_ = lean_string_length(v_linePrefix_2141_);
lean_dec_ref(v_linePrefix_2141_);
v___x_2143_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCodeBlock(v___x_2142_, v_content_2137_);
lean_dec_ref(v_content_2137_);
v___x_2144_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2143_, v___y_2140_);
lean_dec_ref(v___x_2143_);
v_snd_2145_ = lean_ctor_get(v___x_2144_, 1);
lean_inc(v_snd_2145_);
lean_dec_ref(v___x_2144_);
v___x_2146_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2145_);
return v___x_2146_;
}
v___jp_2147_:
{
if (v___y_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v_snd_2151_; 
v___x_2149_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2150_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2149_, v_a_2129_);
v_snd_2151_ = lean_ctor_get(v___x_2150_, 1);
lean_inc(v_snd_2151_);
lean_dec_ref(v___x_2150_);
v___y_2139_ = v_a_2128_;
v___y_2140_ = v_snd_2151_;
goto v___jp_2138_;
}
else
{
v___y_2139_ = v_a_2128_;
v___y_2140_ = v_a_2129_;
goto v___jp_2138_;
}
}
}
case 2:
{
lean_object* v_items_2161_; lean_object* v___x_2162_; size_t v_sz_2163_; size_t v___x_2164_; lean_object* v___x_2165_; lean_object* v_snd_2166_; lean_object* v___x_2167_; 
v_items_2161_ = lean_ctor_get(v_x_2127_, 0);
lean_inc_ref(v_items_2161_);
lean_dec_ref(v_x_2127_);
v___x_2162_ = lean_box(0);
v_sz_2163_ = lean_array_size(v_items_2161_);
v___x_2164_ = ((size_t)0ULL);
v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4(v_items_2161_, v_sz_2163_, v___x_2164_, v___x_2162_, v_a_2128_, v_a_2129_);
lean_dec_ref(v_items_2161_);
v_snd_2166_ = lean_ctor_get(v___x_2165_, 1);
lean_inc(v_snd_2166_);
lean_dec_ref(v___x_2165_);
v___x_2167_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2166_);
return v___x_2167_;
}
case 3:
{
lean_object* v_start_2168_; lean_object* v_items_2169_; lean_object* v___y_2171_; lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v_start_2168_ = lean_ctor_get(v_x_2127_, 0);
lean_inc(v_start_2168_);
v_items_2169_ = lean_ctor_get(v_x_2127_, 1);
lean_inc_ref(v_items_2169_);
lean_dec_ref(v_x_2127_);
v___x_2177_ = lean_unsigned_to_nat(1u);
v___x_2178_ = l_Int_toNat(v_start_2168_);
lean_dec(v_start_2168_);
v___x_2179_ = lean_nat_dec_le(v___x_2177_, v___x_2178_);
if (v___x_2179_ == 0)
{
lean_dec(v___x_2178_);
v___y_2171_ = v___x_2177_;
goto v___jp_2170_;
}
else
{
v___y_2171_ = v___x_2178_;
goto v___jp_2170_;
}
v___jp_2170_:
{
size_t v_sz_2172_; size_t v___x_2173_; lean_object* v___x_2174_; lean_object* v_snd_2175_; lean_object* v___x_2176_; 
v_sz_2172_ = lean_array_size(v_items_2169_);
v___x_2173_ = ((size_t)0ULL);
v___x_2174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_items_2169_, v_sz_2172_, v___x_2173_, v___y_2171_, v_a_2128_, v_a_2129_);
lean_dec_ref(v_items_2169_);
v_snd_2175_ = lean_ctor_get(v___x_2174_, 1);
lean_inc(v_snd_2175_);
lean_dec_ref(v___x_2174_);
v___x_2176_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2175_);
return v___x_2176_;
}
}
case 4:
{
lean_object* v_items_2180_; lean_object* v___x_2181_; size_t v_sz_2182_; size_t v___x_2183_; lean_object* v___x_2184_; lean_object* v_snd_2185_; lean_object* v___x_2186_; 
v_items_2180_ = lean_ctor_get(v_x_2127_, 0);
lean_inc_ref(v_items_2180_);
lean_dec_ref(v_x_2127_);
v___x_2181_ = lean_box(0);
v_sz_2182_ = lean_array_size(v_items_2180_);
v___x_2183_ = ((size_t)0ULL);
v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_items_2180_, v_sz_2182_, v___x_2183_, v___x_2181_, v_a_2128_, v_a_2129_);
lean_dec_ref(v_items_2180_);
v_snd_2185_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_snd_2185_);
lean_dec_ref(v___x_2184_);
v___x_2186_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2185_);
return v___x_2186_;
}
case 5:
{
lean_object* v_items_2187_; uint8_t v_inEmph_2188_; uint8_t v_inBold_2189_; uint8_t v_inLink_2190_; lean_object* v_linePrefix_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2206_; 
v_items_2187_ = lean_ctor_get(v_x_2127_, 0);
lean_inc_ref(v_items_2187_);
lean_dec_ref(v_x_2127_);
v_inEmph_2188_ = lean_ctor_get_uint8(v_a_2128_, sizeof(void*)*1);
v_inBold_2189_ = lean_ctor_get_uint8(v_a_2128_, sizeof(void*)*1 + 1);
v_inLink_2190_ = lean_ctor_get_uint8(v_a_2128_, sizeof(void*)*1 + 2);
v_linePrefix_2191_ = lean_ctor_get(v_a_2128_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_a_2128_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2193_ = v_a_2128_;
v_isShared_2194_ = v_isSharedCheck_2206_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_linePrefix_2191_);
lean_dec(v_a_2128_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2206_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; size_t v_sz_2196_; size_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2195_ = lean_box(0);
v_sz_2196_ = lean_array_size(v_items_2187_);
v___x_2197_ = ((size_t)0ULL);
v___x_2198_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0));
v___x_2199_ = lean_string_append(v_linePrefix_2191_, v___x_2198_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2199_);
v___x_2201_ = v___x_2193_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2199_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*1, v_inEmph_2188_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*1 + 1, v_inBold_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*1 + 2, v_inLink_2190_);
v___x_2201_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; lean_object* v_snd_2203_; lean_object* v___x_2204_; 
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_items_2187_, v_sz_2196_, v___x_2197_, v___x_2195_, v___x_2201_, v_a_2129_);
lean_dec_ref(v_items_2187_);
v_snd_2203_ = lean_ctor_get(v___x_2202_, 1);
lean_inc(v_snd_2203_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2203_);
return v___x_2204_;
}
}
}
case 6:
{
lean_object* v_content_2207_; lean_object* v___x_2208_; size_t v_sz_2209_; size_t v___x_2210_; lean_object* v___x_2211_; lean_object* v_snd_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
v_content_2207_ = lean_ctor_get(v_x_2127_, 0);
lean_inc_ref(v_content_2207_);
lean_dec_ref(v_x_2127_);
v___x_2208_ = lean_box(0);
v_sz_2209_ = lean_array_size(v_content_2207_);
v___x_2210_ = ((size_t)0ULL);
v___x_2211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_content_2207_, v_sz_2209_, v___x_2210_, v___x_2208_, v_a_2128_, v_a_2129_);
lean_dec_ref(v_content_2207_);
v_snd_2212_ = lean_ctor_get(v___x_2211_, 1);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2219_ == 0)
{
lean_object* v_unused_2220_; 
v_unused_2220_ = lean_ctor_get(v___x_2211_, 0);
lean_dec(v_unused_2220_);
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_snd_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2208_);
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_snd_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
default: 
{
lean_object* v_content_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2242_; 
v_content_2221_ = lean_ctor_get(v_x_2127_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_x_2127_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; 
v_unused_2243_ = lean_ctor_get(v_x_2127_, 0);
lean_dec(v_unused_2243_);
v___x_2223_ = v_x_2127_;
v_isShared_2224_ = v_isSharedCheck_2242_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_content_2221_);
lean_dec(v_x_2127_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2242_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = lean_array_get_size(v_content_2221_);
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_nat_dec_lt(v___x_2225_, v___x_2226_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2230_; 
lean_dec_ref(v_content_2221_);
lean_dec_ref(v_a_2128_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 0);
lean_ctor_set(v___x_2223_, 1, v_a_2129_);
lean_ctor_set(v___x_2223_, 0, v___x_2227_);
v___x_2230_ = v___x_2223_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_a_2129_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
else
{
uint8_t v___x_2232_; 
v___x_2232_ = lean_nat_dec_le(v___x_2226_, v___x_2226_);
if (v___x_2232_ == 0)
{
if (v___x_2228_ == 0)
{
lean_object* v___x_2234_; 
lean_dec_ref(v_content_2221_);
lean_dec_ref(v_a_2128_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 0);
lean_ctor_set(v___x_2223_, 1, v_a_2129_);
lean_ctor_set(v___x_2223_, 0, v___x_2227_);
v___x_2234_ = v___x_2223_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_a_2129_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
else
{
size_t v___x_2236_; size_t v___x_2237_; lean_object* v___x_2238_; 
lean_del_object(v___x_2223_);
v___x_2236_ = ((size_t)0ULL);
v___x_2237_ = lean_usize_of_nat(v___x_2226_);
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_content_2221_, v___x_2236_, v___x_2237_, v___x_2227_, v_a_2128_, v_a_2129_);
lean_dec_ref(v_content_2221_);
return v___x_2238_;
}
}
else
{
size_t v___x_2239_; size_t v___x_2240_; lean_object* v___x_2241_; 
lean_del_object(v___x_2223_);
v___x_2239_ = ((size_t)0ULL);
v___x_2240_ = lean_usize_of_nat(v___x_2226_);
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_content_2221_, v___x_2239_, v___x_2240_, v___x_2227_, v_a_2128_, v_a_2129_);
lean_dec_ref(v_content_2221_);
return v___x_2241_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(lean_object* v_as_2244_, size_t v_i_2245_, size_t v_stop_2246_, lean_object* v_b_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
uint8_t v___x_2250_; 
v___x_2250_ = lean_usize_dec_eq(v_i_2245_, v_stop_2246_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v_fst_2253_; lean_object* v_snd_2254_; size_t v___x_2255_; size_t v___x_2256_; 
v___x_2251_ = lean_array_uget_borrowed(v_as_2244_, v_i_2245_);
lean_inc_ref(v___y_2248_);
lean_inc(v___x_2251_);
v___x_2252_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v___x_2251_, v___y_2248_, v___y_2249_);
v_fst_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_fst_2253_);
v_snd_2254_ = lean_ctor_get(v___x_2252_, 1);
lean_inc(v_snd_2254_);
lean_dec_ref(v___x_2252_);
v___x_2255_ = ((size_t)1ULL);
v___x_2256_ = lean_usize_add(v_i_2245_, v___x_2255_);
v_i_2245_ = v___x_2256_;
v_b_2247_ = v_fst_2253_;
v___y_2249_ = v_snd_2254_;
goto _start;
}
else
{
lean_object* v___x_2258_; 
lean_dec_ref(v___y_2248_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v_b_2247_);
lean_ctor_set(v___x_2258_, 1, v___y_2249_);
return v___x_2258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7___boxed(lean_object* v_as_2259_, lean_object* v_i_2260_, lean_object* v_stop_2261_, lean_object* v_b_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
size_t v_i_boxed_2265_; size_t v_stop_boxed_2266_; lean_object* v_res_2267_; 
v_i_boxed_2265_ = lean_unbox_usize(v_i_2260_);
lean_dec(v_i_2260_);
v_stop_boxed_2266_ = lean_unbox_usize(v_stop_2261_);
lean_dec(v_stop_2261_);
v_res_2267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v_as_2259_, v_i_boxed_2265_, v_stop_boxed_2266_, v_b_2262_, v___y_2263_, v___y_2264_);
lean_dec_ref(v_as_2259_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2___boxed(lean_object* v_as_2268_, lean_object* v_sz_2269_, lean_object* v_i_2270_, lean_object* v_b_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
size_t v_sz_boxed_2274_; size_t v_i_boxed_2275_; lean_object* v_res_2276_; 
v_sz_boxed_2274_ = lean_unbox_usize(v_sz_2269_);
lean_dec(v_sz_2269_);
v_i_boxed_2275_ = lean_unbox_usize(v_i_2270_);
lean_dec(v_i_2270_);
v_res_2276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_as_2268_, v_sz_boxed_2274_, v_i_boxed_2275_, v_b_2271_, v___y_2272_, v___y_2273_);
lean_dec_ref(v_as_2268_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4___boxed(lean_object* v_as_2277_, lean_object* v_sz_2278_, lean_object* v_i_2279_, lean_object* v_b_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
size_t v_sz_boxed_2283_; size_t v_i_boxed_2284_; lean_object* v_res_2285_; 
v_sz_boxed_2283_ = lean_unbox_usize(v_sz_2278_);
lean_dec(v_sz_2278_);
v_i_boxed_2284_ = lean_unbox_usize(v_i_2279_);
lean_dec(v_i_2279_);
v_res_2285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__4(v_as_2277_, v_sz_boxed_2283_, v_i_boxed_2284_, v_b_2280_, v___y_2281_, v___y_2282_);
lean_dec_ref(v_as_2277_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___boxed(lean_object* v_as_2286_, lean_object* v_sz_2287_, lean_object* v_i_2288_, lean_object* v_b_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
size_t v_sz_boxed_2292_; size_t v_i_boxed_2293_; lean_object* v_res_2294_; 
v_sz_boxed_2292_ = lean_unbox_usize(v_sz_2287_);
lean_dec(v_sz_2287_);
v_i_boxed_2293_ = lean_unbox_usize(v_i_2288_);
lean_dec(v_i_2288_);
v_res_2294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_as_2286_, v_sz_boxed_2292_, v_i_boxed_2293_, v_b_2289_, v___y_2290_, v___y_2291_);
lean_dec_ref(v_as_2286_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___boxed(lean_object* v_as_2295_, lean_object* v_sz_2296_, lean_object* v_i_2297_, lean_object* v_b_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
size_t v_sz_boxed_2301_; size_t v_i_boxed_2302_; lean_object* v_res_2303_; 
v_sz_boxed_2301_ = lean_unbox_usize(v_sz_2296_);
lean_dec(v_sz_2296_);
v_i_boxed_2302_ = lean_unbox_usize(v_i_2297_);
lean_dec(v_i_2297_);
v_res_2303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_as_2295_, v_sz_boxed_2301_, v_i_boxed_2302_, v_b_2298_, v___y_2299_, v___y_2300_);
lean_dec_ref(v_as_2295_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg(lean_object* v_level_2305_, lean_object* v_part_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v_snd_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v_snd_2317_; lean_object* v_title_2318_; lean_object* v_content_2319_; lean_object* v_subParts_2320_; lean_object* v___x_2321_; size_t v_sz_2322_; size_t v___x_2323_; lean_object* v___x_2324_; lean_object* v_snd_2325_; lean_object* v___x_2326_; lean_object* v_snd_2327_; size_t v_sz_2328_; lean_object* v___x_2329_; lean_object* v_snd_2330_; lean_object* v___x_2331_; lean_object* v_snd_2332_; size_t v_sz_2333_; lean_object* v___x_2334_; lean_object* v_snd_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
v___x_2309_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_2310_ = lean_unsigned_to_nat(1u);
v___x_2311_ = lean_nat_add(v_level_2305_, v___x_2310_);
lean_inc(v___x_2311_);
v___x_2312_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__1(v___x_2311_, v___x_2309_);
v___x_2313_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2312_, v_a_2308_);
lean_dec_ref(v___x_2312_);
v_snd_2314_ = lean_ctor_get(v___x_2313_, 1);
lean_inc(v_snd_2314_);
lean_dec_ref(v___x_2313_);
v___x_2315_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg___closed__0));
v___x_2316_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_2315_, v_snd_2314_);
v_snd_2317_ = lean_ctor_get(v___x_2316_, 1);
lean_inc(v_snd_2317_);
lean_dec_ref(v___x_2316_);
v_title_2318_ = lean_ctor_get(v_part_2306_, 0);
v_content_2319_ = lean_ctor_get(v_part_2306_, 3);
v_subParts_2320_ = lean_ctor_get(v_part_2306_, 4);
v___x_2321_ = lean_box(0);
v_sz_2322_ = lean_array_size(v_title_2318_);
v___x_2323_ = ((size_t)0ULL);
lean_inc_ref(v_a_2307_);
v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__3(v_title_2318_, v_sz_2322_, v___x_2323_, v___x_2321_, v_a_2307_, v_snd_2317_);
v_snd_2325_ = lean_ctor_get(v___x_2324_, 1);
lean_inc(v_snd_2325_);
lean_dec_ref(v___x_2324_);
v___x_2326_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2325_);
v_snd_2327_ = lean_ctor_get(v___x_2326_, 1);
lean_inc(v_snd_2327_);
lean_dec_ref(v___x_2326_);
v_sz_2328_ = lean_array_size(v_content_2319_);
lean_inc_ref(v_a_2307_);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_content_2319_, v_sz_2328_, v___x_2323_, v___x_2321_, v_a_2307_, v_snd_2327_);
v_snd_2330_ = lean_ctor_get(v___x_2329_, 1);
lean_inc(v_snd_2330_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_2330_);
v_snd_2332_ = lean_ctor_get(v___x_2331_, 1);
lean_inc(v_snd_2332_);
lean_dec_ref(v___x_2331_);
v_sz_2333_ = lean_array_size(v_subParts_2320_);
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__2___redArg(v___x_2311_, v_subParts_2320_, v_sz_2333_, v___x_2323_, v___x_2321_, v_a_2307_, v_snd_2332_);
lean_dec(v___x_2311_);
v_snd_2335_ = lean_ctor_get(v___x_2334_, 1);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; 
v_unused_2343_ = lean_ctor_get(v___x_2334_, 0);
lean_dec(v_unused_2343_);
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_snd_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2321_);
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_snd_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__2___redArg(lean_object* v___x_2344_, lean_object* v_as_2345_, size_t v_sz_2346_, size_t v_i_2347_, lean_object* v_b_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
uint8_t v___x_2351_; 
v___x_2351_ = lean_usize_dec_lt(v_i_2347_, v_sz_2346_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; 
lean_dec_ref(v___y_2349_);
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v_b_2348_);
lean_ctor_set(v___x_2352_, 1, v___y_2350_);
return v___x_2352_;
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2354_; lean_object* v_snd_2355_; lean_object* v___x_2356_; size_t v___x_2357_; size_t v___x_2358_; 
v_a_2353_ = lean_array_uget_borrowed(v_as_2345_, v_i_2347_);
lean_inc_ref(v___y_2349_);
v___x_2354_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg(v___x_2344_, v_a_2353_, v___y_2349_, v___y_2350_);
v_snd_2355_ = lean_ctor_get(v___x_2354_, 1);
lean_inc(v_snd_2355_);
lean_dec_ref(v___x_2354_);
v___x_2356_ = lean_box(0);
v___x_2357_ = ((size_t)1ULL);
v___x_2358_ = lean_usize_add(v_i_2347_, v___x_2357_);
v_i_2347_ = v___x_2358_;
v_b_2348_ = v___x_2356_;
v___y_2350_ = v_snd_2355_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v___x_2360_, lean_object* v_as_2361_, lean_object* v_sz_2362_, lean_object* v_i_2363_, lean_object* v_b_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
size_t v_sz_boxed_2367_; size_t v_i_boxed_2368_; lean_object* v_res_2369_; 
v_sz_boxed_2367_ = lean_unbox_usize(v_sz_2362_);
lean_dec(v_sz_2362_);
v_i_boxed_2368_ = lean_unbox_usize(v_i_2363_);
lean_dec(v_i_2363_);
v_res_2369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__2___redArg(v___x_2360_, v_as_2361_, v_sz_boxed_2367_, v_i_boxed_2368_, v_b_2364_, v___y_2365_, v___y_2366_);
lean_dec_ref(v_as_2361_);
lean_dec(v___x_2360_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg___boxed(lean_object* v_level_2370_, lean_object* v_part_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg(v_level_2370_, v_part_2371_, v_a_2372_, v_a_2373_);
lean_dec_ref(v_part_2371_);
lean_dec(v_level_2370_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(lean_object* v_part_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_unsigned_to_nat(0u);
v___x_2379_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg(v___x_2378_, v_part_2375_, v_a_2376_, v_a_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___boxed(lean_object* v_part_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_part_2380_, v_a_2381_, v_a_2382_);
lean_dec_ref(v_part_2380_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(lean_object* v_as_2384_, size_t v_sz_2385_, size_t v_i_2386_, lean_object* v_b_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
uint8_t v___x_2390_; 
v___x_2390_ = lean_usize_dec_lt(v_i_2386_, v_sz_2385_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; 
lean_dec_ref(v___y_2388_);
v___x_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2391_, 0, v_b_2387_);
lean_ctor_set(v___x_2391_, 1, v___y_2389_);
return v___x_2391_;
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2393_; lean_object* v_snd_2394_; lean_object* v___x_2395_; size_t v___x_2396_; size_t v___x_2397_; 
v_a_2392_ = lean_array_uget_borrowed(v_as_2384_, v_i_2386_);
lean_inc_ref(v___y_2388_);
v___x_2393_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_a_2392_, v___y_2388_, v___y_2389_);
v_snd_2394_ = lean_ctor_get(v___x_2393_, 1);
lean_inc(v_snd_2394_);
lean_dec_ref(v___x_2393_);
v___x_2395_ = lean_box(0);
v___x_2396_ = ((size_t)1ULL);
v___x_2397_ = lean_usize_add(v_i_2386_, v___x_2396_);
v_i_2386_ = v___x_2397_;
v_b_2387_ = v___x_2395_;
v___y_2389_ = v_snd_2394_;
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
lean_dec_ref(v_as_2399_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(lean_object* v_text_2408_, size_t v_sz_2409_, size_t v___x_2410_, lean_object* v___x_2411_, lean_object* v_subsections_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2415_; lean_object* v_snd_2416_; size_t v_sz_2417_; lean_object* v___x_2418_; lean_object* v_snd_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_inc_ref(v___y_2413_);
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
size_t v_sz_boxed_2435_; size_t v___x_10700__boxed_2436_; lean_object* v_res_2437_; 
v_sz_boxed_2435_ = lean_unbox_usize(v_sz_2429_);
lean_dec(v_sz_2429_);
v___x_10700__boxed_2436_ = lean_unbox_usize(v___x_2430_);
lean_dec(v___x_2430_);
v_res_2437_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(v_text_2428_, v_sz_boxed_2435_, v___x_10700__boxed_2436_, v___x_2431_, v_subsections_2432_, v___y_2433_, v___y_2434_);
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
v___x_2448_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__11));
v___x_2449_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__13, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__13_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__13);
v___x_2450_ = l_Lean_Doc_MarkdownM_run_x27(v___f_2447_, v___x_2448_, v___x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(lean_object* v_p_2451_, lean_object* v_part_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_part_2452_, v_a_2453_, v_a_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___boxed(lean_object* v_p_2456_, lean_object* v_part_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(v_p_2456_, v_part_2457_, v_a_2458_, v_a_2459_);
lean_dec_ref(v_part_2457_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(lean_object* v_p_2461_, lean_object* v_level_2462_, lean_object* v_part_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg(v_level_2462_, v_part_2463_, v_a_2464_, v_a_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___boxed(lean_object* v_p_2467_, lean_object* v_level_2468_, lean_object* v_part_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v_p_2467_, v_level_2468_, v_part_2469_, v_a_2470_, v_a_2471_);
lean_dec_ref(v_part_2469_);
lean_dec(v_level_2468_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__2(lean_object* v_p_2473_, lean_object* v___x_2474_, lean_object* v_as_2475_, size_t v_sz_2476_, size_t v_i_2477_, lean_object* v_b_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__2___redArg(v___x_2474_, v_as_2475_, v_sz_2476_, v_i_2477_, v_b_2478_, v___y_2479_, v___y_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__2___boxed(lean_object* v_p_2482_, lean_object* v___x_2483_, lean_object* v_as_2484_, lean_object* v_sz_2485_, lean_object* v_i_2486_, lean_object* v_b_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
size_t v_sz_boxed_2490_; size_t v_i_boxed_2491_; lean_object* v_res_2492_; 
v_sz_boxed_2490_ = lean_unbox_usize(v_sz_2485_);
lean_dec(v_sz_2485_);
v_i_boxed_2491_ = lean_unbox_usize(v_i_2486_);
lean_dec(v_i_2486_);
v_res_2492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__2(v_p_2482_, v___x_2483_, v_as_2484_, v_sz_boxed_2490_, v_i_boxed_2491_, v_b_2487_, v___y_2488_, v___y_2489_);
lean_dec_ref(v_as_2484_);
lean_dec(v___x_2483_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5(lean_object* v_s_2493_, lean_object* v_pattern_2494_, lean_object* v_replacement_2495_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___redArg(v_s_2493_, v_replacement_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5___boxed(lean_object* v_s_2497_, lean_object* v_pattern_2498_, lean_object* v_replacement_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5(v_s_2497_, v_pattern_2498_, v_replacement_2499_);
lean_dec_ref(v_replacement_2499_);
lean_dec_ref(v_pattern_2498_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8(lean_object* v_s_2501_, lean_object* v_replacement_2502_, lean_object* v_inst_2503_, lean_object* v_R_2504_, lean_object* v_a_2505_, lean_object* v_b_2506_, lean_object* v_c_2507_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8___redArg(v_s_2501_, v_replacement_2502_, v_a_2505_, v_b_2506_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_s_2509_, lean_object* v_replacement_2510_, lean_object* v_inst_2511_, lean_object* v_R_2512_, lean_object* v_a_2513_, lean_object* v_b_2514_, lean_object* v_c_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2_spec__5_spec__8(v_s_2509_, v_replacement_2510_, v_inst_2511_, v_R_2512_, v_a_2513_, v_b_2514_, v_c_2515_);
lean_dec_ref(v_replacement_2510_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_2517_, lean_object* v_declName_2518_, uint8_t v_includeBuiltin_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_findInternalDocString_x3f(v_env_2517_, v_declName_2518_, v_includeBuiltin_2519_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2550_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2550_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2550_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
if (lean_obj_tag(v_a_2522_) == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2526_ = lean_box(0);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2526_);
v___x_2528_ = v___x_2524_;
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
else
{
lean_object* v_val_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2549_; 
v_val_2530_ = lean_ctor_get(v_a_2522_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_a_2522_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2532_ = v_a_2522_;
v_isShared_2533_ = v_isSharedCheck_2549_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_val_2530_);
lean_dec(v_a_2522_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2549_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
if (lean_obj_tag(v_val_2530_) == 0)
{
lean_object* v_val_2534_; lean_object* v___x_2536_; 
v_val_2534_ = lean_ctor_get(v_val_2530_, 0);
lean_inc(v_val_2534_);
lean_dec_ref(v_val_2530_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v_val_2534_);
v___x_2536_ = v___x_2532_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_val_2534_);
v___x_2536_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2538_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2536_);
v___x_2538_ = v___x_2524_;
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
else
{
lean_object* v_val_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
v_val_2541_ = lean_ctor_get(v_val_2530_, 0);
lean_inc(v_val_2541_);
lean_dec_ref(v_val_2530_);
v___x_2542_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(v_val_2541_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2542_);
v___x_2544_ = v___x_2532_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2546_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2544_);
v___x_2546_ = v___x_2524_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2544_);
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
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
v_a_2551_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2521_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2521_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_2559_, lean_object* v_declName_2560_, lean_object* v_includeBuiltin_2561_, lean_object* v_a_2562_){
_start:
{
uint8_t v_includeBuiltin_boxed_2563_; lean_object* v_res_2564_; 
v_includeBuiltin_boxed_2563_ = lean_unbox(v_includeBuiltin_2561_);
v_res_2564_ = l_Lean_findSimpleDocString_x3f(v_env_2559_, v_declName_2560_, v_includeBuiltin_boxed_2563_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object* v_x_2567_, lean_object* v_x_2568_, lean_object* v_es_2569_, uint8_t v_level_2570_){
_start:
{
uint8_t v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = 1;
v___x_2572_ = l_Lean_instOrdOLeanLevel_ord(v_level_2570_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
lean_dec(v_es_2569_);
v___x_2573_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_));
return v___x_2573_;
}
else
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_array_mk(v_es_2569_);
return v___x_2574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object* v_x_2575_, lean_object* v_x_2576_, lean_object* v_es_2577_, lean_object* v_level_2578_){
_start:
{
uint8_t v_level_boxed_2579_; lean_object* v_res_2580_; 
v_level_boxed_2579_ = lean_unbox(v_level_2578_);
v_res_2580_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(v_x_2575_, v_x_2576_, v_es_2577_, v_level_boxed_2579_);
lean_dec_ref(v_x_2576_);
lean_dec_ref(v_x_2575_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object* v_es_2581_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_array_mk(v_es_2581_);
return v___x_2582_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_unsigned_to_nat(32u);
v___x_2584_ = lean_mk_empty_array_with_capacity(v___x_2583_);
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(lean_object* v___x_2586_, lean_object* v_x_2587_){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; size_t v___x_2591_; lean_object* v___x_2592_; 
v___x_2588_ = lean_unsigned_to_nat(32u);
v___x_2589_ = lean_mk_empty_array_with_capacity(v___x_2588_);
v___x_2590_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_);
v___x_2591_ = ((size_t)5ULL);
lean_inc(v___x_2586_);
v___x_2592_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2592_, 0, v___x_2590_);
lean_ctor_set(v___x_2592_, 1, v___x_2589_);
lean_ctor_set(v___x_2592_, 2, v___x_2586_);
lean_ctor_set(v___x_2592_, 3, v___x_2586_);
lean_ctor_set_usize(v___x_2592_, 4, v___x_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object* v___x_2593_, lean_object* v_x_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(v___x_2593_, v_x_2594_);
lean_dec_ref(v_x_2594_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_));
v___x_2617_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2____boxed(lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_3367263305____hygCtx___hyg_2_();
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object* v_env_2620_, lean_object* v_doc_2621_){
_start:
{
lean_object* v___x_2622_; lean_object* v_toEnvExtension_2623_; lean_object* v_asyncMode_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2622_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc_ref(v_toEnvExtension_2623_);
v_asyncMode_2624_ = lean_ctor_get(v_toEnvExtension_2623_, 2);
lean_inc(v_asyncMode_2624_);
lean_dec_ref(v_toEnvExtension_2623_);
v___x_2625_ = lean_box(0);
v___x_2626_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2622_, v_env_2620_, v_doc_2621_, v_asyncMode_2624_, v___x_2625_);
lean_dec(v_asyncMode_2624_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_getMainModuleDoc___closed__0(void){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object* v_env_2628_){
_start:
{
lean_object* v___x_2629_; lean_object* v_toEnvExtension_2630_; lean_object* v_asyncMode_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2629_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc_ref(v_toEnvExtension_2630_);
v_asyncMode_2631_ = lean_ctor_get(v_toEnvExtension_2630_, 2);
lean_inc(v_asyncMode_2631_);
lean_dec_ref(v_toEnvExtension_2630_);
v___x_2632_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2633_ = lean_box(0);
v___x_2634_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2632_, v___x_2629_, v_env_2628_, v_asyncMode_2631_, v___x_2633_);
lean_dec(v_asyncMode_2631_);
return v___x_2634_;
}
}
static lean_object* _init_l_Lean_getModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2636_ = lean_box(0);
v___x_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
lean_ctor_set(v___x_2637_, 1, v___x_2635_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object* v_env_2638_, lean_object* v_moduleName_2639_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_Environment_getModuleIdx_x3f(v_env_2638_, v_moduleName_2639_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v___x_2641_; 
v___x_2641_ = lean_box(0);
return v___x_2641_;
}
else
{
lean_object* v_val_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2653_; 
v_val_2642_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2644_ = v___x_2640_;
v_isShared_2645_ = v_isSharedCheck_2653_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_val_2642_);
lean_dec(v___x_2640_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2653_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2646_ = lean_obj_once(&l_Lean_getModuleDoc_x3f___closed__0, &l_Lean_getModuleDoc_x3f___closed__0_once, _init_l_Lean_getModuleDoc_x3f___closed__0);
v___x_2647_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v___x_2648_ = 1;
v___x_2649_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2646_, v___x_2647_, v_env_2638_, v_val_2642_, v___x_2648_);
lean_dec(v_val_2642_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2649_);
v___x_2651_ = v___x_2644_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object* v_env_2654_, lean_object* v_moduleName_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_getModuleDoc_x3f(v_env_2654_, v_moduleName_2655_);
lean_dec(v_moduleName_2655_);
lean_dec_ref(v_env_2654_);
return v_res_2656_;
}
}
static lean_object* _init_l_Lean_getDocStringText___redArg___closed__1(void){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__0));
v___x_2659_ = l_Lean_stringToMessageData(v___x_2658_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_stx_2665_){
_start:
{
lean_object* v_toApplicative_2672_; lean_object* v_toPure_2673_; lean_object* v_val_2675_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_toApplicative_2672_ = lean_ctor_get(v_inst_2663_, 0);
v_toPure_2673_ = lean_ctor_get(v_toApplicative_2672_, 1);
v___x_2682_ = lean_unsigned_to_nat(1u);
v___x_2683_ = l_Lean_Syntax_getArg(v_stx_2665_, v___x_2682_);
switch(lean_obj_tag(v___x_2683_))
{
case 2:
{
lean_object* v_val_2684_; 
lean_inc(v_toPure_2673_);
lean_dec(v_stx_2665_);
lean_dec_ref(v_inst_2664_);
lean_dec_ref(v_inst_2663_);
v_val_2684_ = lean_ctor_get(v___x_2683_, 1);
lean_inc_ref(v_val_2684_);
lean_dec_ref(v___x_2683_);
v_val_2675_ = v_val_2684_;
goto v___jp_2674_;
}
case 1:
{
lean_object* v_kind_2685_; 
v_kind_2685_ = lean_ctor_get(v___x_2683_, 1);
lean_inc(v_kind_2685_);
if (lean_obj_tag(v_kind_2685_) == 1)
{
lean_object* v_pre_2686_; 
v_pre_2686_ = lean_ctor_get(v_kind_2685_, 0);
lean_inc(v_pre_2686_);
if (lean_obj_tag(v_pre_2686_) == 1)
{
lean_object* v_pre_2687_; 
v_pre_2687_ = lean_ctor_get(v_pre_2686_, 0);
lean_inc(v_pre_2687_);
if (lean_obj_tag(v_pre_2687_) == 1)
{
lean_object* v_pre_2688_; 
v_pre_2688_ = lean_ctor_get(v_pre_2687_, 0);
lean_inc(v_pre_2688_);
if (lean_obj_tag(v_pre_2688_) == 1)
{
lean_object* v_pre_2689_; 
v_pre_2689_ = lean_ctor_get(v_pre_2688_, 0);
if (lean_obj_tag(v_pre_2689_) == 0)
{
lean_object* v_str_2690_; lean_object* v_str_2691_; lean_object* v_str_2692_; lean_object* v_str_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v_str_2690_ = lean_ctor_get(v_kind_2685_, 1);
lean_inc_ref(v_str_2690_);
lean_dec_ref(v_kind_2685_);
v_str_2691_ = lean_ctor_get(v_pre_2686_, 1);
lean_inc_ref(v_str_2691_);
lean_dec_ref(v_pre_2686_);
v_str_2692_ = lean_ctor_get(v_pre_2687_, 1);
lean_inc_ref(v_str_2692_);
lean_dec_ref(v_pre_2687_);
v_str_2693_ = lean_ctor_get(v_pre_2688_, 1);
lean_inc_ref(v_str_2693_);
lean_dec_ref(v_pre_2688_);
v___x_2694_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_2695_ = lean_string_dec_eq(v_str_2693_, v___x_2694_);
lean_dec_ref(v_str_2693_);
if (v___x_2695_ == 0)
{
lean_dec_ref(v_str_2692_);
lean_dec_ref(v_str_2691_);
lean_dec_ref(v_str_2690_);
lean_dec_ref(v___x_2683_);
goto v___jp_2666_;
}
else
{
lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2696_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__2));
v___x_2697_ = lean_string_dec_eq(v_str_2692_, v___x_2696_);
lean_dec_ref(v_str_2692_);
if (v___x_2697_ == 0)
{
lean_dec_ref(v_str_2691_);
lean_dec_ref(v_str_2690_);
lean_dec_ref(v___x_2683_);
goto v___jp_2666_;
}
else
{
lean_object* v___x_2698_; uint8_t v___x_2699_; 
v___x_2698_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__3));
v___x_2699_ = lean_string_dec_eq(v_str_2691_, v___x_2698_);
lean_dec_ref(v_str_2691_);
if (v___x_2699_ == 0)
{
lean_dec_ref(v_str_2690_);
lean_dec_ref(v___x_2683_);
goto v___jp_2666_;
}
else
{
lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2700_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__4));
v___x_2701_ = lean_string_dec_eq(v_str_2690_, v___x_2700_);
lean_dec_ref(v_str_2690_);
if (v___x_2701_ == 0)
{
lean_dec_ref(v___x_2683_);
goto v___jp_2666_;
}
else
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_unsigned_to_nat(0u);
v___x_2703_ = l_Lean_Syntax_getArg(v___x_2683_, v___x_2702_);
lean_dec_ref(v___x_2683_);
if (lean_obj_tag(v___x_2703_) == 2)
{
lean_object* v_val_2704_; 
lean_inc(v_toPure_2673_);
lean_dec(v_stx_2665_);
lean_dec_ref(v_inst_2664_);
lean_dec_ref(v_inst_2663_);
v_val_2704_ = lean_ctor_get(v___x_2703_, 1);
lean_inc_ref(v_val_2704_);
lean_dec_ref(v___x_2703_);
v_val_2675_ = v_val_2704_;
goto v___jp_2674_;
}
else
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_dec(v___x_2703_);
v___x_2705_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2665_);
v___x_2706_ = l_Lean_MessageData_ofSyntax(v_stx_2665_);
v___x_2707_ = l_Lean_indentD(v___x_2706_);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2705_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = l_Lean_throwErrorAt___redArg(v_inst_2663_, v_inst_2664_, v_stx_2665_, v___x_2708_);
return v___x_2709_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2688_);
lean_dec_ref(v_pre_2687_);
lean_dec_ref(v_pre_2686_);
lean_dec_ref(v_kind_2685_);
lean_dec_ref(v___x_2683_);
goto v___jp_2666_;
}
}
else
{
lean_dec(v_pre_2688_);
lean_dec_ref(v_pre_2687_);
lean_dec_ref(v_pre_2686_);
lean_dec_ref(v_kind_2685_);
lean_dec_ref(v___x_2683_);
goto v___jp_2666_;
}
}
else
{
lean_dec_ref(v_pre_2686_);
lean_dec(v_pre_2687_);
lean_dec_ref(v_kind_2685_);
lean_dec_ref(v___x_2683_);
goto v___jp_2666_;
}
}
else
{
lean_dec(v_pre_2686_);
lean_dec_ref(v_kind_2685_);
lean_dec_ref(v___x_2683_);
goto v___jp_2666_;
}
}
else
{
lean_dec(v_kind_2685_);
lean_dec_ref(v___x_2683_);
goto v___jp_2666_;
}
}
default: 
{
lean_dec(v___x_2683_);
goto v___jp_2666_;
}
}
v___jp_2666_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2667_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2665_);
v___x_2668_ = l_Lean_MessageData_ofSyntax(v_stx_2665_);
v___x_2669_ = l_Lean_indentD(v___x_2668_);
v___x_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2667_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = l_Lean_throwErrorAt___redArg(v_inst_2663_, v_inst_2664_, v_stx_2665_, v___x_2670_);
return v___x_2671_;
}
v___jp_2674_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = lean_string_utf8_byte_size(v_val_2675_);
v___x_2678_ = lean_unsigned_to_nat(2u);
v___x_2679_ = lean_nat_sub(v___x_2677_, v___x_2678_);
v___x_2680_ = lean_string_utf8_extract(v_val_2675_, v___x_2676_, v___x_2679_);
lean_dec(v___x_2679_);
lean_dec_ref(v_val_2675_);
v___x_2681_ = lean_apply_2(v_toPure_2673_, lean_box(0), v___x_2680_);
return v___x_2681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object* v_m_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_stx_2713_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_getDocStringText___redArg(v_inst_2711_, v_inst_2712_, v_stx_2713_);
return v___x_2714_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_2716_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default___closed__0));
v___x_2717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
lean_ctor_set(v___x_2717_, 2, v___x_2715_);
return v___x_2717_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default(void){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = lean_obj_once(&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0, &l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0_once, _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0);
return v___x_2718_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet(void){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object* v_a_2720_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = lean_nat_to_int(v_a_2720_);
return v___x_2721_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = lean_unsigned_to_nat(2u);
v___x_2729_ = lean_nat_to_int(v___x_2728_);
return v___x_2729_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = lean_unsigned_to_nat(1u);
v___x_2731_ = lean_nat_to_int(v___x_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object* v_x_2744_, lean_object* v_x_2745_, lean_object* v_x_2746_){
_start:
{
if (lean_obj_tag(v_x_2746_) == 0)
{
lean_dec(v_x_2744_);
return v_x_2745_;
}
else
{
lean_object* v_head_2747_; lean_object* v_tail_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2759_; 
v_head_2747_ = lean_ctor_get(v_x_2746_, 0);
v_tail_2748_ = lean_ctor_get(v_x_2746_, 1);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_x_2746_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2750_ = v_x_2746_;
v_isShared_2751_ = v_isSharedCheck_2759_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_tail_2748_);
lean_inc(v_head_2747_);
lean_dec(v_x_2746_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2759_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
lean_inc(v_x_2744_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set_tag(v___x_2750_, 5);
lean_ctor_set(v___x_2750_, 1, v_x_2744_);
lean_ctor_set(v___x_2750_, 0, v_x_2745_);
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_x_2745_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_x_2744_);
v___x_2753_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = lean_unsigned_to_nat(0u);
v___x_2755_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2747_, v___x_2754_);
v___x_2756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2753_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v_x_2745_ = v___x_2756_;
v_x_2746_ = v_tail_2748_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object* v_x_2760_, lean_object* v_x_2761_, lean_object* v_x_2762_){
_start:
{
if (lean_obj_tag(v_x_2762_) == 0)
{
lean_dec(v_x_2760_);
return v_x_2761_;
}
else
{
lean_object* v_head_2763_; lean_object* v_tail_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2775_; 
v_head_2763_ = lean_ctor_get(v_x_2762_, 0);
v_tail_2764_ = lean_ctor_get(v_x_2762_, 1);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_x_2762_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2766_ = v_x_2762_;
v_isShared_2767_ = v_isSharedCheck_2775_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_tail_2764_);
lean_inc(v_head_2763_);
lean_dec(v_x_2762_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2775_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
lean_inc(v_x_2760_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set_tag(v___x_2766_, 5);
lean_ctor_set(v___x_2766_, 1, v_x_2760_);
lean_ctor_set(v___x_2766_, 0, v_x_2761_);
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_x_2761_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_x_2760_);
v___x_2769_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2770_ = lean_unsigned_to_nat(0u);
v___x_2771_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2763_, v___x_2770_);
v___x_2772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2769_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
v___x_2773_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(v_x_2760_, v___x_2772_, v_tail_2764_);
return v___x_2773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2776_, lean_object* v_x_2777_){
_start:
{
if (lean_obj_tag(v_x_2776_) == 0)
{
lean_object* v___x_2778_; 
lean_dec(v_x_2777_);
v___x_2778_ = lean_box(0);
return v___x_2778_;
}
else
{
lean_object* v_tail_2779_; 
v_tail_2779_ = lean_ctor_get(v_x_2776_, 1);
if (lean_obj_tag(v_tail_2779_) == 0)
{
lean_object* v_head_2780_; lean_object* v___x_2781_; 
lean_dec(v_x_2777_);
v_head_2780_ = lean_ctor_get(v_x_2776_, 0);
lean_inc(v_head_2780_);
lean_dec_ref(v_x_2776_);
v___x_2781_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2780_);
return v___x_2781_;
}
else
{
lean_object* v_head_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_inc(v_tail_2779_);
v_head_2782_ = lean_ctor_get(v_x_2776_, 0);
lean_inc(v_head_2782_);
lean_dec_ref(v_x_2776_);
v___x_2783_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2782_);
v___x_2784_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(v_x_2777_, v___x_2783_, v_tail_2779_);
return v___x_2784_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0));
v___x_2787_ = lean_string_length(v___x_2786_);
return v___x_2787_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4);
v___x_2789_ = lean_nat_to_int(v___x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_xs_2797_){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2798_ = lean_array_get_size(v_xs_2797_);
v___x_2799_ = lean_unsigned_to_nat(0u);
v___x_2800_ = lean_nat_dec_eq(v___x_2798_, v___x_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2801_ = lean_array_to_list(v_xs_2797_);
v___x_2802_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2803_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_2801_, v___x_2802_);
v___x_2804_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_2805_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_2806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
lean_ctor_set(v___x_2806_, 1, v___x_2803_);
v___x_2807_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2804_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = l_Std_Format_fill(v___x_2809_);
return v___x_2810_;
}
else
{
lean_object* v___x_2811_; 
lean_dec_ref(v_xs_2797_);
v___x_2811_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_2811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_2866_, lean_object* v_prec_2867_){
_start:
{
switch(lean_obj_tag(v_x_2866_))
{
case 0:
{
lean_object* v_string_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2888_; 
v_string_2868_ = lean_ctor_get(v_x_2866_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_x_2866_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2870_ = v_x_2866_;
v_isShared_2871_ = v_isSharedCheck_2888_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_string_2868_);
lean_dec(v_x_2866_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2888_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___y_2873_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v___x_2884_ = lean_unsigned_to_nat(1024u);
v___x_2885_ = lean_nat_dec_le(v___x_2884_, v_prec_2867_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; 
v___x_2886_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2873_ = v___x_2886_;
goto v___jp_2872_;
}
else
{
lean_object* v___x_2887_; 
v___x_2887_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2873_ = v___x_2887_;
goto v___jp_2872_;
}
v___jp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2874_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_2875_ = l_String_quote(v_string_2868_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set_tag(v___x_2870_, 3);
lean_ctor_set(v___x_2870_, 0, v___x_2875_);
v___x_2877_ = v___x_2870_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2874_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
v___x_2879_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___y_2873_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = 0;
v___x_2881_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set_uint8(v___x_2881_, sizeof(void*)*1, v___x_2880_);
v___x_2882_ = l_Repr_addAppParen(v___x_2881_, v_prec_2867_);
return v___x_2882_;
}
}
}
}
case 1:
{
lean_object* v_content_2889_; lean_object* v___y_2891_; lean_object* v___x_2899_; uint8_t v___x_2900_; 
v_content_2889_ = lean_ctor_get(v_x_2866_, 0);
lean_inc_ref(v_content_2889_);
lean_dec_ref(v_x_2866_);
v___x_2899_ = lean_unsigned_to_nat(1024u);
v___x_2900_ = lean_nat_dec_le(v___x_2899_, v_prec_2867_);
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
v___x_2892_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7));
v___x_2893_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2889_);
v___x_2894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___y_2891_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = 0;
v___x_2897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set_uint8(v___x_2897_, sizeof(void*)*1, v___x_2896_);
v___x_2898_ = l_Repr_addAppParen(v___x_2897_, v_prec_2867_);
return v___x_2898_;
}
}
case 2:
{
lean_object* v_content_2903_; lean_object* v___y_2905_; lean_object* v___x_2913_; uint8_t v___x_2914_; 
v_content_2903_ = lean_ctor_get(v_x_2866_, 0);
lean_inc_ref(v_content_2903_);
lean_dec_ref(v_x_2866_);
v___x_2913_ = lean_unsigned_to_nat(1024u);
v___x_2914_ = lean_nat_dec_le(v___x_2913_, v_prec_2867_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; 
v___x_2915_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2905_ = v___x_2915_;
goto v___jp_2904_;
}
else
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2905_ = v___x_2916_;
goto v___jp_2904_;
}
v___jp_2904_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2906_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10));
v___x_2907_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2903_);
v___x_2908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___y_2905_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = 0;
v___x_2911_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set_uint8(v___x_2911_, sizeof(void*)*1, v___x_2910_);
v___x_2912_ = l_Repr_addAppParen(v___x_2911_, v_prec_2867_);
return v___x_2912_;
}
}
case 3:
{
lean_object* v_string_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2937_; 
v_string_2917_ = lean_ctor_get(v_x_2866_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_x_2866_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2919_ = v_x_2866_;
v_isShared_2920_ = v_isSharedCheck_2937_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_string_2917_);
lean_dec(v_x_2866_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2937_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___y_2922_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v___x_2933_ = lean_unsigned_to_nat(1024u);
v___x_2934_ = lean_nat_dec_le(v___x_2933_, v_prec_2867_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2922_ = v___x_2935_;
goto v___jp_2921_;
}
else
{
lean_object* v___x_2936_; 
v___x_2936_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2922_ = v___x_2936_;
goto v___jp_2921_;
}
v___jp_2921_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2923_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13));
v___x_2924_ = l_String_quote(v_string_2917_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v___x_2924_);
v___x_2926_ = v___x_2919_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2923_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___y_2922_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = 0;
v___x_2930_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2930_, 0, v___x_2928_);
lean_ctor_set_uint8(v___x_2930_, sizeof(void*)*1, v___x_2929_);
v___x_2931_ = l_Repr_addAppParen(v___x_2930_, v_prec_2867_);
return v___x_2931_;
}
}
}
}
case 4:
{
uint8_t v_mode_2938_; lean_object* v_string_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2964_; 
v_mode_2938_ = lean_ctor_get_uint8(v_x_2866_, sizeof(void*)*1);
v_string_2939_ = lean_ctor_get(v_x_2866_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v_x_2866_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2941_ = v_x_2866_;
v_isShared_2942_ = v_isSharedCheck_2964_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_string_2939_);
lean_dec(v_x_2866_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2964_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___y_2944_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2960_ = lean_unsigned_to_nat(1024u);
v___x_2961_ = lean_nat_dec_le(v___x_2960_, v_prec_2867_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2944_ = v___x_2962_;
goto v___jp_2943_;
}
else
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2944_ = v___x_2963_;
goto v___jp_2943_;
}
v___jp_2943_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; uint8_t v___x_2955_; lean_object* v___x_2957_; 
v___x_2945_ = lean_box(1);
v___x_2946_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16));
v___x_2947_ = lean_unsigned_to_nat(1024u);
v___x_2948_ = l_Lean_Doc_instReprMathMode_repr(v_mode_2938_, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2946_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
v___x_2950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
lean_ctor_set(v___x_2950_, 1, v___x_2945_);
v___x_2951_ = l_String_quote(v_string_2939_);
v___x_2952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
v___x_2953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2950_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___y_2944_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = 0;
if (v_isShared_2942_ == 0)
{
lean_ctor_set_tag(v___x_2941_, 6);
lean_ctor_set(v___x_2941_, 0, v___x_2954_);
v___x_2957_ = v___x_2941_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2954_);
v___x_2957_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; 
lean_ctor_set_uint8(v___x_2957_, sizeof(void*)*1, v___x_2955_);
v___x_2958_ = l_Repr_addAppParen(v___x_2957_, v_prec_2867_);
return v___x_2958_;
}
}
}
}
case 5:
{
lean_object* v_string_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2985_; 
v_string_2965_ = lean_ctor_get(v_x_2866_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_x_2866_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2967_ = v_x_2866_;
v_isShared_2968_ = v_isSharedCheck_2985_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_string_2965_);
lean_dec(v_x_2866_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2985_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___y_2970_; lean_object* v___x_2981_; uint8_t v___x_2982_; 
v___x_2981_ = lean_unsigned_to_nat(1024u);
v___x_2982_ = lean_nat_dec_le(v___x_2981_, v_prec_2867_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; 
v___x_2983_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2970_ = v___x_2983_;
goto v___jp_2969_;
}
else
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2970_ = v___x_2984_;
goto v___jp_2969_;
}
v___jp_2969_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2971_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19));
v___x_2972_ = l_String_quote(v_string_2965_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set_tag(v___x_2967_, 3);
lean_ctor_set(v___x_2967_, 0, v___x_2972_);
v___x_2974_ = v___x_2967_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2971_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___y_2970_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = 0;
v___x_2978_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2978_, 0, v___x_2976_);
lean_ctor_set_uint8(v___x_2978_, sizeof(void*)*1, v___x_2977_);
v___x_2979_ = l_Repr_addAppParen(v___x_2978_, v_prec_2867_);
return v___x_2979_;
}
}
}
}
case 6:
{
lean_object* v_content_2986_; lean_object* v_url_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3011_; 
v_content_2986_ = lean_ctor_get(v_x_2866_, 0);
v_url_2987_ = lean_ctor_get(v_x_2866_, 1);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_x_2866_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_2989_ = v_x_2866_;
v_isShared_2990_ = v_isSharedCheck_3011_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_url_2987_);
lean_inc(v_content_2986_);
lean_dec(v_x_2866_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3011_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___y_2992_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = lean_unsigned_to_nat(1024u);
v___x_3008_ = lean_nat_dec_le(v___x_3007_, v_prec_2867_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2992_ = v___x_3009_;
goto v___jp_2991_;
}
else
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2992_ = v___x_3010_;
goto v___jp_2991_;
}
v___jp_2991_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2993_ = lean_box(1);
v___x_2994_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22));
v___x_2995_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2986_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set_tag(v___x_2989_, 5);
lean_ctor_set(v___x_2989_, 1, v___x_2995_);
lean_ctor_set(v___x_2989_, 0, v___x_2994_);
v___x_2997_ = v___x_2989_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_3006_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_2998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
lean_ctor_set(v___x_2998_, 1, v___x_2993_);
v___x_2999_ = l_String_quote(v_url_2987_);
v___x_3000_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
v___x_3001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2998_);
lean_ctor_set(v___x_3001_, 1, v___x_3000_);
v___x_3002_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___y_2992_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = 0;
v___x_3004_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3004_, 0, v___x_3002_);
lean_ctor_set_uint8(v___x_3004_, sizeof(void*)*1, v___x_3003_);
v___x_3005_ = l_Repr_addAppParen(v___x_3004_, v_prec_2867_);
return v___x_3005_;
}
}
}
}
case 7:
{
lean_object* v_name_3012_; lean_object* v_content_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3037_; 
v_name_3012_ = lean_ctor_get(v_x_2866_, 0);
v_content_3013_ = lean_ctor_get(v_x_2866_, 1);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_x_2866_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3015_ = v_x_2866_;
v_isShared_3016_ = v_isSharedCheck_3037_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_content_3013_);
lean_inc(v_name_3012_);
lean_dec(v_x_2866_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3037_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___y_3018_; lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = lean_unsigned_to_nat(1024u);
v___x_3034_ = lean_nat_dec_le(v___x_3033_, v_prec_2867_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3018_ = v___x_3035_;
goto v___jp_3017_;
}
else
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3018_ = v___x_3036_;
goto v___jp_3017_;
}
v___jp_3017_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3019_ = lean_box(1);
v___x_3020_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25));
v___x_3021_ = l_String_quote(v_name_3012_);
v___x_3022_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set_tag(v___x_3015_, 5);
lean_ctor_set(v___x_3015_, 1, v___x_3022_);
lean_ctor_set(v___x_3015_, 0, v___x_3020_);
v___x_3024_ = v___x_3015_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v___x_3019_);
v___x_3026_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3013_);
v___x_3027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3025_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___y_3018_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = 0;
v___x_3030_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set_uint8(v___x_3030_, sizeof(void*)*1, v___x_3029_);
v___x_3031_ = l_Repr_addAppParen(v___x_3030_, v_prec_2867_);
return v___x_3031_;
}
}
}
}
case 8:
{
lean_object* v_alt_3038_; lean_object* v_url_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3064_; 
v_alt_3038_ = lean_ctor_get(v_x_2866_, 0);
v_url_3039_ = lean_ctor_get(v_x_2866_, 1);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_x_2866_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3041_ = v_x_2866_;
v_isShared_3042_ = v_isSharedCheck_3064_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_url_3039_);
lean_inc(v_alt_3038_);
lean_dec(v_x_2866_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3064_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___y_3044_; lean_object* v___x_3060_; uint8_t v___x_3061_; 
v___x_3060_ = lean_unsigned_to_nat(1024u);
v___x_3061_ = lean_nat_dec_le(v___x_3060_, v_prec_2867_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3044_ = v___x_3062_;
goto v___jp_3043_;
}
else
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3044_ = v___x_3063_;
goto v___jp_3043_;
}
v___jp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3045_ = lean_box(1);
v___x_3046_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28));
v___x_3047_ = l_String_quote(v_alt_3038_);
v___x_3048_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set_tag(v___x_3041_, 5);
lean_ctor_set(v___x_3041_, 1, v___x_3048_);
lean_ctor_set(v___x_3041_, 0, v___x_3046_);
v___x_3050_ = v___x_3041_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3046_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v___x_3045_);
v___x_3052_ = l_String_quote(v_url_3039_);
v___x_3053_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
v___x_3054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3051_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___y_3044_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
v___x_3056_ = 0;
v___x_3057_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3057_, 0, v___x_3055_);
lean_ctor_set_uint8(v___x_3057_, sizeof(void*)*1, v___x_3056_);
v___x_3058_ = l_Repr_addAppParen(v___x_3057_, v_prec_2867_);
return v___x_3058_;
}
}
}
}
case 9:
{
lean_object* v_content_3065_; lean_object* v___y_3067_; lean_object* v___x_3075_; uint8_t v___x_3076_; 
v_content_3065_ = lean_ctor_get(v_x_2866_, 0);
lean_inc_ref(v_content_3065_);
lean_dec_ref(v_x_2866_);
v___x_3075_ = lean_unsigned_to_nat(1024u);
v___x_3076_ = lean_nat_dec_le(v___x_3075_, v_prec_2867_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; 
v___x_3077_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3067_ = v___x_3077_;
goto v___jp_3066_;
}
else
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3067_ = v___x_3078_;
goto v___jp_3066_;
}
v___jp_3066_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; uint8_t v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3068_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31));
v___x_3069_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3065_);
v___x_3070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3068_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___y_3067_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = 0;
v___x_3073_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3073_, 0, v___x_3071_);
lean_ctor_set_uint8(v___x_3073_, sizeof(void*)*1, v___x_3072_);
v___x_3074_ = l_Repr_addAppParen(v___x_3073_, v_prec_2867_);
return v___x_3074_;
}
}
default: 
{
lean_object* v_container_3079_; lean_object* v_content_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3128_; 
v_container_3079_ = lean_ctor_get(v_x_2866_, 0);
v_content_3080_ = lean_ctor_get(v_x_2866_, 1);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_x_2866_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3082_ = v_x_2866_;
v_isShared_3083_ = v_isSharedCheck_3128_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_content_3080_);
lean_inc(v_container_3079_);
lean_dec(v_x_2866_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3128_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___y_3085_; lean_object* v___x_3124_; uint8_t v___x_3125_; 
v___x_3124_ = lean_unsigned_to_nat(1024u);
v___x_3125_ = lean_nat_dec_le(v___x_3124_, v_prec_2867_);
if (v___x_3125_ == 0)
{
lean_object* v___x_3126_; 
v___x_3126_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3085_ = v___x_3126_;
goto v___jp_3084_;
}
else
{
lean_object* v___x_3127_; 
v___x_3127_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3085_ = v___x_3127_;
goto v___jp_3084_;
}
v___jp_3084_:
{
lean_object* v_name_3086_; lean_object* v_val_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3123_; 
v_name_3086_ = lean_ctor_get(v_container_3079_, 0);
v_val_3087_ = lean_ctor_get(v_container_3079_, 1);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_container_3079_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3089_ = v_container_3079_;
v_isShared_3090_ = v_isSharedCheck_3123_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_val_3087_);
lean_inc(v_name_3086_);
lean_dec(v_container_3079_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3123_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3091_ = lean_box(1);
v___x_3092_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34));
v___x_3093_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3094_ = lean_unsigned_to_nat(0u);
v___x_3095_ = l_Lean_Name_reprPrec(v_name_3086_, v___x_3094_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set_tag(v___x_3089_, 5);
lean_ctor_set(v___x_3089_, 1, v___x_3095_);
lean_ctor_set(v___x_3089_, 0, v___x_3093_);
v___x_3097_ = v___x_3089_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
lean_object* v___x_3098_; uint8_t v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
v___x_3098_ = l_Std_Format_nestD(v___x_3097_);
v___x_3099_ = 0;
v___x_3100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3100_, 0, v___x_3098_);
lean_ctor_set_uint8(v___x_3100_, sizeof(void*)*1, v___x_3099_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set_tag(v___x_3082_, 5);
lean_ctor_set(v___x_3082_, 1, v___x_3091_);
lean_ctor_set(v___x_3082_, 0, v___x_3100_);
v___x_3102_ = v___x_3082_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v___x_3091_);
v___x_3102_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3103_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3104_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3087_);
lean_dec(v_val_3087_);
v___x_3105_ = l_Lean_Name_reprPrec(v___x_3104_, v___x_3094_);
v___x_3106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3103_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = l_Std_Format_nestD(v___x_3108_);
v___x_3110_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
lean_ctor_set_uint8(v___x_3110_, sizeof(void*)*1, v___x_3099_);
v___x_3111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3102_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = l_Std_Format_nestD(v___x_3111_);
v___x_3113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
lean_ctor_set_uint8(v___x_3113_, sizeof(void*)*1, v___x_3099_);
v___x_3114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3092_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
v___x_3115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
lean_ctor_set(v___x_3115_, 1, v___x_3091_);
v___x_3116_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_3080_);
v___x_3117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3115_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___y_3085_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
v___x_3119_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
lean_ctor_set_uint8(v___x_3119_, sizeof(void*)*1, v___x_3099_);
v___x_3120_ = l_Repr_addAppParen(v___x_3119_, v_prec_2867_);
return v___x_3120_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_unsigned_to_nat(0u);
v___x_3131_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v___y_3129_, v___x_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_3132_, lean_object* v_prec_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_x_3132_, v_prec_3133_);
lean_dec(v_prec_3133_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object* v_xs_3135_){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3136_ = lean_array_get_size(v_xs_3135_);
v___x_3137_ = lean_unsigned_to_nat(0u);
v___x_3138_ = lean_nat_dec_eq(v___x_3136_, v___x_3137_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3139_ = lean_array_to_list(v_xs_3135_);
v___x_3140_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3141_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_3139_, v___x_3140_);
v___x_3142_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3143_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
lean_ctor_set(v___x_3144_, 1, v___x_3141_);
v___x_3145_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3142_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = l_Std_Format_fill(v___x_3147_);
return v___x_3148_;
}
else
{
lean_object* v___x_3149_; 
lean_dec_ref(v_xs_3135_);
v___x_3149_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3149_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = lean_unsigned_to_nat(12u);
v___x_3181_ = lean_nat_to_int(v___x_3180_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object* v_x_3182_, lean_object* v_x_3183_, lean_object* v_x_3184_){
_start:
{
if (lean_obj_tag(v_x_3184_) == 0)
{
lean_dec(v_x_3182_);
return v_x_3183_;
}
else
{
lean_object* v_head_3185_; lean_object* v_tail_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3197_; 
v_head_3185_ = lean_ctor_get(v_x_3184_, 0);
v_tail_3186_ = lean_ctor_get(v_x_3184_, 1);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_x_3184_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3188_ = v_x_3184_;
v_isShared_3189_ = v_isSharedCheck_3197_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_tail_3186_);
lean_inc(v_head_3185_);
lean_dec(v_x_3184_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3197_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
lean_inc(v_x_3182_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set_tag(v___x_3188_, 5);
lean_ctor_set(v___x_3188_, 1, v_x_3182_);
lean_ctor_set(v___x_3188_, 0, v_x_3183_);
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_x_3183_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v_x_3182_);
v___x_3191_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_3185_, v___x_3192_);
v___x_3194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3191_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v_x_3183_ = v___x_3194_;
v_x_3184_ = v_tail_3186_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object* v_x_3198_, lean_object* v_x_3199_, lean_object* v_x_3200_){
_start:
{
if (lean_obj_tag(v_x_3200_) == 0)
{
lean_dec(v_x_3198_);
return v_x_3199_;
}
else
{
lean_object* v_head_3201_; lean_object* v_tail_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3213_; 
v_head_3201_ = lean_ctor_get(v_x_3200_, 0);
v_tail_3202_ = lean_ctor_get(v_x_3200_, 1);
v_isSharedCheck_3213_ = !lean_is_exclusive(v_x_3200_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3204_ = v_x_3200_;
v_isShared_3205_ = v_isSharedCheck_3213_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_tail_3202_);
lean_inc(v_head_3201_);
lean_dec(v_x_3200_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3213_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
lean_inc(v_x_3198_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 5);
lean_ctor_set(v___x_3204_, 1, v_x_3198_);
lean_ctor_set(v___x_3204_, 0, v_x_3199_);
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_x_3199_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v_x_3198_);
v___x_3207_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3208_ = lean_unsigned_to_nat(0u);
v___x_3209_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_3201_, v___x_3208_);
v___x_3210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3207_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(v_x_3198_, v___x_3210_, v_tail_3202_);
return v___x_3211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object* v_x_3214_, lean_object* v_x_3215_){
_start:
{
if (lean_obj_tag(v_x_3214_) == 0)
{
lean_object* v___x_3216_; 
lean_dec(v_x_3215_);
v___x_3216_ = lean_box(0);
return v___x_3216_;
}
else
{
lean_object* v_tail_3217_; 
v_tail_3217_ = lean_ctor_get(v_x_3214_, 1);
if (lean_obj_tag(v_tail_3217_) == 0)
{
lean_object* v_head_3218_; lean_object* v___x_3219_; 
lean_dec(v_x_3215_);
v_head_3218_ = lean_ctor_get(v_x_3214_, 0);
lean_inc(v_head_3218_);
lean_dec_ref(v_x_3214_);
v___x_3219_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3218_);
return v___x_3219_;
}
else
{
lean_object* v_head_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_inc(v_tail_3217_);
v_head_3220_ = lean_ctor_get(v_x_3214_, 0);
lean_inc(v_head_3220_);
lean_dec_ref(v_x_3214_);
v___x_3221_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3220_);
v___x_3222_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(v_x_3215_, v___x_3221_, v_tail_3217_);
return v___x_3222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object* v_xs_3223_){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; uint8_t v___x_3226_; 
v___x_3224_ = lean_array_get_size(v_xs_3223_);
v___x_3225_ = lean_unsigned_to_nat(0u);
v___x_3226_ = lean_nat_dec_eq(v___x_3224_, v___x_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3227_ = lean_array_to_list(v_xs_3223_);
v___x_3228_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3229_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3227_, v___x_3228_);
v___x_3230_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3231_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v___x_3229_);
v___x_3233_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3230_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = l_Std_Format_fill(v___x_3235_);
return v___x_3236_;
}
else
{
lean_object* v___x_3237_; 
lean_dec_ref(v_xs_3223_);
v___x_3237_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3237_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_3240_ = lean_string_length(v___x_3239_);
return v___x_3240_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9);
v___x_3242_ = lean_nat_to_int(v___x_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_x_3248_){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3249_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6));
v___x_3250_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3251_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_x_3248_);
v___x_3252_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = 0;
v___x_3254_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set_uint8(v___x_3254_, sizeof(void*)*1, v___x_3253_);
v___x_3255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3249_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3257_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
lean_ctor_set(v___x_3258_, 1, v___x_3255_);
v___x_3259_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3256_);
lean_ctor_set(v___x_3261_, 1, v___x_3260_);
v___x_3262_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set_uint8(v___x_3262_, sizeof(void*)*1, v___x_3253_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object* v_x_3263_, lean_object* v_x_3264_, lean_object* v_x_3265_){
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
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3266_);
v___x_3274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v_x_3264_ = v___x_3274_;
v_x_3265_ = v_tail_3267_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object* v_x_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_){
_start:
{
if (lean_obj_tag(v_x_3280_) == 0)
{
lean_dec(v_x_3278_);
return v_x_3279_;
}
else
{
lean_object* v_head_3281_; lean_object* v_tail_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3292_; 
v_head_3281_ = lean_ctor_get(v_x_3280_, 0);
v_tail_3282_ = lean_ctor_get(v_x_3280_, 1);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_x_3280_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3284_ = v_x_3280_;
v_isShared_3285_ = v_isSharedCheck_3292_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_tail_3282_);
lean_inc(v_head_3281_);
lean_dec(v_x_3280_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3292_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
lean_inc(v_x_3278_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set_tag(v___x_3284_, 5);
lean_ctor_set(v___x_3284_, 1, v_x_3278_);
lean_ctor_set(v___x_3284_, 0, v_x_3279_);
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_x_3279_);
lean_ctor_set(v_reuseFailAlloc_3291_, 1, v_x_3278_);
v___x_3287_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3281_);
v___x_3289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3287_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(v_x_3278_, v___x_3289_, v_tail_3282_);
return v___x_3290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object* v_x_3293_, lean_object* v_x_3294_){
_start:
{
if (lean_obj_tag(v_x_3293_) == 0)
{
lean_object* v___x_3295_; 
lean_dec(v_x_3294_);
v___x_3295_ = lean_box(0);
return v___x_3295_;
}
else
{
lean_object* v_tail_3296_; 
v_tail_3296_ = lean_ctor_get(v_x_3293_, 1);
if (lean_obj_tag(v_tail_3296_) == 0)
{
lean_object* v_head_3297_; lean_object* v___x_3298_; 
lean_dec(v_x_3294_);
v_head_3297_ = lean_ctor_get(v_x_3293_, 0);
lean_inc(v_head_3297_);
lean_dec_ref(v_x_3293_);
v___x_3298_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3297_);
return v___x_3298_;
}
else
{
lean_object* v_head_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_inc(v_tail_3296_);
v_head_3299_ = lean_ctor_get(v_x_3293_, 0);
lean_inc(v_head_3299_);
lean_dec_ref(v_x_3293_);
v___x_3300_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3299_);
v___x_3301_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(v_x_3294_, v___x_3300_, v_tail_3296_);
return v___x_3301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object* v_xs_3302_){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v___x_3303_ = lean_array_get_size(v_xs_3302_);
v___x_3304_ = lean_unsigned_to_nat(0u);
v___x_3305_ = lean_nat_dec_eq(v___x_3303_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3306_ = lean_array_to_list(v_xs_3302_);
v___x_3307_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3308_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(v___x_3306_, v___x_3307_);
v___x_3309_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3310_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
lean_ctor_set(v___x_3311_, 1, v___x_3308_);
v___x_3312_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3309_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = l_Std_Format_fill(v___x_3314_);
return v___x_3315_;
}
else
{
lean_object* v___x_3316_; 
lean_dec_ref(v_xs_3302_);
v___x_3316_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3316_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = lean_unsigned_to_nat(0u);
v___x_3324_ = lean_nat_to_int(v___x_3323_);
return v___x_3324_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_unsigned_to_nat(8u);
v___x_3341_ = lean_nat_to_int(v___x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_x_3345_){
_start:
{
lean_object* v_term_3346_; lean_object* v_desc_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3379_; 
v_term_3346_ = lean_ctor_get(v_x_3345_, 0);
v_desc_3347_ = lean_ctor_get(v_x_3345_, 1);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_x_3345_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3349_ = v_x_3345_;
v_isShared_3350_ = v_isSharedCheck_3379_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_desc_3347_);
lean_inc(v_term_3346_);
lean_dec(v_x_3345_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3379_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3351_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3352_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3));
v___x_3353_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3354_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_term_3346_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set_tag(v___x_3349_, 4);
lean_ctor_set(v___x_3349_, 1, v___x_3354_);
lean_ctor_set(v___x_3349_, 0, v___x_3353_);
v___x_3356_ = v___x_3349_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
uint8_t v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3357_ = 0;
v___x_3358_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3358_, 0, v___x_3356_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*1, v___x_3357_);
v___x_3359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3352_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3359_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = lean_box(1);
v___x_3363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3361_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
v___x_3364_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6));
v___x_3365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3363_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v___x_3351_);
v___x_3367_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_desc_3347_);
v___x_3368_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3353_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
lean_ctor_set_uint8(v___x_3369_, sizeof(void*)*1, v___x_3357_);
v___x_3370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3366_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3372_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
lean_ctor_set(v___x_3373_, 1, v___x_3370_);
v___x_3374_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3373_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3371_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
lean_ctor_set_uint8(v___x_3377_, sizeof(void*)*1, v___x_3357_);
return v___x_3377_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object* v_x_3380_, lean_object* v_x_3381_, lean_object* v_x_3382_){
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
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3383_);
v___x_3391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3389_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v_x_3381_ = v___x_3391_;
v_x_3382_ = v_tail_3384_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object* v_x_3395_, lean_object* v_x_3396_, lean_object* v_x_3397_){
_start:
{
if (lean_obj_tag(v_x_3397_) == 0)
{
lean_dec(v_x_3395_);
return v_x_3396_;
}
else
{
lean_object* v_head_3398_; lean_object* v_tail_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3409_; 
v_head_3398_ = lean_ctor_get(v_x_3397_, 0);
v_tail_3399_ = lean_ctor_get(v_x_3397_, 1);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_x_3397_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3401_ = v_x_3397_;
v_isShared_3402_ = v_isSharedCheck_3409_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_tail_3399_);
lean_inc(v_head_3398_);
lean_dec(v_x_3397_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3409_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
lean_inc(v_x_3395_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 5);
lean_ctor_set(v___x_3401_, 1, v_x_3395_);
lean_ctor_set(v___x_3401_, 0, v_x_3396_);
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_x_3396_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_x_3395_);
v___x_3404_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3405_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3398_);
v___x_3406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3404_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(v_x_3395_, v___x_3406_, v_tail_3399_);
return v___x_3407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object* v_x_3410_, lean_object* v_x_3411_){
_start:
{
if (lean_obj_tag(v_x_3410_) == 0)
{
lean_object* v___x_3412_; 
lean_dec(v_x_3411_);
v___x_3412_ = lean_box(0);
return v___x_3412_;
}
else
{
lean_object* v_tail_3413_; 
v_tail_3413_ = lean_ctor_get(v_x_3410_, 1);
if (lean_obj_tag(v_tail_3413_) == 0)
{
lean_object* v_head_3414_; lean_object* v___x_3415_; 
lean_dec(v_x_3411_);
v_head_3414_ = lean_ctor_get(v_x_3410_, 0);
lean_inc(v_head_3414_);
lean_dec_ref(v_x_3410_);
v___x_3415_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3414_);
return v___x_3415_;
}
else
{
lean_object* v_head_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_inc(v_tail_3413_);
v_head_3416_ = lean_ctor_get(v_x_3410_, 0);
lean_inc(v_head_3416_);
lean_dec_ref(v_x_3410_);
v___x_3417_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3416_);
v___x_3418_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(v_x_3411_, v___x_3417_, v_tail_3413_);
return v___x_3418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object* v_xs_3419_){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
v___x_3420_ = lean_array_get_size(v_xs_3419_);
v___x_3421_ = lean_unsigned_to_nat(0u);
v___x_3422_ = lean_nat_dec_eq(v___x_3420_, v___x_3421_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3423_ = lean_array_to_list(v_xs_3419_);
v___x_3424_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3425_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(v___x_3423_, v___x_3424_);
v___x_3426_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3427_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
lean_ctor_set(v___x_3428_, 1, v___x_3425_);
v___x_3429_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3426_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = l_Std_Format_fill(v___x_3431_);
return v___x_3432_;
}
else
{
lean_object* v___x_3433_; 
lean_dec_ref(v_xs_3419_);
v___x_3433_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object* v_x_3452_, lean_object* v_prec_3453_){
_start:
{
switch(lean_obj_tag(v_x_3452_))
{
case 0:
{
lean_object* v_contents_3454_; lean_object* v___y_3456_; lean_object* v___x_3464_; uint8_t v___x_3465_; 
v_contents_3454_ = lean_ctor_get(v_x_3452_, 0);
lean_inc_ref(v_contents_3454_);
lean_dec_ref(v_x_3452_);
v___x_3464_ = lean_unsigned_to_nat(1024u);
v___x_3465_ = lean_nat_dec_le(v___x_3464_, v_prec_3453_);
if (v___x_3465_ == 0)
{
lean_object* v___x_3466_; 
v___x_3466_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3456_ = v___x_3466_;
goto v___jp_3455_;
}
else
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3456_ = v___x_3467_;
goto v___jp_3455_;
}
v___jp_3455_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3457_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2));
v___x_3458_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_contents_3454_);
v___x_3459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3457_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
v___x_3460_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___y_3456_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = 0;
v___x_3462_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set_uint8(v___x_3462_, sizeof(void*)*1, v___x_3461_);
v___x_3463_ = l_Repr_addAppParen(v___x_3462_, v_prec_3453_);
return v___x_3463_;
}
}
case 1:
{
lean_object* v_content_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3488_; 
v_content_3468_ = lean_ctor_get(v_x_3452_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v_x_3452_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3470_ = v_x_3452_;
v_isShared_3471_ = v_isSharedCheck_3488_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_content_3468_);
lean_dec(v_x_3452_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3488_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___y_3473_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v___x_3484_ = lean_unsigned_to_nat(1024u);
v___x_3485_ = lean_nat_dec_le(v___x_3484_, v_prec_3453_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; 
v___x_3486_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3473_ = v___x_3486_;
goto v___jp_3472_;
}
else
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3473_ = v___x_3487_;
goto v___jp_3472_;
}
v___jp_3472_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3474_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5));
v___x_3475_ = l_String_quote(v_content_3468_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set_tag(v___x_3470_, 3);
lean_ctor_set(v___x_3470_, 0, v___x_3475_);
v___x_3477_ = v___x_3470_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3474_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___y_3473_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
v___x_3480_ = 0;
v___x_3481_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3481_, 0, v___x_3479_);
lean_ctor_set_uint8(v___x_3481_, sizeof(void*)*1, v___x_3480_);
v___x_3482_ = l_Repr_addAppParen(v___x_3481_, v_prec_3453_);
return v___x_3482_;
}
}
}
}
case 2:
{
lean_object* v_items_3489_; lean_object* v___y_3491_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v_items_3489_ = lean_ctor_get(v_x_3452_, 0);
lean_inc_ref(v_items_3489_);
lean_dec_ref(v_x_3452_);
v___x_3499_ = lean_unsigned_to_nat(1024u);
v___x_3500_ = lean_nat_dec_le(v___x_3499_, v_prec_3453_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
v___x_3501_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3491_ = v___x_3501_;
goto v___jp_3490_;
}
else
{
lean_object* v___x_3502_; 
v___x_3502_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3491_ = v___x_3502_;
goto v___jp_3490_;
}
v___jp_3490_:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3492_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8));
v___x_3493_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3489_);
v___x_3494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3492_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___y_3491_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = 0;
v___x_3497_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3497_, 0, v___x_3495_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*1, v___x_3496_);
v___x_3498_ = l_Repr_addAppParen(v___x_3497_, v_prec_3453_);
return v___x_3498_;
}
}
case 3:
{
lean_object* v_start_3503_; lean_object* v_items_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3539_; 
v_start_3503_ = lean_ctor_get(v_x_3452_, 0);
v_items_3504_ = lean_ctor_get(v_x_3452_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_x_3452_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3506_ = v_x_3452_;
v_isShared_3507_ = v_isSharedCheck_3539_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_items_3504_);
lean_inc(v_start_3503_);
lean_dec(v_x_3452_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3539_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3524_; lean_object* v___x_3535_; uint8_t v___x_3536_; 
v___x_3535_ = lean_unsigned_to_nat(1024u);
v___x_3536_ = lean_nat_dec_le(v___x_3535_, v_prec_3453_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
v___x_3537_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3524_ = v___x_3537_;
goto v___jp_3523_;
}
else
{
lean_object* v___x_3538_; 
v___x_3538_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3524_ = v___x_3538_;
goto v___jp_3523_;
}
v___jp_3508_:
{
lean_object* v___x_3514_; 
if (v_isShared_3507_ == 0)
{
lean_ctor_set_tag(v___x_3506_, 5);
lean_ctor_set(v___x_3506_, 1, v___y_3512_);
lean_ctor_set(v___x_3506_, 0, v___y_3510_);
v___x_3514_ = v___x_3506_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___y_3510_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v___y_3512_);
v___x_3514_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3514_);
lean_ctor_set(v___x_3515_, 1, v___y_3511_);
v___x_3516_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3504_);
v___x_3517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3515_);
lean_ctor_set(v___x_3517_, 1, v___x_3516_);
v___x_3518_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___y_3509_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
v___x_3519_ = 0;
v___x_3520_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set_uint8(v___x_3520_, sizeof(void*)*1, v___x_3519_);
v___x_3521_ = l_Repr_addAppParen(v___x_3520_, v_prec_3453_);
return v___x_3521_;
}
}
v___jp_3523_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; uint8_t v___x_3528_; 
v___x_3525_ = lean_box(1);
v___x_3526_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11));
v___x_3527_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12, &l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12);
v___x_3528_ = lean_int_dec_lt(v_start_3503_, v___x_3527_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = l_Int_repr(v_start_3503_);
lean_dec(v_start_3503_);
v___x_3530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
v___y_3509_ = v___y_3524_;
v___y_3510_ = v___x_3526_;
v___y_3511_ = v___x_3525_;
v___y_3512_ = v___x_3530_;
goto v___jp_3508_;
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3531_ = lean_unsigned_to_nat(1024u);
v___x_3532_ = l_Int_repr(v_start_3503_);
lean_dec(v_start_3503_);
v___x_3533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
v___x_3534_ = l_Repr_addAppParen(v___x_3533_, v___x_3531_);
v___y_3509_ = v___y_3524_;
v___y_3510_ = v___x_3526_;
v___y_3511_ = v___x_3525_;
v___y_3512_ = v___x_3534_;
goto v___jp_3508_;
}
}
}
}
case 4:
{
lean_object* v_items_3540_; lean_object* v___y_3542_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v_items_3540_ = lean_ctor_get(v_x_3452_, 0);
lean_inc_ref(v_items_3540_);
lean_dec_ref(v_x_3452_);
v___x_3550_ = lean_unsigned_to_nat(1024u);
v___x_3551_ = lean_nat_dec_le(v___x_3550_, v_prec_3453_);
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
v___x_3543_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15));
v___x_3544_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(v_items_3540_);
v___x_3545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3543_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___y_3542_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = 0;
v___x_3548_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3548_, 0, v___x_3546_);
lean_ctor_set_uint8(v___x_3548_, sizeof(void*)*1, v___x_3547_);
v___x_3549_ = l_Repr_addAppParen(v___x_3548_, v_prec_3453_);
return v___x_3549_;
}
}
case 5:
{
lean_object* v_items_3554_; lean_object* v___y_3556_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v_items_3554_ = lean_ctor_get(v_x_3452_, 0);
lean_inc_ref(v_items_3554_);
lean_dec_ref(v_x_3452_);
v___x_3564_ = lean_unsigned_to_nat(1024u);
v___x_3565_ = lean_nat_dec_le(v___x_3564_, v_prec_3453_);
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
v___x_3557_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18));
v___x_3558_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_items_3554_);
v___x_3559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3557_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___y_3556_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = 0;
v___x_3562_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set_uint8(v___x_3562_, sizeof(void*)*1, v___x_3561_);
v___x_3563_ = l_Repr_addAppParen(v___x_3562_, v_prec_3453_);
return v___x_3563_;
}
}
case 6:
{
lean_object* v_content_3568_; lean_object* v___y_3570_; lean_object* v___x_3578_; uint8_t v___x_3579_; 
v_content_3568_ = lean_ctor_get(v_x_3452_, 0);
lean_inc_ref(v_content_3568_);
lean_dec_ref(v_x_3452_);
v___x_3578_ = lean_unsigned_to_nat(1024u);
v___x_3579_ = lean_nat_dec_le(v___x_3578_, v_prec_3453_);
if (v___x_3579_ == 0)
{
lean_object* v___x_3580_; 
v___x_3580_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3570_ = v___x_3580_;
goto v___jp_3569_;
}
else
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3570_ = v___x_3581_;
goto v___jp_3569_;
}
v___jp_3569_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3571_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21));
v___x_3572_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3568_);
v___x_3573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3571_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___y_3570_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v___x_3575_ = 0;
v___x_3576_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3576_, 0, v___x_3574_);
lean_ctor_set_uint8(v___x_3576_, sizeof(void*)*1, v___x_3575_);
v___x_3577_ = l_Repr_addAppParen(v___x_3576_, v_prec_3453_);
return v___x_3577_;
}
}
default: 
{
lean_object* v_container_3582_; lean_object* v_content_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3631_; 
v_container_3582_ = lean_ctor_get(v_x_3452_, 0);
v_content_3583_ = lean_ctor_get(v_x_3452_, 1);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_x_3452_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3585_ = v_x_3452_;
v_isShared_3586_ = v_isSharedCheck_3631_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_content_3583_);
lean_inc(v_container_3582_);
lean_dec(v_x_3452_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3631_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___y_3588_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3627_ = lean_unsigned_to_nat(1024u);
v___x_3628_ = lean_nat_dec_le(v___x_3627_, v_prec_3453_);
if (v___x_3628_ == 0)
{
lean_object* v___x_3629_; 
v___x_3629_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3588_ = v___x_3629_;
goto v___jp_3587_;
}
else
{
lean_object* v___x_3630_; 
v___x_3630_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3588_ = v___x_3630_;
goto v___jp_3587_;
}
v___jp_3587_:
{
lean_object* v_name_3589_; lean_object* v_val_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3626_; 
v_name_3589_ = lean_ctor_get(v_container_3582_, 0);
v_val_3590_ = lean_ctor_get(v_container_3582_, 1);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_container_3582_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3592_ = v_container_3582_;
v_isShared_3593_ = v_isSharedCheck_3626_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_val_3590_);
lean_inc(v_name_3589_);
lean_dec(v_container_3582_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3626_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3600_; 
v___x_3594_ = lean_box(1);
v___x_3595_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24));
v___x_3596_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3597_ = lean_unsigned_to_nat(0u);
v___x_3598_ = l_Lean_Name_reprPrec(v_name_3589_, v___x_3597_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set_tag(v___x_3592_, 5);
lean_ctor_set(v___x_3592_, 1, v___x_3598_);
lean_ctor_set(v___x_3592_, 0, v___x_3596_);
v___x_3600_ = v___x_3592_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_object* v___x_3601_; uint8_t v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3601_ = l_Std_Format_nestD(v___x_3600_);
v___x_3602_ = 0;
v___x_3603_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3603_, 0, v___x_3601_);
lean_ctor_set_uint8(v___x_3603_, sizeof(void*)*1, v___x_3602_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set_tag(v___x_3585_, 5);
lean_ctor_set(v___x_3585_, 1, v___x_3594_);
lean_ctor_set(v___x_3585_, 0, v___x_3603_);
v___x_3605_ = v___x_3585_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v___x_3594_);
v___x_3605_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3606_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3607_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3590_);
lean_dec(v_val_3590_);
v___x_3608_ = l_Lean_Name_reprPrec(v___x_3607_, v___x_3597_);
v___x_3609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3606_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = l_Std_Format_nestD(v___x_3611_);
v___x_3613_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
lean_ctor_set_uint8(v___x_3613_, sizeof(void*)*1, v___x_3602_);
v___x_3614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3605_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = l_Std_Format_nestD(v___x_3614_);
v___x_3616_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
lean_ctor_set_uint8(v___x_3616_, sizeof(void*)*1, v___x_3602_);
v___x_3617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3595_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
lean_ctor_set(v___x_3618_, 1, v___x_3594_);
v___x_3619_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3583_);
v___x_3620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___y_3588_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
lean_ctor_set_uint8(v___x_3622_, sizeof(void*)*1, v___x_3602_);
v___x_3623_ = l_Repr_addAppParen(v___x_3622_, v_prec_3453_);
return v___x_3623_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object* v___y_3632_){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = lean_unsigned_to_nat(0u);
v___x_3634_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v___y_3632_, v___x_3633_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object* v_x_3635_, lean_object* v_prec_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_x_3635_, v_prec_3636_);
lean_dec(v_prec_3636_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object* v_xs_3638_){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; uint8_t v___x_3641_; 
v___x_3639_ = lean_array_get_size(v_xs_3638_);
v___x_3640_ = lean_unsigned_to_nat(0u);
v___x_3641_ = lean_nat_dec_eq(v___x_3639_, v___x_3640_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3642_ = lean_array_to_list(v_xs_3638_);
v___x_3643_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3644_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3642_, v___x_3643_);
v___x_3645_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3646_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
lean_ctor_set(v___x_3647_, 1, v___x_3644_);
v___x_3648_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3645_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
v___x_3651_ = l_Std_Format_fill(v___x_3650_);
return v___x_3651_;
}
else
{
lean_object* v___x_3652_; 
lean_dec_ref(v_xs_3638_);
v___x_3652_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3652_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object* v_x_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = ((lean_object*)(l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1));
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object* v_x_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3658_);
lean_dec(v_x_3658_);
return v_res_3659_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3669_ = lean_unsigned_to_nat(9u);
v___x_3670_ = lean_nat_to_int(v___x_3669_);
return v___x_3670_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = lean_unsigned_to_nat(15u);
v___x_3675_ = lean_nat_to_int(v___x_3674_);
return v___x_3675_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12(void){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = lean_unsigned_to_nat(11u);
v___x_3683_ = lean_nat_to_int(v___x_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object* v_x_3687_, lean_object* v_x_3688_, lean_object* v_x_3689_){
_start:
{
if (lean_obj_tag(v_x_3689_) == 0)
{
lean_dec(v_x_3687_);
return v_x_3688_;
}
else
{
lean_object* v_head_3690_; lean_object* v_tail_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3701_; 
v_head_3690_ = lean_ctor_get(v_x_3689_, 0);
v_tail_3691_ = lean_ctor_get(v_x_3689_, 1);
v_isSharedCheck_3701_ = !lean_is_exclusive(v_x_3689_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3693_ = v_x_3689_;
v_isShared_3694_ = v_isSharedCheck_3701_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_tail_3691_);
lean_inc(v_head_3690_);
lean_dec(v_x_3689_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3701_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
lean_inc(v_x_3687_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set_tag(v___x_3693_, 5);
lean_ctor_set(v___x_3693_, 1, v_x_3687_);
lean_ctor_set(v___x_3693_, 0, v_x_3688_);
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_x_3688_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_x_3687_);
v___x_3696_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3697_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3690_);
v___x_3698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3696_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(v_x_3687_, v___x_3698_, v_tail_3691_);
return v___x_3699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object* v_x_3702_, lean_object* v_x_3703_){
_start:
{
if (lean_obj_tag(v_x_3702_) == 0)
{
lean_object* v___x_3704_; 
lean_dec(v_x_3703_);
v___x_3704_ = lean_box(0);
return v___x_3704_;
}
else
{
lean_object* v_tail_3705_; 
v_tail_3705_ = lean_ctor_get(v_x_3702_, 1);
if (lean_obj_tag(v_tail_3705_) == 0)
{
lean_object* v_head_3706_; lean_object* v___x_3707_; 
lean_dec(v_x_3703_);
v_head_3706_ = lean_ctor_get(v_x_3702_, 0);
lean_inc(v_head_3706_);
lean_dec_ref(v_x_3702_);
v___x_3707_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3706_);
return v___x_3707_;
}
else
{
lean_object* v_head_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
lean_inc(v_tail_3705_);
v_head_3708_ = lean_ctor_get(v_x_3702_, 0);
lean_inc(v_head_3708_);
lean_dec_ref(v_x_3702_);
v___x_3709_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3708_);
v___x_3710_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(v_x_3703_, v___x_3709_, v_tail_3705_);
return v___x_3710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object* v_xs_3711_){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; uint8_t v___x_3714_; 
v___x_3712_ = lean_array_get_size(v_xs_3711_);
v___x_3713_ = lean_unsigned_to_nat(0u);
v___x_3714_ = lean_nat_dec_eq(v___x_3712_, v___x_3713_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3715_ = lean_array_to_list(v_xs_3711_);
v___x_3716_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3717_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(v___x_3715_, v___x_3716_);
v___x_3718_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3719_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
lean_ctor_set(v___x_3720_, 1, v___x_3717_);
v___x_3721_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3720_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3718_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = l_Std_Format_fill(v___x_3723_);
return v___x_3724_;
}
else
{
lean_object* v___x_3725_; 
lean_dec_ref(v_xs_3711_);
v___x_3725_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object* v_x_3726_){
_start:
{
lean_object* v_title_3727_; lean_object* v_titleString_3728_; lean_object* v_metadata_3729_; lean_object* v_content_3730_; lean_object* v_subParts_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; uint8_t v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v_title_3727_ = lean_ctor_get(v_x_3726_, 0);
lean_inc_ref(v_title_3727_);
v_titleString_3728_ = lean_ctor_get(v_x_3726_, 1);
lean_inc_ref(v_titleString_3728_);
v_metadata_3729_ = lean_ctor_get(v_x_3726_, 2);
lean_inc(v_metadata_3729_);
v_content_3730_ = lean_ctor_get(v_x_3726_, 3);
lean_inc_ref(v_content_3730_);
v_subParts_3731_ = lean_ctor_get(v_x_3726_, 4);
lean_inc_ref(v_subParts_3731_);
lean_dec_ref(v_x_3726_);
v___x_3732_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3733_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3));
v___x_3734_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4);
v___x_3735_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_title_3727_);
v___x_3736_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3734_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = 0;
v___x_3738_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3738_, 0, v___x_3736_);
lean_ctor_set_uint8(v___x_3738_, sizeof(void*)*1, v___x_3737_);
v___x_3739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3733_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_box(1);
v___x_3743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3741_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
v___x_3744_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6));
v___x_3745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3743_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
lean_ctor_set(v___x_3746_, 1, v___x_3732_);
v___x_3747_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7);
v___x_3748_ = l_String_quote(v_titleString_3728_);
v___x_3749_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
v___x_3750_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3747_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
lean_ctor_set_uint8(v___x_3751_, sizeof(void*)*1, v___x_3737_);
v___x_3752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3746_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
lean_ctor_set(v___x_3753_, 1, v___x_3740_);
v___x_3754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
lean_ctor_set(v___x_3754_, 1, v___x_3742_);
v___x_3755_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9));
v___x_3756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3754_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set(v___x_3757_, 1, v___x_3732_);
v___x_3758_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3759_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_metadata_3729_);
lean_dec(v_metadata_3729_);
v___x_3760_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3758_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
lean_ctor_set_uint8(v___x_3761_, sizeof(void*)*1, v___x_3737_);
v___x_3762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3757_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
lean_ctor_set(v___x_3763_, 1, v___x_3740_);
v___x_3764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3763_);
lean_ctor_set(v___x_3764_, 1, v___x_3742_);
v___x_3765_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11));
v___x_3766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3764_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
lean_ctor_set(v___x_3767_, 1, v___x_3732_);
v___x_3768_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12);
v___x_3769_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_content_3730_);
v___x_3770_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3768_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
lean_ctor_set_uint8(v___x_3771_, sizeof(void*)*1, v___x_3737_);
v___x_3772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3767_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
lean_ctor_set(v___x_3773_, 1, v___x_3740_);
v___x_3774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
lean_ctor_set(v___x_3774_, 1, v___x_3742_);
v___x_3775_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14));
v___x_3776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3774_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
v___x_3777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
lean_ctor_set(v___x_3777_, 1, v___x_3732_);
v___x_3778_ = l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(v_subParts_3731_);
v___x_3779_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3758_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*1, v___x_3737_);
v___x_3781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3777_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
v___x_3782_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3783_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
lean_ctor_set(v___x_3784_, 1, v___x_3781_);
v___x_3785_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3784_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3782_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3788_, 0, v___x_3787_);
lean_ctor_set_uint8(v___x_3788_, sizeof(void*)*1, v___x_3737_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object* v_x_3789_, lean_object* v_x_3790_, lean_object* v_x_3791_){
_start:
{
if (lean_obj_tag(v_x_3791_) == 0)
{
lean_dec(v_x_3789_);
return v_x_3790_;
}
else
{
lean_object* v_head_3792_; lean_object* v_tail_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3803_; 
v_head_3792_ = lean_ctor_get(v_x_3791_, 0);
v_tail_3793_ = lean_ctor_get(v_x_3791_, 1);
v_isSharedCheck_3803_ = !lean_is_exclusive(v_x_3791_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3795_ = v_x_3791_;
v_isShared_3796_ = v_isSharedCheck_3803_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_tail_3793_);
lean_inc(v_head_3792_);
lean_dec(v_x_3791_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3803_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
lean_inc(v_x_3789_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set_tag(v___x_3795_, 5);
lean_ctor_set(v___x_3795_, 1, v_x_3789_);
lean_ctor_set(v___x_3795_, 0, v_x_3790_);
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_x_3790_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_x_3789_);
v___x_3798_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3792_);
v___x_3800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3798_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v_x_3790_ = v___x_3800_;
v_x_3791_ = v_tail_3793_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object* v_x_3804_, lean_object* v_x_3805_){
_start:
{
lean_object* v_fst_3806_; lean_object* v_snd_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3817_; 
v_fst_3806_ = lean_ctor_get(v_x_3804_, 0);
v_snd_3807_ = lean_ctor_get(v_x_3804_, 1);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_x_3804_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3809_ = v_x_3804_;
v_isShared_3810_ = v_isSharedCheck_3817_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_snd_3807_);
lean_inc(v_fst_3806_);
lean_dec(v_x_3804_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3817_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3811_ = l_Lean_instReprDeclarationRange_repr___redArg(v_fst_3806_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set_tag(v___x_3809_, 1);
lean_ctor_set(v___x_3809_, 1, v_x_3805_);
lean_ctor_set(v___x_3809_, 0, v___x_3811_);
v___x_3813_ = v___x_3809_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_x_3805_);
v___x_3813_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_snd_3807_);
v___x_3815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
lean_ctor_set(v___x_3815_, 1, v___x_3813_);
return v___x_3815_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object* v_x_3818_, lean_object* v_x_3819_, lean_object* v_x_3820_){
_start:
{
if (lean_obj_tag(v_x_3820_) == 0)
{
lean_dec(v_x_3818_);
return v_x_3819_;
}
else
{
lean_object* v_head_3821_; lean_object* v_tail_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3831_; 
v_head_3821_ = lean_ctor_get(v_x_3820_, 0);
v_tail_3822_ = lean_ctor_get(v_x_3820_, 1);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_x_3820_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3824_ = v_x_3820_;
v_isShared_3825_ = v_isSharedCheck_3831_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_tail_3822_);
lean_inc(v_head_3821_);
lean_dec(v_x_3820_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3831_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
lean_inc(v_x_3818_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set_tag(v___x_3824_, 5);
lean_ctor_set(v___x_3824_, 1, v_x_3818_);
lean_ctor_set(v___x_3824_, 0, v_x_3819_);
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_x_3819_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_x_3818_);
v___x_3827_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3827_);
lean_ctor_set(v___x_3828_, 1, v_head_3821_);
v_x_3819_ = v___x_3828_;
v_x_3820_ = v_tail_3822_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object* v_x_3832_, lean_object* v_x_3833_){
_start:
{
if (lean_obj_tag(v_x_3832_) == 0)
{
lean_object* v___x_3834_; 
lean_dec(v_x_3833_);
v___x_3834_ = lean_box(0);
return v___x_3834_;
}
else
{
lean_object* v_tail_3835_; 
v_tail_3835_ = lean_ctor_get(v_x_3832_, 1);
if (lean_obj_tag(v_tail_3835_) == 0)
{
lean_object* v_head_3836_; 
lean_dec(v_x_3833_);
v_head_3836_ = lean_ctor_get(v_x_3832_, 0);
lean_inc(v_head_3836_);
lean_dec_ref(v_x_3832_);
return v_head_3836_;
}
else
{
lean_object* v_head_3837_; lean_object* v___x_3838_; 
lean_inc(v_tail_3835_);
v_head_3837_ = lean_ctor_get(v_x_3832_, 0);
lean_inc(v_head_3837_);
lean_dec_ref(v_x_3832_);
v___x_3838_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(v_x_3833_, v_head_3837_, v_tail_3835_);
return v___x_3838_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3840_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0));
v___x_3841_ = lean_string_length(v___x_3840_);
return v___x_3841_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1);
v___x_3843_ = lean_nat_to_int(v___x_3842_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object* v_x_3848_){
_start:
{
lean_object* v_fst_3849_; lean_object* v_snd_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3872_; 
v_fst_3849_ = lean_ctor_get(v_x_3848_, 0);
v_snd_3850_ = lean_ctor_get(v_x_3848_, 1);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_x_3848_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3852_ = v_x_3848_;
v_isShared_3853_ = v_isSharedCheck_3872_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_snd_3850_);
lean_inc(v_fst_3849_);
lean_dec(v_x_3848_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3872_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3854_ = l_Nat_reprFast(v_fst_3849_);
v___x_3855_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
v___x_3856_ = lean_box(0);
if (v_isShared_3853_ == 0)
{
lean_ctor_set_tag(v___x_3852_, 1);
lean_ctor_set(v___x_3852_, 1, v___x_3856_);
lean_ctor_set(v___x_3852_, 0, v___x_3855_);
v___x_3858_ = v___x_3852_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; lean_object* v___x_3870_; 
v___x_3859_ = l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(v_snd_3850_, v___x_3858_);
v___x_3860_ = l_List_reverse___redArg(v___x_3859_);
v___x_3861_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3862_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(v___x_3860_, v___x_3861_);
v___x_3863_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2);
v___x_3864_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3));
v___x_3865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
lean_ctor_set(v___x_3865_, 1, v___x_3862_);
v___x_3866_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4));
v___x_3867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3865_);
lean_ctor_set(v___x_3867_, 1, v___x_3866_);
v___x_3868_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3863_);
lean_ctor_set(v___x_3868_, 1, v___x_3867_);
v___x_3869_ = 0;
v___x_3870_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3870_, 0, v___x_3868_);
lean_ctor_set_uint8(v___x_3870_, sizeof(void*)*1, v___x_3869_);
return v___x_3870_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object* v_x_3873_, lean_object* v_x_3874_, lean_object* v_x_3875_){
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
lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3883_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3876_);
v___x_3884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3882_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v_x_3874_ = v___x_3884_;
v_x_3875_ = v_tail_3877_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object* v_x_3888_, lean_object* v_x_3889_, lean_object* v_x_3890_){
_start:
{
if (lean_obj_tag(v_x_3890_) == 0)
{
lean_dec(v_x_3888_);
return v_x_3889_;
}
else
{
lean_object* v_head_3891_; lean_object* v_tail_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3902_; 
v_head_3891_ = lean_ctor_get(v_x_3890_, 0);
v_tail_3892_ = lean_ctor_get(v_x_3890_, 1);
v_isSharedCheck_3902_ = !lean_is_exclusive(v_x_3890_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3894_ = v_x_3890_;
v_isShared_3895_ = v_isSharedCheck_3902_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_tail_3892_);
lean_inc(v_head_3891_);
lean_dec(v_x_3890_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3902_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
lean_inc(v_x_3888_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set_tag(v___x_3894_, 5);
lean_ctor_set(v___x_3894_, 1, v_x_3888_);
lean_ctor_set(v___x_3894_, 0, v_x_3889_);
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_x_3889_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_x_3888_);
v___x_3897_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3898_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3891_);
v___x_3899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3897_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(v_x_3888_, v___x_3899_, v_tail_3892_);
return v___x_3900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object* v_x_3903_, lean_object* v_x_3904_){
_start:
{
if (lean_obj_tag(v_x_3903_) == 0)
{
lean_object* v___x_3905_; 
lean_dec(v_x_3904_);
v___x_3905_ = lean_box(0);
return v___x_3905_;
}
else
{
lean_object* v_tail_3906_; 
v_tail_3906_ = lean_ctor_get(v_x_3903_, 1);
if (lean_obj_tag(v_tail_3906_) == 0)
{
lean_object* v_head_3907_; lean_object* v___x_3908_; 
lean_dec(v_x_3904_);
v_head_3907_ = lean_ctor_get(v_x_3903_, 0);
lean_inc(v_head_3907_);
lean_dec_ref(v_x_3903_);
v___x_3908_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3907_);
return v___x_3908_;
}
else
{
lean_object* v_head_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_inc(v_tail_3906_);
v_head_3909_ = lean_ctor_get(v_x_3903_, 0);
lean_inc(v_head_3909_);
lean_dec_ref(v_x_3903_);
v___x_3910_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3909_);
v___x_3911_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(v_x_3904_, v___x_3910_, v_tail_3906_);
return v___x_3911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object* v_xs_3912_){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; uint8_t v___x_3915_; 
v___x_3913_ = lean_array_get_size(v_xs_3912_);
v___x_3914_ = lean_unsigned_to_nat(0u);
v___x_3915_ = lean_nat_dec_eq(v___x_3913_, v___x_3914_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3916_ = lean_array_to_list(v_xs_3912_);
v___x_3917_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3918_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(v___x_3916_, v___x_3917_);
v___x_3919_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3920_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
lean_ctor_set(v___x_3921_, 1, v___x_3918_);
v___x_3922_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3919_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = l_Std_Format_fill(v___x_3924_);
return v___x_3925_;
}
else
{
lean_object* v___x_3926_; 
lean_dec_ref(v_xs_3912_);
v___x_3926_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3926_;
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3942_ = lean_unsigned_to_nat(20u);
v___x_3943_ = lean_nat_to_int(v___x_3942_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object* v_x_3944_){
_start:
{
lean_object* v_text_3945_; lean_object* v_sections_3946_; lean_object* v_declarationRange_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; uint8_t v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_text_3945_ = lean_ctor_get(v_x_3944_, 0);
lean_inc_ref(v_text_3945_);
v_sections_3946_ = lean_ctor_get(v_x_3944_, 1);
lean_inc_ref(v_sections_3946_);
v_declarationRange_3947_ = lean_ctor_get(v_x_3944_, 2);
lean_inc_ref(v_declarationRange_3947_);
lean_dec_ref(v_x_3944_);
v___x_3948_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3949_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3));
v___x_3950_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3951_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_text_3945_);
v___x_3952_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3950_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = 0;
v___x_3954_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3954_, 0, v___x_3952_);
lean_ctor_set_uint8(v___x_3954_, sizeof(void*)*1, v___x_3953_);
v___x_3955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3949_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
v___x_3956_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3955_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = lean_box(1);
v___x_3959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3957_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5));
v___x_3961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3959_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v___x_3948_);
v___x_3963_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3964_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(v_sections_3946_);
v___x_3965_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3963_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
v___x_3966_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
lean_ctor_set_uint8(v___x_3966_, sizeof(void*)*1, v___x_3953_);
v___x_3967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3962_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
lean_ctor_set(v___x_3968_, 1, v___x_3956_);
v___x_3969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
lean_ctor_set(v___x_3969_, 1, v___x_3958_);
v___x_3970_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7));
v___x_3971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3969_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
v___x_3972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
lean_ctor_set(v___x_3972_, 1, v___x_3948_);
v___x_3973_ = lean_obj_once(&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8, &l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once, _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8);
v___x_3974_ = l_Lean_instReprDeclarationRange_repr___redArg(v_declarationRange_3947_);
v___x_3975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3973_);
lean_ctor_set(v___x_3975_, 1, v___x_3974_);
v___x_3976_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
lean_ctor_set_uint8(v___x_3976_, sizeof(void*)*1, v___x_3953_);
v___x_3977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3972_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3979_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
lean_ctor_set(v___x_3980_, 1, v___x_3977_);
v___x_3981_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3980_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
v___x_3983_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3978_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
v___x_3984_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3984_, 0, v___x_3983_);
lean_ctor_set_uint8(v___x_3984_, sizeof(void*)*1, v___x_3953_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object* v_x_3985_, lean_object* v_prec_3986_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(v_x_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object* v_x_3988_, lean_object* v_prec_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_VersoModuleDocs_instReprSnippet_repr(v_x_3988_, v_prec_3989_);
lean_dec(v_prec_3989_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object* v_x_3991_, lean_object* v_x_3992_){
_start:
{
lean_object* v___x_3993_; 
v___x_3993_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_x_3991_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object* v_x_3994_, lean_object* v_x_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(v_x_3994_, v_x_3995_);
lean_dec(v_x_3995_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_3997_, lean_object* v_prec_3998_){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_x_3997_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_x_4000_, lean_object* v_prec_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(v_x_4000_, v_prec_4001_);
lean_dec(v_prec_4001_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object* v_x_4003_, lean_object* v_prec_4004_){
_start:
{
lean_object* v___x_4005_; 
v___x_4005_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_x_4003_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_x_4006_, lean_object* v_prec_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(v_x_4006_, v_prec_4007_);
lean_dec(v_prec_4007_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object* v_x_4009_, lean_object* v_x_4010_){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_4009_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object* v_x_4012_, lean_object* v_x_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(v_x_4012_, v_x_4013_);
lean_dec(v_x_4013_);
lean_dec(v_x_4012_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object* v_x_4015_, lean_object* v_prec_4016_){
_start:
{
lean_object* v___x_4017_; 
v___x_4017_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_x_4015_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object* v_x_4018_, lean_object* v_prec_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(v_x_4018_, v_prec_4019_);
lean_dec(v_prec_4019_);
return v_res_4020_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object* v_level_4023_, lean_object* v_snippet_4024_){
_start:
{
lean_object* v_sections_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; uint8_t v___x_4028_; 
v_sections_4025_ = lean_ctor_get(v_snippet_4024_, 1);
v___x_4026_ = lean_unsigned_to_nat(0u);
v___x_4027_ = lean_array_get_size(v_sections_4025_);
v___x_4028_ = lean_nat_dec_lt(v___x_4026_, v___x_4027_);
if (v___x_4028_ == 0)
{
uint8_t v___x_4029_; 
v___x_4029_ = 1;
return v___x_4029_;
}
else
{
lean_object* v___x_4030_; lean_object* v_fst_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; uint8_t v___x_4034_; 
v___x_4030_ = lean_array_fget_borrowed(v_sections_4025_, v___x_4026_);
v_fst_4031_ = lean_ctor_get(v___x_4030_, 0);
v___x_4032_ = lean_unsigned_to_nat(1u);
v___x_4033_ = lean_nat_add(v_level_4023_, v___x_4032_);
v___x_4034_ = lean_nat_dec_le(v_fst_4031_, v___x_4033_);
lean_dec(v___x_4033_);
return v___x_4034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object* v_level_4035_, lean_object* v_snippet_4036_){
_start:
{
uint8_t v_res_4037_; lean_object* v_r_4038_; 
v_res_4037_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_level_4035_, v_snippet_4036_);
lean_dec_ref(v_snippet_4036_);
lean_dec(v_level_4035_);
v_r_4038_ = lean_box(v_res_4037_);
return v_r_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object* v_snippet_4039_){
_start:
{
lean_object* v_sections_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; uint8_t v___x_4044_; 
v_sections_4040_ = lean_ctor_get(v_snippet_4039_, 1);
v___x_4041_ = lean_array_get_size(v_sections_4040_);
v___x_4042_ = lean_unsigned_to_nat(1u);
v___x_4043_ = lean_nat_sub(v___x_4041_, v___x_4042_);
v___x_4044_ = lean_nat_dec_lt(v___x_4043_, v___x_4041_);
if (v___x_4044_ == 0)
{
lean_object* v___x_4045_; 
lean_dec(v___x_4043_);
v___x_4045_ = lean_box(0);
return v___x_4045_;
}
else
{
lean_object* v___x_4046_; lean_object* v_fst_4047_; lean_object* v___x_4048_; 
v___x_4046_ = lean_array_fget_borrowed(v_sections_4040_, v___x_4043_);
lean_dec(v___x_4043_);
v_fst_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_fst_4047_);
v___x_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4048_, 0, v_fst_4047_);
return v___x_4048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object* v_snippet_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4049_);
lean_dec_ref(v_snippet_4049_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object* v_snippet_4051_, lean_object* v_block_4052_){
_start:
{
lean_object* v_text_4053_; lean_object* v_sections_4054_; lean_object* v_declarationRange_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; uint8_t v___x_4058_; 
v_text_4053_ = lean_ctor_get(v_snippet_4051_, 0);
v_sections_4054_ = lean_ctor_get(v_snippet_4051_, 1);
v_declarationRange_4055_ = lean_ctor_get(v_snippet_4051_, 2);
v___x_4056_ = lean_array_get_size(v_sections_4054_);
v___x_4057_ = lean_unsigned_to_nat(0u);
v___x_4058_ = lean_nat_dec_eq(v___x_4056_, v___x_4057_);
if (v___x_4058_ == 0)
{
lean_object* v___x_4059_; lean_object* v___x_4060_; uint8_t v___x_4061_; 
v___x_4059_ = lean_unsigned_to_nat(1u);
v___x_4060_ = lean_nat_sub(v___x_4056_, v___x_4059_);
v___x_4061_ = lean_nat_dec_lt(v___x_4060_, v___x_4056_);
if (v___x_4061_ == 0)
{
lean_dec(v___x_4060_);
lean_dec_ref(v_block_4052_);
return v_snippet_4051_;
}
else
{
lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4105_; 
lean_inc_ref(v_declarationRange_4055_);
lean_inc_ref(v_sections_4054_);
lean_inc_ref(v_text_4053_);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_snippet_4051_);
if (v_isSharedCheck_4105_ == 0)
{
lean_object* v_unused_4106_; lean_object* v_unused_4107_; lean_object* v_unused_4108_; 
v_unused_4106_ = lean_ctor_get(v_snippet_4051_, 2);
lean_dec(v_unused_4106_);
v_unused_4107_ = lean_ctor_get(v_snippet_4051_, 1);
lean_dec(v_unused_4107_);
v_unused_4108_ = lean_ctor_get(v_snippet_4051_, 0);
lean_dec(v_unused_4108_);
v___x_4063_ = v_snippet_4051_;
v_isShared_4064_ = v_isSharedCheck_4105_;
goto v_resetjp_4062_;
}
else
{
lean_dec(v_snippet_4051_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4105_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v_v_4065_; lean_object* v_snd_4066_; lean_object* v_snd_4067_; lean_object* v_fst_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4103_; 
v_v_4065_ = lean_array_fget(v_sections_4054_, v___x_4060_);
v_snd_4066_ = lean_ctor_get(v_v_4065_, 1);
lean_inc(v_snd_4066_);
v_snd_4067_ = lean_ctor_get(v_snd_4066_, 1);
lean_inc(v_snd_4067_);
v_fst_4068_ = lean_ctor_get(v_v_4065_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v_v_4065_);
if (v_isSharedCheck_4103_ == 0)
{
lean_object* v_unused_4104_; 
v_unused_4104_ = lean_ctor_get(v_v_4065_, 1);
lean_dec(v_unused_4104_);
v___x_4070_ = v_v_4065_;
v_isShared_4071_ = v_isSharedCheck_4103_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_fst_4068_);
lean_dec(v_v_4065_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4103_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v_fst_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4101_; 
v_fst_4072_ = lean_ctor_get(v_snd_4066_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_snd_4066_);
if (v_isSharedCheck_4101_ == 0)
{
lean_object* v_unused_4102_; 
v_unused_4102_ = lean_ctor_get(v_snd_4066_, 1);
lean_dec(v_unused_4102_);
v___x_4074_ = v_snd_4066_;
v_isShared_4075_ = v_isSharedCheck_4101_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_fst_4072_);
lean_dec(v_snd_4066_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4101_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v_title_4076_; lean_object* v_titleString_4077_; lean_object* v_metadata_4078_; lean_object* v_content_4079_; lean_object* v_subParts_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4100_; 
v_title_4076_ = lean_ctor_get(v_snd_4067_, 0);
v_titleString_4077_ = lean_ctor_get(v_snd_4067_, 1);
v_metadata_4078_ = lean_ctor_get(v_snd_4067_, 2);
v_content_4079_ = lean_ctor_get(v_snd_4067_, 3);
v_subParts_4080_ = lean_ctor_get(v_snd_4067_, 4);
v_isSharedCheck_4100_ = !lean_is_exclusive(v_snd_4067_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4082_ = v_snd_4067_;
v_isShared_4083_ = v_isSharedCheck_4100_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_subParts_4080_);
lean_inc(v_content_4079_);
lean_inc(v_metadata_4078_);
lean_inc(v_titleString_4077_);
lean_inc(v_title_4076_);
lean_dec(v_snd_4067_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4100_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4084_; lean_object* v_xs_x27_4085_; lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4084_ = lean_box(0);
v_xs_x27_4085_ = lean_array_fset(v_sections_4054_, v___x_4060_, v___x_4084_);
v___x_4086_ = lean_array_push(v_content_4079_, v_block_4052_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 3, v___x_4086_);
v___x_4088_ = v___x_4082_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_title_4076_);
lean_ctor_set(v_reuseFailAlloc_4099_, 1, v_titleString_4077_);
lean_ctor_set(v_reuseFailAlloc_4099_, 2, v_metadata_4078_);
lean_ctor_set(v_reuseFailAlloc_4099_, 3, v___x_4086_);
lean_ctor_set(v_reuseFailAlloc_4099_, 4, v_subParts_4080_);
v___x_4088_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4090_; 
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 1, v___x_4088_);
v___x_4090_ = v___x_4074_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_fst_4072_);
lean_ctor_set(v_reuseFailAlloc_4098_, 1, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
lean_object* v___x_4092_; 
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 1, v___x_4090_);
v___x_4092_ = v___x_4070_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_fst_4068_);
lean_ctor_set(v_reuseFailAlloc_4097_, 1, v___x_4090_);
v___x_4092_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
lean_object* v___x_4093_; lean_object* v___x_4095_; 
v___x_4093_ = lean_array_fset(v_xs_x27_4085_, v___x_4060_, v___x_4092_);
lean_dec(v___x_4060_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 1, v___x_4093_);
v___x_4095_ = v___x_4063_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_text_4053_);
lean_ctor_set(v_reuseFailAlloc_4096_, 1, v___x_4093_);
lean_ctor_set(v_reuseFailAlloc_4096_, 2, v_declarationRange_4055_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
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
lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4116_; 
lean_inc_ref(v_declarationRange_4055_);
lean_inc_ref(v_sections_4054_);
lean_inc_ref(v_text_4053_);
v_isSharedCheck_4116_ = !lean_is_exclusive(v_snippet_4051_);
if (v_isSharedCheck_4116_ == 0)
{
lean_object* v_unused_4117_; lean_object* v_unused_4118_; lean_object* v_unused_4119_; 
v_unused_4117_ = lean_ctor_get(v_snippet_4051_, 2);
lean_dec(v_unused_4117_);
v_unused_4118_ = lean_ctor_get(v_snippet_4051_, 1);
lean_dec(v_unused_4118_);
v_unused_4119_ = lean_ctor_get(v_snippet_4051_, 0);
lean_dec(v_unused_4119_);
v___x_4110_ = v_snippet_4051_;
v_isShared_4111_ = v_isSharedCheck_4116_;
goto v_resetjp_4109_;
}
else
{
lean_dec(v_snippet_4051_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4116_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4112_; lean_object* v___x_4114_; 
v___x_4112_ = lean_array_push(v_text_4053_, v_block_4052_);
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 0, v___x_4112_);
v___x_4114_ = v___x_4110_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4112_);
lean_ctor_set(v_reuseFailAlloc_4115_, 1, v_sections_4054_);
lean_ctor_set(v_reuseFailAlloc_4115_, 2, v_declarationRange_4055_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object* v_snippet_4120_, lean_object* v_level_4121_, lean_object* v_range_4122_, lean_object* v_part_4123_){
_start:
{
lean_object* v_text_4124_; lean_object* v_sections_4125_; lean_object* v_declarationRange_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4136_; 
v_text_4124_ = lean_ctor_get(v_snippet_4120_, 0);
v_sections_4125_ = lean_ctor_get(v_snippet_4120_, 1);
v_declarationRange_4126_ = lean_ctor_get(v_snippet_4120_, 2);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_snippet_4120_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4128_ = v_snippet_4120_;
v_isShared_4129_ = v_isSharedCheck_4136_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_declarationRange_4126_);
lean_inc(v_sections_4125_);
lean_inc(v_text_4124_);
lean_dec(v_snippet_4120_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4136_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4134_; 
v___x_4130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4130_, 0, v_range_4122_);
lean_ctor_set(v___x_4130_, 1, v_part_4123_);
v___x_4131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4131_, 0, v_level_4121_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
v___x_4132_ = lean_array_push(v_sections_4125_, v___x_4131_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 1, v___x_4132_);
v___x_4134_ = v___x_4128_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_text_4124_);
lean_ctor_set(v_reuseFailAlloc_4135_, 1, v___x_4132_);
lean_ctor_set(v_reuseFailAlloc_4135_, 2, v_declarationRange_4126_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0(lean_object* v___x_4137_, lean_object* v___x_4138_, lean_object* v_x_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v___x_4143_; 
v___x_4143_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v___x_4137_, v___x_4138_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1(lean_object* v___x_4144_, lean_object* v___x_4145_, lean_object* v___x_4146_, lean_object* v_a_4147_, lean_object* v_x_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v___x_4152_; lean_object* v_snd_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4161_; 
v___x_4152_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(lean_box(0), lean_box(0), v___x_4144_, v___x_4145_, v_a_4147_, v___y_4150_, v___y_4151_);
v_snd_4153_ = lean_ctor_get(v___x_4152_, 1);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4161_ == 0)
{
lean_object* v_unused_4162_; 
v_unused_4162_ = lean_ctor_get(v___x_4152_, 0);
lean_dec(v_unused_4162_);
v___x_4155_ = v___x_4152_;
v_isShared_4156_ = v_isSharedCheck_4161_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_snd_4153_);
lean_dec(v___x_4152_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4161_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4157_; lean_object* v___x_4159_; 
v___x_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4146_);
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 0, v___x_4157_);
v___x_4159_ = v___x_4155_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4157_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v_snd_4153_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__2(lean_object* v___x_4163_, lean_object* v___x_4164_, lean_object* v_a_4165_, lean_object* v_x_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v___x_4170_; lean_object* v_snd_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4179_; 
v___x_4170_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(lean_box(0), v___x_4163_, v_a_4165_, v___y_4168_, v___y_4169_);
v_snd_4171_ = lean_ctor_get(v___x_4170_, 1);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4179_ == 0)
{
lean_object* v_unused_4180_; 
v_unused_4180_ = lean_ctor_get(v___x_4170_, 0);
lean_dec(v_unused_4180_);
v___x_4173_ = v___x_4170_;
v_isShared_4174_ = v_isSharedCheck_4179_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_snd_4171_);
lean_dec(v___x_4170_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4179_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4175_; lean_object* v___x_4177_; 
v___x_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4164_);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v___x_4175_);
v___x_4177_ = v___x_4173_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4175_);
lean_ctor_set(v_reuseFailAlloc_4178_, 1, v_snd_4171_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3(uint32_t v___x_4181_, lean_object* v_s_4182_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = lean_string_push(v_s_4182_, v___x_4181_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__3___boxed(lean_object* v___x_4184_, lean_object* v_s_4185_){
_start:
{
uint32_t v___x_5724__boxed_4186_; lean_object* v_res_4187_; 
v___x_5724__boxed_4186_ = lean_unbox_uint32(v___x_4184_);
lean_dec(v___x_4184_);
v_res_4187_ = l_Lean_instToMarkdownSnippet___lam__3(v___x_5724__boxed_4186_, v_s_4185_);
return v_res_4187_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_4188_; lean_object* v___x_4189_; 
v___x_4188_ = 35;
v___x_4189_ = lean_box_uint32(v___x_4188_);
return v___x_4189_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0(void){
_start:
{
lean_object* v___x_4190_; lean_object* v___f_4191_; 
v___x_4190_ = l_Lean_instToMarkdownSnippet___lam__4___closed__0___boxed__const__1;
v___f_4191_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__3___boxed), 2, 1);
lean_closure_set(v___f_4191_, 0, v___x_4190_);
return v___f_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__4(lean_object* v___x_4192_, lean_object* v___f_4193_, lean_object* v___x_4194_, lean_object* v___f_4195_, lean_object* v_a_4196_, lean_object* v_x_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v_snd_4201_; lean_object* v_fst_4202_; lean_object* v_snd_4203_; lean_object* v___x_4204_; lean_object* v___f_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v_snd_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v_snd_4213_; lean_object* v_title_4214_; lean_object* v_content_4215_; size_t v_sz_4216_; size_t v___x_4217_; lean_object* v___x_5585__overap_4218_; lean_object* v___x_4219_; lean_object* v_snd_4220_; lean_object* v___x_4221_; lean_object* v_snd_4222_; size_t v_sz_4223_; lean_object* v___x_5591__overap_4224_; lean_object* v___x_4225_; lean_object* v_snd_4226_; lean_object* v___x_4227_; lean_object* v_snd_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4236_; 
v_snd_4201_ = lean_ctor_get(v_a_4196_, 1);
lean_inc(v_snd_4201_);
v_fst_4202_ = lean_ctor_get(v_a_4196_, 0);
lean_inc(v_fst_4202_);
lean_dec_ref(v_a_4196_);
v_snd_4203_ = lean_ctor_get(v_snd_4201_, 1);
lean_inc(v_snd_4203_);
lean_dec(v_snd_4201_);
v___x_4204_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___f_4205_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___lam__4___closed__0, &l_Lean_instToMarkdownSnippet___lam__4___closed__0_once, _init_l_Lean_instToMarkdownSnippet___lam__4___closed__0);
v___x_4206_ = lean_unsigned_to_nat(1u);
v___x_4207_ = lean_nat_add(v_fst_4202_, v___x_4206_);
lean_dec(v_fst_4202_);
v___x_4208_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___f_4205_, v___x_4207_, v___x_4204_);
v___x_4209_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_4208_, v___y_4200_);
lean_dec(v___x_4208_);
v_snd_4210_ = lean_ctor_get(v___x_4209_, 1);
lean_inc(v_snd_4210_);
lean_dec_ref(v___x_4209_);
v___x_4211_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_partMarkdown___at___00Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___private__1___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___redArg___closed__0));
v___x_4212_ = l_Lean_Doc_MarkdownM_push___redArg(v___x_4211_, v_snd_4210_);
v_snd_4213_ = lean_ctor_get(v___x_4212_, 1);
lean_inc(v_snd_4213_);
lean_dec_ref(v___x_4212_);
v_title_4214_ = lean_ctor_get(v_snd_4203_, 0);
lean_inc_ref(v_title_4214_);
v_content_4215_ = lean_ctor_get(v_snd_4203_, 3);
lean_inc_ref(v_content_4215_);
lean_dec(v_snd_4203_);
v_sz_4216_ = lean_array_size(v_title_4214_);
v___x_4217_ = ((size_t)0ULL);
lean_inc_ref(v___x_4192_);
v___x_5585__overap_4218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4192_, v_title_4214_, v___f_4193_, v_sz_4216_, v___x_4217_, v___x_4194_);
lean_inc_ref(v___y_4199_);
v___x_4219_ = lean_apply_2(v___x_5585__overap_4218_, v___y_4199_, v_snd_4213_);
v_snd_4220_ = lean_ctor_get(v___x_4219_, 1);
lean_inc(v_snd_4220_);
lean_dec_ref(v___x_4219_);
v___x_4221_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4220_);
v_snd_4222_ = lean_ctor_get(v___x_4221_, 1);
lean_inc(v_snd_4222_);
lean_dec_ref(v___x_4221_);
v_sz_4223_ = lean_array_size(v_content_4215_);
v___x_5591__overap_4224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4192_, v_content_4215_, v___f_4195_, v_sz_4223_, v___x_4217_, v___x_4194_);
v___x_4225_ = lean_apply_2(v___x_5591__overap_4224_, v___y_4199_, v_snd_4222_);
v_snd_4226_ = lean_ctor_get(v___x_4225_, 1);
lean_inc(v_snd_4226_);
lean_dec_ref(v___x_4225_);
v___x_4227_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4226_);
v_snd_4228_ = lean_ctor_get(v___x_4227_, 1);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4236_ == 0)
{
lean_object* v_unused_4237_; 
v_unused_4237_ = lean_ctor_get(v___x_4227_, 0);
lean_dec(v_unused_4237_);
v___x_4230_ = v___x_4227_;
v_isShared_4231_ = v_isSharedCheck_4236_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_snd_4228_);
lean_dec(v___x_4227_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4236_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4232_; lean_object* v___x_4234_; 
v___x_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4194_);
if (v_isShared_4231_ == 0)
{
lean_ctor_set(v___x_4230_, 0, v___x_4232_);
v___x_4234_ = v___x_4230_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4232_);
lean_ctor_set(v_reuseFailAlloc_4235_, 1, v_snd_4228_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__5(lean_object* v___x_4238_, lean_object* v___x_4239_, lean_object* v___x_4240_, lean_object* v___f_4241_, lean_object* v_x_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_text_4245_; lean_object* v_sections_4246_; lean_object* v_snd_4248_; lean_object* v___y_4269_; lean_object* v___x_4271_; lean_object* v___x_4272_; uint8_t v___x_4273_; 
v_text_4245_ = lean_ctor_get(v_x_4242_, 0);
lean_inc_ref(v_text_4245_);
v_sections_4246_ = lean_ctor_get(v_x_4242_, 1);
lean_inc_ref(v_sections_4246_);
lean_dec_ref(v_x_4242_);
v___x_4271_ = lean_unsigned_to_nat(0u);
v___x_4272_ = lean_array_get_size(v_text_4245_);
v___x_4273_ = lean_nat_dec_lt(v___x_4271_, v___x_4272_);
if (v___x_4273_ == 0)
{
lean_dec_ref(v_text_4245_);
lean_dec_ref(v___f_4241_);
v_snd_4248_ = v___y_4244_;
goto v___jp_4247_;
}
else
{
lean_object* v___x_4274_; uint8_t v___x_4275_; 
v___x_4274_ = lean_box(0);
v___x_4275_ = lean_nat_dec_le(v___x_4272_, v___x_4272_);
if (v___x_4275_ == 0)
{
if (v___x_4273_ == 0)
{
lean_dec_ref(v_text_4245_);
lean_dec_ref(v___f_4241_);
v_snd_4248_ = v___y_4244_;
goto v___jp_4247_;
}
else
{
size_t v___x_4276_; size_t v___x_4277_; lean_object* v___x_5634__overap_4278_; lean_object* v___x_4279_; 
v___x_4276_ = ((size_t)0ULL);
v___x_4277_ = lean_usize_of_nat(v___x_4272_);
lean_inc_ref(v___x_4240_);
v___x_5634__overap_4278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4240_, v___f_4241_, v_text_4245_, v___x_4276_, v___x_4277_, v___x_4274_);
lean_inc_ref(v___y_4243_);
v___x_4279_ = lean_apply_2(v___x_5634__overap_4278_, v___y_4243_, v___y_4244_);
v___y_4269_ = v___x_4279_;
goto v___jp_4268_;
}
}
else
{
size_t v___x_4280_; size_t v___x_4281_; lean_object* v___x_5637__overap_4282_; lean_object* v___x_4283_; 
v___x_4280_ = ((size_t)0ULL);
v___x_4281_ = lean_usize_of_nat(v___x_4272_);
lean_inc_ref(v___x_4240_);
v___x_5637__overap_4282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4240_, v___f_4241_, v_text_4245_, v___x_4280_, v___x_4281_, v___x_4274_);
lean_inc_ref(v___y_4243_);
v___x_4283_ = lean_apply_2(v___x_5637__overap_4282_, v___y_4243_, v___y_4244_);
v___y_4269_ = v___x_4283_;
goto v___jp_4268_;
}
}
v___jp_4247_:
{
lean_object* v___x_4249_; lean_object* v_snd_4250_; lean_object* v___x_4251_; lean_object* v___f_4252_; lean_object* v___f_4253_; lean_object* v___f_4254_; size_t v_sz_4255_; size_t v___x_4256_; lean_object* v___x_5619__overap_4257_; lean_object* v___x_4258_; lean_object* v_snd_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
v___x_4249_ = l_Lean_Doc_MarkdownM_endBlock___redArg(v_snd_4248_);
v_snd_4250_ = lean_ctor_get(v___x_4249_, 1);
lean_inc(v_snd_4250_);
lean_dec_ref(v___x_4249_);
v___x_4251_ = lean_box(0);
lean_inc_ref(v___x_4238_);
v___f_4252_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__1), 8, 3);
lean_closure_set(v___f_4252_, 0, v___x_4238_);
lean_closure_set(v___f_4252_, 1, v___x_4239_);
lean_closure_set(v___f_4252_, 2, v___x_4251_);
v___f_4253_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__2), 7, 2);
lean_closure_set(v___f_4253_, 0, v___x_4238_);
lean_closure_set(v___f_4253_, 1, v___x_4251_);
lean_inc_ref(v___x_4240_);
v___f_4254_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__4), 9, 4);
lean_closure_set(v___f_4254_, 0, v___x_4240_);
lean_closure_set(v___f_4254_, 1, v___f_4253_);
lean_closure_set(v___f_4254_, 2, v___x_4251_);
lean_closure_set(v___f_4254_, 3, v___f_4252_);
v_sz_4255_ = lean_array_size(v_sections_4246_);
v___x_4256_ = ((size_t)0ULL);
v___x_5619__overap_4257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_4240_, v_sections_4246_, v___f_4254_, v_sz_4255_, v___x_4256_, v___x_4251_);
v___x_4258_ = lean_apply_2(v___x_5619__overap_4257_, v___y_4243_, v_snd_4250_);
v_snd_4259_ = lean_ctor_get(v___x_4258_, 1);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4266_ == 0)
{
lean_object* v_unused_4267_; 
v_unused_4267_ = lean_ctor_get(v___x_4258_, 0);
lean_dec(v_unused_4267_);
v___x_4261_ = v___x_4258_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_snd_4259_);
lean_dec(v___x_4258_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
lean_ctor_set(v___x_4261_, 0, v___x_4251_);
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4251_);
lean_ctor_set(v_reuseFailAlloc_4265_, 1, v_snd_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
v___jp_4268_:
{
lean_object* v_snd_4270_; 
v_snd_4270_ = lean_ctor_get(v___y_4269_, 1);
lean_inc(v_snd_4270_);
lean_dec_ref(v___y_4269_);
v_snd_4248_ = v_snd_4270_;
goto v___jp_4247_;
}
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___closed__0(void){
_start:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___f_4286_; 
v___x_4284_ = l_Lean_instMarkdownBlockElabInlineElabBlock;
v___x_4285_ = l_Lean_instMarkdownInlineElabInline;
v___f_4286_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__0), 6, 2);
lean_closure_set(v___f_4286_, 0, v___x_4285_);
lean_closure_set(v___f_4286_, 1, v___x_4284_);
return v___f_4286_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet___closed__1(void){
_start:
{
lean_object* v___f_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___f_4291_; 
v___f_4287_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___closed__0, &l_Lean_instToMarkdownSnippet___closed__0_once, _init_l_Lean_instToMarkdownSnippet___closed__0);
v___x_4288_ = lean_obj_once(&l_Lean_instMarkdownInlineElabInline___closed__20, &l_Lean_instMarkdownInlineElabInline___closed__20_once, _init_l_Lean_instMarkdownInlineElabInline___closed__20);
v___x_4289_ = l_Lean_instMarkdownBlockElabInlineElabBlock;
v___x_4290_ = l_Lean_instMarkdownInlineElabInline;
v___f_4291_ = lean_alloc_closure((void*)(l_Lean_instToMarkdownSnippet___lam__5), 7, 4);
lean_closure_set(v___f_4291_, 0, v___x_4290_);
lean_closure_set(v___f_4291_, 1, v___x_4289_);
lean_closure_set(v___f_4291_, 2, v___x_4288_);
lean_closure_set(v___f_4291_, 3, v___f_4287_);
return v___f_4291_;
}
}
static lean_object* _init_l_Lean_instToMarkdownSnippet(void){
_start:
{
lean_object* v___f_4292_; 
v___f_4292_ = lean_obj_once(&l_Lean_instToMarkdownSnippet___closed__1, &l_Lean_instToMarkdownSnippet___closed__1_once, _init_l_Lean_instToMarkdownSnippet___closed__1);
return v___f_4292_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0(void){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_4293_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1(void){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = lean_box(0);
v___x_4295_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_4296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
lean_ctor_set(v___x_4296_, 1, v___x_4294_);
return v___x_4296_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default(void){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__1, &l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1);
return v___x_4297_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs(void){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Lean_instInhabitedVersoModuleDocs_default;
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object* v___x_4305_, lean_object* v_v_4306_, lean_object* v_x_4307_){
_start:
{
lean_object* v_snippets_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4331_; 
v_snippets_4308_ = lean_ctor_get(v_v_4306_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v_v_4306_);
if (v_isSharedCheck_4331_ == 0)
{
lean_object* v_unused_4332_; 
v_unused_4332_ = lean_ctor_get(v_v_4306_, 1);
lean_dec(v_unused_4332_);
v___x_4310_ = v_v_4306_;
v_isShared_4311_ = v_isSharedCheck_4331_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_snippets_4308_);
lean_dec(v_v_4306_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4331_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4319_; 
v___x_4312_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___x_4313_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_4314_ = lean_box(1);
v___x_4315_ = ((lean_object*)(l_Lean_instReprVersoModuleDocs___lam__0___closed__2));
v___x_4316_ = l_Lean_PersistentArray_toArray___redArg(v_snippets_4308_);
lean_dec_ref(v_snippets_4308_);
v___x_4317_ = l_Array_repr___redArg(v___x_4305_, v___x_4316_);
if (v_isShared_4311_ == 0)
{
lean_ctor_set_tag(v___x_4310_, 5);
lean_ctor_set(v___x_4310_, 1, v___x_4317_);
lean_ctor_set(v___x_4310_, 0, v___x_4315_);
v___x_4319_ = v___x_4310_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4315_);
lean_ctor_set(v_reuseFailAlloc_4330_, 1, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
lean_object* v___x_4320_; uint8_t v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4312_);
lean_ctor_set(v___x_4320_, 1, v___x_4319_);
v___x_4321_ = 0;
v___x_4322_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4322_, 0, v___x_4320_);
lean_ctor_set_uint8(v___x_4322_, sizeof(void*)*1, v___x_4321_);
lean_inc_ref(v___x_4322_);
v___x_4323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4313_);
lean_ctor_set(v___x_4323_, 1, v___x_4322_);
v___x_4324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4323_);
lean_ctor_set(v___x_4324_, 1, v___x_4314_);
v___x_4325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4324_);
lean_ctor_set(v___x_4325_, 1, v___x_4322_);
v___x_4326_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_4327_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4325_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
v___x_4328_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4328_, 0, v___x_4312_);
lean_ctor_set(v___x_4328_, 1, v___x_4327_);
v___x_4329_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4329_, 0, v___x_4328_);
lean_ctor_set_uint8(v___x_4329_, sizeof(void*)*1, v___x_4321_);
return v___x_4329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object* v___x_4333_, lean_object* v_v_4334_, lean_object* v_x_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l_Lean_instReprVersoModuleDocs___lam__0(v___x_4333_, v_v_4334_, v_x_4335_);
lean_dec(v_x_4335_);
return v_res_4336_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object* v_docs_4340_){
_start:
{
lean_object* v_snippets_4341_; uint8_t v___x_4342_; 
v_snippets_4341_ = lean_ctor_get(v_docs_4340_, 0);
v___x_4342_ = l_Lean_PersistentArray_isEmpty___redArg(v_snippets_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object* v_docs_4343_){
_start:
{
uint8_t v_res_4344_; lean_object* v_r_4345_; 
v_res_4344_ = l_Lean_VersoModuleDocs_isEmpty(v_docs_4343_);
lean_dec_ref(v_docs_4343_);
v_r_4345_ = lean_box(v_res_4344_);
return v_r_4345_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object* v_docs_4346_, lean_object* v_snippet_4347_){
_start:
{
lean_object* v_terminalNesting_4348_; 
v_terminalNesting_4348_ = lean_ctor_get(v_docs_4346_, 1);
if (lean_obj_tag(v_terminalNesting_4348_) == 1)
{
lean_object* v_val_4349_; uint8_t v___x_4350_; 
v_val_4349_ = lean_ctor_get(v_terminalNesting_4348_, 0);
v___x_4350_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4349_, v_snippet_4347_);
return v___x_4350_;
}
else
{
uint8_t v___x_4351_; 
v___x_4351_ = 1;
return v___x_4351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object* v_docs_4352_, lean_object* v_snippet_4353_){
_start:
{
uint8_t v_res_4354_; lean_object* v_r_4355_; 
v_res_4354_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4352_, v_snippet_4353_);
lean_dec_ref(v_snippet_4353_);
lean_dec_ref(v_docs_4352_);
v_r_4355_ = lean_box(v_res_4354_);
return v_r_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object* v_docs_4359_, lean_object* v_snippet_4360_){
_start:
{
uint8_t v___x_4361_; 
v___x_4361_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4359_, v_snippet_4360_);
if (v___x_4361_ == 0)
{
lean_object* v___x_4362_; 
lean_dec_ref(v_snippet_4360_);
lean_dec_ref(v_docs_4359_);
v___x_4362_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__1));
return v___x_4362_;
}
else
{
lean_object* v_snippets_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4373_; 
v_snippets_4363_ = lean_ctor_get(v_docs_4359_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v_docs_4359_);
if (v_isSharedCheck_4373_ == 0)
{
lean_object* v_unused_4374_; 
v_unused_4374_ = lean_ctor_get(v_docs_4359_, 1);
lean_dec(v_unused_4374_);
v___x_4365_ = v_docs_4359_;
v_isShared_4366_ = v_isSharedCheck_4373_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_snippets_4363_);
lean_dec(v_docs_4359_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4373_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4370_; 
lean_inc_ref(v_snippet_4360_);
v___x_4367_ = l_Lean_PersistentArray_push___redArg(v_snippets_4363_, v_snippet_4360_);
v___x_4368_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4360_);
lean_dec_ref(v_snippet_4360_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 1, v___x_4368_);
lean_ctor_set(v___x_4365_, 0, v___x_4367_);
v___x_4370_ = v___x_4365_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4367_);
lean_ctor_set(v_reuseFailAlloc_4372_, 1, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
lean_object* v___x_4371_; 
v___x_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4370_);
return v___x_4371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object* v_msg_4375_){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_4377_ = lean_panic_fn(v___x_4376_, v_msg_4375_);
return v___x_4377_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_add_x21___closed__2(void){
_start:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4380_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__0));
v___x_4381_ = lean_unsigned_to_nat(4u);
v___x_4382_ = lean_unsigned_to_nat(336u);
v___x_4383_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__1));
v___x_4384_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__0));
v___x_4385_ = l_mkPanicMessageWithDecl(v___x_4384_, v___x_4383_, v___x_4382_, v___x_4381_, v___x_4380_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object* v_docs_4386_, lean_object* v_snippet_4387_){
_start:
{
lean_object* v_snippets_4388_; lean_object* v_terminalNesting_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4403_; 
v_snippets_4388_ = lean_ctor_get(v_docs_4386_, 0);
v_terminalNesting_4389_ = lean_ctor_get(v_docs_4386_, 1);
v_isSharedCheck_4403_ = !lean_is_exclusive(v_docs_4386_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4391_ = v_docs_4386_;
v_isShared_4392_ = v_isSharedCheck_4403_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_terminalNesting_4389_);
lean_inc(v_snippets_4388_);
lean_dec(v_docs_4386_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4403_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
if (lean_obj_tag(v_terminalNesting_4389_) == 1)
{
lean_object* v_val_4399_; uint8_t v___x_4400_; 
v_val_4399_ = lean_ctor_get(v_terminalNesting_4389_, 0);
lean_inc(v_val_4399_);
lean_dec_ref(v_terminalNesting_4389_);
v___x_4400_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4399_, v_snippet_4387_);
lean_dec(v_val_4399_);
if (v___x_4400_ == 0)
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
lean_del_object(v___x_4391_);
lean_dec_ref(v_snippets_4388_);
lean_dec_ref(v_snippet_4387_);
v___x_4401_ = lean_obj_once(&l_Lean_VersoModuleDocs_add_x21___closed__2, &l_Lean_VersoModuleDocs_add_x21___closed__2_once, _init_l_Lean_VersoModuleDocs_add_x21___closed__2);
v___x_4402_ = l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(v___x_4401_);
return v___x_4402_;
}
else
{
goto v___jp_4393_;
}
}
else
{
lean_dec(v_terminalNesting_4389_);
goto v___jp_4393_;
}
v___jp_4393_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4397_; 
lean_inc_ref(v_snippet_4387_);
v___x_4394_ = l_Lean_PersistentArray_push___redArg(v_snippets_4388_, v_snippet_4387_);
v___x_4395_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_4387_);
lean_dec_ref(v_snippet_4387_);
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 1, v___x_4395_);
lean_ctor_set(v___x_4391_, 0, v___x_4394_);
v___x_4397_ = v___x_4391_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4394_);
lean_ctor_set(v_reuseFailAlloc_4398_, 1, v___x_4395_);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object* v_ctx_4404_){
_start:
{
lean_object* v_context_4405_; lean_object* v___x_4406_; 
v_context_4405_ = lean_ctor_get(v_ctx_4404_, 2);
v___x_4406_ = lean_array_get_size(v_context_4405_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object* v_ctx_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4407_);
lean_dec_ref(v_ctx_4407_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object* v_ctx_4412_){
_start:
{
lean_object* v_content_4413_; lean_object* v_priorParts_4414_; lean_object* v_context_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4438_; 
v_content_4413_ = lean_ctor_get(v_ctx_4412_, 0);
v_priorParts_4414_ = lean_ctor_get(v_ctx_4412_, 1);
v_context_4415_ = lean_ctor_get(v_ctx_4412_, 2);
v_isSharedCheck_4438_ = !lean_is_exclusive(v_ctx_4412_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4417_ = v_ctx_4412_;
v_isShared_4418_ = v_isSharedCheck_4438_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_context_4415_);
lean_inc(v_priorParts_4414_);
lean_inc(v_content_4413_);
lean_dec(v_ctx_4412_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4438_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4419_ = lean_array_get_size(v_context_4415_);
v___x_4420_ = lean_unsigned_to_nat(0u);
v___x_4421_ = lean_nat_dec_eq(v___x_4419_, v___x_4420_);
if (v___x_4421_ == 0)
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v_last_4424_; lean_object* v_content_4425_; lean_object* v_priorParts_4426_; lean_object* v_titleString_4427_; lean_object* v_title_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4422_ = lean_unsigned_to_nat(1u);
v___x_4423_ = lean_nat_sub(v___x_4419_, v___x_4422_);
v_last_4424_ = lean_array_fget_borrowed(v_context_4415_, v___x_4423_);
lean_dec(v___x_4423_);
v_content_4425_ = lean_ctor_get(v_last_4424_, 0);
lean_inc_ref(v_content_4425_);
v_priorParts_4426_ = lean_ctor_get(v_last_4424_, 1);
v_titleString_4427_ = lean_ctor_get(v_last_4424_, 2);
v_title_4428_ = lean_ctor_get(v_last_4424_, 3);
v___x_4429_ = lean_box(0);
lean_inc_ref(v_titleString_4427_);
lean_inc_ref(v_title_4428_);
v___x_4430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4430_, 0, v_title_4428_);
lean_ctor_set(v___x_4430_, 1, v_titleString_4427_);
lean_ctor_set(v___x_4430_, 2, v___x_4429_);
lean_ctor_set(v___x_4430_, 3, v_content_4413_);
lean_ctor_set(v___x_4430_, 4, v_priorParts_4414_);
lean_inc_ref(v_priorParts_4426_);
v___x_4431_ = lean_array_push(v_priorParts_4426_, v___x_4430_);
v___x_4432_ = lean_array_pop(v_context_4415_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 2, v___x_4432_);
lean_ctor_set(v___x_4417_, 1, v___x_4431_);
lean_ctor_set(v___x_4417_, 0, v_content_4425_);
v___x_4434_ = v___x_4417_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_content_4425_);
lean_ctor_set(v_reuseFailAlloc_4436_, 1, v___x_4431_);
lean_ctor_set(v_reuseFailAlloc_4436_, 2, v___x_4432_);
v___x_4434_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4435_; 
v___x_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
return v___x_4435_;
}
}
else
{
lean_object* v___x_4437_; 
lean_del_object(v___x_4417_);
lean_dec_ref(v_context_4415_);
lean_dec_ref(v_priorParts_4414_);
lean_dec_ref(v_content_4413_);
v___x_4437_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1));
return v___x_4437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object* v_ctx_4439_){
_start:
{
lean_object* v_context_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; uint8_t v___x_4443_; 
v_context_4440_ = lean_ctor_get(v_ctx_4439_, 2);
v___x_4441_ = lean_array_get_size(v_context_4440_);
v___x_4442_ = lean_unsigned_to_nat(0u);
v___x_4443_ = lean_nat_dec_eq(v___x_4441_, v___x_4442_);
if (v___x_4443_ == 0)
{
lean_object* v___x_4444_; 
v___x_4444_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4439_);
if (lean_obj_tag(v___x_4444_) == 0)
{
return v___x_4444_;
}
else
{
lean_object* v_a_4445_; 
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_a_4445_);
lean_dec_ref(v___x_4444_);
v_ctx_4439_ = v_a_4445_;
goto _start;
}
}
else
{
lean_object* v___x_4447_; 
v___x_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4447_, 0, v_ctx_4439_);
return v___x_4447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object* v_ctx_4450_, lean_object* v_partLevel_4451_, lean_object* v_part_4452_){
_start:
{
lean_object* v___x_4453_; uint8_t v___x_4454_; 
v___x_4453_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4450_);
v___x_4454_ = lean_nat_dec_lt(v___x_4453_, v_partLevel_4451_);
if (v___x_4454_ == 0)
{
uint8_t v___x_4455_; 
v___x_4455_ = lean_nat_dec_eq(v_partLevel_4451_, v___x_4453_);
lean_dec(v___x_4453_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; 
v___x_4456_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4450_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_dec_ref(v_part_4452_);
lean_dec(v_partLevel_4451_);
return v___x_4456_;
}
else
{
lean_object* v_a_4457_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_a_4457_);
lean_dec_ref(v___x_4456_);
v_ctx_4450_ = v_a_4457_;
goto _start;
}
}
else
{
lean_object* v_content_4459_; lean_object* v_priorParts_4460_; lean_object* v_context_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4470_; 
lean_dec(v_partLevel_4451_);
v_content_4459_ = lean_ctor_get(v_ctx_4450_, 0);
v_priorParts_4460_ = lean_ctor_get(v_ctx_4450_, 1);
v_context_4461_ = lean_ctor_get(v_ctx_4450_, 2);
v_isSharedCheck_4470_ = !lean_is_exclusive(v_ctx_4450_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4463_ = v_ctx_4450_;
v_isShared_4464_ = v_isSharedCheck_4470_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_context_4461_);
lean_inc(v_priorParts_4460_);
lean_inc(v_content_4459_);
lean_dec(v_ctx_4450_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4470_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; lean_object* v___x_4467_; 
v___x_4465_ = lean_array_push(v_priorParts_4460_, v_part_4452_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 1, v___x_4465_);
v___x_4467_ = v___x_4463_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_content_4459_);
lean_ctor_set(v_reuseFailAlloc_4469_, 1, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4469_, 2, v_context_4461_);
v___x_4467_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
lean_object* v___x_4468_; 
v___x_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
return v___x_4468_;
}
}
}
}
else
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
lean_dec_ref(v_part_4452_);
lean_dec_ref(v_ctx_4450_);
v___x_4471_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0));
v___x_4472_ = l_Nat_reprFast(v___x_4453_);
v___x_4473_ = lean_string_append(v___x_4471_, v___x_4472_);
lean_dec_ref(v___x_4472_);
v___x_4474_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1));
v___x_4475_ = lean_string_append(v___x_4473_, v___x_4474_);
v___x_4476_ = l_Nat_reprFast(v_partLevel_4451_);
v___x_4477_ = lean_string_append(v___x_4475_, v___x_4476_);
lean_dec_ref(v___x_4476_);
v___x_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4477_);
return v___x_4478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object* v_ctx_4482_, lean_object* v_blocks_4483_){
_start:
{
lean_object* v_content_4484_; lean_object* v_priorParts_4485_; lean_object* v_context_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4499_; 
v_content_4484_ = lean_ctor_get(v_ctx_4482_, 0);
v_priorParts_4485_ = lean_ctor_get(v_ctx_4482_, 1);
v_context_4486_ = lean_ctor_get(v_ctx_4482_, 2);
v_isSharedCheck_4499_ = !lean_is_exclusive(v_ctx_4482_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4488_ = v_ctx_4482_;
v_isShared_4489_ = v_isSharedCheck_4499_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_context_4486_);
lean_inc(v_priorParts_4485_);
lean_inc(v_content_4484_);
lean_dec(v_ctx_4482_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4499_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; uint8_t v___x_4492_; 
v___x_4490_ = lean_array_get_size(v_priorParts_4485_);
v___x_4491_ = lean_unsigned_to_nat(0u);
v___x_4492_ = lean_nat_dec_eq(v___x_4490_, v___x_4491_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; 
lean_del_object(v___x_4488_);
lean_dec_ref(v_context_4486_);
lean_dec_ref(v_priorParts_4485_);
lean_dec_ref(v_content_4484_);
v___x_4493_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1));
return v___x_4493_;
}
else
{
lean_object* v___x_4494_; lean_object* v___x_4496_; 
v___x_4494_ = l_Array_append___redArg(v_content_4484_, v_blocks_4483_);
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 0, v___x_4494_);
v___x_4496_ = v___x_4488_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4494_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v_priorParts_4485_);
lean_ctor_set(v_reuseFailAlloc_4498_, 2, v_context_4486_);
v___x_4496_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
lean_object* v___x_4497_; 
v___x_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4496_);
return v___x_4497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object* v_ctx_4500_, lean_object* v_blocks_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4500_, v_blocks_4501_);
lean_dec_ref(v_blocks_4501_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object* v_as_4503_, size_t v_sz_4504_, size_t v_i_4505_, lean_object* v_b_4506_){
_start:
{
uint8_t v___x_4507_; 
v___x_4507_ = lean_usize_dec_lt(v_i_4505_, v_sz_4504_);
if (v___x_4507_ == 0)
{
lean_object* v___x_4508_; 
v___x_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4508_, 0, v_b_4506_);
return v___x_4508_;
}
else
{
lean_object* v_a_4509_; lean_object* v_snd_4510_; lean_object* v_fst_4511_; lean_object* v_snd_4512_; lean_object* v___x_4513_; 
v_a_4509_ = lean_array_uget_borrowed(v_as_4503_, v_i_4505_);
v_snd_4510_ = lean_ctor_get(v_a_4509_, 1);
v_fst_4511_ = lean_ctor_get(v_a_4509_, 0);
v_snd_4512_ = lean_ctor_get(v_snd_4510_, 1);
lean_inc(v_snd_4512_);
lean_inc(v_fst_4511_);
v___x_4513_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(v_b_4506_, v_fst_4511_, v_snd_4512_);
if (lean_obj_tag(v___x_4513_) == 0)
{
return v___x_4513_;
}
else
{
lean_object* v_a_4514_; size_t v___x_4515_; size_t v___x_4516_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref(v___x_4513_);
v___x_4515_ = ((size_t)1ULL);
v___x_4516_ = lean_usize_add(v_i_4505_, v___x_4515_);
v_i_4505_ = v___x_4516_;
v_b_4506_ = v_a_4514_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object* v_as_4518_, lean_object* v_sz_4519_, lean_object* v_i_4520_, lean_object* v_b_4521_){
_start:
{
size_t v_sz_boxed_4522_; size_t v_i_boxed_4523_; lean_object* v_res_4524_; 
v_sz_boxed_4522_ = lean_unbox_usize(v_sz_4519_);
lean_dec(v_sz_4519_);
v_i_boxed_4523_ = lean_unbox_usize(v_i_4520_);
lean_dec(v_i_4520_);
v_res_4524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_as_4518_, v_sz_boxed_4522_, v_i_boxed_4523_, v_b_4521_);
lean_dec_ref(v_as_4518_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object* v_ctx_4525_, lean_object* v_snippet_4526_){
_start:
{
lean_object* v_text_4527_; lean_object* v_sections_4528_; lean_object* v___x_4529_; 
v_text_4527_ = lean_ctor_get(v_snippet_4526_, 0);
v_sections_4528_ = lean_ctor_get(v_snippet_4526_, 1);
v___x_4529_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4525_, v_text_4527_);
if (lean_obj_tag(v___x_4529_) == 0)
{
return v___x_4529_;
}
else
{
lean_object* v_a_4530_; size_t v_sz_4531_; size_t v___x_4532_; lean_object* v___x_4533_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref(v___x_4529_);
v_sz_4531_ = lean_array_size(v_sections_4528_);
v___x_4532_ = ((size_t)0ULL);
v___x_4533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_sections_4528_, v_sz_4531_, v___x_4532_, v_a_4530_);
return v___x_4533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object* v_ctx_4534_, lean_object* v_snippet_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_ctx_4534_, v_snippet_4535_);
lean_dec_ref(v_snippet_4535_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object* v_as_4537_, size_t v_sz_4538_, size_t v_i_4539_, lean_object* v_b_4540_){
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
lean_object* v_snd_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4565_; 
v_snd_4543_ = lean_ctor_get(v_b_4540_, 1);
v_isSharedCheck_4565_ = !lean_is_exclusive(v_b_4540_);
if (v_isSharedCheck_4565_ == 0)
{
lean_object* v_unused_4566_; 
v_unused_4566_ = lean_ctor_get(v_b_4540_, 0);
lean_dec(v_unused_4566_);
v___x_4545_ = v_b_4540_;
v_isShared_4546_ = v_isSharedCheck_4565_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_snd_4543_);
lean_dec(v_b_4540_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4565_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v_a_4547_; lean_object* v___x_4548_; 
v_a_4547_ = lean_array_uget_borrowed(v_as_4537_, v_i_4539_);
v___x_4548_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4543_, v_a_4547_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_del_object(v___x_4545_);
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4548_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
else
{
lean_object* v_a_4557_; lean_object* v___x_4558_; lean_object* v___x_4560_; 
v_a_4557_ = lean_ctor_get(v___x_4548_, 0);
lean_inc(v_a_4557_);
lean_dec_ref(v___x_4548_);
v___x_4558_ = lean_box(0);
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 1, v_a_4557_);
lean_ctor_set(v___x_4545_, 0, v___x_4558_);
v___x_4560_ = v___x_4545_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4558_);
lean_ctor_set(v_reuseFailAlloc_4564_, 1, v_a_4557_);
v___x_4560_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
size_t v___x_4561_; size_t v___x_4562_; 
v___x_4561_ = ((size_t)1ULL);
v___x_4562_ = lean_usize_add(v_i_4539_, v___x_4561_);
v_i_4539_ = v___x_4562_;
v_b_4540_ = v___x_4560_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4567_, lean_object* v_sz_4568_, lean_object* v_i_4569_, lean_object* v_b_4570_){
_start:
{
size_t v_sz_boxed_4571_; size_t v_i_boxed_4572_; lean_object* v_res_4573_; 
v_sz_boxed_4571_ = lean_unbox_usize(v_sz_4568_);
lean_dec(v_sz_4568_);
v_i_boxed_4572_ = lean_unbox_usize(v_i_4569_);
lean_dec(v_i_4569_);
v_res_4573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4567_, v_sz_boxed_4571_, v_i_boxed_4572_, v_b_4570_);
lean_dec_ref(v_as_4567_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object* v_as_4574_, size_t v_sz_4575_, size_t v_i_4576_, lean_object* v_b_4577_){
_start:
{
uint8_t v___x_4578_; 
v___x_4578_ = lean_usize_dec_lt(v_i_4576_, v_sz_4575_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; 
v___x_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4579_, 0, v_b_4577_);
return v___x_4579_;
}
else
{
lean_object* v_snd_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4602_; 
v_snd_4580_ = lean_ctor_get(v_b_4577_, 1);
v_isSharedCheck_4602_ = !lean_is_exclusive(v_b_4577_);
if (v_isSharedCheck_4602_ == 0)
{
lean_object* v_unused_4603_; 
v_unused_4603_ = lean_ctor_get(v_b_4577_, 0);
lean_dec(v_unused_4603_);
v___x_4582_ = v_b_4577_;
v_isShared_4583_ = v_isSharedCheck_4602_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_snd_4580_);
lean_dec(v_b_4577_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4602_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v_a_4584_; lean_object* v___x_4585_; 
v_a_4584_ = lean_array_uget_borrowed(v_as_4574_, v_i_4576_);
v___x_4585_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4580_, v_a_4584_);
if (lean_obj_tag(v___x_4585_) == 0)
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
lean_del_object(v___x_4582_);
v_a_4586_ = lean_ctor_get(v___x_4585_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4588_ = v___x_4585_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4585_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4586_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
else
{
lean_object* v_a_4594_; lean_object* v___x_4595_; lean_object* v___x_4597_; 
v_a_4594_ = lean_ctor_get(v___x_4585_, 0);
lean_inc(v_a_4594_);
lean_dec_ref(v___x_4585_);
v___x_4595_ = lean_box(0);
if (v_isShared_4583_ == 0)
{
lean_ctor_set(v___x_4582_, 1, v_a_4594_);
lean_ctor_set(v___x_4582_, 0, v___x_4595_);
v___x_4597_ = v___x_4582_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4595_);
lean_ctor_set(v_reuseFailAlloc_4601_, 1, v_a_4594_);
v___x_4597_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
size_t v___x_4598_; size_t v___x_4599_; lean_object* v___x_4600_; 
v___x_4598_ = ((size_t)1ULL);
v___x_4599_ = lean_usize_add(v_i_4576_, v___x_4598_);
v___x_4600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4574_, v_sz_4575_, v___x_4599_, v___x_4597_);
return v___x_4600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object* v_as_4604_, lean_object* v_sz_4605_, lean_object* v_i_4606_, lean_object* v_b_4607_){
_start:
{
size_t v_sz_boxed_4608_; size_t v_i_boxed_4609_; lean_object* v_res_4610_; 
v_sz_boxed_4608_ = lean_unbox_usize(v_sz_4605_);
lean_dec(v_sz_4605_);
v_i_boxed_4609_ = lean_unbox_usize(v_i_4606_);
lean_dec(v_i_4606_);
v_res_4610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_as_4604_, v_sz_boxed_4608_, v_i_boxed_4609_, v_b_4607_);
lean_dec_ref(v_as_4604_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_4611_, size_t v_sz_4612_, size_t v_i_4613_, lean_object* v_b_4614_){
_start:
{
uint8_t v___x_4615_; 
v___x_4615_ = lean_usize_dec_lt(v_i_4613_, v_sz_4612_);
if (v___x_4615_ == 0)
{
lean_object* v___x_4616_; 
v___x_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4616_, 0, v_b_4614_);
return v___x_4616_;
}
else
{
lean_object* v_snd_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4639_; 
v_snd_4617_ = lean_ctor_get(v_b_4614_, 1);
v_isSharedCheck_4639_ = !lean_is_exclusive(v_b_4614_);
if (v_isSharedCheck_4639_ == 0)
{
lean_object* v_unused_4640_; 
v_unused_4640_ = lean_ctor_get(v_b_4614_, 0);
lean_dec(v_unused_4640_);
v___x_4619_ = v_b_4614_;
v_isShared_4620_ = v_isSharedCheck_4639_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_snd_4617_);
lean_dec(v_b_4614_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4639_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v_a_4621_; lean_object* v___x_4622_; 
v_a_4621_ = lean_array_uget_borrowed(v_as_4611_, v_i_4613_);
v___x_4622_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4617_, v_a_4621_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
lean_del_object(v___x_4619_);
v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4622_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4622_);
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
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4631_; lean_object* v___x_4632_; lean_object* v___x_4634_; 
v_a_4631_ = lean_ctor_get(v___x_4622_, 0);
lean_inc(v_a_4631_);
lean_dec_ref(v___x_4622_);
v___x_4632_ = lean_box(0);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 1, v_a_4631_);
lean_ctor_set(v___x_4619_, 0, v___x_4632_);
v___x_4634_ = v___x_4619_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4632_);
lean_ctor_set(v_reuseFailAlloc_4638_, 1, v_a_4631_);
v___x_4634_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
size_t v___x_4635_; size_t v___x_4636_; 
v___x_4635_ = ((size_t)1ULL);
v___x_4636_ = lean_usize_add(v_i_4613_, v___x_4635_);
v_i_4613_ = v___x_4636_;
v_b_4614_ = v___x_4634_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_4641_, lean_object* v_sz_4642_, lean_object* v_i_4643_, lean_object* v_b_4644_){
_start:
{
size_t v_sz_boxed_4645_; size_t v_i_boxed_4646_; lean_object* v_res_4647_; 
v_sz_boxed_4645_ = lean_unbox_usize(v_sz_4642_);
lean_dec(v_sz_4642_);
v_i_boxed_4646_ = lean_unbox_usize(v_i_4643_);
lean_dec(v_i_4643_);
v_res_4647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4641_, v_sz_boxed_4645_, v_i_boxed_4646_, v_b_4644_);
lean_dec_ref(v_as_4641_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object* v_as_4648_, size_t v_sz_4649_, size_t v_i_4650_, lean_object* v_b_4651_){
_start:
{
uint8_t v___x_4652_; 
v___x_4652_ = lean_usize_dec_lt(v_i_4650_, v_sz_4649_);
if (v___x_4652_ == 0)
{
lean_object* v___x_4653_; 
v___x_4653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4653_, 0, v_b_4651_);
return v___x_4653_;
}
else
{
lean_object* v_snd_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4676_; 
v_snd_4654_ = lean_ctor_get(v_b_4651_, 1);
v_isSharedCheck_4676_ = !lean_is_exclusive(v_b_4651_);
if (v_isSharedCheck_4676_ == 0)
{
lean_object* v_unused_4677_; 
v_unused_4677_ = lean_ctor_get(v_b_4651_, 0);
lean_dec(v_unused_4677_);
v___x_4656_ = v_b_4651_;
v_isShared_4657_ = v_isSharedCheck_4676_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_snd_4654_);
lean_dec(v_b_4651_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4676_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v_a_4658_; lean_object* v___x_4659_; 
v_a_4658_ = lean_array_uget_borrowed(v_as_4648_, v_i_4650_);
v___x_4659_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4654_, v_a_4658_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_del_object(v___x_4656_);
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4659_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4659_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
else
{
lean_object* v_a_4668_; lean_object* v___x_4669_; lean_object* v___x_4671_; 
v_a_4668_ = lean_ctor_get(v___x_4659_, 0);
lean_inc(v_a_4668_);
lean_dec_ref(v___x_4659_);
v___x_4669_ = lean_box(0);
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 1, v_a_4668_);
lean_ctor_set(v___x_4656_, 0, v___x_4669_);
v___x_4671_ = v___x_4656_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4669_);
lean_ctor_set(v_reuseFailAlloc_4675_, 1, v_a_4668_);
v___x_4671_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
size_t v___x_4672_; size_t v___x_4673_; lean_object* v___x_4674_; 
v___x_4672_ = ((size_t)1ULL);
v___x_4673_ = lean_usize_add(v_i_4650_, v___x_4672_);
v___x_4674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4648_, v_sz_4649_, v___x_4673_, v___x_4671_);
return v___x_4674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4678_, lean_object* v_sz_4679_, lean_object* v_i_4680_, lean_object* v_b_4681_){
_start:
{
size_t v_sz_boxed_4682_; size_t v_i_boxed_4683_; lean_object* v_res_4684_; 
v_sz_boxed_4682_ = lean_unbox_usize(v_sz_4679_);
lean_dec(v_sz_4679_);
v_i_boxed_4683_ = lean_unbox_usize(v_i_4680_);
lean_dec(v_i_4680_);
v_res_4684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_as_4678_, v_sz_boxed_4682_, v_i_boxed_4683_, v_b_4681_);
lean_dec_ref(v_as_4678_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object* v_inh_4685_, lean_object* v_n_4686_, lean_object* v_b_4687_){
_start:
{
if (lean_obj_tag(v_n_4686_) == 0)
{
lean_object* v_cs_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4722_; 
v_cs_4688_ = lean_ctor_get(v_n_4686_, 0);
v_isSharedCheck_4722_ = !lean_is_exclusive(v_n_4686_);
if (v_isSharedCheck_4722_ == 0)
{
v___x_4690_ = v_n_4686_;
v_isShared_4691_ = v_isSharedCheck_4722_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_cs_4688_);
lean_dec(v_n_4686_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4722_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; size_t v_sz_4694_; size_t v___x_4695_; lean_object* v___x_4696_; 
v___x_4692_ = lean_box(0);
v___x_4693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4692_);
lean_ctor_set(v___x_4693_, 1, v_b_4687_);
v_sz_4694_ = lean_array_size(v_cs_4688_);
v___x_4695_ = ((size_t)0ULL);
v___x_4696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_inh_4685_, v_cs_4688_, v_sz_4694_, v___x_4695_, v___x_4693_);
lean_dec_ref(v_cs_4688_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_del_object(v___x_4690_);
v_a_4697_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4696_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4696_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
else
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4721_; 
v_a_4705_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4707_ = v___x_4696_;
v_isShared_4708_ = v_isSharedCheck_4721_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4696_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4721_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v_fst_4709_; 
v_fst_4709_ = lean_ctor_get(v_a_4705_, 0);
if (lean_obj_tag(v_fst_4709_) == 0)
{
lean_object* v_snd_4710_; lean_object* v___x_4712_; 
v_snd_4710_ = lean_ctor_get(v_a_4705_, 1);
lean_inc(v_snd_4710_);
lean_dec(v_a_4705_);
if (v_isShared_4691_ == 0)
{
lean_ctor_set_tag(v___x_4690_, 1);
lean_ctor_set(v___x_4690_, 0, v_snd_4710_);
v___x_4712_ = v___x_4690_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_snd_4710_);
v___x_4712_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
lean_object* v___x_4714_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 0, v___x_4712_);
v___x_4714_ = v___x_4707_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4712_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
else
{
lean_object* v_val_4717_; lean_object* v___x_4719_; 
lean_inc_ref(v_fst_4709_);
lean_dec(v_a_4705_);
lean_del_object(v___x_4690_);
v_val_4717_ = lean_ctor_get(v_fst_4709_, 0);
lean_inc(v_val_4717_);
lean_dec_ref(v_fst_4709_);
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 0, v_val_4717_);
v___x_4719_ = v___x_4707_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_val_4717_);
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
}
}
else
{
lean_object* v_vs_4723_; lean_object* v___x_4725_; uint8_t v_isShared_4726_; uint8_t v_isSharedCheck_4757_; 
v_vs_4723_ = lean_ctor_get(v_n_4686_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v_n_4686_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4725_ = v_n_4686_;
v_isShared_4726_ = v_isSharedCheck_4757_;
goto v_resetjp_4724_;
}
else
{
lean_inc(v_vs_4723_);
lean_dec(v_n_4686_);
v___x_4725_ = lean_box(0);
v_isShared_4726_ = v_isSharedCheck_4757_;
goto v_resetjp_4724_;
}
v_resetjp_4724_:
{
lean_object* v___x_4727_; lean_object* v___x_4728_; size_t v_sz_4729_; size_t v___x_4730_; lean_object* v___x_4731_; 
v___x_4727_ = lean_box(0);
v___x_4728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4727_);
lean_ctor_set(v___x_4728_, 1, v_b_4687_);
v_sz_4729_ = lean_array_size(v_vs_4723_);
v___x_4730_ = ((size_t)0ULL);
v___x_4731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_vs_4723_, v_sz_4729_, v___x_4730_, v___x_4728_);
lean_dec_ref(v_vs_4723_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4739_; 
lean_del_object(v___x_4725_);
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4734_ = v___x_4731_;
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4731_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4737_; 
if (v_isShared_4735_ == 0)
{
v___x_4737_ = v___x_4734_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4732_);
v___x_4737_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
return v___x_4737_;
}
}
}
else
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4756_; 
v_a_4740_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4742_ = v___x_4731_;
v_isShared_4743_ = v_isSharedCheck_4756_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4731_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4756_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v_fst_4744_; 
v_fst_4744_ = lean_ctor_get(v_a_4740_, 0);
if (lean_obj_tag(v_fst_4744_) == 0)
{
lean_object* v_snd_4745_; lean_object* v___x_4747_; 
v_snd_4745_ = lean_ctor_get(v_a_4740_, 1);
lean_inc(v_snd_4745_);
lean_dec(v_a_4740_);
if (v_isShared_4726_ == 0)
{
lean_ctor_set(v___x_4725_, 0, v_snd_4745_);
v___x_4747_ = v___x_4725_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_snd_4745_);
v___x_4747_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
lean_object* v___x_4749_; 
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v___x_4747_);
v___x_4749_ = v___x_4742_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4747_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
else
{
lean_object* v_val_4752_; lean_object* v___x_4754_; 
lean_inc_ref(v_fst_4744_);
lean_dec(v_a_4740_);
lean_del_object(v___x_4725_);
v_val_4752_ = lean_ctor_get(v_fst_4744_, 0);
lean_inc(v_val_4752_);
lean_dec_ref(v_fst_4744_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v_val_4752_);
v___x_4754_ = v___x_4742_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_val_4752_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object* v_inh_4758_, lean_object* v_as_4759_, size_t v_sz_4760_, size_t v_i_4761_, lean_object* v_b_4762_){
_start:
{
uint8_t v___x_4763_; 
v___x_4763_ = lean_usize_dec_lt(v_i_4761_, v_sz_4760_);
if (v___x_4763_ == 0)
{
lean_object* v___x_4764_; 
v___x_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4764_, 0, v_b_4762_);
return v___x_4764_;
}
else
{
lean_object* v_snd_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4799_; 
v_snd_4765_ = lean_ctor_get(v_b_4762_, 1);
v_isSharedCheck_4799_ = !lean_is_exclusive(v_b_4762_);
if (v_isSharedCheck_4799_ == 0)
{
lean_object* v_unused_4800_; 
v_unused_4800_ = lean_ctor_get(v_b_4762_, 0);
lean_dec(v_unused_4800_);
v___x_4767_ = v_b_4762_;
v_isShared_4768_ = v_isSharedCheck_4799_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_snd_4765_);
lean_dec(v_b_4762_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4799_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v_a_4769_; lean_object* v___x_4770_; 
v_a_4769_ = lean_array_uget_borrowed(v_as_4759_, v_i_4761_);
lean_inc(v_snd_4765_);
lean_inc(v_a_4769_);
v___x_4770_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_inh_4758_, v_a_4769_, v_snd_4765_);
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
lean_del_object(v___x_4767_);
lean_dec(v_snd_4765_);
v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4770_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4770_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4776_; 
if (v_isShared_4774_ == 0)
{
v___x_4776_ = v___x_4773_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
else
{
lean_object* v_a_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4798_; 
v_a_4779_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4781_ = v___x_4770_;
v_isShared_4782_ = v_isSharedCheck_4798_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_a_4779_);
lean_dec(v___x_4770_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4798_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
if (lean_obj_tag(v_a_4779_) == 0)
{
lean_object* v___x_4783_; lean_object* v___x_4785_; 
v___x_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4783_, 0, v_a_4779_);
if (v_isShared_4768_ == 0)
{
lean_ctor_set(v___x_4767_, 0, v___x_4783_);
v___x_4785_ = v___x_4767_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4783_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_snd_4765_);
v___x_4785_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
lean_object* v___x_4787_; 
if (v_isShared_4782_ == 0)
{
lean_ctor_set(v___x_4781_, 0, v___x_4785_);
v___x_4787_ = v___x_4781_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4785_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4791_; lean_object* v___x_4793_; 
lean_del_object(v___x_4781_);
lean_dec(v_snd_4765_);
v_a_4790_ = lean_ctor_get(v_a_4779_, 0);
lean_inc(v_a_4790_);
lean_dec_ref(v_a_4779_);
v___x_4791_ = lean_box(0);
if (v_isShared_4768_ == 0)
{
lean_ctor_set(v___x_4767_, 1, v_a_4790_);
lean_ctor_set(v___x_4767_, 0, v___x_4791_);
v___x_4793_ = v___x_4767_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4791_);
lean_ctor_set(v_reuseFailAlloc_4797_, 1, v_a_4790_);
v___x_4793_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
size_t v___x_4794_; size_t v___x_4795_; 
v___x_4794_ = ((size_t)1ULL);
v___x_4795_ = lean_usize_add(v_i_4761_, v___x_4794_);
v_i_4761_ = v___x_4795_;
v_b_4762_ = v___x_4793_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object* v_inh_4801_, lean_object* v_as_4802_, lean_object* v_sz_4803_, lean_object* v_i_4804_, lean_object* v_b_4805_){
_start:
{
size_t v_sz_boxed_4806_; size_t v_i_boxed_4807_; lean_object* v_res_4808_; 
v_sz_boxed_4806_ = lean_unbox_usize(v_sz_4803_);
lean_dec(v_sz_4803_);
v_i_boxed_4807_ = lean_unbox_usize(v_i_4804_);
lean_dec(v_i_4804_);
v_res_4808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_inh_4801_, v_as_4802_, v_sz_boxed_4806_, v_i_boxed_4807_, v_b_4805_);
lean_dec_ref(v_as_4802_);
lean_dec_ref(v_inh_4801_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object* v_inh_4809_, lean_object* v_n_4810_, lean_object* v_b_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_inh_4809_, v_n_4810_, v_b_4811_);
lean_dec_ref(v_inh_4809_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object* v_t_4813_, lean_object* v_init_4814_){
_start:
{
lean_object* v_root_4815_; lean_object* v_tail_4816_; lean_object* v___x_4817_; 
v_root_4815_ = lean_ctor_get(v_t_4813_, 0);
lean_inc_ref(v_root_4815_);
v_tail_4816_ = lean_ctor_get(v_t_4813_, 1);
lean_inc_ref(v_tail_4816_);
lean_dec_ref(v_t_4813_);
lean_inc_ref(v_init_4814_);
v___x_4817_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4814_, v_root_4815_, v_init_4814_);
lean_dec_ref(v_init_4814_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
lean_dec_ref(v_tail_4816_);
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
else
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4862_; 
v_a_4826_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4828_ = v___x_4817_;
v_isShared_4829_ = v_isSharedCheck_4862_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4817_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4862_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
if (lean_obj_tag(v_a_4826_) == 0)
{
lean_object* v_a_4830_; lean_object* v___x_4832_; 
lean_dec_ref(v_tail_4816_);
v_a_4830_ = lean_ctor_get(v_a_4826_, 0);
lean_inc(v_a_4830_);
lean_dec_ref(v_a_4826_);
if (v_isShared_4829_ == 0)
{
lean_ctor_set(v___x_4828_, 0, v_a_4830_);
v___x_4832_ = v___x_4828_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4830_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
else
{
lean_object* v_a_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; size_t v_sz_4837_; size_t v___x_4838_; lean_object* v___x_4839_; 
lean_del_object(v___x_4828_);
v_a_4834_ = lean_ctor_get(v_a_4826_, 0);
lean_inc(v_a_4834_);
lean_dec_ref(v_a_4826_);
v___x_4835_ = lean_box(0);
v___x_4836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4835_);
lean_ctor_set(v___x_4836_, 1, v_a_4834_);
v_sz_4837_ = lean_array_size(v_tail_4816_);
v___x_4838_ = ((size_t)0ULL);
v___x_4839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_tail_4816_, v_sz_4837_, v___x_4838_, v___x_4836_);
lean_dec_ref(v_tail_4816_);
if (lean_obj_tag(v___x_4839_) == 0)
{
lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4847_; 
v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4839_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4842_ = v___x_4839_;
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4839_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4845_; 
if (v_isShared_4843_ == 0)
{
v___x_4845_ = v___x_4842_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_a_4840_);
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
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4861_; 
v_a_4848_ = lean_ctor_get(v___x_4839_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4839_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4850_ = v___x_4839_;
v_isShared_4851_ = v_isSharedCheck_4861_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4839_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4861_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v_fst_4852_; 
v_fst_4852_ = lean_ctor_get(v_a_4848_, 0);
if (lean_obj_tag(v_fst_4852_) == 0)
{
lean_object* v_snd_4853_; lean_object* v___x_4855_; 
v_snd_4853_ = lean_ctor_get(v_a_4848_, 1);
lean_inc(v_snd_4853_);
lean_dec(v_a_4848_);
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 0, v_snd_4853_);
v___x_4855_ = v___x_4850_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_snd_4853_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
else
{
lean_object* v_val_4857_; lean_object* v___x_4859_; 
lean_inc_ref(v_fst_4852_);
lean_dec(v_a_4848_);
v_val_4857_ = lean_ctor_get(v_fst_4852_, 0);
lean_inc(v_val_4857_);
lean_dec_ref(v_fst_4852_);
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 0, v_val_4857_);
v___x_4859_ = v___x_4850_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_val_4857_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
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
lean_object* v___x_4865_; lean_object* v_ctx_4866_; 
v___x_4865_ = ((lean_object*)(l_Lean_VersoModuleDocs_assemble___closed__0));
v_ctx_4866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctx_4866_, 0, v___x_4865_);
lean_ctor_set(v_ctx_4866_, 1, v___x_4865_);
lean_ctor_set(v_ctx_4866_, 2, v___x_4865_);
return v_ctx_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object* v_docs_4867_){
_start:
{
lean_object* v_snippets_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4905_; 
v_snippets_4868_ = lean_ctor_get(v_docs_4867_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v_docs_4867_);
if (v_isSharedCheck_4905_ == 0)
{
lean_object* v_unused_4906_; 
v_unused_4906_ = lean_ctor_get(v_docs_4867_, 1);
lean_dec(v_unused_4906_);
v___x_4870_ = v_docs_4867_;
v_isShared_4871_ = v_isSharedCheck_4905_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_snippets_4868_);
lean_dec(v_docs_4867_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4905_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v_ctx_4872_; lean_object* v___x_4873_; 
v_ctx_4872_ = lean_obj_once(&l_Lean_VersoModuleDocs_assemble___closed__1, &l_Lean_VersoModuleDocs_assemble___closed__1_once, _init_l_Lean_VersoModuleDocs_assemble___closed__1);
v___x_4873_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_snippets_4868_, v_ctx_4872_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
lean_del_object(v___x_4870_);
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
lean_object* v_a_4882_; lean_object* v___x_4883_; 
v_a_4882_ = lean_ctor_get(v___x_4873_, 0);
lean_inc(v_a_4882_);
lean_dec_ref(v___x_4873_);
v___x_4883_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(v_a_4882_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
lean_del_object(v___x_4870_);
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4883_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4883_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4889_; 
if (v_isShared_4887_ == 0)
{
v___x_4889_ = v___x_4886_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4884_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4904_; 
v_a_4892_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4894_ = v___x_4883_;
v_isShared_4895_ = v_isSharedCheck_4904_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4883_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4904_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v_content_4896_; lean_object* v_priorParts_4897_; lean_object* v___x_4899_; 
v_content_4896_ = lean_ctor_get(v_a_4892_, 0);
lean_inc_ref(v_content_4896_);
v_priorParts_4897_ = lean_ctor_get(v_a_4892_, 1);
lean_inc_ref(v_priorParts_4897_);
lean_dec(v_a_4892_);
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 1, v_priorParts_4897_);
lean_ctor_set(v___x_4870_, 0, v_content_4896_);
v___x_4899_ = v___x_4870_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_content_4896_);
lean_ctor_set(v_reuseFailAlloc_4903_, 1, v_priorParts_4897_);
v___x_4899_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
lean_object* v___x_4901_; 
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 0, v___x_4899_);
v___x_4901_ = v___x_4894_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4899_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object* v_x_4909_, lean_object* v_x_4910_, lean_object* v_es_4911_, uint8_t v_level_4912_){
_start:
{
uint8_t v___x_4913_; uint8_t v___x_4914_; 
v___x_4913_ = 1;
v___x_4914_ = l_Lean_instOrdOLeanLevel_ord(v_level_4912_, v___x_4913_);
if (v___x_4914_ == 0)
{
lean_object* v___x_4915_; 
lean_dec(v_es_4911_);
v___x_4915_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_));
return v___x_4915_;
}
else
{
lean_object* v___x_4916_; 
v___x_4916_ = lean_array_mk(v_es_4911_);
return v___x_4916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object* v_x_4917_, lean_object* v_x_4918_, lean_object* v_es_4919_, lean_object* v_level_4920_){
_start:
{
uint8_t v_level_boxed_4921_; lean_object* v_res_4922_; 
v_level_boxed_4921_ = lean_unbox(v_level_4920_);
v_res_4922_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(v_x_4917_, v_x_4918_, v_es_4919_, v_level_boxed_4921_);
lean_dec_ref(v_x_4918_);
lean_dec_ref(v_x_4917_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object* v_es_4923_){
_start:
{
lean_object* v___x_4924_; 
v___x_4924_ = lean_array_mk(v_es_4923_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_as_4925_, lean_object* v_i_4926_){
_start:
{
lean_object* v_zero_4927_; uint8_t v_isZero_4928_; 
v_zero_4927_ = lean_unsigned_to_nat(0u);
v_isZero_4928_ = lean_nat_dec_eq(v_i_4926_, v_zero_4927_);
if (v_isZero_4928_ == 1)
{
lean_object* v___x_4929_; 
lean_dec(v_i_4926_);
v___x_4929_ = lean_box(0);
return v___x_4929_;
}
else
{
lean_object* v_one_4930_; lean_object* v_n_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v_one_4930_ = lean_unsigned_to_nat(1u);
v_n_4931_ = lean_nat_sub(v_i_4926_, v_one_4930_);
lean_dec(v_i_4926_);
v___x_4932_ = lean_array_fget_borrowed(v_as_4925_, v_n_4931_);
v___x_4933_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v___x_4932_);
if (lean_obj_tag(v___x_4933_) == 0)
{
v_i_4926_ = v_n_4931_;
goto _start;
}
else
{
lean_dec(v_n_4931_);
return v___x_4933_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_as_4935_, lean_object* v_i_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_4935_, v_i_4936_);
lean_dec_ref(v_as_4935_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_as_4938_, lean_object* v_i_4939_){
_start:
{
lean_object* v_zero_4940_; uint8_t v_isZero_4941_; 
v_zero_4940_ = lean_unsigned_to_nat(0u);
v_isZero_4941_ = lean_nat_dec_eq(v_i_4939_, v_zero_4940_);
if (v_isZero_4941_ == 1)
{
lean_object* v___x_4942_; 
lean_dec(v_i_4939_);
v___x_4942_ = lean_box(0);
return v___x_4942_;
}
else
{
lean_object* v_one_4943_; lean_object* v_n_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
v_one_4943_ = lean_unsigned_to_nat(1u);
v_n_4944_ = lean_nat_sub(v_i_4939_, v_one_4943_);
lean_dec(v_i_4939_);
v___x_4945_ = lean_array_fget_borrowed(v_as_4938_, v_n_4944_);
v___x_4946_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(v___x_4945_);
if (lean_obj_tag(v___x_4946_) == 0)
{
v_i_4939_ = v_n_4944_;
goto _start;
}
else
{
lean_dec(v_n_4944_);
return v___x_4946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_x_4948_){
_start:
{
if (lean_obj_tag(v_x_4948_) == 0)
{
lean_object* v_cs_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
v_cs_4949_ = lean_ctor_get(v_x_4948_, 0);
v___x_4950_ = lean_array_get_size(v_cs_4949_);
v___x_4951_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_cs_4949_, v___x_4950_);
return v___x_4951_;
}
else
{
lean_object* v_vs_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v_vs_4952_ = lean_ctor_get(v_x_4948_, 0);
v___x_4953_ = lean_array_get_size(v_vs_4952_);
v___x_4954_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(v_vs_4952_, v___x_4953_);
return v___x_4954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_x_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(v_x_4955_);
lean_dec_ref(v_x_4955_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_4957_, lean_object* v_i_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_as_4957_, v_i_4958_);
lean_dec_ref(v_as_4957_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0(lean_object* v_t_4960_){
_start:
{
lean_object* v_root_4961_; lean_object* v_tail_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v_root_4961_ = lean_ctor_get(v_t_4960_, 0);
v_tail_4962_ = lean_ctor_get(v_t_4960_, 1);
v___x_4963_ = lean_array_get_size(v_tail_4962_);
v___x_4964_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(v_tail_4962_, v___x_4963_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v___x_4965_; 
v___x_4965_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1(v_root_4961_);
return v___x_4965_;
}
else
{
return v___x_4964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0___boxed(lean_object* v_t_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0(v_t_4966_);
lean_dec_ref(v_t_4966_);
return v_res_4967_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4968_ = lean_unsigned_to_nat(32u);
v___x_4969_ = lean_mk_empty_array_with_capacity(v___x_4968_);
v___x_4970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4970_, 0, v___x_4969_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(lean_object* v___x_4971_, lean_object* v_x_4972_){
_start:
{
lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; size_t v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4973_ = lean_unsigned_to_nat(32u);
v___x_4974_ = lean_mk_empty_array_with_capacity(v___x_4973_);
v___x_4975_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_);
v___x_4976_ = ((size_t)5ULL);
lean_inc(v___x_4971_);
v___x_4977_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4977_, 0, v___x_4975_);
lean_ctor_set(v___x_4977_, 1, v___x_4974_);
lean_ctor_set(v___x_4977_, 2, v___x_4971_);
lean_ctor_set(v___x_4977_, 3, v___x_4971_);
lean_ctor_set_usize(v___x_4977_, 4, v___x_4976_);
v___x_4978_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0(v___x_4977_);
v___x_4979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4977_);
lean_ctor_set(v___x_4979_, 1, v___x_4978_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object* v___x_4980_, lean_object* v_x_4981_){
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(v___x_4980_, v_x_4981_);
lean_dec_ref(v_x_4981_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_5003_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_));
v___x_5004_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5003_);
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2____boxed(lean_object* v_a_5005_){
_start:
{
lean_object* v_res_5006_; 
v_res_5006_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2_();
return v_res_5006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_5007_, lean_object* v_i_5008_, lean_object* v_a_5009_){
_start:
{
lean_object* v___x_5010_; 
v___x_5010_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___redArg(v_as_5007_, v_i_5008_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_5011_, lean_object* v_i_5012_, lean_object* v_a_5013_){
_start:
{
lean_object* v_res_5014_; 
v_res_5014_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__0(v_as_5011_, v_i_5012_, v_a_5013_);
lean_dec_ref(v_as_5011_);
return v_res_5014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_as_5015_, lean_object* v_i_5016_, lean_object* v_a_5017_){
_start:
{
lean_object* v___x_5018_; 
v___x_5018_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_as_5015_, v_i_5016_);
return v___x_5018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2___boxed(lean_object* v_as_5019_, lean_object* v_i_5020_, lean_object* v_a_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_71268105____hygCtx___hyg_2__spec__0_spec__1_spec__2(v_as_5019_, v_i_5020_, v_a_5021_);
lean_dec_ref(v_as_5019_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object* v_env_5023_){
_start:
{
lean_object* v___x_5024_; lean_object* v_toEnvExtension_5025_; lean_object* v_asyncMode_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5024_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_5025_ = lean_ctor_get(v___x_5024_, 0);
lean_inc_ref(v_toEnvExtension_5025_);
v_asyncMode_5026_ = lean_ctor_get(v_toEnvExtension_5025_, 2);
lean_inc(v_asyncMode_5026_);
lean_dec_ref(v_toEnvExtension_5025_);
v___x_5027_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_5028_ = lean_box(0);
v___x_5029_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_5027_, v___x_5024_, v_env_5023_, v_asyncMode_5026_, v___x_5028_);
lean_dec(v_asyncMode_5026_);
return v___x_5029_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object* v_env_5030_){
_start:
{
lean_object* v___x_5031_; 
v___x_5031_ = l_Lean_getMainVersoModuleDocs(v_env_5030_);
return v___x_5031_;
}
}
static lean_object* _init_l_Lean_getVersoModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5032_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_5033_ = lean_box(0);
v___x_5034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5034_, 0, v___x_5033_);
lean_ctor_set(v___x_5034_, 1, v___x_5032_);
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object* v_env_5035_, lean_object* v_moduleName_5036_){
_start:
{
lean_object* v___x_5037_; 
v___x_5037_ = l_Lean_Environment_getModuleIdx_x3f(v_env_5035_, v_moduleName_5036_);
if (lean_obj_tag(v___x_5037_) == 0)
{
lean_object* v___x_5038_; 
v___x_5038_ = lean_box(0);
return v___x_5038_;
}
else
{
lean_object* v_val_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5050_; 
v_val_5039_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5050_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5050_ == 0)
{
v___x_5041_ = v___x_5037_;
v_isShared_5042_ = v_isSharedCheck_5050_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_val_5039_);
lean_dec(v___x_5037_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5050_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; uint8_t v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5048_; 
v___x_5043_ = lean_obj_once(&l_Lean_getVersoModuleDoc_x3f___closed__0, &l_Lean_getVersoModuleDoc_x3f___closed__0_once, _init_l_Lean_getVersoModuleDoc_x3f___closed__0);
v___x_5044_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v___x_5045_ = 1;
v___x_5046_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_5043_, v___x_5044_, v_env_5035_, v_val_5039_, v___x_5045_);
lean_dec(v_val_5039_);
if (v_isShared_5042_ == 0)
{
lean_ctor_set(v___x_5041_, 0, v___x_5046_);
v___x_5048_ = v___x_5041_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v___x_5046_);
v___x_5048_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
return v___x_5048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object* v_env_5051_, lean_object* v_moduleName_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l_Lean_getVersoModuleDoc_x3f(v_env_5051_, v_moduleName_5052_);
lean_dec(v_moduleName_5052_);
lean_dec_ref(v_env_5051_);
return v_res_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object* v_env_5056_, lean_object* v_snippet_5057_){
_start:
{
lean_object* v_docs_5058_; uint8_t v___x_5059_; 
lean_inc_ref(v_env_5056_);
v_docs_5058_ = l_Lean_getMainVersoModuleDocs(v_env_5056_);
v___x_5059_ = l_Lean_VersoModuleDocs_canAdd(v_docs_5058_, v_snippet_5057_);
if (v___x_5059_ == 0)
{
lean_object* v_terminalNesting_5060_; lean_object* v___x_5061_; lean_object* v___y_5063_; 
lean_dec_ref(v_snippet_5057_);
lean_dec_ref(v_env_5056_);
v_terminalNesting_5060_ = lean_ctor_get(v_docs_5058_, 1);
lean_inc(v_terminalNesting_5060_);
lean_dec_ref(v_docs_5058_);
v___x_5061_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__0));
if (lean_obj_tag(v_terminalNesting_5060_) == 0)
{
lean_object* v___x_5068_; 
v___x_5068_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___y_5063_ = v___x_5068_;
goto v___jp_5062_;
}
else
{
lean_object* v_val_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; 
v_val_5069_ = lean_ctor_get(v_terminalNesting_5060_, 0);
lean_inc(v_val_5069_);
lean_dec_ref(v_terminalNesting_5060_);
v___x_5070_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__1));
v___x_5071_ = l_Nat_reprFast(v_val_5069_);
v___x_5072_ = lean_string_append(v___x_5070_, v___x_5071_);
lean_dec_ref(v___x_5071_);
v___x_5073_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__8));
v___x_5074_ = lean_string_append(v___x_5072_, v___x_5073_);
v___y_5063_ = v___x_5074_;
goto v___jp_5062_;
}
v___jp_5062_:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5064_ = lean_string_append(v___x_5061_, v___y_5063_);
lean_dec_ref(v___y_5063_);
v___x_5065_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__2___closed__8));
v___x_5066_ = lean_string_append(v___x_5064_, v___x_5065_);
v___x_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5066_);
return v___x_5067_;
}
}
else
{
lean_object* v___x_5075_; lean_object* v_toEnvExtension_5076_; lean_object* v_asyncMode_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; 
lean_dec_ref(v_docs_5058_);
v___x_5075_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_5076_ = lean_ctor_get(v___x_5075_, 0);
lean_inc_ref(v_toEnvExtension_5076_);
v_asyncMode_5077_ = lean_ctor_get(v_toEnvExtension_5076_, 2);
lean_inc(v_asyncMode_5077_);
lean_dec_ref(v_toEnvExtension_5076_);
v___x_5078_ = lean_box(0);
v___x_5079_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5075_, v_env_5056_, v_snippet_5057_, v_asyncMode_5077_, v___x_5078_);
lean_dec(v_asyncMode_5077_);
v___x_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5080_, 0, v___x_5079_);
return v___x_5080_;
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
